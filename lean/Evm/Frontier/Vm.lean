/-
  Evm.Frontier.Vm — execution environment record + Vm umbrella.

  EELS reference: ethereum/frontier/vm/__init__.py. The `Vm` record holds
  the per-frame state during execution; `Message` carries the inputs.
-/

import Evm.BaseTypes
import Evm.Frontier.ForkTypes
import Evm.Frontier.State
import Evm.Frontier.Vm.Exceptions
import Evm.Frontier.Vm.Stack
import Evm.Frontier.Vm.Memory
import Evm.Frontier.Vm.Gas
import Evm.Frontier.Vm.Runtime

namespace Evm.Frontier.Vm

/-- Per-call inputs (the EVM "Message"). -/
structure Message where
  caller        : Evm.Address
  /-- The callee. `none` denotes a contract-creation call. -/
  target        : Option Evm.Address
  /-- The address whose storage and balance the running code operates on.
      Differs from `target` for CALLCODE (and, post-Frontier, DELEGATECALL). -/
  currentTarget : Evm.Address
  value         : Evm.U256
  data          : Evm.Bytes
  code          : Evm.Bytes
  gas           : Gas.Gas
  depth         : Nat
  /-- EIP-214 static-call flag (Byzantium+). When `true`, the frame
      is read-only: SSTORE, SELFDESTRUCT, LOG, CREATE, and any CALL
      with `value > 0` raise an exception. Sub-frames inherit `true`
      (a child of a static frame is itself static). Always `false`
      in pre-Byzantium forks. -/
  isStatic      : Bool             := false
  deriving Inhabited

/-- A single log record emitted by the LOG0..LOG4 opcodes. -/
structure Log where
  address : Evm.Address
  topics  : List Evm.U256
  data    : Evm.Bytes
  deriving Inhabited

/-- Transaction-level environment. Persists across all call frames in a
    single transaction; sub-frames inherit it, so cumulative effects
    (logs emitted, accounts to-be-deleted, refund counter) are visible
    everywhere and survive sub-frame merges as a single value.

    Mirrors EELS `frontier.vm.Environment`. -/
structure Environment where
  origin          : Evm.Address
  gasPrice        : Evm.U256
  coinbase        : Evm.Address
  number          : Nat
  difficulty      : Nat
  gasLimit        : Nat
  timestamp       : Nat
  /-- The 256 most recent ancestor block hashes, indexed by descending
      block number. Used by the BLOCKHASH opcode. -/
  blockHashes     : List Evm.Hash32  := []
  state           : Evm.Frontier.State
  /-- Emitted logs (LOG0..LOG4). Reverted along with state when a frame
      fails; merged into the parent on success. -/
  logs            : List Log         := []
  /-- Accounts queued for deletion by SELFDESTRUCT in this transaction.
      Tracked here (not per-frame) so that the "first time per (account,
      tx)" refund rule actually sees prior frames' selfdestructs. -/
  selfDestructSet : List Evm.Address := []
  /-- Refund accumulator (SSTORE clears, SELFDESTRUCT). Applied at the
      end of the transaction, capped at gasUsed/2. -/
  refundCounter   : Nat              := 0
  /-- EIP-161 touched-account set (only populated at SpuriousDragon and
      later — left empty by the Frontier / Homestead / TW interpreters).
      Accounts in this list that are empty at end-of-tx are swept by
      `SD.sweepEmptyAccounts`. -/
  touched         : List Evm.Address := []
  /-- EIP-4399 prev-randao (Paris+). Beacon-chain random value exposed
      by the DIFFICULTY opcode (0x44), which is renamed PREVRANDAO at
      Paris and reads this field instead of `difficulty`. Defaults to
      `0` so pre-Paris fork code that never sets it still typechecks;
      the Paris dispatcher overrides 0x44 to push this value. See EELS
      `forks/paris/vm/instructions/block.py` `prev_randao` (line 168ff)
      and `forks/paris/fork.py` `state_transition` (line 180, the
      `prev_randao=block.header.prev_randao` plumbing into
      `BlockEnvironment`). -/
  prevRandao      : Evm.Hash32        := 0
  /-- EIP-1344 (Istanbul+): chain identifier exposed by the CHAINID
      opcode. Defaults to `1` (mainnet) so older forks that never read
      the field keep their existing semantics. EELS reference:
      `forks/istanbul/vm/__init__.py` `BlockEnvironment.chain_id` (the
      field is plumbed via `prepare_message`). -/
  chainId         : Evm.U256          := 1
  /-- EIP-2200 (Istanbul+): snapshot of `state` at the start of the
      enclosing transaction. The net-metering SSTORE rules need
      `original_value` — the slot's value at tx start, not the most
      recent committed write — to decide whether the slot is "clean"
      or "dirty". Pre-Istanbul interpreters never consult this field;
      we leave it at the empty state there. EELS reference:
      `state_tracker.get_storage_original` in
      `forks/istanbul/state_tracker.py`. -/
  originalState   : Evm.Frontier.State := {}
  /-- EIP-2929 (Berlin+): set of addresses warmed in this transaction.
      Pre-Berlin forks ignore this field. EELS reference:
      `forks/berlin/state_tracker.py` `accessed_addresses`. -/
  accessedAddresses    : List Evm.Address              := []
  /-- EIP-2929 (Berlin+): set of (address, slot) pairs warmed in this
      transaction. Pre-Berlin forks ignore. EELS reference:
      `forks/berlin/state_tracker.py` `accessed_storage_keys`. -/
  accessedStorageKeys  : List (Evm.Address × Evm.U256) := []
  /-- EIP-2929 (Berlin+) lazy "original value" cache for SSTORE net
      metering: the first time a (addr, slot) is read or written in
      the transaction, the value is snapshotted here so EIP-2200's
      `original_value` term has a stable reference. EELS uses a
      snapshot stack on the State type itself; we expose it as a
      separate field keyed by `(addr, slot)`. Pre-Berlin SSTORE
      paths don't touch this. -/
  storageOriginals     : List ((Evm.Address × Evm.U256) × Evm.U256) := []
  /-- EIP-1559 (London+): base fee per gas burned by every tx in this
      block. Pre-London forks read this as 0 and ignore. EELS reference:
      `forks/london/blocks.py` `Header.base_fee_per_gas`. -/
  baseFeePerGas        : Nat                           := 0
  /-- EIP-1153 (Cancun+): transient storage `(addr, slot) → value`,
      cleared at end of tx. Pre-Cancun forks never read or write this.
      EELS reference: `forks/cancun/vm/instructions/storage.py`
      `tload` / `tstore`. -/
  transientStorage     : List ((Evm.Address × Evm.U256) × Evm.U256) := []
  /-- EIP-6780 (Cancun+): addresses CREATEd in the current transaction.
      SELFDESTRUCT only fully destroys the account if its address is
      in this set; otherwise the call is a balance transfer and the
      account survives. Pre-Cancun forks ignore this distinction. EELS
      reference: `forks/cancun/vm/instructions/system.py`
      `selfdestruct`. -/
  createdAccounts      : List Evm.Address              := []
  /-- EIP-4844 (Cancun+): blob versioned hashes for the current tx
      (from `BlobTransaction.blob_versioned_hashes`). BLOBHASH opcode
      reads here; out-of-bounds → 0. Pre-Cancun: always empty. EELS
      reference: `forks/cancun/vm/instructions/block.py` `blob_hash`. -/
  blobVersionedHashes  : List Evm.Hash32               := []
  /-- EIP-4844 (Cancun+): blob gas base fee for the current block,
      derived from `header.excess_blob_gas` via `fake_exponential`.
      BLOBBASEFEE opcode (0x4a) pushes this value. Pre-Cancun: 0.
      EELS reference: `forks/cancun/vm/gas.py`
      `calculate_blob_gas_price`. -/
  blobBaseFee          : Nat                           := 0
  /-- EIP-4844 (Cancun+): the parent block's `excess_blob_gas`, used
      to derive `blobBaseFee`. Pre-Cancun: 0. -/
  excessBlobGas        : Nat                           := 0
  /-- Amsterdam (EIP-7732/SLOTNUM): consensus-layer slot number for the
      current block. Plumbed from `Header.slot_number` via
      `BlockEnvironment` in EELS
      `forks/amsterdam/fork.py::execute_block` (the `BlockEnvironment(...,
      slot_number=block.header.slot_number, ...)` construction) and read
      by the 0x4B SLOTNUM opcode in
      `forks/amsterdam/vm/instructions/block.py::slot_number`. Pre-Amsterdam
      forks never read this field; defaults to `0`. -/
  slotNumber           : Nat                           := 0
  /-- Optimism Granite+ (OP-stack): if `some n`, the bn256 pairing
      precompile (0x08) refuses inputs strictly longer than `n` bytes.
      The Granite hardfork sets this to `some 1536` (= 8 pairs × 192
      bytes); every other fork leaves it `none` (no cap, gas-only
      limit). Read by the precompile dispatcher in
      `Evm/Cancun/Vm/Effect.lean` `trampoline`. EELS-equivalent:
      `op-geth/core/vm/contracts.go` `bn256PairingGranite`. -/
  opBn256PairingCap    : Option Nat                    := none
  /-- Optimism Fjord+: routes 0x100 → P256VERIFY at the callLike
      dispatch point, charging the given gas (`none`: 0x100 is an
      ordinary account) — the fork's `Evm.Optimism.Fjord.Spec.p256VerifyGas`:
      RIP-7212's 3450 Fjord..Isthmus, EIP-7951's 6900 from Azul. Stored
      as data (not a function-bearing list) so `Environment` stays
      first-order — Auto/cvc5 can't handle function types in SMT
      translation. The verifier is `Evm.Crypto.p256VerifyWith`. -/
  opP256VerifyGas      : Option Nat                   := none
  /-- Prague (Isthmus on OP) EIP-7702: enables sub-CALL resolution
      of the `0xef 0x01 0x00 || delegated_address` designator. When
      true, the trampoline's `callLike` branch checks the callee's
      code for the designator; if matched, substitutes the
      delegated address's code as the callee's `msg.code` AND
      charges the extra EIP-2929 access cost for the delegated
      address. Defaults `false` for pre-Prague forks. -/
  pragueDelegation     : Bool                         := false
  /-- Debug-only: when true, the EVM emits a `dbg_trace` per
      `step1` call with pc / opcode / gasLeft / top-of-stack. Used
      by tooling that diffs our per-step trace against op-geth's
      `structLogTracer` to localise divergence on real Base blocks.
      Defaults false so production paths see zero overhead. -/
  debugTrace           : Bool                         := false
  deriving Inhabited

/-- Live execution state for one EVM call frame. -/
structure Evm where
  pc              : Nat        := 0
  stack           : Stack      := Stack.empty
  memory          : Memory     := Memory.empty
  gasLeft         : Gas.Gas
  message         : Message
  env             : Environment
  returnData      : Evm.Bytes  := Evm.Bytes.empty
  /-- Per-frame JUMPDEST bitmap: byte `i` is `1` iff position `i`
      is a valid 0x5b JUMPDEST. Default `empty` means uncached —
      JUMP / JUMPI fall back to scanning `message.code` linearly,
      O(n) per jump. `Evm.fresh` populates this so JUMP-heavy
      contracts (e.g. `JUMPDEST_AttackwithJump`) finish in time. -/
  jumpDests       : Evm.Bytes  := Evm.Bytes.empty
  halted          : Bool       := false
  /-- EIP-140 revert flag (Byzantium+). When set alongside `halted`,
      the frame terminated via the REVERT opcode rather than STOP /
      RETURN: state mutations are NOT merged into the parent, but
      `output` IS preserved as the parent's returndata and gas is
      not fully consumed. Always `false` in pre-Byzantium forks. -/
  reverted        : Bool       := false
  output          : Evm.Bytes  := Evm.Bytes.empty
  deriving Inhabited

namespace Evm

/-- Fresh execution frame for `message` against `env`. Pre-computes
    the JUMPDEST bitmap for `message.code` so JUMP/JUMPI hits an
    O(1) lookup instead of rescanning the code each time. -/
def fresh (message : Message) (env : Environment) : Evm :=
  { gasLeft   := message.gas,
    message   := message,
    env       := env,
    jumpDests := Runtime.jumpDestBitmap message.code }

end Evm

end Evm.Frontier.Vm
