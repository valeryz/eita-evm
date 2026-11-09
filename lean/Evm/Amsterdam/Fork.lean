/-
  Evm.Amsterdam — the post-Fusaka hard fork ("Amsterdam" execution-layer
  name; EIP-7773 umbrella).

  EELS reference: `ethereum/forks/amsterdam/`. Activation: `Unscheduled`
  on mainnet at time of writing (see `forks/amsterdam/__init__.py` line
  17: `FORK_CRITERIA: ForkCriteria = Unscheduled(order_index=3)`).

  This is **not** a BPO (Blob Parameter Only) hard fork — Amsterdam
  carries new EVM-level changes — but it is a smaller fork than Osaka.
  The EIPs (per `forks/amsterdam/__init__.py` and observed deltas in
  `vm/instructions/__init__.py`):

    * EIP-7928 — Block-Level Access Lists. A per-block authenticated
      summary of every account/storage access, deltas, and balance/code
      changes. Header gains `block_access_list_hash`; block body gains
      `block_access_list`. EELS pulls in a sizeable
      `block_access_lists.py` module with `BlockAccessListBuilder` /
      `build_block_access_list` / `hash_block_access_list`.
      The actual encoding/hashing is large and is **not** modelled
      here yet (a TODO at the next pass).
    * EIP-7954 — Increase Maximum Contract Size. `MAX_CODE_SIZE` rises
      from `0x6000` (24 576 bytes, EIP-170) to `0x10000` (65 536 bytes),
      `MAX_INIT_CODE_SIZE = 2 * MAX_CODE_SIZE`. EELS (execution-specs
      636b5f1): `forks/amsterdam/vm/interpreter.py` 80-81. NOT yet in the
      implementation (Create / Tx / the derived effects still cap at
      0x6000): `Evm.Amsterdam.Spec.Refinement.validDeployedCodeSize_sound_shape`
      stays open until it is.
    * EIP-7732 (slot-number plumbing) / SLOTNUM (0x4B) — exposes the
      consensus-layer slot number to the EVM. EELS:
      `forks/amsterdam/vm/instructions/block.py::slot_number` and the
      dispatch addition at `forks/amsterdam/vm/instructions/__init__.py`
      line 102 (`SLOTNUM = 0x4B`); gas = BASE (=2) per
      `gas.py::OPCODE_SLOTNUM`.
    * EIP-8024 — Stack-access instructions: DUPN (0xE6), SWAPN (0xE7),
      EXCHANGE (0xE8). Each reads a one-byte immediate. All three
      cost VERY_LOW (=3). EELS:
      `forks/amsterdam/vm/instructions/stack.py::dupn / swapn / exchange`.
    * EIP-7981 — calldata token re-pricing: each access-list address
      contributes `ACCESS_LIST_ADDRESS_FLOOR_TOKENS = 80` tokens, each
      storage key `ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS = 128`. Used
      in the `calculate_intrinsic_cost` floor calculation. EELS:
      `forks/amsterdam/transactions.py` lines 32-49 + 580-587.
    * Transfer-log auto-emission. EELS `forks/amsterdam/vm/__init__.py`
      lines 31-39 + 207-279 add `TRANSFER_TOPIC` / `BURN_TOPIC` constants
      and an `emit_transfer_log` helper. `process_message` (interpreter.py
      lines 274-278) emits a synthetic ERC-20-style Transfer log whenever
      `message.caller ≠ message.current_target ∧ message.value ≠ 0`.

  Scope of this Lean module: per the brief, when a fork is small we
  declare the constants and dispatch shape; full machinery (block
  access lists, intrinsic-gas re-pricing, automatic Transfer-log
  emission) lands in follow-up passes. The bits implemented here are:

    * EIP-7954's `MAX_CODE_SIZE` (`Evm.Amsterdam.Spec.maxCodeSize`).
    * `Vm/Effect.lean` intercepts 0x1E (CLZ from Osaka, falls through to
      Osaka), 0x4B (SLOTNUM), 0xE6/E7/E8 (DUPN/SWAPN/EXCHANGE).
    * Spec relations for SLOTNUM, DUPN, SWAPN, EXCHANGE and the
      `maxCodeSize` bump.

  Per-tx and block-level transitions are inherited verbatim from Osaka;
  the EIP-7928 block-access-list reconciliation is **not** implemented.
-/

import Evm.BaseTypes
import Evm.Osaka.Fork
import Evm.Amsterdam.Vm.Effect

namespace Evm.Amsterdam

/-! ## EIP-7981 calldata floor tokens (constants only — formula TODO) -/

/-- EELS `forks/amsterdam/transactions.py` lines 32-37. -/
def accessListAddressFloorTokens    : Nat := 80
/-- EELS `forks/amsterdam/transactions.py` lines 38-49. -/
def accessListStorageKeyFloorTokens : Nat := 128

/-! ## Per-transaction / block transition

    For now Amsterdam routes transactions and blocks through Osaka.
    The EIP-7981 intrinsic-gas floor re-pricing and the EIP-7928
    block-access-list construction / hash reconciliation are TODOs;
    refer to the Spec/ files for the relations they will be refined
    against. -/

abbrev Header     := Evm.Prague.Header
abbrev Block      := Evm.Prague.Block
abbrev BlockResult := Evm.Prague.BlockResult

/-- Run one transaction: `Evm.Frontier.Vm.Tx.run` at Amsterdam (fork ordinal 21) with
    Amsterdam's trampoline — Osaka's tx level (EELS Amsterdam's state-gas reservoir and block
    access list are not in the Lean spec; recorded in `Evm.Frontier.Vm.Tx`). -/
def processTransaction
    (state       : Evm.Prague.State)
    (header      : Evm.Prague.Header)
    (blockHashes : List Evm.Hash32)
    (sender      : Evm.Address)
    (tx          : Evm.Prague.Transaction) :
    Except String (Evm.Prague.State × Evm.Frontier.TxResult) :=
  Evm.Prague.processTransaction state header blockHashes sender tx 21 Evm.Amsterdam.Vm.Effect.trampoline

def applyBlock (state : Evm.Prague.State) (block : Block) :
    Except String BlockResult :=
  -- TODO: EIP-7928 BAL reconciliation against header.block_access_list_hash.
  Evm.Osaka.applyBlock state block

end Evm.Amsterdam
