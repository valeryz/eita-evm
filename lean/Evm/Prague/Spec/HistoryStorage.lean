/-
  Evm.Prague.Spec.HistoryStorage — EIP-2935 BLOCKHASH from a system
  contract.

  EELS reference: `forks/prague/fork.py::apply_body` (the early-block
  system call to `HISTORY_STORAGE_ADDRESS` after the beacon-roots
  call), and `forks/prague/vm/instructions/block.py::block_hash` (the
  re-wired BLOCKHASH opcode handler that now SLOADs from the history
  contract instead of walking `evm.env.block_hashes`).

  Two parts to EIP-2935:

    1. At the start of every Prague+ block, a SYSTEM call into
       `HISTORY_STORAGE_ADDRESS = 0x0000F90827F1C53a10cb7A02335B175320002935`
       with calldata = `parent_block_hash` (32 bytes BE). The contract
       stores the value at storage slot
       `block_number % HISTORY_SERVE_WINDOW` where
       `HISTORY_SERVE_WINDOW = 8191`. After ~27 hours of operation
       the contract's storage holds the most recent 8192 block
       hashes (ring buffer).

    2. The BLOCKHASH opcode (0x40) is repointed: instead of consulting
       `evm.env.block_hashes` (a 256-entry chain walk), it issues an
       implicit SLOAD into `HISTORY_STORAGE_ADDRESS` at slot
       `n % HISTORY_SERVE_WINDOW` for the requested block `n`,
       provided `n` is in the valid range
       `[current - HISTORY_SERVE_WINDOW + 1, current - 1]`.

  Gas:
    * BLOCKHASH opcode: still 20 gas (`Gas.blockHash`); the implicit
      SLOAD is not separately charged because the EIP designates the
      access "implicit".
    * System call: 30M gas budget, like all SYSTEM calls.

  Inheritance: introduced at Prague.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm

namespace Evm.Prague.Spec

open Evm.Frontier.Vm
open Evm.Frontier (State)

/-! ## Addresses and constants -/

/-- EIP-2935 history-storage contract address. EELS:
    `forks/prague/fork.py::HISTORY_STORAGE_ADDRESS`. -/
def historyStorageAddress : Evm.Address :=
  Evm.Address.ofNat 0x0000F90827F1C53a10cb7A02335B175320002935

/-- The ring-buffer length. EELS:
    `forks/prague/fork.py::HISTORY_SERVE_WINDOW = 8191`. -/
def historyServeWindow : Nat := 8191

/-! ## System-call wiring (parallel to BeaconRoot)

    At block-entry, the SYSTEM caller invokes
    `HISTORY_STORAGE_ADDRESS` with the parent block's hash. We spec
    the call shape — the contract itself does the storage update. -/

/-- Calldata for the history-storage system call: 32 bytes BE of the
    parent block hash. -/
def historyStorageCalldata (parentHash : Evm.Hash32) : Evm.Bytes :=
  Evm.U256.toBytesBE parentHash

/-! ## BLOCKHASH re-direction

    `IsBlockhashViaHistory` describes the Prague BLOCKHASH semantics:
    the opcode pops `n : U256`, looks up
    `state.getStorage(HISTORY_STORAGE_ADDRESS, n % HISTORY_SERVE_WINDOW)`,
    and pushes the result.

    A request outside the valid range returns 0 — same as pre-Prague
    BLOCKHASH, just with a different "out of range" criterion (Prague
    uses a fixed 8192-window instead of always-256).  -/

/-- The valid range of block numbers that BLOCKHASH can answer at
    Prague: `[currentBlock - HISTORY_SERVE_WINDOW, currentBlock - 1]`.
    Queries outside this range return 0. -/
def IsBlockhashRangeValid (currentBlock requested : Nat) : Prop :=
  requested + 1 ≤ currentBlock ∧
  currentBlock ≤ requested + historyServeWindow

/-- The Prague BLOCKHASH lookup. Returns the storage value at
    `(HISTORY_STORAGE_ADDRESS, requested % HISTORY_SERVE_WINDOW)` if
    `requested` is in range; otherwise 0.

    Note: at impl time the contract's storage table is populated by
    the per-block system call (which we spec separately); this
    function reads whatever is there. -/
def blockhashFromHistory (state : State) (currentBlock requested : Nat) :
    Evm.U256 :=
  if requested + 1 ≤ currentBlock ∧ currentBlock ≤ requested + historyServeWindow then
    let slot := Evm.U256.ofNat (requested % historyServeWindow)
    state.getStorage historyStorageAddress slot
  else
    0

/-- Prague BLOCKHASH (0x40) opcode step relation. Same arity and gas
    as Frontier (`Gas.blockHash = 20`); only the lookup source
    changes. -/
def IsBlockhashStep (evm evm' : Evm) : Prop :=
  ∃ requested rest,
    evm.stack = requested :: rest ∧
    rest.length < stackLimit ∧
    evm.gasLeft ≥ Gas.blockHash ∧
    let result := blockhashFromHistory evm.env.state evm.env.number requested.toNat
    evm' = { evm with
      stack   := result :: rest,
      gasLeft := evm.gasLeft - Gas.blockHash,
      pc      := evm.pc + 1 }

/-! ## Notes

    * The "implicit SLOAD" the EIP describes is *not* an extra gas
      charge — it's absorbed into the unchanged 20-gas BLOCKHASH
      cost. An impl that adds a 2100-gas cold-access surcharge here
      fails the spec.

    * The pre-Prague chain-walk fallback (consulting
      `env.blockHashes`) is REMOVED at Prague — even if the history
      contract's storage is empty (genesis, first ~27 hours), the
      opcode returns 0, NOT the legacy value. The genesis-stub
      issue is documented in EIP-2935 §"Backwards compatibility":
      "The transition window will have BLOCKHASH return 0 for
      queries beyond the contract's recorded range." -/

end Evm.Prague.Spec
