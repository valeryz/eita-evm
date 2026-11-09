/-
  Evm.Prague.Fork — top-level state transition for a Prague block.

  EELS reference: ethereum/forks/prague/fork.py.
  Activation: timestamp 1,746,612,311 (mainnet, 2025-05-07).

  This is the Pectra hard fork — the largest single-fork addition since
  Berlin. The block-level transition extends Cancun's `apply_body`
  with three new system-contract calls and a new header field
  (`requestsHash`). Sequencing (per EELS `apply_body`):

      1. SYSTEM call into BEACON_ROOTS_ADDRESS, writing the parent
         beacon block root to its storage (EIP-4788 — predates Prague,
         repeated here for completeness).
      2. SYSTEM call into HISTORY_STORAGE_ADDRESS, writing the parent
         block's hash (EIP-2935 — new in Prague; replaces the
         BLOCKHASH opcode's chain walk).
      3. Transactions, in order.
      4. Withdrawals (EIP-4895 — Shanghai shape; credit `amount`
         Gwei × 10⁹ wei to each `recipient`).
      5. SYSTEM call into WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS;
         return data parsed into EIP-7002 withdrawal requests.
      6. SYSTEM call into CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS;
         return data parsed into EIP-7251 consolidation requests.
      7. Deposit logs harvested from receipts → EIP-6110 deposit
         requests.
      8. `requestsHash = compute_requests_hash(deposits ++
         withdrawalRequests ++ consolidationRequests)`. The expected
         header `requestsHash` is checked against this.

  The system calls (steps 1, 2, 5, 6) are `Evm.Frontier.Vm.System` (EELS
  `process_unchecked_system_transaction` / `process_checked_system_transaction`).
  Steps 3 and 7 are not run at this layer: typed-tx decoding is `Replay.lean`'s, so
  `applyBlock` runs an empty body and has no deposit logs.

  Per-transaction processing (`process_transaction`) is
  `Evm.Frontier.Vm.Tx.run` at Prague: every tx type, the EIP-1559 fee
  split, the blob fee, EIP-7702's authorization list and delegation,
  EIP-7623's calldata floor.
-/

import Evm.BaseTypes
import Evm.Frontier.State
import Evm.Frontier.Transactions
import Evm.Frontier.Vm.Tx
import Evm.Frontier.Vm.System
import Evm.Frontier.Vm.Block
import Evm.Cancun.Vm.Effect
import Evm.Prague.State
import Evm.Prague.Blocks
import Evm.Prague.Transactions
import Evm.Prague.Vm.PrecompiledContracts
import Evm.Prague.Vm.Effect
import Evm.Prague.Utils.Authorization
import Evm.Prague.Requests
import Evm.Prague.Spec.CalldataCost

namespace Evm.Prague



/-! ## System contract calls

    EELS `forks/prague/fork.py` `apply_body` 742-753 (EIP-4788, EIP-2935:
    `process_unchecked_system_transaction`) and `process_general_purpose_requests` 767-811
    (EIP-7002, EIP-7251: `process_checked_system_transaction`, a non-empty output is the
    type's request) — `Evm.Frontier.Vm.System` at the fork, under the EELS rule (nothing
    warm, GASPRICE the base fee), on the block environment. -/

/-- An unchecked system call (EIP-4788, EIP-2935): the world after it. -/
def uncheckedCall (k : Nat) (runSub : Evm.Frontier.Vm.Evm → Except Evm.Frontier.Vm.Exception Evm.Frontier.Vm.Evm)
    (env : Evm.Frontier.Vm.Environment) (state : Evm.Prague.State) (target : Evm.Address)
    (data : Evm.Bytes) : Evm.Prague.State :=
  { state with inner := (Evm.Frontier.Vm.System.unchecked k env state.inner (Evm.Frontier.Vm.System.eels env)
      target data (Evm.Frontier.Vm.Tx.table k) runSub).1 }

/-- A checked system call (EIP-7002, EIP-7251): the world after it and the request it
    returns (none for an empty output), or the block is invalid. -/
def requestCall (k : Nat) (runSub : Evm.Frontier.Vm.Evm → Except Evm.Frontier.Vm.Exception Evm.Frontier.Vm.Evm)
    (env : Evm.Frontier.Vm.Environment) (state : Evm.Prague.State) (target : Evm.Address)
    (type : UInt8) : Except String (Evm.Prague.State × List Evm.Prague.Request) := do
  let (st, out) ← Evm.Frontier.Vm.System.checked k env state.inner (Evm.Frontier.Vm.System.eels env)
    target Evm.Bytes.empty (Evm.Frontier.Vm.Tx.table k) runSub
  return ({ state with inner := st }, Evm.Prague.Requests.ofOutput type out)

/-- EIP-6110 deposit harvesting from receipt logs. Stub (no receipts
    are tracked yet at this layer). -/
def harvestDepositRequests (_logs : List Evm.Frontier.Vm.Log) :
    List Evm.Prague.Request :=
  []

/-! ## Per-transaction processing -/

/-- The block environment of a Prague header (EIP-4844's blob base fee at fork `k`'s blob
    schedule — EIP-7691 from Prague, EIP-7892's BPO entries after Osaka). -/
def blockEnv (header : Header) (blockHashes : List Evm.Hash32) (k : Nat := 17) :
    Evm.Frontier.Vm.Environment :=
  let ebg := header.excessBlobGas.toNat
  Evm.Frontier.Vm.Tx.blockEnv header.coinbase header.number.toNat header.difficulty.toNat
    header.gasLimit.toNat header.timestamp.toNat blockHashes header.baseFeePerGas.toNat
    header.prevRandao
    (Evm.CL.GasEmit.blobBaseFee.eval (fun y =>
      if y = "excess-blob-gas" then ebg else if y = "fork-ord" then k else 0)) ebg

/-- Run one transaction (EELS `process_transaction`): the one definition every fork's is,
    `Evm.Frontier.Vm.Tx.run`, at Prague (fork ordinal 17: EIP-7702's authorization list
    and delegations, EIP-7623's calldata floor, EIP-2537's precompiles), with the Cancun
    trampoline over Prague's precompile table and `recoverAuthority` for the
    authorizations. Osaka (18) and Amsterdam (21) pass their ordinal and trampoline. -/
def processTransaction
    (state       : Evm.Prague.State)
    (header      : Header)
    (blockHashes : List Evm.Hash32)
    (sender      : Evm.Address)
    (tx          : Evm.Prague.Transaction)
    (k           : Nat := 17)
    (runSub      : Evm.Frontier.Vm.Evm → Except Evm.Frontier.Vm.Exception Evm.Frontier.Vm.Evm :=
                     Evm.Cancun.Vm.Effect.trampoline (Evm.Frontier.Vm.Call.precompiles 17)) :
    Except String (Evm.Prague.State × Evm.Frontier.TxResult) := do
  let r ← Evm.Frontier.Vm.Tx.run k (blockEnv header blockHashes k) state.inner sender
    (Evm.Frontier.Vm.Tx.ofPrague tx) (Evm.Frontier.Vm.Tx.table k) runSub
    Evm.Prague.Utils.recoverAuthority
  return ({ state with inner := r.state }, r)

private partial def processAll
    (state : Evm.Prague.State) (header : Header)
    (blockHashes : List Evm.Hash32) (txs : List Evm.Prague.Transaction)
    (gasAcc : Nat) (logsAcc : List Evm.Frontier.Vm.Log) :
    Except String (Evm.Prague.State × Nat × List Evm.Frontier.Vm.Log) :=
  match txs with
  | [] => .ok (state, gasAcc, logsAcc)
  | tx :: txs' => do
    -- Sender recovery isn't wired yet for typed Prague txs (each tx
    -- type has its own signing-hash schema; EELS dispatches on
    -- `tx.type`). For now use a sentinel zero address — sufficient
    -- for shape testing; real bring-up will plumb
    -- `Prague.Utils.recover_sender`.
    let sender : Evm.Address := 0
    let (state, r) ← processTransaction state header blockHashes sender tx
    processAll state header blockHashes txs' (gasAcc + r.gasUsed)
      (logsAcc ++ r.logs)

/-! ## Withdrawals (EIP-4895)

    `Evm.Frontier.Vm.Block.processWithdrawals` at Prague: each credits `amount * 10^9`
    wei (the amount is in gwei) to `address`, and an account left empty goes. -/

def applyWithdrawals (state : Evm.Prague.State) (ws : List Withdrawal) :
    Evm.Prague.State :=
  { state with inner := Evm.Frontier.Vm.Block.processWithdrawals 17 state.inner
                          (ws.map fun w => (w.address, w.amount.toNat)) }

/-! ## Block-level transition -/

/-- Result of executing a Prague block. -/
structure BlockResult where
  state         : Evm.Prague.State
  gasUsed       : Nat
  logs          : List Evm.Frontier.Vm.Log
  requestsHash  : Evm.Hash32
  deriving Inhabited

/-- Apply a full Prague block. Sequencing per EELS
    `ethereum/forks/prague/fork.py::apply_body`:

      1. beacon-root system call.
      2. history-storage system call (EIP-2935).
      3. all transactions in order.
      4. withdrawals.
      5. withdrawal-requests system call.
      6. consolidation-requests system call.
      7. compute requestsHash from (deposits || withdrawalReqs ||
         consolidationReqs).
      8. verify requestsHash matches header.

    The system calls are `Evm.Frontier.Vm.System` (above); the transactions are not run here
    (an empty body: typed-tx decoding is `Replay.lean`'s, which drives them through
    `Tx.run`), so deposit-log scanning has no logs. Fork `k` and its trampoline `runSub`:
    Prague's by default, Osaka passes its own. -/
def applyBlock (state : Evm.Prague.State) (block : Block) (k : Nat := 17)
    (runSub : Evm.Frontier.Vm.Evm → Except Evm.Frontier.Vm.Exception Evm.Frontier.Vm.Evm :=
      Evm.Cancun.Vm.Effect.trampoline (Evm.Frontier.Vm.Call.precompiles 17)) :
    Except String BlockResult := do
  -- (0) Post-merge invariants.
  if ¬ block.ommers.isEmpty then
    .error "Prague block has ommers (forbidden post-merge)"
  let env := blockEnv block.header ([] : List Evm.Hash32) k
  -- (1) EIP-4788 beacon-root.
  let state := uncheckedCall k runSub env state Evm.Prague.Requests.beaconRootsAddress
    (Evm.U256.toBytesBE block.header.parentBeaconBlockRoot)
  -- (2) EIP-2935 history storage: the parent hash.
  let state := uncheckedCall k runSub env state Evm.Prague.Requests.historyStorageAddress
    (Evm.U256.toBytesBE block.header.parentHash)
  -- (3) The transactions: not decoded at this layer (see above).
  let txs : List Evm.Prague.Transaction := []
  let (state, gasUsed, logs) ← processAll state block.header
    ([] : List Evm.Hash32) txs 0 []
  -- (4) Withdrawals.
  let state := applyWithdrawals state block.withdrawals
  -- (5) EIP-6110 deposits, (6) EIP-7002 withdrawal requests, (7) EIP-7251 consolidations.
  let dreqs := harvestDepositRequests logs
  let (state, wreqs) ← requestCall k runSub env state
    Evm.Prague.Requests.withdrawalRequestPredeploy Evm.Prague.Requests.withdrawalRequestType
  let (state, creqs) ← requestCall k runSub env state
    Evm.Prague.Requests.consolidationRequestPredeploy Evm.Prague.Requests.consolidationRequestType
  let computedHash := Evm.Prague.Requests.computeRequestsHash (dreqs ++ wreqs ++ creqs)
  if computedHash ≠ block.header.requestsHash then
    .error "requestsHash mismatch"
  return { state := state, gasUsed := gasUsed, logs := logs,
           requestsHash := computedHash }

end Evm.Prague
