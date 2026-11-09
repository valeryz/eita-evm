/-
  Evm.Cancun.Fork — top-level state transition for a Cancun block.

  EELS reference:
    - `forks/cancun/fork.py:apply_body`        (block-level orchestration)
    - `forks/cancun/fork.py:process_transaction`
    - `forks/cancun/fork.py:process_system_transaction`
    - `forks/cancun/fork.py:check_transaction`
    - `forks/cancun/fork.py:validate_blob_gas_price`

  Activation: timestamp 1,710,338,135 (2024-03-13). EIPs:
    - 1153 transient storage
    - 4788 beacon block root system contract
    - 4844 blob transactions + blob gas market
    - 5656 MCOPY
    - 6780 SELFDESTRUCT only-same-tx
    - 7516 BLOBBASEFEE

  Block-level orchestration (`apply_body`, with EELS line numbers
  matching the May 2024 snapshot):

      1. process_system_transaction(BEACON_ROOTS_ADDRESS,
                                    block.parent_beacon_block_root)
                                                              # ~line 540
      2. for tx in block.transactions:
            process_transaction(...)                          # ~line 555
      3. for w in block.withdrawals:
            process_withdrawal(w)                             # ~line 600
      4. distribute_block_rewards(...)
         # Post-merge: block reward is 0. We still call into Frontier's
         #  reward helper for ommers (always empty post-merge but the
         #  shape is preserved).

  STATUS NOTES:
    - The beacon-roots system call (step 1) is EELS
      `process_unchecked_system_transaction` (`Evm.Frontier.Vm.System.unchecked`
      at Cancun, the EELS rule: nothing warm, GASPRICE the base fee).
    - Transactions (every type, the blob fee and its validation) are
      `Evm.Frontier.Vm.Tx.run` at Cancun (`processTransaction`,
      `applyBlockTyped`).
    - Blob market math (`calculateExcessBlobGas`,
      `calculateBlobGasPrice`) is implemented in `Vm/Gas.lean`
      and is set on the environment at block entry; the *header
      validation* leg (parent_excess_blob_gas + parent_blob_gas_used
      → header.excess_blob_gas equation) is **not** enforced here —
      the driver passes `header.excessBlobGas` straight through.
-/

import Evm.BaseTypes
import Evm.Frontier.Fork
import Evm.Homestead.Fork
import Evm.TangerineWhistle.Fork
import Evm.SpuriousDragon.Utils.Signature
import Evm.SpuriousDragon.Vm.Interpreter
import Evm.SpuriousDragon.Fork
import Evm.Byzantium.Fork
import Evm.Byzantium.Vm.Effect
import Evm.London.Fork
import Evm.Shanghai.Withdrawals
import Evm.Shanghai.Fork
import Evm.Cancun.Blocks
import Evm.Cancun.Transactions
import Evm.Cancun.State
import Evm.Cancun.Vm.Gas
import Evm.Cancun.Vm.PrecompiledContracts
import Evm.Cancun.Vm.Effect
import Evm.Frontier.Vm.System

namespace Evm.Cancun

open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Log Environment Message Evm)
open Evm.Cancun (Header Block Transaction BlobTransaction)

/-! ## Constants

    EELS `forks/cancun/fork.py` plus EIP-4788. -/

/-- EIP-4788 beacon-roots system contract address (`0x000F3DF6…BEAC02`). -/
def beaconRootsAddress : Evm.Address :=
  Evm.Address.ofNat 0x000F3DF6D732807EF1319FB7B8BB8522D0BEAC02

/-! ## Beacon-root system call (EIP-4788)

    EELS `forks/cancun/fork.py` `apply_body` 646-650: `process_unchecked_system_transaction`
    to `BEACON_ROOTS_ADDRESS` with the parent beacon block root — `System.unchecked` at
    Cancun under the EELS rule. -/

/-- The beacon-roots system call (the world after it; its success does not matter). -/
def beaconRootCall (state : State) (env : Environment) (parentBeaconBlockRoot : Evm.Hash32) : State :=
  (Evm.Frontier.Vm.System.unchecked 16 env state (Evm.Frontier.Vm.System.eels env) beaconRootsAddress
    (Evm.U256.toBytesBE (Evm.U256.ofNat parentBeaconBlockRoot.toNat)) (Evm.Frontier.Vm.Tx.table 16)
    (Evm.Cancun.Vm.Effect.trampoline Evm.Cancun.Vm.PrecompiledContracts.lookup)).1

/-! ## Per-transaction execution -/

/-- The block environment of a Cancun header: EIP-4844's blob base fee from the header's
    excess blob gas (EELS `calculate_blob_gas_price`, once per block). -/
def blockEnv (header : Header) (blockHashes : List Evm.Hash32) : Environment :=
  Evm.Frontier.Vm.Tx.blockEnv header.coinbase header.number 0 header.gasLimit header.timestamp
    blockHashes header.baseFeePerGas.toNat header.mixDigest
    (Evm.Cancun.Vm.Gas.calculateBlobGasPrice header.excessBlobGas) header.excessBlobGas

/-- Run one transaction (EELS `process_transaction`): the one definition every fork's is,
    `Evm.Frontier.Vm.Tx.run`, at Cancun (fork ordinal 16: EIP-4844's blob fee and blob
    hashes, EIP-1153's transient storage and EIP-6780's created set start empty), with
    Cancun's trampoline and precompile table. -/
def processTransaction (state : State) (header : Header) (blockHashes : List Evm.Hash32)
    (sender : Evm.Address) (tx : Evm.Frontier.Vm.Tx.Tx) : Except String Evm.Frontier.TxResult :=
  Evm.Frontier.Vm.Tx.run 16 (blockEnv header blockHashes) state sender tx
    (Evm.Frontier.Vm.Tx.table 16) (Evm.Cancun.Vm.Effect.trampoline Evm.Cancun.Vm.PrecompiledContracts.lookup)
    (fun _ => none)

/-- Drive all the legacy-shaped transactions in a Cancun block. -/
private partial def processAll
    (state : State) (header : Header) (blockHashes : List Evm.Hash32)
    (txs : List Evm.Frontier.Transaction)
    (gasAcc : Nat) (logsAcc : List Log) :
    Except String (State × Nat × List Log) :=
  match txs with
  | [] => .ok (state, gasAcc, logsAcc)
  | tx :: txs' => do
    let sender ← match Evm.SpuriousDragon.Utils.recoverSender tx with
      | some s => .ok s
      | none   => .error "invalid signature"
    let r ← processTransaction state header blockHashes sender (Evm.Frontier.Vm.Tx.ofLegacy tx)
    processAll r.state header blockHashes txs'
      (gasAcc + r.gasUsed) (logsAcc ++ r.logs)

/-! ## EIP-4895 withdrawals -/

def processWithdrawals (state : State) (ws : List Evm.Shanghai.Withdrawal) :
    State :=
  Evm.Frontier.Vm.Block.processWithdrawals 16 state (Evm.Shanghai.withdrawalPairs ws)

/-! ## Block driver

    EELS `forks/cancun/fork.py:apply_body` (May 2024 snapshot):

      1. (EIP-4788) system call to beacon-roots contract
      2. for each tx: process_transaction
      3. for each withdrawal: process_withdrawal
      4. (post-merge) no block reward, but ommers list must be empty

    Mainnet Cancun blocks always have ommers = []. We don't enforce
    that here — invalid blocks with ommers ≠ [] will silently
    proceed without issuing ommer rewards (post-merge reward
    helpers are 0-valued). -/
def applyBlock
    (state       : State)
    (block       : Block)
    (blockHashes : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  let header := block.header

  -- (1) EIP-4788 system call. State mutations from this stick.
  let state := beaconRootCall state (blockEnv header blockHashes) header.parentBeaconBlockRoot

  -- (2) Process transactions. This entry takes the legacy-shaped
  -- `block.transactions` (Frontier.Transaction list). Typed-tx
  -- routing for Cancun (EIP-2930 / 1559 / 4844) goes through
  -- `applyBlockTyped` below; Replay's "Cancun" dispatch picks
  -- this path only when the block is pure-legacy.
  let (state, gasUsed, logs) ←
    processAll state header blockHashes block.transactions 0 []

  -- (3) EIP-4895 withdrawals.
  let state := processWithdrawals state block.withdrawals

  -- (4) Post-merge: block reward = 0. We omit the explicit
  -- coinbase-credit step.

  return { state := state, gasUsed := gasUsed, logs := logs }

/-- Drive a Cancun block whose transactions arrive typed and paired with senders: the
    EIP-4788 beacon-root system call, `Evm.Frontier.Vm.Tx.runAll` at Cancun, then the
    EIP-4895 withdrawals; no block reward (post-merge). -/
def applyBlockTyped
    (state                 : State)
    (header                : Header)
    (txsWithSender         : List (Evm.Frontier.Vm.Tx.Tx × Evm.Address))
    (withdrawals           : List Evm.Shanghai.Withdrawal)
    (blockHashes           : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  let state := beaconRootCall state (blockEnv header blockHashes) header.parentBeaconBlockRoot
  let (state, gasUsed, logs) ← Evm.Frontier.Vm.Tx.runAll 16 (blockEnv header blockHashes)
    (Evm.Frontier.Vm.Tx.table 16) (Evm.Cancun.Vm.Effect.trampoline Evm.Cancun.Vm.PrecompiledContracts.lookup)
    (fun _ => none) state txsWithSender 0 0 []
  let state := processWithdrawals state withdrawals
  return { state := state, gasUsed := gasUsed, logs := logs }

end Evm.Cancun
