/-
  Evm.London — EIP-1559 fee market.

  EELS reference: ethereum/forks/london/.
  Activation: block 12,965,000 (2021-08-05).

  Introduces relative to Berlin:
    - EIP-1559: Base fee + priority fee transaction model; type-2 tx.
    - EIP-3198: BASEFEE opcode.
    - EIP-3529: Refund reduction; SELFDESTRUCT refund removed.
    - EIP-3541: Reject new contract code starting with 0xEF.
    - EIP-3554: Difficulty bomb delay (skipped — we don't model the bomb).

  ----

  Berlin (predecessor) is itself a stub in this worktree, so the user's
  brief asked us to base London directly on Byzantium and fold in the
  Berlin deltas we actually need. Berlin contributed:
    * EIP-2718: typed-transaction envelope — implemented in
      `Evm.London.Transactions` (sum type with three variants).
    * EIP-2929: warm/cold storage / account access pricing —
      Berlin's per-opcode handlers in `Evm.Berlin.Vm.Effect` are
      now reached at London via the `Paris → London → Berlin`
      fall-through in the step1 chain (see commit ce9f6bc).
      The tx level (`Evm.Frontier.Vm.Tx`) pre-seeds
      `accessedAddresses` from the precompiles, sender, target and
      access list.
    * EIP-2565 (cheaper modexp): unchanged at this level.

  ----

  Block reward: EELS `forks/london/fork.py` line 75:
  `BLOCK_REWARD = U256(2 * 10**18)` — 2 ETH (down from Byzantium's 3
  via Constantinople/EIP-1234). We use 2 here directly.
-/

import Evm.Frontier.Vm.Block
import Evm.Frontier.Vm.Create
import Evm.Frontier.Fork
import Evm.Homestead.Fork
import Evm.TangerineWhistle.Fork
import Evm.SpuriousDragon.Utils.Signature
import Evm.SpuriousDragon.Vm.Interpreter
import Evm.SpuriousDragon.Fork
import Evm.Byzantium.Fork
import Evm.Istanbul.Fork
import Evm.London.Blocks
import Evm.London.Transactions
import Evm.London.Vm.Gas
import Evm.London.Vm.Effect

namespace Evm.London

open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Log)

/-- Run one transaction (EELS `process_transaction`): the one definition every fork's is,
    `Evm.Frontier.Vm.Tx.run`, at London (fork ordinal 11: EIP-1559's effective price and
    burned base fee, EIP-3529's refund cap), with London's trampoline and precompile
    table. -/
def processTransaction
    (state          : State)
    (blockHashes    : List Evm.Hash32)
    (coinbase       : Evm.Address)
    (number difficulty gasLimit timestamp : Nat)
    (baseFeePerGas  : Nat)
    (sender         : Evm.Address)
    (tx             : Transaction) :
    Except String Evm.Frontier.TxResult :=
  Evm.Frontier.Vm.Tx.run 11
    (Evm.Frontier.Vm.Tx.blockEnv coinbase number difficulty gasLimit timestamp blockHashes baseFeePerGas)
    state sender (Evm.Frontier.Vm.Tx.ofLondon tx)
    (Evm.Frontier.Vm.Tx.table 11) Vm.Effect.trampoline (fun _ => none)

/-! ## applyBlock

    EELS `forks/london/fork.py` lines 575-613 (`apply_body`) + 692-729
    (`pay_rewards`). We thread `header.baseFeePerGas` through to
    `processTransaction` and use the 2-ETH miner reward + uncle
    inclusion bonus (lines 720, 727).

    `applyBlock` takes legacy txs (`.legacy`), `applyBlockTyped` the
    typed ones as `Evm.Frontier.Vm.Tx.Tx` (the Lean replay harness).
-/

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
    let r ← processTransaction state blockHashes header.coinbase
              header.number header.difficulty header.gasLimit header.timestamp
              header.baseFeePerGas sender (.legacy tx)
    processAll r.state header blockHashes txs'
      (gasAcc + r.gasUsed) (logsAcc ++ r.logs)

/-- Top-level state transition for a London block. -/
def applyBlock
    (state       : State)
    (block       : Block)
    (blockHashes : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  let (state, gasUsed, logs) ← processAll state block.header blockHashes
    block.transactions 0 []
  let state := Evm.Frontier.Vm.Block.payRewards 11 state block.header.coinbase block.header.number
    (block.ommers.map fun o => (o.coinbase, o.number))
  return { state := state, gasUsed := gasUsed, logs := logs }

/-- Block driver for typed (EIP-2930 / EIP-1559) transactions. -/
def applyBlockTyped
    (state         : State)
    (header        : Evm.Frontier.Header)
    (ommers        : List Evm.Frontier.Header)
    (txsWithSender : List (Evm.Frontier.Vm.Tx.Tx × Evm.Address))
    (blockHashes   : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  let (state, gasUsed, logs) ← Evm.Frontier.Vm.Tx.runAll 11
    (Evm.Frontier.Vm.Tx.blockEnv header.coinbase header.number header.difficulty header.gasLimit
      header.timestamp blockHashes header.baseFeePerGas)
    (Evm.Frontier.Vm.Tx.table 11) Vm.Effect.trampoline (fun _ => none) state txsWithSender 0 0 []
  let state := Evm.Frontier.Vm.Block.payRewards 11 state header.coinbase header.number
    (ommers.map fun o => (o.coinbase, o.number))
  return { state := state, gasUsed := gasUsed, logs := logs }

end Evm.London
