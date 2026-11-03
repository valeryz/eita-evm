/-
  Evm.Frontier — the Ethereum genesis fork.

  EELS reference: ethereum/frontier/.
  Activation: block 0 (2015-07-30).

  This module re-exports every Frontier submodule and provides the
  top-level transitions `processTransaction` and `applyBlock`, mirroring
  `ethereum/frontier/fork.py`.

  Frontier specifics worth highlighting:
    * Tx intrinsic gas: `21000 + 4·#zero-bytes + 68·#non-zero-bytes`.
      Contract-creation has no extra base cost in Frontier (Homestead
      adds +32000, EIP-2).
    * Block reward: 5 ETH to miner; uncle/ommer rewards are not yet
      implemented in this port.
    * Sender recovery is currently a stub — `processTransaction` takes
      the sender as an argument; the caller is responsible for getting
      it from somewhere (until ecrecover is implemented for real).
-/

import Evm.Frontier.Vm.Block
import Evm.Frontier.Vm.Create
import Evm.Frontier.Vm.Tx
import Evm.Frontier.ForkTypes
import Evm.Frontier.Bloom
import Evm.Frontier.Blocks
import Evm.Frontier.Transactions
import Evm.Frontier.Trie
import Evm.Frontier.State
import Evm.Frontier.StateRoot
import Evm.Frontier.Utils.Address
import Evm.Frontier.Utils.Signature
import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions.Arithmetic
import Evm.Frontier.Vm.Instructions.Comparison
import Evm.Frontier.Vm.Instructions.Bitwise
import Evm.Frontier.Vm.Instructions.Stack
import Evm.Frontier.Vm.Instructions.Memory
import Evm.Frontier.Vm.Instructions.Storage
import Evm.Frontier.Vm.Instructions.ControlFlow
import Evm.Frontier.Vm.Instructions.Environment
import Evm.Frontier.Vm.Instructions.Block
import Evm.Frontier.Vm.Instructions.Keccak
import Evm.Frontier.Vm.Instructions.Log
import Evm.Frontier.Vm.Instructions.System
import Evm.Frontier.Vm.Runtime
import Evm.Frontier.Vm.PrecompiledContracts
import Evm.Frontier.Vm.Interpreter
import Evm.Frontier.Vm.Effect

namespace Evm.Frontier

open Evm.Frontier.Vm

/-- Run one transaction against `state` (EELS `process_transaction`): the one definition
    every fork's is, `Evm.Frontier.Vm.Tx.run`, at Frontier (fork ordinal 0), with
    Frontier's trampoline and precompile table. The sender is the caller's
    (`Utils.recoverSender`). -/
def processTransaction
    (state       : State)
    (blockHashes : List Evm.Hash32)
    (coinbase    : Evm.Address)
    (number difficulty gasLimit timestamp : Nat)
    (sender      : Evm.Address)
    (tx          : Transaction) :
    Except String TxResult :=
  Evm.Frontier.Vm.Tx.run 0
    { origin := sender, gasPrice := 0, coinbase := coinbase, number := number,
      difficulty := difficulty, gasLimit := gasLimit, timestamp := timestamp,
      blockHashes := blockHashes, state := state }
    state sender (Evm.Frontier.Vm.Tx.ofLegacy tx)
    (fun _ a => Evm.Frontier.Vm.Call.precompiles 0 a) Vm.Effect.trampoline (fun _ => none)

/-- Result of executing one block: post-state and the per-block totals
    needed to compute receipts / fill in the next block header. -/
structure BlockResult where
  state   : State
  gasUsed : Nat
  logs    : List Log
  deriving Inhabited

private partial def processAll
    (state : State) (header : Header) (blockHashes : List Evm.Hash32)
    (txs : List Transaction)
    (gasAcc : Nat) (logsAcc : List Log) :
    Except String (State × Nat × List Log) :=
  match txs with
  | [] => .ok (state, gasAcc, logsAcc)
  | tx :: txs' => do
    let sender ← match Utils.recoverSender tx with
      | some s => .ok s
      | none   => .error "invalid signature"
    let r ← processTransaction state blockHashes header.coinbase
              header.number header.difficulty header.gasLimit header.timestamp
              sender tx
    processAll r.state header blockHashes txs'
      (gasAcc + r.gasUsed) (logsAcc ++ r.logs)

/-- Top-level state transition for a Frontier block. Recovers each
    sender, runs each transaction, then pays the block and ommer rewards
    (`Evm.Frontier.Vm.Block.payRewards`, EELS `pay_rewards`).

    Not yet handled: header validation against the parent, the official
    `state` / `transactions` / `receipts` trie roots. -/
def applyBlock
    (state       : State)
    (block       : Block)
    (blockHashes : List Evm.Hash32) :
    Except String BlockResult := do
  let (state, gasUsed, logs) ← processAll state block.header blockHashes
    block.transactions 0 []
  let state := Evm.Frontier.Vm.Block.payRewards 0 state block.header.coinbase block.header.number
    (block.ommers.map fun o => (o.coinbase, o.number))
  return { state := state, gasUsed := gasUsed, logs := logs }

end Evm.Frontier
