/-
  Evm.TangerineWhistle — gas-cost repricing after the 2016 Shanghai DoS.

  EELS reference: ethereum/tangerine_whistle/.
  Activation: block 2,463,000 (2016-10-18).

  EIP-150 changes (the only thing this fork does):
    - Base gas costs raised for IO-heavy ops (EXTCODESIZE, EXTCODECOPY,
      BALANCE, CALL family, SELFDESTRUCT, SLOAD).
    - 63/64-of-remaining cap on forwarded gas for CALL family + CREATE,
      replacing pre-EIP-150's "pre-pay or OOG" rule.
    - SELFDESTRUCT pays `GAS_NEW_ACCOUNT` (25000) when the beneficiary
      doesn't already exist in state.

  Tx-level rules (intrinsic gas, signing hash, low-s requirement, mining
  reward, uncle rewards) all carry over unchanged from Homestead.
-/

import Evm.Frontier.Vm.Block
import Evm.Frontier.Vm.Create
import Evm.Frontier.Fork                  -- types + signature helpers
import Evm.Homestead.Fork                 -- intrinsicGas + low-s sender recovery
import Evm.Homestead.Utils.Signature
import Evm.TangerineWhistle.Vm.Interpreter
import Evm.TangerineWhistle.Vm.Effect

namespace Evm.TangerineWhistle

open Evm.Frontier (State Account Transaction Block Header)
open Evm.Frontier.Vm (Log)

/-- Run one transaction (EELS `process_transaction`): the one definition every fork's is,
    `Evm.Frontier.Vm.Tx.run`, at Tangerine Whistle (fork ordinal 3), with Tangerine Whistle's trampoline and
    precompile table. -/
def processTransaction
    (state       : State)
    (blockHashes : List Evm.Hash32)
    (coinbase    : Evm.Address)
    (number difficulty gasLimit timestamp : Nat)
    (sender      : Evm.Address)
    (tx          : Transaction) :
    Except String Evm.Frontier.TxResult :=
  Evm.Frontier.Vm.Tx.run 3
    { origin := sender, gasPrice := 0, coinbase := coinbase, number := number,
      difficulty := difficulty, gasLimit := gasLimit, timestamp := timestamp,
      blockHashes := blockHashes, state := state }
    state sender (Evm.Frontier.Vm.Tx.ofLegacy tx)
    (fun _ a => Evm.Frontier.Vm.Call.precompiles 3 a) Vm.Effect.trampoline (fun _ => none)

private partial def processAll
    (state : State) (header : Header) (blockHashes : List Evm.Hash32)
    (txs : List Transaction)
    (gasAcc : Nat) (logsAcc : List Log) :
    Except String (State × Nat × List Log) :=
  match txs with
  | [] => .ok (state, gasAcc, logsAcc)
  | tx :: txs' => do
    let sender ← match Evm.Homestead.Utils.recoverSender tx with
      | some s => .ok s
      | none   => .error "invalid signature"
    let r ← processTransaction state blockHashes header.coinbase
              header.number header.difficulty header.gasLimit header.timestamp
              sender tx
    processAll r.state header blockHashes txs'
      (gasAcc + r.gasUsed) (logsAcc ++ r.logs)

/-- Top-level state transition for a Tangerine-Whistle block. -/
def applyBlock
    (state       : State)
    (block       : Block)
    (blockHashes : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  let (state, gasUsed, logs) ← processAll state block.header blockHashes
    block.transactions 0 []
  let state := Evm.Frontier.Vm.Block.payRewards 3 state block.header.coinbase block.header.number
    (block.ommers.map fun o => (o.coinbase, o.number))
  return { state := state, gasUsed := gasUsed, logs := logs }

end Evm.TangerineWhistle
