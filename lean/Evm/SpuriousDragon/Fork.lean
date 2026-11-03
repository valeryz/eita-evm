/-
  Evm.SpuriousDragon — replay-protection + state-clearing fork.

  EELS reference: ethereum/spurious_dragon/.
  Activation: block 2,675,000 (2016-11-22).

  EIPs:
    * EIP-155: replay protection (chainId in tx signing hash).
    * EIP-160: EXP byte cost 10 → 50.
    * EIP-161: state-clearing — `is_dead` redefines "exists" to
      include the empty-account check; CALL / SELFDESTRUCT
      NEW_ACCOUNT charge becomes value-gated; touched empty accounts
      are swept at end of tx.
    * EIP-170: 24576-byte max for deployed contract code.

  Intrinsic gas and the rest of the tx-level shape are unchanged from
  Tangerine Whistle.
-/

import Evm.Frontier.Vm.Block
import Evm.Frontier.Vm.Create
import Evm.Frontier.Fork
import Evm.Homestead.Fork
import Evm.TangerineWhistle.Fork
import Evm.SpuriousDragon.Utils.Signature
import Evm.SpuriousDragon.Vm.Interpreter
import Evm.SpuriousDragon.Vm.Effect

namespace Evm.SpuriousDragon

open Evm.Frontier (State Account Transaction Block Header)
open Evm.Frontier.Vm (Log)

/-- Run one transaction (EELS `process_transaction`): the one definition every fork's is,
    `Evm.Frontier.Vm.Tx.run`, at Spurious Dragon (fork ordinal 4), with Spurious Dragon's trampoline and
    precompile table. -/
def processTransaction
    (state       : State)
    (blockHashes : List Evm.Hash32)
    (coinbase    : Evm.Address)
    (number difficulty gasLimit timestamp : Nat)
    (sender      : Evm.Address)
    (tx          : Transaction) :
    Except String Evm.Frontier.TxResult :=
  Evm.Frontier.Vm.Tx.run 4
    { origin := sender, gasPrice := 0, coinbase := coinbase, number := number,
      difficulty := difficulty, gasLimit := gasLimit, timestamp := timestamp,
      blockHashes := blockHashes, state := state }
    state sender (Evm.Frontier.Vm.Tx.ofLegacy tx)
    (fun _ a => Evm.Frontier.Vm.Call.precompiles 4 a) Vm.Effect.trampoline (fun _ => none)

private partial def processAll
    (state : State) (header : Header) (blockHashes : List Evm.Hash32)
    (txs : List Transaction)
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
              sender tx
    processAll r.state header blockHashes txs'
      (gasAcc + r.gasUsed) (logsAcc ++ r.logs)

/-- Top-level state transition for a Spurious Dragon block. -/
def applyBlock
    (state       : State)
    (block       : Block)
    (blockHashes : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  let (state, gasUsed, logs) ← processAll state block.header blockHashes
    block.transactions 0 []
  let state := Evm.Frontier.Vm.Block.payRewards 4 state block.header.coinbase block.header.number
    (block.ommers.map fun o => (o.coinbase, o.number))
  return { state := state, gasUsed := gasUsed, logs := logs }

end Evm.SpuriousDragon
