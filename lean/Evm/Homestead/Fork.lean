/-
  Evm.Homestead — first scheduled fork after Frontier.

  EELS reference: ethereum/homestead/.
  Activation: block 1,150,000 (2016-03-14).

  Changes relative to Frontier:
    * EIP-2: contract-creation tx pays an extra 32000 gas (`G_txcreate`).
             Also: low-s signature requirement and CREATE deposit-failure
             reverts (the latter is implemented in
             `Homestead.Vm.Interpreter.create`).
    * EIP-7: DELEGATECALL (0xf4), in `Homestead.Vm.Interpreter`.
    * EIP-8: networking-layer forward compatibility — not EVM-relevant.

  Unchanged types and modules (`State`, `Account`, `Block`, `Transaction`,
  `Trie`, `Bloom`, the Vm primitives, the unchanged opcode handlers,
  precompiles, address derivation, ...) are referenced from
  `Evm.Frontier.*` directly rather than duplicated here.
-/

import Evm.Frontier.Vm.Block
import Evm.Frontier.Vm.Create
import Evm.Frontier.Fork              -- gives us all Frontier types + handlers
import Evm.Homestead.Vm.Gas
import Evm.Homestead.Vm.Interpreter
import Evm.Homestead.Vm.Effect
import Evm.Homestead.Utils.Signature

namespace Evm.Homestead

open Evm.Frontier (State Account Transaction Block Header)
open Evm.Frontier.Vm (Log)

/-- Run one transaction (EELS `process_transaction`): the one definition every fork's is,
    `Evm.Frontier.Vm.Tx.run`, at Homestead (fork ordinal 1), with Homestead's trampoline and
    precompile table. -/
def processTransaction
    (state       : State)
    (blockHashes : List Evm.Hash32)
    (coinbase    : Evm.Address)
    (number difficulty gasLimit timestamp : Nat)
    (sender      : Evm.Address)
    (tx          : Transaction) :
    Except String Evm.Frontier.TxResult :=
  Evm.Frontier.Vm.Tx.run 1
    { origin := sender, gasPrice := 0, coinbase := coinbase, number := number,
      difficulty := difficulty, gasLimit := gasLimit, timestamp := timestamp,
      blockHashes := blockHashes, state := state }
    state sender (Evm.Frontier.Vm.Tx.ofLegacy tx)
    (fun _ a => Evm.Frontier.Vm.Call.precompiles 1 a) Vm.Effect.trampoline (fun _ => none)

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
      | none   => .error "invalid signature (or s > n/2, EIP-2)"
    let r ← processTransaction state blockHashes header.coinbase
              header.number header.difficulty header.gasLimit header.timestamp
              sender tx
    processAll r.state header blockHashes txs'
      (gasAcc + r.gasUsed) (logsAcc ++ r.logs)

/-- Top-level state transition for a Homestead block. Same shape as
    `Evm.Frontier.applyBlock`: mining reward stays 5 ETH (Byzantium
    drops it to 3); uncle bonuses use the Frontier formula. -/
def applyBlock
    (state       : State)
    (block       : Block)
    (blockHashes : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  let (state, gasUsed, logs) ← processAll state block.header blockHashes
    block.transactions 0 []
  let state := Evm.Frontier.Vm.Block.payRewards 1 state block.header.coinbase block.header.number
    (block.ommers.map fun o => (o.coinbase, o.number))
  return { state := state, gasUsed := gasUsed, logs := logs }

end Evm.Homestead
