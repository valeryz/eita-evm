/-
  Evm.Byzantium — Metropolis Part 1.

  EELS reference: ethereum/byzantium/.
  Activation: block 4,370,000 (2017-10-16).

  EIPs (relative to SpuriousDragon):
    * EIP-100: difficulty adjustment includes uncle factor.
    * EIP-140: REVERT (0xfd).
    * EIP-196: alt_bn128 ADD / MUL precompiles (0x06, 0x07).
    * EIP-197: alt_bn128 pairing precompile (0x08).
    * EIP-198: BIGMODEXP precompile (0x05).
    * EIP-211: RETURNDATASIZE (0x3d) / RETURNDATACOPY (0x3e).
    * EIP-214: STATICCALL (0xfa).
    * EIP-649: difficulty-bomb delay; block reward 5 → 3 ETH.
    * EIP-658: transaction receipts include status byte.

  Intrinsic gas is unchanged from Homestead. The state-clearing /
  touched-set machinery is inherited from SpuriousDragon.
-/

import Evm.Frontier.Vm.Block
import Evm.Frontier.Vm.Create
import Evm.Frontier.Fork
import Evm.Homestead.Fork
import Evm.TangerineWhistle.Fork
import Evm.SpuriousDragon.Utils.Signature
import Evm.SpuriousDragon.Vm.Interpreter
import Evm.SpuriousDragon.Fork
import Evm.Byzantium.Vm.Effect
import Evm.Byzantium.Vm.PrecompiledContracts

namespace Evm.Byzantium

open Evm.Frontier (State Account Transaction Block Header)
open Evm.Frontier.Vm (Log)

/-- Run one transaction (EELS `process_transaction`): the one definition every fork's is,
    `Evm.Frontier.Vm.Tx.run`, at Byzantium (fork ordinal 5), with Byzantium's trampoline and
    precompile table. -/
def processTransaction
    (state       : State)
    (blockHashes : List Evm.Hash32)
    (coinbase    : Evm.Address)
    (number difficulty gasLimit timestamp : Nat)
    (sender      : Evm.Address)
    (tx          : Transaction) :
    Except String Evm.Frontier.TxResult :=
  Evm.Frontier.Vm.Tx.run 5
    { origin := sender, gasPrice := 0, coinbase := coinbase, number := number,
      difficulty := difficulty, gasLimit := gasLimit, timestamp := timestamp,
      blockHashes := blockHashes, state := state }
    state sender (Evm.Frontier.Vm.Tx.ofLegacy tx)
    (fun _ a => Evm.Frontier.Vm.Call.precompiles 5 a) Vm.Effect.trampoline (fun _ => none)

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
  let state := Evm.Frontier.Vm.Block.payRewards 5 state block.header.coinbase block.header.number
    (block.ommers.map fun o => (o.coinbase, o.number))
  return { state := state, gasUsed := gasUsed, logs := logs }

end Evm.Byzantium
