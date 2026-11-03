/-
  Evm.Petersburg — Constantinople minus EIP-1283 (the version of
  Constantinople that actually shipped to mainnet at block 7,280,000).

  EELS reference: ethereum/forks/constantinople/ (EELS keeps no
  separate `petersburg` directory; what it labels "constantinople" is
  the EIP-1283-removed flavour our project labels "Petersburg" —
  Constantinople-with-EIP-1283 was never deployed to mainnet).

  Activation on mainnet: block 7,280,000 (2019-02-28), at the same
  height the original Constantinople was scheduled for. The night
  before activation EIP-1283 was found to enable cheap reentrancy
  against contracts that assumed a 5000-gas-floor SSTORE; the network
  agreed to ship without it, and the result was labelled "Petersburg"
  in client UX (also "ConstantinopleFix" in ethereum/tests fixtures).

  EIPs included (delta vs Byzantium):
    * EIP-145:  Bitwise shifting opcodes (SHL, SHR, SAR).
    * EIP-1014: CREATE2 deterministic deployment.
    * EIP-1052: EXTCODEHASH.
    * EIP-1234: Difficulty bomb delay; block reward 3 → 2 ETH.

  Pointedly NOT included (the whole reason this fork exists):
    * EIP-1283: net SSTORE gas metering. SSTORE keeps its Byzantium
      two-bucket schedule (`sSet`/`sReset` based on `oldValue`).
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
import Evm.Petersburg.Vm.Effect

namespace Evm.Petersburg

open Evm.Frontier (State Account Transaction Block Header)
open Evm.Frontier.Vm (Log)

/-- Run one transaction (EELS `process_transaction`): the one definition every fork's is,
    `Evm.Frontier.Vm.Tx.run`, at Petersburg (fork ordinal 7), with Petersburg's trampoline and
    precompile table. -/
def processTransaction
    (state       : State)
    (blockHashes : List Evm.Hash32)
    (coinbase    : Evm.Address)
    (number difficulty gasLimit timestamp : Nat)
    (sender      : Evm.Address)
    (tx          : Transaction) :
    Except String Evm.Frontier.TxResult :=
  Evm.Frontier.Vm.Tx.run 7
    { origin := sender, gasPrice := 0, coinbase := coinbase, number := number,
      difficulty := difficulty, gasLimit := gasLimit, timestamp := timestamp,
      blockHashes := blockHashes, state := state }
    state sender (Evm.Frontier.Vm.Tx.ofLegacy tx)
    (fun _ a => Evm.Frontier.Vm.Call.precompiles 7 a) Vm.Effect.trampoline (fun _ => none)

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

/-- Top-level state transition for a Petersburg block. -/
def applyBlock
    (state       : State)
    (block       : Block)
    (blockHashes : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  let (state, gasUsed, logs) ← processAll state block.header blockHashes
    block.transactions 0 []
  let state := Evm.Frontier.Vm.Block.payRewards 7 state block.header.coinbase block.header.number
    (block.ommers.map fun o => (o.coinbase, o.number))
  return { state := state, gasUsed := gasUsed, logs := logs }

end Evm.Petersburg
