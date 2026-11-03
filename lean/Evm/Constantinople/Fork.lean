/-
  Evm.Constantinople — Metropolis part 2.

  EELS reference: ethereum/forks/constantinople/fork.py.
  Mainnet activation: block 7,280,000 (2019-02-28), but reverted just
  before activation due to an EIP-1283 reentrancy issue; Petersburg
  shipped the same block instead. Constantinople semantics ran briefly
  on Ropsten and similar testnets, and the ethereum/tests corpus still
  contains a `Constantinople` test network.

  Deltas from Byzantium:
    - EIP-145: bitwise shifting opcodes (SHL, SHR, SAR).
    - EIP-1014: CREATE2 deterministic deployment.
    - EIP-1052: EXTCODEHASH.
    - EIP-1234: difficulty-bomb delay; block reward 3 ETH → 2 ETH
      (`forks/constantinople/fork.py` line 64:
       `BLOCK_REWARD = U256(2 * 10**18)`). The difficulty bomb delay
      itself is not modeled here because we don't validate difficulty.
    - EIP-1283: net SSTORE gas metering. Reverted in Petersburg.

  Intrinsic gas, state-clearing (EIP-161), code-size cap (EIP-170),
  REVERT (EIP-140), and the EIP-150 / EIP-158 reprices all inherit
  from Byzantium / SD / TW. The transaction level is
  `Evm.Frontier.Vm.Tx.run` at Constantinople (its interpreter,
  `Constantinople.Vm.Effect`; `originalState` for EIP-1283 is the
  world before the tx).
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
import Evm.Constantinople.Vm.Effect

namespace Evm.Constantinople

open Evm.Frontier (State Account Transaction Block Header)
open Evm.Frontier.Vm (Log)

/-- Run one transaction (EELS `process_transaction`): the one definition every fork's is,
    `Evm.Frontier.Vm.Tx.run`, at Constantinople (fork ordinal 6), with Constantinople's trampoline and
    precompile table. -/
def processTransaction
    (state       : State)
    (blockHashes : List Evm.Hash32)
    (coinbase    : Evm.Address)
    (number difficulty gasLimit timestamp : Nat)
    (sender      : Evm.Address)
    (tx          : Transaction) :
    Except String Evm.Frontier.TxResult :=
  Evm.Frontier.Vm.Tx.run 6
    { origin := sender, gasPrice := 0, coinbase := coinbase, number := number,
      difficulty := difficulty, gasLimit := gasLimit, timestamp := timestamp,
      blockHashes := blockHashes, state := state }
    state sender (Evm.Frontier.Vm.Tx.ofLegacy tx)
    (fun _ a => Evm.Frontier.Vm.Call.precompiles 6 a) Vm.Effect.trampoline (fun _ => none)

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

/-- Top-level state transition for a Constantinople block.

    EELS reference: forks/constantinople/fork.py `state_transition`
    (around line 296). The rewards are `Evm.Frontier.Vm.Block.payRewards` at
    Constantinople (EIP-1234's 2 ETH). -/
def applyBlock
    (state       : State)
    (block       : Block)
    (blockHashes : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  let (state, gasUsed, logs) ← processAll state block.header blockHashes
    block.transactions 0 []
  let state := Evm.Frontier.Vm.Block.payRewards 6 state block.header.coinbase block.header.number
    (block.ommers.map fun o => (o.coinbase, o.number))
  return { state := state, gasUsed := gasUsed, logs := logs }

end Evm.Constantinople
