/-
  Evm.Istanbul — Fork module.

  EELS reference: `forks/istanbul/`. Activation: block 9,069,000
  (2019-12-08).

  Introduces relative to Byzantium (we skip Constantinople +
  Petersburg as standalone modules; their non-EIP-1283 deltas are
  inlined into Istanbul's `Vm/Effect.lean` since they all carried
  forward unchanged):
    * EIP-145  SHL / SHR / SAR.
    * EIP-152  BLAKE2F precompile (0x09).
    * EIP-1014 CREATE2.
    * EIP-1052 EXTCODEHASH (priced 700 here, was 400 at Constantinople).
    * EIP-1108 alt_bn128 re-pricing (constants only; precompiles are
      still stubs in this codebase).
    * EIP-1234 block reward 3 → 2 ETH (was a Constantinople change;
      we honour it directly).
    * EIP-1344 CHAINID opcode (0x46).
    * EIP-1884 SLOAD 200→800, BALANCE 400→700, EXTCODEHASH 400→700,
      SELFBALANCE opcode (0x47) at 5 gas.
    * EIP-2028 non-zero calldata byte 68 → 16.
    * EIP-2200 net SSTORE gas metering.

  ## Block reward
  EELS `forks/istanbul/fork.py` line 64: `BLOCK_REWARD = U256(2 * 10**18)`.
  This is the EIP-1234 reduction (3 → 2 ETH) that landed at
  Constantinople and Istanbul inherited.

  ## Intrinsic gas
  EELS `forks/istanbul/transactions.py` `calculate_intrinsic_cost`
  (line 110). Same shape as Homestead/Byzantium but uses Istanbul's
  `TX_DATA_PER_NON_ZERO = 16` (EIP-2028). Zero bytes stay at 4.

  ## processTransaction / applyBlock
  `Evm.Frontier.Vm.Tx.run` at Istanbul (`originalState` is the world
  before the tx, for EIP-2200; `chainId` defaults to 1), over
  `Istanbul.Vm.Effect` and the Istanbul precompile table.
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
import Evm.Istanbul.Vm.Effect
import Evm.Istanbul.Vm.Gas
import Evm.Istanbul.Vm.PrecompiledContracts

namespace Evm.Istanbul

open Evm.Frontier (State Account Transaction Block Header)
open Evm.Frontier.Vm (Log)

/-- Run one transaction (EELS `process_transaction`): the one definition every fork's is,
    `Evm.Frontier.Vm.Tx.run`, at Istanbul (fork ordinal 8), with Istanbul's trampoline and
    precompile table. -/
def processTransaction
    (state       : State)
    (blockHashes : List Evm.Hash32)
    (coinbase    : Evm.Address)
    (number difficulty gasLimit timestamp : Nat)
    (sender      : Evm.Address)
    (tx          : Transaction) :
    Except String Evm.Frontier.TxResult :=
  Evm.Frontier.Vm.Tx.run 8
    { origin := sender, gasPrice := 0, coinbase := coinbase, number := number,
      difficulty := difficulty, gasLimit := gasLimit, timestamp := timestamp,
      blockHashes := blockHashes, state := state }
    state sender (Evm.Frontier.Vm.Tx.ofLegacy tx)
    (fun _ a => Evm.Frontier.Vm.Call.precompiles 8 a) Vm.Effect.trampoline (fun _ => none)

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

/-- Top-level state transition for an Istanbul block. EELS
    `forks/istanbul/fork.py` `apply_body` (line 451) followed by
    `pay_rewards` (around line 576). -/
def applyBlock
    (state       : State)
    (block       : Block)
    (blockHashes : List Evm.Hash32) :
    Except String Evm.Frontier.BlockResult := do
  let (state, gasUsed, logs) ← processAll state block.header blockHashes
    block.transactions 0 []
  let state := Evm.Frontier.Vm.Block.payRewards 8 state block.header.coinbase block.header.number
    (block.ommers.map fun o => (o.coinbase, o.number))
  return { state := state, gasUsed := gasUsed, logs := logs }

end Evm.Istanbul
