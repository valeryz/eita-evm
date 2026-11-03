import Evm.CL.EffectIR
import Evm.Frontier.Vm.Block

/-! # CL/EffectBlock — the block's own credits, derived (docs/effect-layer-derivation.md §4.11)

After a block's transactions, EELS `apply_body` pays the block and ommer rewards
(`pay_rewards`, Frontier..London) and credits the EIP-4895 withdrawals
(`process_withdrawals`, Shanghai+). `Evm.Frontier.Vm.Block.postBlock` is that, for every
fork; this term is its derivation, emitted as `spec-block-credits` (inputs: the coinbase,
the block number, the ommers and the withdrawals as `(address . number)` lists), and
`credits_refines` (`Evm.CL.EffectBlockProof`) proves the two equal for every fork, state
and lists.

The amounts are the emitted formulas the term calls by name (`spec-block-base-reward`,
`spec-uncle-inclusion-bonus`, `spec-uncle-reward`); the per-credit primitive is
`block-credit!` (the storage view's credit outside a tx: no journal). -/

namespace Evm.CL.EffectBlock

open Evm.CL.EffectIR

abbrev coinbase : AExp := .var "coinbase"
abbrev pAddr : AExp := .var "p-addr"

/-- EELS `miner_reward = BLOCK_REWARD + ommer_count * (BLOCK_REWARD // 32)`. -/
def minerG : GExp :=
  .add (.formulaK "spec-block-base-reward" GasEmit.blockBaseReward)
       (.mul (.len "uncles") (.formulaK "spec-uncle-inclusion-bonus" GasEmit.uncleInclusionBonus))

/-- EELS `ommer_miner_reward = ((8 - ommer_age) * BLOCK_REWARD) // 8`. -/
def ommerG : GExp :=
  .formulaK2 "spec-uncle-reward" GasEmit.uncleReward "uncle-num" (.var "p-n") "block-num" (.var "number")

/-- EELS `pay_rewards` (not from Paris: EIP-3675). -/
def rewards : Stmt :=
  .ite (.not (.forkGe 14)) (.seq (.pay coinbase minerG) (.forPairs "uncles" (.pay pAddr ommerG))) .skip

/-- One withdrawal: `create_ether` of `amount · 10^9`, then `modify_state`'s
    destroy-if-empty. -/
def withdrawal : Stmt :=
  .seq (.pay pAddr (.mul (.var "p-n") (.lit 1000000000))) (.ite (.dead pAddr) (.deleteAccount pAddr) .skip)

/-- EELS `process_withdrawals` (from Shanghai). -/
def withdrawals : Stmt := .ite (.forkGe 15) (.forPairs "withdrawals" withdrawal) .skip

/-- The block's credits after its transactions. -/
def credits : Stmt := .seq rewards withdrawals

def params : List String := ["coinbase", "number", "uncles", "withdrawals"]

def creditsCL : String := Stmt.toDefun "spec-block-credits" params credits

end Evm.CL.EffectBlock
