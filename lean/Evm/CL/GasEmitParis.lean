import Evm.CL.GasEmit
import Evm.Paris.Spec.NoBlockReward

/-! # Evm.CL.GasEmitParis — the emitted block reward is the Paris spec's schedule

`Evm.CL.GasEmit.blockBaseReward` is what the host pays the coinbase at the end of a block
(`pay-block-rewards!`, via the emitted `spec-block-base-reward`); `Evm.Paris.Spec.rewardAt`
is the fork-typed schedule with EIP-3675's step to zero. This file proves them the same
function of the fork, so the replay cannot pay a reward on a proof-of-stake block, nor stop
paying one early. Same pattern as `GasEmitShanghai`. -/

namespace Evm.CL.GasEmitParis

open Evm.CL.GasEmit

/-- For every fork `f` (as the host's `fork-ord`): the emitted reward is `rewardAt f`. -/
theorem blockBaseReward_eq_rewardAt (ρ : Env) (f : Evm.Fork) (hf : ρ "fork-ord" = f.ord) :
    blockBaseReward.eval ρ = Evm.Paris.Spec.rewardAt f := by
  simp only [blockBaseReward, fork, Expr.eval, hf, Evm.Paris.Spec.rewardAt, Evm.Fork.atLeast]
  cases f <;> simp [Evm.Fork.ord]

set_option backward.isDefEq.respectTransparency false in
/-- Corollary in the shape the driver relies on: from Paris on, nothing is paid. -/
theorem blockBaseReward_zero_from_paris (ρ : Env) (h : 14 ≤ ρ "fork-ord") :
    blockBaseReward.eval ρ = 0 := by
  simp only [blockBaseReward, fork, Expr.eval]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

end Evm.CL.GasEmitParis
