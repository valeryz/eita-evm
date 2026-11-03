import Evm.CL.GasEmit
import Evm.Shanghai.Spec.InitcodeCap

/-! # Evm.CL.GasEmitShanghai — the emitted EIP-3860 cap decision is the Shanghai spec's

`Evm.CL.GasEmit.createInitcodeOversize` is what the host (cb-create, via the emitted
`spec-create-initcode-oversize`) decides on; `Evm.Shanghai.Spec.initcodeWithinCapAt` is
the fork-typed statement of EIP-3860's cap. This file proves them the same function, so
the executable cannot drift from the spec on either the fork gate (Shanghai = ordinal 15)
or the bound (`2 · MAX_CODE_SIZE = 49152`). Same pattern as `GasEmitPrague`. -/

namespace Evm.CL.GasEmitShanghai

open Evm.CL.GasEmit

/-- The emitted decision reads 1 exactly when the Shanghai spec's cap rejects the init
    code: for every fork `f` (as the host's `fork-ord`) and every length. -/
theorem createInitcodeOversize_eq_cap (ρ : Env) (f : Evm.Fork) (len : Nat)
    (hf : ρ "fork-ord" = f.ord) (hl : ρ "initcode-len" = len) :
    (createInitcodeOversize.eval ρ = 1)
      ↔ Evm.Shanghai.Spec.initcodeWithinCapAt f len = false := by
  simp only [createInitcodeOversize, fork, Expr.eval, hf, hl,
             Evm.Shanghai.Spec.initcodeWithinCapAt, Evm.Fork.atLeast,
             Evm.Shanghai.Spec.maxInitCodeSize, Evm.SpuriousDragon.Vm.Gas.maxCodeSize]
  cases f <;> simp [Evm.Fork.ord] <;> omega

/-- Corollary in the shape cb-create uses: before Shanghai the decision is never 1. -/
theorem createInitcodeOversize_pre_shanghai (ρ : Env) (h : ρ "fork-ord" < 15) :
    createInitcodeOversize.eval ρ = 0 := by
  simp [createInitcodeOversize, fork, Expr.eval, h]

end Evm.CL.GasEmitShanghai
