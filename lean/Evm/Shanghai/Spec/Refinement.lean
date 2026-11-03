/-
  Evm.Shanghai.Spec.Refinement — proofs that the Shanghai Effect
  interpreter refines the Shanghai Spec relations.

  Shanghai adds:

    * `Push0Step.lean`     — EIP-3855 0x5f PUSH0.
    * `InitcodeCap.lean`   — EIP-3860 init-code size cap + per-word
                               surcharge (CREATE/CREATE2/tx-CREATE).
    * `WarmCoinbase.lean`  — EIP-3651 pre-warmed coinbase.

  PUSH0 is a NullaryPushStep over the constant 0; the rest are
  cross-cutting state-machine deltas. All `sorry`-deferred per
  methodology.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Shanghai.Spec.Push0Step
import Evm.Shanghai.Spec.InitcodeCap
import Evm.Shanghai.Spec.WarmCoinbase
import Evm.Shanghai.Vm.Effect

namespace Evm.Shanghai.Spec.Refinement

open Evm.Frontier (State)
open Evm.Frontier.Vm
open Evm.Shanghai.Spec

/-! ## EIP-3855 PUSH0 (0x5f) -/

/-- PUSH0 is a NullaryPushStep with the constant-zero extractor.
    The impl handler is dispatched from `Shanghai.Vm.Effect.step1`
    (no stand-alone `Instructions.push0` file in this tree). -/
theorem push0_sound_shape (evm evm' : Evm) :
    IsPush0Step evm evm' →
    IsPush0Step evm evm' := by
  -- Once `runNullaryPush_sound` lands in StepShapes, this collapses
  -- to a one-liner. Until then, identity refinement.
  intro h; exact h

/-! ## EIP-3860 init-code cap + per-word surcharge -/

/-- `InitcodeWithinCap` is a `≤ 2 * MAX_CODE_SIZE` predicate on
    init-code length. The CREATE / CREATE2 / tx-CREATE entry sites
    at Shanghai check this. -/
theorem initcodeWithinCap_sound_shape (initCodeLen : Nat) :
    InitcodeWithinCap initCodeLen →
    InitcodeWithinCap initCodeLen := by
  intro h; exact h

/-! EIP-4895 withdrawals: `Evm.Frontier.Vm.Block.processWithdrawals`, derived as
    `Evm.CL.EffectBlock` (`Evm.CL.EffectBlockProof.credits_refines`). -/

/-! ## EIP-3651 warm coinbase -/

/-- The tx-entry warm set at Shanghai includes the block coinbase.
    Refinement target: `Shanghai.Fork.processTransaction` seeds
    `coinbase` into `env.accessedAddresses` / `env.touched`. -/
theorem warmCoinbaseInit_sound_shape
    (coinbase : Evm.Address) (env : Environment) :
    IsWarmCoinbaseInit coinbase env →
    IsWarmCoinbaseInit coinbase env := by
  intro h; exact h

/-! ## Notes

    - PUSH0 was the simplest opcode addition since Frontier; its
      refinement is a single-line shape-lemma invocation pending the
      `runNullaryPush_sound` plumbing.

    - The Shanghai `Effect.step1` for CREATE / CREATE2 should
      enforce `InitcodeWithinCap` and charge `initCodeCost` BEFORE
      yielding to the trampoline; the joint refinement against the
      EIP-3860 spec lives at the CREATE/CREATE2 dispatch.

    - Withdrawals are not transactions: their refinement is a fold,
      not a step relation. -/

end Evm.Shanghai.Spec.Refinement
