/-
  Evm.Frontier.Spec.SelfdestructRefinement — `Effect.doSelfdestruct`
  and `handleYield`'s `.selfdestruct` arm refine the Spec-layer
  SELFDESTRUCT relations.

  Simplest of the terminator refinements: no gas chain (GAS_ZERO),
  no sub-frame, no stack push. The apply-side theorem quantifies over
  `Effect.handleYield` directly — it is a TOTAL extracted def (unlike
  `partial def trampoline`), so the kernel can unfold it and the
  match iota-reduces on the literal `.selfdestruct` constructor.
-/

import Evm.Frontier.Spec.SelfdestructStep
import Evm.Frontier.Vm.Effect

namespace Evm.Frontier.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Effect

theorem pop_ok {s : Stack} {a : Evm.U256} {rest : Stack}
    (h : Stack.pop s = .ok (a, rest)) : s = a :: rest := by
  rcases s with _ | ⟨x, r⟩ <;> simp [Stack.pop] at h
  simp_all

/-! ## Entry-side refinement -/

/-- Whenever `doSelfdestruct` yields, the payload satisfies
    `IsSelfdestructEntry`. -/
theorem doSelfdestruct_yield_isSelfdestructEntry
    {evm frame : Evm} {b : Evm.Address}
    (h : Effect.doSelfdestruct evm = .yield frame (.selfdestruct b)) :
    IsSelfdestructEntry evm frame b := by
  unfold Effect.doSelfdestruct at h
  split at h
  · nomatch h
  · next hstatic =>
    split at h
    · nomatch h
    · next bW rest hpop =>
      injection h with hframe heff
      injection heff with hb
      exact ⟨bW, rest, pop_ok hpop, hb.symm,
        Bool.not_eq_true _ ▸ hstatic, hframe.symm⟩

/-- Completeness companion: a non-static frame with a non-empty stack
    always reaches the yield (the only failure modes are the static
    guard and stack underflow). -/
theorem doSelfdestruct_total (evm : Evm) (bW : Evm.U256) (rest : Stack)
    (hs : evm.stack = bW :: rest)
    (hstatic : evm.message.isStatic = false) :
    Effect.doSelfdestruct evm
      = .yield evm (.selfdestruct (Evm.Address.ofNat bW.toNat)) := by
  unfold Effect.doSelfdestruct
  simp [hstatic, hs, Stack.pop, u256ToAddr]

/-! ## Apply-side refinement -/

/-- The `.selfdestruct` arm of `handleYield` refines
    `IsSelfdestructApply`. -/
theorem handleYield_selfdestruct_isSelfdestructApply
    {frame : Evm} {b : Evm.Address} {frame' : Evm}
    {runSub : Evm → Except Exception Evm}
    (h : Effect.handleYield frame (.selfdestruct b) runSub
           = .ok frame') :
    IsSelfdestructApply frame b frame' := by
  unfold Effect.handleYield Effect.resumeSelfdestruct at h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  simp only [IsSelfdestructApply]
  exact h.symm

/-- Completeness companion: the arm cannot fail (no charge, no
    push). -/
theorem handleYield_selfdestruct_total
    (frame : Evm) (b : Evm.Address)
    (runSub : Evm → Except Exception Evm) :
    ∃ frame',
      Effect.handleYield frame (.selfdestruct b) runSub
        = .ok frame' := by
  unfold Effect.handleYield Effect.resumeSelfdestruct
  exact ⟨_, rfl⟩

end Evm.Frontier.Spec
