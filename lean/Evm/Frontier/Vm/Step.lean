/-
  Evm.Frontier.Vm.Step — operational semantics as inductive relations.

  Computational reference + relational spec + correspondence:

    * `Instructions.add` (etc.)   — total executable.
    * `AddStep`         (etc.)    — inductive: when the opcode
                                     succeeds and what post-state.
    * `add_iff_step`              — handler success iff relation holds.

  Once correspondence is in place, properties of programs reduce to
  induction on a sequence of `Step`s — no need to wrestle with the
  executable's `do`-notation in every proof.

  This first drop demonstrates the pattern for ADD; the remaining
  arithmetic / stack / bitwise / comparison opcodes follow the same
  shape and can be added incrementally.

  System opcodes (CALL / CREATE / CALLCODE / SELFDESTRUCT) need
  fuel-aware step relations and a frame-stack treatment of recursion;
  out of scope here.
-/

import Evm.Frontier.Vm.Instructions.Arithmetic
import Evm.Frontier.Vm.Interpreter

namespace Evm.Frontier.Vm.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions

/-! ## Monadic-Except iff-lemmas

    These are the reusable building blocks for analyzing any
    do-block. With them tagged `@[simp]`, a goal of the form
    `(do let x ← e; body x) = .ok y` reduces — in a single
    `simp only [Except.bind_eq_ok]` rewrite — to an existential
    `∃ x, e = .ok x ∧ body x = .ok y`. The whole do-block-walk
    collapses to a chain of `rcases`. -/

@[simp] theorem Except.bind_eq_ok {ε α β}
    {x : Except ε α} {f : α → Except ε β} {b : β} :
    x.bind f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => simp [Except.bind]
  | ok a =>
    constructor
    · intro h
      refine ⟨a, rfl, ?_⟩
      simpa [Except.bind] using h
    · rintro ⟨a', heq, hf⟩
      injection heq with heq
      subst heq
      simpa [Except.bind] using hf

/-! ## Computational lemmas

    These characterise the three monadic effects `runBinary` uses,
    extracted as `iff`s so the correspondence proofs can rewrite. -/

theorem Gas.charge_eq_ok_iff (r n g : Nat) :
    Gas.charge r n = .ok g ↔ n ≤ r ∧ g = r - n := by
  unfold Gas.charge
  constructor
  · intro h
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h
      rename_i hge
      exact ⟨Nat.le_of_not_lt hge, h.symm⟩
  · rintro ⟨hle, rfl⟩
    simp [Nat.not_lt.mpr hle]

theorem Stack.push_eq_ok_iff (s : Stack) (x : Evm.U256) (s' : Stack) :
    Stack.push s x = .ok s' ↔ s.length < stackLimit ∧ s' = x :: s := by
  unfold Stack.push
  constructor
  · intro h
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h
      rename_i hge
      exact ⟨Nat.lt_of_not_le hge, h.symm⟩
  · rintro ⟨hlt, rfl⟩
    simp [Nat.not_le.mpr hlt]

theorem Stack.pop2_eq_ok_iff (s : Stack) (a b : Evm.U256) (rest : Stack) :
    Stack.pop2 s = .ok (a, b, rest) ↔ s = a :: b :: rest := by
  constructor
  · intro h
    cases s with
    | nil =>
      simp [Stack.pop2, Stack.pop, bind, Except.bind] at h
    | cons x xs =>
      cases xs with
      | nil =>
        simp [Stack.pop2, Stack.pop, bind, Except.bind] at h
      | cons y ys =>
        simp [Stack.pop2, Stack.pop, bind, Except.bind,
              pure, Except.pure] at h
        obtain ⟨ha, hb, hr⟩ := h
        subst ha; subst hb; subst hr
        rfl
  · rintro rfl
    simp [Stack.pop2, Stack.pop, bind, Except.bind, pure, Except.pure]

theorem Stack.pop_eq_ok_iff (s : Stack) (a : Evm.U256) (rest : Stack) :
    Stack.pop s = .ok (a, rest) ↔ s = a :: rest := by
  unfold Stack.pop
  constructor
  · intro h
    cases s with
    | nil => simp at h
    | cons x xs =>
      simp at h
      rcases h with ⟨hx, hxs⟩
      subst hx; subst hxs; rfl
  · rintro rfl; rfl

theorem Stack.pop3_eq_ok_iff (s : Stack) (a b c : Evm.U256) (rest : Stack) :
    Stack.pop3 s = .ok (a, b, c, rest) ↔ s = a :: b :: c :: rest := by
  constructor
  · intro h
    cases s with
    | nil => simp [Stack.pop3, Stack.pop, bind, Except.bind] at h
    | cons x xs =>
      cases xs with
      | nil => simp [Stack.pop3, Stack.pop, bind, Except.bind] at h
      | cons y ys =>
        cases ys with
        | nil => simp [Stack.pop3, Stack.pop, bind, Except.bind] at h
        | cons z zs =>
          simp [Stack.pop3, Stack.pop, bind, Except.bind,
                pure, Except.pure] at h
          obtain ⟨ha, hb, hc, hr⟩ := h
          subst ha; subst hb; subst hc; subst hr
          rfl
  · rintro rfl
    simp [Stack.pop3, Stack.pop, bind, Except.bind, pure, Except.pure]

/-! ## ADD (0x01)

    `Instructions.add = runBinary Gas.veryLow (· + ·)`, where addition
    is `BitVec 256` addition (mod 2²⁵⁶). -/

/-- ADD's small-step relation: pop two operands, charge `Gas.veryLow`
    (= 3), push the sum. `rest.length < stackLimit` is automatic in a
    well-formed state but stated explicitly so the relation matches
    the executable's success condition exactly. -/
inductive AddStep : Evm → Evm → Prop
  | mk (evm : Evm) (a b : Evm.U256) (rest : Stack)
       (hStack : evm.stack = a :: b :: rest)
       (hLen   : rest.length < stackLimit)
       (hGas   : evm.gasLeft ≥ Gas.veryLow) :
    AddStep evm
      { evm with
        gasLeft := evm.gasLeft - Gas.veryLow,
        stack   := (a + b) :: rest,
        pc      := evm.pc + 1 }

/-- The executable `add` handler succeeds exactly when `AddStep` holds
    with the same post-state. -/
theorem add_iff_step (evm evm' : Evm) :
    Instructions.add evm = .ok evm' ↔ AddStep evm evm' := by
  constructor
  · -- (→) handler success ⇒ AddStep.
    intro h
    unfold Instructions.add Instructions.runBinary at h
    simp only [bind, Except.bind] at h
    -- Walk through the three monadic effects, reducing each `match`
    -- as soon as the value is known.
    rcases hg : Gas.charge evm.gasLeft Gas.veryLow with _ | g
    · rw [hg] at h; simp at h
    rw [hg] at h
    simp only at h
    rcases hp2 : Stack.pop2 evm.stack with _ | ⟨a, b, rest⟩
    · rw [hp2] at h; simp at h
    rw [hp2] at h
    simp only at h
    rcases hpush : Stack.push rest (a + b) with _ | s'
    · rw [hpush] at h; simp at h
    rw [hpush] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    -- Extract conditions and the post-state.
    obtain ⟨hle, hgEq⟩ := (Gas.charge_eq_ok_iff _ _ _).mp hg
    obtain hStack      := (Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
    obtain ⟨hlt, hsEq⟩ := (Stack.push_eq_ok_iff _ _ _).mp hpush
    subst hgEq; subst hsEq; subst h
    exact AddStep.mk evm a b rest hStack hlt hle
  · -- (←) AddStep ⇒ handler success.
    intro h
    cases h with
    | mk a b rest hStack hLen hGas =>
      unfold Instructions.add Instructions.runBinary
      simp only [bind, Except.bind,
                 (Gas.charge_eq_ok_iff _ _ _).mpr ⟨hGas, rfl⟩,
                 (Stack.pop2_eq_ok_iff _ _ _ _).mpr hStack,
                 (Stack.push_eq_ok_iff _ _ _).mpr ⟨hLen, rfl⟩,
                 pure, Except.pure]

/-! ### Downstream theorems

    Once correspondence is in place, structural facts about ADD become
    one-line consequences of the inductive shape. The pattern
    generalises: every per-opcode `*_iff_step` gives the surrounding
    proofs about gas, stack, and `pc` for free. -/

/-- A successful ADD always decrements `gasLeft` by exactly
    `Gas.veryLow` (= 3). -/
theorem add_gas_decrement (evm evm' : Evm) :
    Instructions.add evm = .ok evm' →
    evm.gasLeft = evm'.gasLeft + Gas.veryLow := by
  intro h
  cases (add_iff_step evm evm').mp h with
  | mk a b rest hStack hLen hGas =>
    show evm.gasLeft = (evm.gasLeft - Gas.veryLow) + Gas.veryLow
    exact (Nat.sub_add_cancel hGas).symm

/-- A successful ADD always advances `pc` by exactly 1 (no operand
    bytes follow it in the bytecode stream). -/
theorem add_pc_advance (evm evm' : Evm) :
    Instructions.add evm = .ok evm' → evm'.pc = evm.pc + 1 := by
  intro h
  cases (add_iff_step evm evm').mp h
  rfl

/-- A successful ADD reduces stack size by exactly 1 (pops 2, pushes 1). -/
theorem add_stack_shrinks (evm evm' : Evm) :
    Instructions.add evm = .ok evm' →
    evm'.stack.length + 1 = evm.stack.length := by
  intro h
  cases (add_iff_step evm evm').mp h with
  | mk a b rest hStack hLen hGas => simp [hStack]

/-! ## CALL (0xf1) — the recursive case

    `call` is structurally harder than ADD: its body has seven
    sequenced monadic effects (`pop7`, `chargeMemory ×2`,
    `Gas.charge ×2`, `Stack.push`, `runFrame` for the sub-frame),
    branches on a `failFast` flag, and an inner `match` on the
    `runResult` of the sub-call. Each branch produces a different
    post-state but all share `pc := evm.pc + 1`.

    Sketch of the correspondence:

      inductive CallStep (fuel : Nat) : Evm → Evm → Prop
        | failFast       — depth or balance gate fires
        | precompileOk   — precompile dispatched
        | precompileFail
        | subFrameOk     — runFrame returned .ok
        | subFrameFail   — runFrame returned .error

      theorem call_iff_step :
          call fuel evm = .ok evm'  ↔  CallStep fuel evm evm'

    The proof is a case-walk through the do-block: peel each monadic
    bind (`.ok` substitutes and continues, `.error` contradicts
    `.ok evm'`), split on `failFast` and on `runResult`. The first
    five binds peel cleanly with the same `rcases h : f x with _ | y;
    · rw [h] at h; simp at h; rw [h] at h; simp only at h` skeleton
    used in the ADD proof; the inner-`match runResult` split fights
    Lean's reducer because `simp only` between peels can rewrite
    `pure PUnit.unit` into shapes the next `split` doesn't expect.

    Recommendation for the next pass: write `Except.bind_eq_ok` and
    `Except.bind_eq_error` as named iff-lemmas (mirroring the
    `Gas.charge_eq_ok_iff` / `Stack.pop2_eq_ok_iff` pattern), then
    rewrite with `simp only [Except.bind_eq_ok]` to expose the
    nested existentials in one go. -/

/-- Fuel exhaustion at level 0 produces `.error .fuelExhausted` — no
    state change. The fuel parameter is a modelling artefact (see
    `Evm.Frontier.Vm.defaultFuel`); this theorem exists to anchor the
    boundary case in the spec. -/
theorem call_zero_fuel (evm : Evm) :
    call 0 evm = .error .fuelExhausted := by
  simp [call]

/- `call_pc_advance` (sketch, not stated). With `Except.bind_eq_ok` available,
    the first five monadic binds flatten cleanly into existentials.
    The remaining obstacle is converting `pure {evm/merged with ...,
    pc := evm.pc + 1, ...} = .ok evm'` into a substitutable
    `evm' = ...` equation. `simp only [pure, Except.pure,
    Except.ok.injEq]` works in the failFast branch but leaves the
    equation in non-substitutable form in the runResult branch,
    presumably because `merged := mergeChild evm subEvm` obscures
    the structure. The frame-stack reformulation (option #1) should
    dissolve this — each step's post-state is a single record write,
    not a nested record-with on an opaque helper. -/

end Evm.Frontier.Vm.Spec
