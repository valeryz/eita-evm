/-
  Evm.Frontier.Spec.Refinement — proofs that the Effect executable
  refines the Spec relations.

  Each theorem here connects a concrete executable function (from
  `Evm/Frontier/Vm/Effect.lean`) to a spec relation (from
  `Evm/Frontier/Spec/Step.lean` and friends). The shape is always:

    ∀ inputs, executable inputs = .ok output → IsXxxStep inputs output

  i.e. *every* success of the executable IS a valid spec step.
  Optionally (and harder to prove) the converse holds — see
  `add_step1_iff_isAdd` for an example.

  Status: skeleton with `sorry`. The point is to nail down the
  proof obligations. Discharging them is mechanical for simple
  opcodes (case-split on do-block monad), harder for recursive
  ones (CALL/CREATE need induction on the trampoline).
-/

import Evm.Frontier.Spec.Step
import Evm.Frontier.Spec.Invariants
import Evm.Frontier.Vm.Instructions.Arithmetic
import Evm.Frontier.Vm.Effect
import Evm.Frontier.Vm.Step   -- monadic-Except iff-lemmas

namespace Evm.Frontier.Spec.Refinement

open Evm.Frontier.Vm
open Evm.Frontier.Spec

/-! ## Per-shape soundness lemmas

    Once these are proven, every concrete opcode's refinement
    proof is a one-liner. The shape lemma's parameters are
    `op` and `gas`; the concrete opcodes instantiate them via
    `Instructions.add = runBinary Gas.veryLow (· + ·)` etc.

    `runBinary` / `runUnary` / `runTernary` live in
    `Vm/Instructions.lean` (currently unfolded inline in handler
    definitions). The lemmas use them as is. -/

theorem runBinary_sound (gas : Gas.Gas) (op : Evm.U256 → Evm.U256 → Evm.U256)
    (evm evm' : Evm) :
    Instructions.runBinary gas op evm = .ok evm' →
    IsBinaryStep op gas evm evm' := by
  intro h
  unfold Instructions.runBinary at h
  simp only [bind, Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨gasLeft, hg, h⟩
  rcases h with ⟨⟨a, b, rest⟩, hp, h⟩
  rcases h with ⟨s', hpush, h⟩
  obtain ⟨hle, hgEq⟩ := (Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
  obtain hStack      := (Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp
  obtain ⟨hlt, hsEq⟩ := (Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst hgEq; subst hsEq; subst h
  refine ⟨a, b, rest, hStack, hlt, hle, ?_⟩
  rfl

/-- Shape lemma for nullary-push handlers (CHAINID, SELFBALANCE,
    PUSH0, PREVRANDAO, BASEFEE, BLOBBASEFEE, SLOTNUM — anything that
    just charges `gas`, pushes `f evm` onto the stack, and advances
    pc by 1). For a Handler of the shape

      fun evm => do
        let gasLeft ← Gas.charge evm.gasLeft gas
        let s ← Stack.push evm.stack (f evm)
        return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }

    success of the handler implies the matching `IsNullaryPushStep`. -/
theorem nullaryPush_sound (gas : Gas.Gas) (f : Evm → Evm.U256)
    (evm evm' : Evm) :
    (do
      let gasLeft ← Gas.charge evm.gasLeft gas
      let s ← Stack.push evm.stack (f evm)
      pure { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 }) = .ok evm' →
    IsNullaryPushStep f gas evm evm' := by
  intro h
  simp only [bind, Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨gasLeft, hg, h⟩
  rcases h with ⟨s', hpush, h⟩
  obtain ⟨hle, hgEq⟩ := (Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
  obtain ⟨hlt, hsEq⟩ := (Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst hgEq; subst hsEq; subst h
  refine ⟨hlt, hle, ?_⟩
  rfl

theorem runBinary_complete (gas : Gas.Gas) (op : Evm.U256 → Evm.U256 → Evm.U256)
    (evm evm' : Evm) :
    IsBinaryStep op gas evm evm' →
    Instructions.runBinary gas op evm = .ok evm' := by
  rintro ⟨a, b, rest, hStack, hlt, hle, rfl⟩
  unfold Instructions.runBinary
  rw [show Gas.charge evm.gasLeft gas = .ok (evm.gasLeft - gas) from
        (Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mpr ⟨hle, rfl⟩]
  simp only [bind, Except.bind]
  rw [show Stack.pop2 evm.stack = .ok (a, b, rest) from
        (Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mpr hStack]
  simp only
  rw [show Stack.push rest (op a b) = .ok (op a b :: rest) from
        (Vm.Spec.Stack.push_eq_ok_iff _ _ _).mpr ⟨hlt, rfl⟩]
  rfl

theorem runUnary_complete (gas : Gas.Gas) (op : Evm.U256 → Evm.U256)
    (evm evm' : Evm) :
    IsUnaryStep op gas evm evm' →
    Instructions.runUnary gas op evm = .ok evm' := by
  rintro ⟨a, rest, hStack, hlt, hle, rfl⟩
  unfold Instructions.runUnary
  rw [show Gas.charge evm.gasLeft gas = .ok (evm.gasLeft - gas) from
        (Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mpr ⟨hle, rfl⟩]
  simp only [bind, Except.bind]
  rw [show Stack.pop evm.stack = .ok (a, rest) from
        (Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mpr hStack]
  simp only
  rw [show Stack.push rest (op a) = .ok (op a :: rest) from
        (Vm.Spec.Stack.push_eq_ok_iff _ _ _).mpr ⟨hlt, rfl⟩]
  rfl

theorem runTernary_complete (gas : Gas.Gas)
    (op : Evm.U256 → Evm.U256 → Evm.U256 → Evm.U256)
    (evm evm' : Evm) :
    IsTernaryStep op gas evm evm' →
    Instructions.runTernary gas op evm = .ok evm' := by
  rintro ⟨a, b, c, rest, hStack, hlt, hle, rfl⟩
  unfold Instructions.runTernary
  rw [show Gas.charge evm.gasLeft gas = .ok (evm.gasLeft - gas) from
        (Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mpr ⟨hle, rfl⟩]
  simp only [bind, Except.bind]
  rw [show Stack.pop3 evm.stack = .ok (a, b, c, rest) from
        (Vm.Spec.Stack.pop3_eq_ok_iff _ _ _ _ _).mpr hStack]
  simp only
  rw [show Stack.push rest (op a b c) = .ok (op a b c :: rest) from
        (Vm.Spec.Stack.push_eq_ok_iff _ _ _).mpr ⟨hlt, rfl⟩]
  rfl

theorem runNullaryPush_complete (gas : Gas.Gas) (f : Evm → Evm.U256)
    (evm evm' : Evm) :
    IsNullaryPushStep f gas evm evm' →
    Instructions.runNullaryPush gas f evm = .ok evm' := by
  rintro ⟨hlt, hle, rfl⟩
  unfold Instructions.runNullaryPush
  rw [show Gas.charge evm.gasLeft gas = .ok (evm.gasLeft - gas) from
        (Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mpr ⟨hle, rfl⟩]
  simp only [bind, Except.bind]
  rw [show Stack.push evm.stack (f evm) = .ok (f evm :: evm.stack) from
        (Vm.Spec.Stack.push_eq_ok_iff _ _ _).mpr ⟨hlt, rfl⟩]
  rfl

theorem runNullaryPush_sound (gas : Gas.Gas) (f : Evm → Evm.U256)
    (evm evm' : Evm) :
    Instructions.runNullaryPush gas f evm = .ok evm' →
    IsNullaryPushStep f gas evm evm' := by
  unfold Instructions.runNullaryPush
  exact nullaryPush_sound gas f evm evm'

theorem runUnary_sound (gas : Gas.Gas) (op : Evm.U256 → Evm.U256)
    (evm evm' : Evm) :
    Instructions.runUnary gas op evm = .ok evm' →
    IsUnaryStep op gas evm evm' := by
  intro h
  unfold Instructions.runUnary at h
  simp only [bind, Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨gasLeft, hg, h⟩
  rcases h with ⟨⟨a, rest⟩, hp, h⟩
  rcases h with ⟨s', hpush, h⟩
  obtain ⟨hle, hgEq⟩ := (Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
  obtain hStack      := (Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  obtain ⟨hlt, hsEq⟩ := (Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst hgEq; subst hsEq; subst h
  refine ⟨a, rest, hStack, hlt, hle, ?_⟩
  rfl

theorem runTernary_sound (gas : Gas.Gas)
    (op : Evm.U256 → Evm.U256 → Evm.U256 → Evm.U256)
    (evm evm' : Evm) :
    Instructions.runTernary gas op evm = .ok evm' →
    IsTernaryStep op gas evm evm' := by
  intro h
  unfold Instructions.runTernary at h
  simp only [bind, Vm.Spec.Except.bind_eq_ok] at h
  rcases h with ⟨gasLeft, hg, h⟩
  rcases h with ⟨⟨a, b, c, rest⟩, hp, h⟩
  rcases h with ⟨s', hpush, h⟩
  obtain ⟨hle, hgEq⟩ := (Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hg
  obtain hStack      := (Vm.Spec.Stack.pop3_eq_ok_iff _ _ _ _ _).mp hp
  obtain ⟨hlt, hsEq⟩ := (Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst hgEq; subst hsEq; subst h
  refine ⟨a, b, c, rest, hStack, hlt, hle, ?_⟩
  rfl

/-! ## ADD refinement (one-liners via the shape lemma) -/

theorem add_sound (evm evm' : Evm) :
    Instructions.add evm = .ok evm' → IsAddStep evm evm' := by
  unfold Instructions.add
  exact runBinary_sound _ _ evm evm'

theorem add_complete (evm evm' : Evm) :
    IsAddStep evm evm' → Instructions.add evm = .ok evm' := by
  unfold Instructions.add
  exact runBinary_complete _ _ evm evm'

theorem add_iff_isAdd (evm evm' : Evm) :
    Instructions.add evm = .ok evm' ↔ IsAddStep evm evm' :=
  ⟨add_sound _ _, add_complete _ _⟩

/-! ## The sound direction for the remaining pure-stack opcodes.

    The `_complete` lemmas below give spec → impl; correctness needs
    impl → spec, which the same shape lemmas discharge one line each.
    (Coverage-ledger note: `scripts/refinement_coverage.py` flags any
    relation resolved only by `_complete` — 11 of them before this
    block landed.) -/

theorem and_sound (evm evm' : Evm) :
    Instructions.and_ evm = .ok evm' → IsAndStep evm evm' := by
  unfold Instructions.and_; exact runBinary_sound _ _ evm evm'

theorem or_sound (evm evm' : Evm) :
    Instructions.or_ evm = .ok evm' → IsOrStep evm evm' := by
  unfold Instructions.or_; exact runBinary_sound _ _ evm evm'

theorem xor_sound (evm evm' : Evm) :
    Instructions.xor_ evm = .ok evm' → IsXorStep evm evm' := by
  unfold Instructions.xor_; exact runBinary_sound _ _ evm evm'

theorem lt_sound (evm evm' : Evm) :
    Instructions.lt evm = .ok evm' → IsLtStep evm evm' := by
  unfold Instructions.lt; exact runBinary_sound _ _ evm evm'

theorem gt_sound (evm evm' : Evm) :
    Instructions.gt evm = .ok evm' → IsGtStep evm evm' := by
  unfold Instructions.gt; exact runBinary_sound _ _ evm evm'

theorem slt_sound (evm evm' : Evm) :
    Instructions.slt evm = .ok evm' → IsSltStep evm evm' := by
  unfold Instructions.slt; exact runBinary_sound _ _ evm evm'

theorem sgt_sound (evm evm' : Evm) :
    Instructions.sgt evm = .ok evm' → IsSgtStep evm evm' := by
  unfold Instructions.sgt; exact runBinary_sound _ _ evm evm'

theorem eq_sound (evm evm' : Evm) :
    Instructions.eq evm = .ok evm' → IsEqStep evm evm' := by
  unfold Instructions.eq; exact runBinary_sound _ _ evm evm'

theorem iszero_sound (evm evm' : Evm) :
    Instructions.iszero evm = .ok evm' → IsIszeroStep evm evm' := by
  unfold Instructions.iszero; exact runUnary_sound _ _ evm evm'

theorem not_sound (evm evm' : Evm) :
    Instructions.not_ evm = .ok evm' → IsNotStep evm evm' := by
  unfold Instructions.not_; exact runUnary_sound _ _ evm evm'

theorem byte_sound (evm evm' : Evm) :
    Instructions.byte evm = .ok evm' → IsByteStep evm evm' := by
  unfold Instructions.byte; exact runBinary_sound _ _ evm evm'

/-! ## The other binary opcodes — one line each.

    Each refinement proof for a binary opcode is now a single
    appeal to `runBinary_sound`. Below we discharge a few to
    establish the pattern; the rest follow identically. -/

theorem mul_sound (evm evm' : Evm) :
    Instructions.mul evm = .ok evm' → IsMulStep evm evm' := by
  unfold Instructions.mul; exact runBinary_sound _ _ evm evm'

theorem mul_complete (evm evm' : Evm) :
    IsMulStep evm evm' → Instructions.mul evm = .ok evm' := by
  unfold Instructions.mul; exact runBinary_complete _ _ evm evm'

theorem sub_sound (evm evm' : Evm) :
    Instructions.sub evm = .ok evm' → IsSubStep evm evm' := by
  unfold Instructions.sub; exact runBinary_sound _ _ evm evm'

theorem sub_complete (evm evm' : Evm) :
    IsSubStep evm evm' → Instructions.sub evm = .ok evm' := by
  unfold Instructions.sub; exact runBinary_complete _ _ evm evm'

theorem div_sound (evm evm' : Evm) :
    Instructions.div evm = .ok evm' → IsDivStep evm evm' := by
  unfold Instructions.div; exact runBinary_sound _ _ evm evm'

theorem div_complete (evm evm' : Evm) :
    IsDivStep evm evm' → Instructions.div evm = .ok evm' := by
  unfold Instructions.div; exact runBinary_complete _ _ evm evm'

theorem and_complete (evm evm' : Evm) :
    IsAndStep evm evm' → Instructions.and_ evm = .ok evm' := by
  unfold Instructions.and_; exact runBinary_complete _ _ evm evm'

theorem or_complete (evm evm' : Evm) :
    IsOrStep evm evm' → Instructions.or_ evm = .ok evm' := by
  unfold Instructions.or_; exact runBinary_complete _ _ evm evm'

theorem xor_complete (evm evm' : Evm) :
    IsXorStep evm evm' → Instructions.xor_ evm = .ok evm' := by
  unfold Instructions.xor_; exact runBinary_complete _ _ evm evm'

theorem lt_complete (evm evm' : Evm) :
    IsLtStep evm evm' → Instructions.lt evm = .ok evm' := by
  unfold Instructions.lt; exact runBinary_complete _ _ evm evm'

theorem gt_complete (evm evm' : Evm) :
    IsGtStep evm evm' → Instructions.gt evm = .ok evm' := by
  unfold Instructions.gt; exact runBinary_complete _ _ evm evm'

theorem slt_complete (evm evm' : Evm) :
    IsSltStep evm evm' → Instructions.slt evm = .ok evm' := by
  unfold Instructions.slt; exact runBinary_complete _ _ evm evm'

theorem sgt_complete (evm evm' : Evm) :
    IsSgtStep evm evm' → Instructions.sgt evm = .ok evm' := by
  unfold Instructions.sgt; exact runBinary_complete _ _ evm evm'

theorem eq_complete (evm evm' : Evm) :
    IsEqStep evm evm' → Instructions.eq evm = .ok evm' := by
  unfold Instructions.eq; exact runBinary_complete _ _ evm evm'

theorem iszero_complete (evm evm' : Evm) :
    IsIszeroStep evm evm' → Instructions.iszero evm = .ok evm' := by
  unfold Instructions.iszero; exact runUnary_complete _ _ evm evm'

theorem not_complete (evm evm' : Evm) :
    IsNotStep evm evm' → Instructions.not_ evm = .ok evm' := by
  unfold Instructions.not_; exact runUnary_complete _ _ evm evm'

theorem byte_complete (evm evm' : Evm) :
    IsByteStep evm evm' → Instructions.byte evm = .ok evm' := by
  unfold Instructions.byte; exact runBinary_complete _ _ evm evm'

theorem sdiv_complete (evm evm' : Evm) :
    IsSdivStep evm evm' → Instructions.sdiv evm = .ok evm' := by
  unfold Instructions.sdiv; exact runBinary_complete _ _ evm evm'

theorem mod_complete (evm evm' : Evm) :
    IsModStep evm evm' → Instructions.mod_ evm = .ok evm' := by
  unfold Instructions.mod_; exact runBinary_complete _ _ evm evm'

theorem smod_complete (evm evm' : Evm) :
    IsSmodStep evm evm' → Instructions.smod_ evm = .ok evm' := by
  unfold Instructions.smod_; exact runBinary_complete _ _ evm evm'

theorem addmod_complete (evm evm' : Evm) :
    IsAddmodStep evm evm' → Instructions.addmod evm = .ok evm' := by
  unfold Instructions.addmod; exact runTernary_complete _ _ evm evm'

theorem mulmod_complete (evm evm' : Evm) :
    IsMulmodStep evm evm' → Instructions.mulmod evm = .ok evm' := by
  unfold Instructions.mulmod; exact runTernary_complete _ _ evm evm'

theorem signextend_complete (evm evm' : Evm) :
    IsSignextendStep evm evm' → Instructions.signextend evm = .ok evm' := by
  unfold Instructions.signextend; exact runBinary_complete _ _ evm evm'

theorem sdiv_sound (evm evm' : Evm) :
    Instructions.sdiv evm = .ok evm' → IsSdivStep evm evm' := by
  unfold Instructions.sdiv; exact runBinary_sound _ _ evm evm'

theorem mod_sound (evm evm' : Evm) :
    Instructions.mod_ evm = .ok evm' → IsModStep evm evm' := by
  unfold Instructions.mod_; exact runBinary_sound _ _ evm evm'

theorem smod_sound (evm evm' : Evm) :
    Instructions.smod_ evm = .ok evm' → IsSmodStep evm evm' := by
  unfold Instructions.smod_; exact runBinary_sound _ _ evm evm'

theorem addmod_sound (evm evm' : Evm) :
    Instructions.addmod evm = .ok evm' → IsAddmodStep evm evm' := by
  unfold Instructions.addmod; exact runTernary_sound _ _ evm evm'

theorem mulmod_sound (evm evm' : Evm) :
    Instructions.mulmod evm = .ok evm' → IsMulmodStep evm evm' := by
  unfold Instructions.mulmod; exact runTernary_sound _ _ evm evm'

theorem signextend_sound (evm evm' : Evm) :
    Instructions.signextend evm = .ok evm' → IsSignextendStep evm evm' := by
  unfold Instructions.signextend; exact runBinary_sound _ _ evm evm'

-- Comparison / bitwise / unary — same pattern, omitted for brevity.
-- Add as needed by `unfold Instructions.<op>; exact run<Shape>_sound _ _ evm evm'`.

/-! ## Frame-level gas monotonicity for the Effect interpreter

    Any successful `runFrame` either halts the frame or strictly
    decreases gas. This is the umbrella theorem that all per-opcode
    refinements feed into.

    Status: stubbed. Proof strategy is induction on `runFrame`'s
    fuel + case-split on `step1`'s result type. Each opcode handler
    has its own gas-strict-decrease lemma; this aggregates them. -/

theorem runFrame_gas_monotonic (fuel : Nat) (evm : Evm) :
    ∀ result,
      (∃ output, Effect.runFrame fuel evm = .halt result output) ∨
      (∃ eff,    Effect.runFrame fuel evm = .yield result eff) →
      result.gasLeft ≤ evm.gasLeft := by
  sorry

/-! ## Tx-level refinement

    The tx level is `Evm.Frontier.Vm.Tx.run` (every fork's `processTransaction`); the
    derived effect is proved against it in `Evm.CL.EffectTxProof.apply_tx_refines`. -/

/-! ## Notes

    - `add_complete` is essentially circular for ADD (the spec is
      essentially deterministic), so it's mostly a sanity check.
      For more complex opcodes (SSTORE with refunds, CALL with
      gas forwarding) the relation has real non-determinism
      points where the executable picks one valid post-state and
      the spec admits a small set. There completeness IS a real
      theorem.


    - These theorems exist NOT primarily to be proven (though
      that's the long-term goal) but to be STATED. As soon as
      this file compiles, the spec/executable separation is
      real — adding a new opcode requires its `*_sound` theorem,
      and forgetting to update the spec gets caught at proof
      time. -/

end Evm.Frontier.Spec.Refinement
