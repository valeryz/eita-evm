/-
  Evm.IR.Soundness — refinement theorems linking the IR pipeline
  to the executable / spec.

  Two-layer claim:

    1. `IR.execute (IR.compile code) evm = .ok evm'`   IFF
       `Effect.runFrameR _ evm = .halt evm' _`          (vs executable)

    2. `IR.execute (IR.compile code) evm = .ok evm'`   IFF
       `∃ cause, Spec.IsFrameRun (initFrame code evm) cause evm'`
                                                       (vs spec)

  (1) is empirical-style: "two implementations agree." (2) is the
  more interesting refinement: "the IR pipeline produces a result
  the spec accepts." Both are proven at two granularities:

    - chunk level (`compile_sound_vs_effect` / `compile_sound_vs_spec`,
      plus the generalized `compileLoop_sound*` inductions that also
      cover JUMP/JUMPI transfers), and
    - program level (`compileProgram_sound_vs_effect` /
      `compileProgram_sound_vs_spec`): the multi-chunk trampoline
      `IR.executeProgram` over `IR.compileProgram`'s chunk table.
-/

import Evm.IR.Compile
import Evm.IR.Execute
import Evm.Frontier.Vm.Effect
import Evm.Frontier.Spec.FrameRun
import Evm.Frontier.Spec.Refinement
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.IntervalCases


/-! ## `chargeMemory`'s success form (moved from the deleted `Frontier.Spec.CallRefinement`,
    superseded by `Evm.CL.EffectCallProof`; the memory-expansion lemmas below use it). -/
namespace Evm.Frontier.Spec
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions (chargeMemory)

@[simp] theorem memoryExpansionCost_self (a : Nat) :
    Gas.memoryExpansionCost a a = 0 := by
  simp [Gas.memoryExpansionCost]

theorem memoryExpansionCost_max (a b : Nat) :
    Gas.memoryExpansionCost a (max a b) = Gas.memoryExpansionCost a b := by
  unfold Gas.memoryExpansionCost
  rcases Nat.le_total b a with h | h
  · simp [h]
  · rw [Nat.max_eq_right h]

theorem words_extend (m : Memory) (n : Nat) :
    Memory.words (Memory.extend m n)
      = max (Memory.words m) ((n + 31) / 32) := by
  simp only [Memory.extend, Memory.words]
  split
  · next h => omega
  · next h =>
    simp only [ByteArray.size_append]
    simp only [ByteArray.size, Array.size_replicate]
    omega

theorem charge_ok {g n g' : Nat} (h : Gas.charge g n = .ok g') :
    n ≤ g ∧ g' = g - n := by
  unfold Gas.charge at h
  by_cases hlt : g < n
  · rw [ite_eq_left hlt] at h; exact absurd h (by simp)
  · rw [ite_eq_right hlt] at h
    injection h with h
    exact ⟨Nat.not_lt.mp hlt, h.symm⟩

/-- Success characterization of `chargeMemory`: the charged cost is
    the expansion to `max oldWords rangeWords` (0 when the range is
    empty or already covered), and the returned memory's word count
    is exactly that max. -/
theorem chargeMemory_ok {g : Nat} {m : Memory} {off size : Nat}
    {g' : Nat} {m' : Memory}
    (h : chargeMemory g m off size = .ok (g', m')) :
    Gas.memoryExpansionCost (Memory.words m)
      (if size = 0 then Memory.words m
       else max (Memory.words m) ((off + size + 31) / 32)) ≤ g ∧
    g' = g - Gas.memoryExpansionCost (Memory.words m)
      (if size = 0 then Memory.words m
       else max (Memory.words m) ((off + size + 31) / 32)) ∧
    Memory.words m'
      = (if size = 0 then Memory.words m
         else max (Memory.words m) ((off + size + 31) / 32)) ∧
    m' = (if size = 0 then m else Memory.extend m (off + size)) := by
  by_cases hsz : size = 0
  · subst hsz
    simp only [chargeMemory] at h
    simp only [ite_true, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    simp [Gas.memoryExpansionCost]
  · simp only [chargeMemory, hsz, reduceIte, bind, Except.bind, pure,
      Except.pure] at h
    split at h
    · simp at h
    · next g1 hch =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2
      have hc := charge_ok hch
      simp only [hsz, reduceIte]
      rw [memoryExpansionCost_max]
      exact ⟨hc.1, hc.2, words_extend m (off + size), trivial⟩


end Evm.Frontier.Spec

namespace Evm.IR.Soundness

open Evm.Frontier.Vm

/-! ## (1) IR.execute vs Effect.runFrameR

    Claim: compiling bytecode then interpreting the resulting IR
    produces the same halted frame as running the bytecode
    directly through the trampoline-based Effect interpreter.

    Subtleties:
    - The IR pre-charges static gas at chunk entry; Effect charges
      per-opcode. These sum to the same total, but the GAS values
      observed mid-execution differ. The theorem holds for the
      FINAL halted state, not for intermediate observations.
    - Order of memory expansions can differ if the IR coalesces
      chunks. Not an issue in the current no-JUMP slice since each
      MLOAD/MSTORE is still per-op.
    - `Effect.runFrameR` takes a fuel parameter. The theorem
      assumes adequate fuel (i.e., the trampoline doesn't
      artificially exhaust). -/

/-! The chunk-level theorems (`compile_sound_vs_effect`,
    `compile_sound_vs_spec`) live at the END of this file — they
    depend on the per-op machinery below. -/

/-! ## Per-Op equivalence lemmas (same-frame form)

    The shape: "executing this Op on a frame whose bytecode has the
    corresponding opcode at `evm.pc` matches what `Effect.step1`
    would do at that pc."

    These same-frame lemmas (IR and Effect run on the SAME `evm`)
    were the first validation of the simp + kernel-tactic template. The
    chunk-level proof uses the *shifted* variants further down,
    which carry the static-gas offset between the two frames. -/

/-- Per-Op matching for ADD. If
      * the frame is not halted,
      * pc is in bounds,
      * the opcode at `pc` is 0x01,
      * the frame has enough gas for the Effect interpreter to
        charge `veryLow` (3),
      * `IR.execOp evm .add` succeeds with `evm'`,
    then `Effect.step1 evm` produces a `.continue` whose post-state
    is `evm'` with gas charged and pc advanced.

    The chunk-level prover gets `pc < code.size` and `code.get! pc =
    0x01` from JUMPDEST analysis, so this is the practical form. -/
theorem execOp_add_matches_effect (evm evm' : Evm) :
    evm.halted = false →
    evm.pc < evm.message.code.size →
    evm.message.code.get! evm.pc = 0x01 →
    evm.gasLeft ≥ Gas.veryLow →
    IR.execOp evm .add = .ok evm' →
    Effect.step1 evm =
      .continue { evm' with
        gasLeft := evm.gasLeft - Gas.veryLow,
        pc      := evm.pc + 1 } := by
  intro hHalt hSize hCode hGas hIR
  -- (1) IR side: walk the do-block (no Gas.charge — IR pre-charges).
  --     Mirror Step.lean's add_iff_step pattern.
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 evm.stack with _ | ⟨a, b, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (a + b) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  -- hIR : { evm with stack := s' } = evm'
  -- (2) Extract Cons-shape + length witnesses.
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  -- (3) Reduce evm' to concrete shape.
  subst hsEq; subst hIR
  -- (4) Build IsAddStep witness and lift to Instructions.add via
  --     the existing `add_complete` refinement theorem.
  have hIsAdd : Evm.Frontier.Spec.IsAddStep evm
      { evm with stack := (a + b) :: rest,
                 gasLeft := evm.gasLeft - Gas.veryLow,
                 pc := evm.pc + 1 } :=
    ⟨a, b, rest, hStack, hlt, hGas, rfl⟩
  have hAdd := _root_.Evm.Frontier.Spec.Refinement.add_complete _ _ hIsAdd
  -- (5) Reduce Effect.step1: not halted, pc in bounds, opcode = 0x01.
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (evm.pc ≥ evm.message.code.size) from
               Nat.not_le.mpr hSize]
  -- (6) Drive liftPure with the add success.
  show Effect.liftPure Evm.Frontier.Vm.Instructions.add evm = _
  unfold Effect.liftPure
  rw [hAdd]
  -- (7) Residual: `if halted then .halt else .continue`. The
  --     post-state has `halted = evm.halted = false`, so we take
  --     the .continue branch. Pure boolean/record reasoning —
  --     closed by the kernel alone.
  simp [hHalt]

/-- Per-Op matching for SUB (0x03). Same shape as ADD: pop two,
    push `a - b`, charge `veryLow`. Validates that the
    kernel-only pattern transfers across binary opcodes. -/
theorem execOp_sub_matches_effect (evm evm' : Evm) :
    evm.halted = false →
    evm.pc < evm.message.code.size →
    evm.message.code.get! evm.pc = 0x03 →
    evm.gasLeft ≥ Gas.veryLow →
    IR.execOp evm .sub = .ok evm' →
    Effect.step1 evm =
      .continue { evm' with
        gasLeft := evm.gasLeft - Gas.veryLow,
        pc      := evm.pc + 1 } := by
  intro hHalt hSize hCode hGas hIR
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 evm.stack with _ | ⟨a, b, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (a - b) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  have hIsSub : Evm.Frontier.Spec.IsSubStep evm
      { evm with stack := (a - b) :: rest,
                 gasLeft := evm.gasLeft - Gas.veryLow,
                 pc := evm.pc + 1 } :=
    ⟨a, b, rest, hStack, hlt, hGas, rfl⟩
  have hSub := _root_.Evm.Frontier.Spec.Refinement.sub_complete _ _ hIsSub
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (evm.pc ≥ evm.message.code.size) from
               Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.sub evm = _
  unfold Effect.liftPure
  rw [hSub]
  simp [hHalt]

/-- Per-Op matching for MUL (0x02). Costs `Gas.low` (5) rather than
    `Gas.veryLow` (3) -- otherwise identical to the ADD/SUB
    template. Demonstrates that the soundness template adapts
    cleanly across binary opcodes with different gas costs. -/
theorem execOp_mul_matches_effect (evm evm' : Evm) :
    evm.halted = false →
    evm.pc < evm.message.code.size →
    evm.message.code.get! evm.pc = 0x02 →
    evm.gasLeft ≥ Gas.low →
    IR.execOp evm .mul = .ok evm' →
    Effect.step1 evm =
      .continue { evm' with
        gasLeft := evm.gasLeft - Gas.low,
        pc      := evm.pc + 1 } := by
  intro hHalt hSize hCode hGas hIR
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 evm.stack with _ | ⟨a, b, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (a * b) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  have hIsMul : Evm.Frontier.Spec.IsMulStep evm
      { evm with stack := (a * b) :: rest,
                 gasLeft := evm.gasLeft - Gas.low,
                 pc := evm.pc + 1 } :=
    ⟨a, b, rest, hStack, hlt, hGas, rfl⟩
  have hMul := _root_.Evm.Frontier.Spec.Refinement.mul_complete _ _ hIsMul
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (evm.pc ≥ evm.message.code.size) from
               Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.mul evm = _
  unfold Effect.liftPure
  rw [hMul]
  simp [hHalt]

/-- Per-Op matching for DIV (0x04). Same template as ADD/MUL/SUB,
    but the pushed value is `if b = 0 then 0 else BitVec.udiv a b`
    (EVM convention: x/0 = 0). -/
theorem execOp_div_matches_effect (evm evm' : Evm) :
    evm.halted = false →
    evm.pc < evm.message.code.size →
    evm.message.code.get! evm.pc = 0x04 →
    evm.gasLeft ≥ Gas.low →
    IR.execOp evm .div = .ok evm' →
    Effect.step1 evm =
      .continue { evm' with
        gasLeft := evm.gasLeft - Gas.low,
        pc      := evm.pc + 1 } := by
  intro hHalt hSize hCode hGas hIR
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 evm.stack with _ | ⟨a, b, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (if b = 0 then 0 else BitVec.udiv a b)
    with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  have hIsDiv : Evm.Frontier.Spec.IsDivStep evm
      { evm with stack := (if b = 0 then 0 else BitVec.udiv a b) :: rest,
                 gasLeft := evm.gasLeft - Gas.low,
                 pc := evm.pc + 1 } :=
    ⟨a, b, rest, hStack, hlt, hGas, rfl⟩
  have hDiv := _root_.Evm.Frontier.Spec.Refinement.div_complete _ _ hIsDiv
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (evm.pc ≥ evm.message.code.size) from
               Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.div evm = _
  unfold Effect.liftPure
  rw [hDiv]
  simp [hHalt]

/-- Per-Op matching for AND (0x16). -/
theorem execOp_and_matches_effect (evm evm' : Evm) :
    evm.halted = false →
    evm.pc < evm.message.code.size →
    evm.message.code.get! evm.pc = 0x16 →
    evm.gasLeft ≥ Gas.veryLow →
    IR.execOp evm .and_ = .ok evm' →
    Effect.step1 evm =
      .continue { evm' with
        gasLeft := evm.gasLeft - Gas.veryLow,
        pc      := evm.pc + 1 } := by
  intro hHalt hSize hCode hGas hIR
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 evm.stack with _ | ⟨a, b, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (a &&& b) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  have hIsAnd : Evm.Frontier.Spec.IsAndStep evm
      { evm with stack := (a &&& b) :: rest,
                 gasLeft := evm.gasLeft - Gas.veryLow,
                 pc := evm.pc + 1 } :=
    ⟨a, b, rest, hStack, hlt, hGas, rfl⟩
  have hAnd := _root_.Evm.Frontier.Spec.Refinement.and_complete _ _ hIsAnd
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (evm.pc ≥ evm.message.code.size) from
               Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.and_ evm = _
  unfold Effect.liftPure
  rw [hAnd]
  simp [hHalt]

/-- Per-Op matching for OR (0x17). -/
theorem execOp_or_matches_effect (evm evm' : Evm) :
    evm.halted = false →
    evm.pc < evm.message.code.size →
    evm.message.code.get! evm.pc = 0x17 →
    evm.gasLeft ≥ Gas.veryLow →
    IR.execOp evm .or_ = .ok evm' →
    Effect.step1 evm =
      .continue { evm' with
        gasLeft := evm.gasLeft - Gas.veryLow,
        pc      := evm.pc + 1 } := by
  intro hHalt hSize hCode hGas hIR
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 evm.stack with _ | ⟨a, b, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (a ||| b) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  have hIsOr : Evm.Frontier.Spec.IsOrStep evm
      { evm with stack := (a ||| b) :: rest,
                 gasLeft := evm.gasLeft - Gas.veryLow,
                 pc := evm.pc + 1 } :=
    ⟨a, b, rest, hStack, hlt, hGas, rfl⟩
  have hOr := _root_.Evm.Frontier.Spec.Refinement.or_complete _ _ hIsOr
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (evm.pc ≥ evm.message.code.size) from
               Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.or_ evm = _
  unfold Effect.liftPure
  rw [hOr]
  simp [hHalt]

/-- Per-Op matching for XOR (0x18). -/
theorem execOp_xor_matches_effect (evm evm' : Evm) :
    evm.halted = false →
    evm.pc < evm.message.code.size →
    evm.message.code.get! evm.pc = 0x18 →
    evm.gasLeft ≥ Gas.veryLow →
    IR.execOp evm .xor_ = .ok evm' →
    Effect.step1 evm =
      .continue { evm' with
        gasLeft := evm.gasLeft - Gas.veryLow,
        pc      := evm.pc + 1 } := by
  intro hHalt hSize hCode hGas hIR
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 evm.stack with _ | ⟨a, b, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (a ^^^ b) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  have hIsXor : Evm.Frontier.Spec.IsXorStep evm
      { evm with stack := (a ^^^ b) :: rest,
                 gasLeft := evm.gasLeft - Gas.veryLow,
                 pc := evm.pc + 1 } :=
    ⟨a, b, rest, hStack, hlt, hGas, rfl⟩
  have hXor := _root_.Evm.Frontier.Spec.Refinement.xor_complete _ _ hIsXor
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (evm.pc ≥ evm.message.code.size) from
               Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.xor_ evm = _
  unfold Effect.liftPure
  rw [hXor]
  simp [hHalt]

/-! ## Gas-shift helpers

    The chunk-level invariant relates the Effect frame `e` to the IR
    frame `i` by `e = { i with gasLeft := i.gasLeft + gRem, pc := pc }`
    where `gRem` is the static gas of the not-yet-executed ops (the IR
    pre-charged it; the Effect interpreter hasn't charged it yet).
    These lemmas move `Gas.charge` / `chargeMemory` across that
    offset. The arithmetic cores are stated over plain `Nat` — omega
    is blind to `Gas.Gas`-typed hypotheses. -/

private theorem nat_le_add_mid (x c g : Nat) : c ≤ x + (c + g) := by omega
private theorem nat_add_sub_mid (x c g : Nat) : x + (c + g) - c = x + g := by
  omega
private theorem nat_sub_add_comm {c x : Nat} (d : Nat) (h : c ≤ x) :
    x + d - c = x - c + d := by omega
private theorem nat_le_add_mid2 (x c d g : Nat) (h : d ≤ x) :
    c + d ≤ x + (c + g) := by omega
private theorem nat_add_sub_mid2 (x c d g : Nat) (h : d ≤ x) :
    x + (c + g) - (c + d) = x - d + g := by omega
private theorem nat_le_add_mid3 (x c d e g : Nat) (hd : d ≤ x) (he : e ≤ x - d) :
    c + d + e ≤ x + (c + g) := by omega
private theorem nat_add_sub_mid3 (x c d e g : Nat) (hd : d ≤ x) (he : e ≤ x - d) :
    x + (c + g) - (c + d + e) = x - d - e + g := by omega
private theorem nat_le_add_mid3' (x c d e g : Nat) (he : e ≤ x) (hd : d ≤ x - e) :
    c + d + e ≤ x + (c + g) := by omega
private theorem nat_add_sub_mid3' (x c d e g : Nat) (he : e ≤ x) (hd : d ≤ x - e) :
    x + (c + g) - (c + d + e) = x - e - d + g := by omega

/-- Charging `c` from a pool that exceeds the need by `x + g`
    succeeds and leaves exactly `x + g`. -/
theorem charge_shifted (x c g : Nat) :
    Gas.charge (x + (c + g)) c = .ok (x + g) :=
  (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mpr
    ⟨nat_le_add_mid x c g, (nat_add_sub_mid x c g).symm⟩

/-- `chargeMemory` success is stable under adding gas headroom `d`;
    the leftover gas is shifted by exactly `d` and the resulting
    memory is unchanged. -/
theorem chargeMemory_shifted {gl : Nat} {m : Memory} {off size : Nat}
    {gl' : Nat} {m' : Memory} (d : Nat)
    (h : Instructions.chargeMemory gl m off size = .ok (gl', m')) :
    Instructions.chargeMemory (gl + d) m off size = .ok (gl' + d, m') := by
  by_cases hsz : size = 0
  · subst hsz
    simp only [Instructions.chargeMemory, ite_true, pure, Except.pure,
               Except.ok.injEq, Prod.mk.injEq] at h ⊢
    exact ⟨by rw [h.1], h.2⟩
  · simp only [Instructions.chargeMemory, hsz, reduceIte, bind,
               Except.bind, pure, Except.pure] at h ⊢
    split at h
    · simp at h
    · next g1 hch =>
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨hle, rfl⟩ :=
        (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
      rw [(Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mpr
            ⟨Nat.le_add_right_of_le hle, (nat_sub_add_comm d hle).symm⟩]
      simp [h1, h2]

/-! ## Per-Op shifted lemmas

    The forms the chunk-level induction actually consumes. `i` is
    the IR frame (static gas pre-charged), the Effect interpreter
    runs on the shifted frame `{ i with gasLeft := i.gasLeft +
    (c + g), pc := pcv }` where `c` is THIS op's static cost and
    `g` the static cost of the ops after it. Conclusion: one
    `step1` lands on the shifted successor, with the offset now
    down to `g` and pc advanced.

    The `i2.message = i.message ∧ i2.halted = i.halted` conjuncts
    let the induction re-establish its side conditions without a
    70-arm `execOp` preservation lemma. -/

theorem step1_add_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x01)
    (hIR : IR.execOp i .add = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨a, b, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (a + b) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  refine ⟨?_, rfl, rfl⟩
  -- The simp below rewrites `i.halted → false` INSIDE the record
  -- literals, so the IsAddStep witness is stated over the
  -- `halted := false` variants to match the post-simp goal.
  have hIsAdd : Evm.Frontier.Spec.IsAddStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false }
      { i with stack := (a + b) :: rest,
               gasLeft := i.gasLeft + g,
               pc := pcv + 1, halted := false } := by
    refine ⟨a, b, rest, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩
    simp [nat_add_sub_mid]
  have hAdd := _root_.Evm.Frontier.Spec.Refinement.add_complete _ _ hIsAdd
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.add
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false } = _
  unfold Effect.liftPure
  rw [hAdd]
  simp

theorem step1_mul_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x02)
    (hIR : IR.execOp i .mul = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.low + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨a, b, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (a * b) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  refine ⟨?_, rfl, rfl⟩
  have hIsMul : Evm.Frontier.Spec.IsMulStep
      { i with gasLeft := i.gasLeft + (Gas.low + g), pc := pcv,
               halted := false }
      { i with stack := (a * b) :: rest,
               gasLeft := i.gasLeft + g,
               pc := pcv + 1, halted := false } := by
    refine ⟨a, b, rest, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩
    simp [nat_add_sub_mid]
  have hMul := _root_.Evm.Frontier.Spec.Refinement.mul_complete _ _ hIsMul
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.mul
      { i with gasLeft := i.gasLeft + (Gas.low + g), pc := pcv,
               halted := false } = _
  unfold Effect.liftPure
  rw [hMul]
  simp

theorem step1_sub_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x03)
    (hIR : IR.execOp i .sub = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨a, b, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (a - b) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  refine ⟨?_, rfl, rfl⟩
  have hIsSub : Evm.Frontier.Spec.IsSubStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false }
      { i with stack := (a - b) :: rest,
               gasLeft := i.gasLeft + g,
               pc := pcv + 1, halted := false } := by
    refine ⟨a, b, rest, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩
    simp [nat_add_sub_mid]
  have hSub := _root_.Evm.Frontier.Spec.Refinement.sub_complete _ _ hIsSub
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.sub
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false } = _
  unfold Effect.liftPure
  rw [hSub]
  simp

theorem step1_pop_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x50)
    (hIR : IR.execOp i .pop = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp : Stack.pop i.stack with _ | ⟨a, s⟩
  · rw [hp] at hIR; simp at hIR
  rw [hp] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.pop
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv,
               halted := false } = _
  have hPop : Evm.Frontier.Vm.Instructions.pop
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv,
               halted := false }
      = .ok { i with stack := s, gasLeft := i.gasLeft + g, pc := pcv + 1,
                     halted := false } := by
    simp [Evm.Frontier.Vm.Instructions.pop, bind, Except.bind,
          charge_shifted i.gasLeft Gas.base g, hp, pure, Except.pure]
  unfold Effect.liftPure
  rw [hPop]
  simp

theorem step1_mload_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x51)
    (hIR : IR.execOp i .mload = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp : Stack.pop i.stack with _ | ⟨off, s⟩
  · rw [hp] at hIR; simp at hIR
  rw [hp] at hIR
  simp only at hIR
  rcases hcm : Instructions.chargeMemory i.gasLeft i.memory off.toNat 32
      with _ | ⟨gl, mem⟩
  · rw [hcm] at hIR; simp at hIR
  rw [hcm] at hIR
  simp only at hIR
  rcases hpush : Stack.push s (Evm.U256.ofBytesBE (Memory.read mem off.toNat 32))
      with _ | s2
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.mload
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false } = _
  have hMload : Evm.Frontier.Vm.Instructions.mload
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false }
      = .ok { i with stack := s2, memory := mem, gasLeft := gl + g,
                     pc := pcv + 1, halted := false } := by
    simp [Evm.Frontier.Vm.Instructions.mload, bind, Except.bind,
          charge_shifted i.gasLeft Gas.veryLow g, hp,
          chargeMemory_shifted g hcm, hpush, pure, Except.pure]
  unfold Effect.liftPure
  rw [hMload]
  simp

theorem step1_mstore_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x52)
    (hIR : IR.execOp i .mstore = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨off, value, s⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hcm : Instructions.chargeMemory i.gasLeft i.memory off.toNat 32
      with _ | ⟨gl, mem⟩
  · rw [hcm] at hIR; simp at hIR
  rw [hcm] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.mstore
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false } = _
  have hMstore : Evm.Frontier.Vm.Instructions.mstore
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false }
      = .ok { i with stack := s,
                     memory := Memory.write mem off.toNat
                                 (Evm.U256.toBytesBE value),
                     gasLeft := gl + g, pc := pcv + 1,
                     halted := false } := by
    simp [Evm.Frontier.Vm.Instructions.mstore, bind, Except.bind,
          charge_shifted i.gasLeft Gas.veryLow g, hp2,
          chargeMemory_shifted g hcm, pure, Except.pure]
  unfold Effect.liftPure
  rw [hMstore]
  simp

/-! ### Generic shifted cores for pure-stack ops

    One core per stack-arity (binary / unary / ternary). Each takes
    the op's `IR.execOp` success in do-block form — a wrapper's
    `IR.execOp i .x = .ok i2` hypothesis unifies with it by
    delta/iota/beta, provided `f` is passed EXPLICITLY — and
    concludes the gas-shifted `liftPure` step against the
    corresponding `Instructions.run*` handler. A per-op wrapper is
    then ~10 lines: reduce the `step1` dispatch via the opcode
    literal and close with the core by defeq
    (`Instructions.x` delta-unfolds to `run* gas f`). -/

private theorem liftPure_binary_shifted (i i2 : Evm) (g pcv : Nat)
    (gas : Gas.Gas) (f : Evm.U256 → Evm.U256 → Evm.U256)
    (hHalt : i.halted = false)
    (hIR : (do
        let (a, b, s) ← Stack.pop2 i.stack
        let s ← Stack.push s (f a b)
        pure { i with stack := s } : Except Exception Evm) = .ok i2) :
    Effect.liftPure (Instructions.runBinary gas f)
      { i with gasLeft := i.gasLeft + (gas + g), pc := pcv, halted := false }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨a, b, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (f a b) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  refine ⟨?_, rfl, rfl⟩
  have hIs : Evm.Frontier.Spec.IsBinaryStep f gas
      { i with gasLeft := i.gasLeft + (gas + g), pc := pcv,
               halted := false }
      { i with stack := (f a b) :: rest,
               gasLeft := i.gasLeft + g,
               pc := pcv + 1, halted := false } := by
    refine ⟨a, b, rest, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩
    simp [nat_add_sub_mid]
  have hRun := _root_.Evm.Frontier.Spec.Refinement.runBinary_complete
    gas f _ _ hIs
  unfold Effect.liftPure
  rw [hRun]
  simp [hHalt]

private theorem liftPure_unary_shifted (i i2 : Evm) (g pcv : Nat)
    (gas : Gas.Gas) (f : Evm.U256 → Evm.U256)
    (hHalt : i.halted = false)
    (hIR : (do
        let (a, s) ← Stack.pop i.stack
        let s ← Stack.push s (f a)
        pure { i with stack := s } : Except Exception Evm) = .ok i2) :
    Effect.liftPure (Instructions.runUnary gas f)
      { i with gasLeft := i.gasLeft + (gas + g), pc := pcv, halted := false }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  simp only [bind, Except.bind] at hIR
  rcases hp : Stack.pop i.stack with _ | ⟨a, rest⟩
  · rw [hp] at hIR; simp at hIR
  rw [hp] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (f a) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  refine ⟨?_, rfl, rfl⟩
  have hIs : Evm.Frontier.Spec.IsUnaryStep f gas
      { i with gasLeft := i.gasLeft + (gas + g), pc := pcv,
               halted := false }
      { i with stack := (f a) :: rest,
               gasLeft := i.gasLeft + g,
               pc := pcv + 1, halted := false } := by
    refine ⟨a, rest, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩
    simp [nat_add_sub_mid]
  have hRun := _root_.Evm.Frontier.Spec.Refinement.runUnary_complete
    gas f _ _ hIs
  unfold Effect.liftPure
  rw [hRun]
  simp [hHalt]

private theorem liftPure_ternary_shifted (i i2 : Evm) (g pcv : Nat)
    (gas : Gas.Gas) (f : Evm.U256 → Evm.U256 → Evm.U256 → Evm.U256)
    (hHalt : i.halted = false)
    (hIR : (do
        let (a, b, c, s) ← Stack.pop3 i.stack
        let s ← Stack.push s (f a b c)
        pure { i with stack := s } : Except Exception Evm) = .ok i2) :
    Effect.liftPure (Instructions.runTernary gas f)
      { i with gasLeft := i.gasLeft + (gas + g), pc := pcv, halted := false }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  simp only [bind, Except.bind] at hIR
  rcases hp3 : Stack.pop3 i.stack with _ | ⟨a, b, c, rest⟩
  · rw [hp3] at hIR; simp at hIR
  rw [hp3] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (f a b c) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop3_eq_ok_iff _ _ _ _ _).mp hp3
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  refine ⟨?_, rfl, rfl⟩
  have hIs : Evm.Frontier.Spec.IsTernaryStep f gas
      { i with gasLeft := i.gasLeft + (gas + g), pc := pcv,
               halted := false }
      { i with stack := (f a b c) :: rest,
               gasLeft := i.gasLeft + g,
               pc := pcv + 1, halted := false } := by
    refine ⟨a, b, c, rest, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩
    simp [nat_add_sub_mid]
  have hRun := _root_.Evm.Frontier.Spec.Refinement.runTernary_complete
    gas f _ _ hIs
  unfold Effect.liftPure
  rw [hRun]
  simp [hHalt]

/-! ### Per-op `step1` wrappers (Phase 2a family)

    18 ops × ~12 lines, all closed by the generic cores above. The
    `f` arguments are the VERBATIM lambdas from `Spec.Step`'s
    abbrevs / the `Instructions` handlers — defeq glue depends on
    it. -/

theorem step1_div_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x04)
    (hIR : IR.execOp i .div = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.low + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_binary_shifted i i2 g pcv Gas.low
      (fun a b => if b = 0 then 0 else BitVec.udiv a b) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_sdiv_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x05)
    (hIR : IR.execOp i .sdiv = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.low + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_binary_shifted i i2 g pcv Gas.low
      (fun a b => if b = 0 then 0 else BitVec.sdiv a b) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_mod_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x06)
    (hIR : IR.execOp i .mod = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.low + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_binary_shifted i i2 g pcv Gas.low
      (fun a b => if b = 0 then 0 else BitVec.umod a b) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_smod_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x07)
    (hIR : IR.execOp i .smod = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.low + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_binary_shifted i i2 g pcv Gas.low
      (fun a b => if b = 0 then 0 else BitVec.srem a b) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_addmod_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x08)
    (hIR : IR.execOp i .addmod = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.mid + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_ternary_shifted i i2 g pcv Gas.mid
      (fun a b n =>
        if n = 0 then 0 else Evm.U256.ofNat ((a.toNat + b.toNat) % n.toNat)) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_mulmod_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x09)
    (hIR : IR.execOp i .mulmod = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.mid + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_ternary_shifted i i2 g pcv Gas.mid
      (fun a b n =>
        if n = 0 then 0 else Evm.U256.ofNat ((a.toNat * b.toNat) % n.toNat)) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_signextend_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x0b)
    (hIR : IR.execOp i .signextend = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.low + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_binary_shifted i i2 g pcv Gas.low
      Instructions.signExtend hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_lt_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x10)
    (hIR : IR.execOp i .lt = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_binary_shifted i i2 g pcv Gas.veryLow
      (fun a b => if a < b then 1 else 0) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_gt_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x11)
    (hIR : IR.execOp i .gt = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_binary_shifted i i2 g pcv Gas.veryLow
      (fun a b => if a > b then 1 else 0) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_slt_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x12)
    (hIR : IR.execOp i .slt = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_binary_shifted i i2 g pcv Gas.veryLow
      (fun a b => if BitVec.slt a b then 1 else 0) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_sgt_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x13)
    (hIR : IR.execOp i .sgt = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_binary_shifted i i2 g pcv Gas.veryLow
      (fun a b => if BitVec.slt b a then 1 else 0) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_eq_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x14)
    (hIR : IR.execOp i .eq = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_binary_shifted i i2 g pcv Gas.veryLow
      (fun a b => if a = b then 1 else 0) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_iszero_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x15)
    (hIR : IR.execOp i .iszero = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_unary_shifted i i2 g pcv Gas.veryLow
      (fun a => if a = 0 then 1 else 0) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_and_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x16)
    (hIR : IR.execOp i .and_ = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_binary_shifted i i2 g pcv Gas.veryLow
      (fun a b => a &&& b) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_or_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x17)
    (hIR : IR.execOp i .or_ = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_binary_shifted i i2 g pcv Gas.veryLow
      (fun a b => a ||| b) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_xor_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x18)
    (hIR : IR.execOp i .xor_ = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_binary_shifted i i2 g pcv Gas.veryLow
      (fun a b => a ^^^ b) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_not_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x19)
    (hIR : IR.execOp i .not_ = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_unary_shifted i i2 g pcv Gas.veryLow
      (fun a => ~~~ a) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_byte_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x1a)
    (hIR : IR.execOp i .byte = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_binary_shifted i i2 g pcv Gas.veryLow
      Instructions.byteOf hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

/-- EXP is the one op whose gas splits across the two charge sites:
    the chunk pre-charges the static `Gas.exp`, the IR op charges
    the dynamic per-byte component at runtime (like MLOAD/MSTORE
    charge memory expansion), and `Instructions.exp` charges both at
    once — so this lemma is bespoke rather than a generic-core
    wrapper. -/
theorem step1_exp_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x0a)
    (hIR : IR.execOp i .exp = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.exp + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨base, e, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hch : Gas.charge i.gasLeft
      (Gas.expByte * Instructions.expByteSize e.toNat) with _ | gl
  · rw [hch] at hIR; simp at hIR
  rw [hch] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest
      (Evm.U256.ofNat (Instructions.powMod base.toNat e.toNat (1 <<< 256)))
      with _ | s2
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  obtain ⟨hdle, rfl⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
  refine ⟨?_, rfl, rfl⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.exp
      { i with gasLeft := i.gasLeft + (Gas.exp + g), pc := pcv,
               halted := false } = _
  have hch2 : Gas.charge (i.gasLeft + (Gas.exp + g))
      (Gas.exp + Gas.expByte * Instructions.expByteSize e.toNat)
      = .ok (i.gasLeft - Gas.expByte * Instructions.expByteSize e.toNat + g) :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mpr
      ⟨nat_le_add_mid2 _ _ _ _ hdle, (nat_add_sub_mid2 _ _ _ g hdle).symm⟩
  have hExp : Evm.Frontier.Vm.Instructions.exp
      { i with gasLeft := i.gasLeft + (Gas.exp + g), pc := pcv,
               halted := false }
      = .ok { i with stack := s2,
                     gasLeft := i.gasLeft
                       - Gas.expByte * Instructions.expByteSize e.toNat + g,
                     pc := pcv + 1, halted := false } := by
    simp only [Evm.Frontier.Vm.Instructions.exp, bind, Except.bind,
               hp2, hch2, pure, Except.pure]
    rw [hpush]
  unfold Effect.liftPure
  rw [hExp]
  simp

/-- KECCAK256 (0x20): like EXP, the gas splits across the two charge
    sites — the chunk pre-charges the static `Gas.keccak256`, the IR
    op charges the per-word component plus memory expansion at
    runtime, while `Instructions.keccak256` charges base + per-word
    in one `Gas.charge` before `chargeMemory`. -/
theorem step1_keccak256_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x20)
    (hIR : IR.execOp i .keccak256 = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.keccak256 + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨offset, len, s⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hch : Gas.charge i.gasLeft
      (Gas.keccak256Word * ((len.toNat + 31) / 32)) with _ | gl1
  · rw [hch] at hIR; simp at hIR
  rw [hch] at hIR
  simp only at hIR
  rcases hcm : Instructions.chargeMemory gl1 i.memory offset.toNat len.toNat
      with _ | ⟨gl, mem⟩
  · rw [hcm] at hIR; simp at hIR
  rw [hcm] at hIR
  simp only at hIR
  rcases hpush : Stack.push s
      (Evm.Crypto.keccak256 (Memory.read mem offset.toNat len.toNat))
      with _ | s2
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  obtain ⟨hdle, rfl⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
  refine ⟨?_, rfl, rfl⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.keccak256
      { i with gasLeft := i.gasLeft + (Gas.keccak256 + g), pc := pcv,
               halted := false } = _
  have hch2 : Gas.charge (i.gasLeft + (Gas.keccak256 + g))
      (Gas.keccak256 + Gas.keccak256Word * ((len.toNat + 31) / 32))
      = .ok (i.gasLeft - Gas.keccak256Word * ((len.toNat + 31) / 32) + g) :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mpr
      ⟨nat_le_add_mid2 _ _ _ _ hdle, (nat_add_sub_mid2 _ _ _ g hdle).symm⟩
  have hK : Evm.Frontier.Vm.Instructions.keccak256
      { i with gasLeft := i.gasLeft + (Gas.keccak256 + g), pc := pcv,
               halted := false }
      = .ok { i with stack := s2, memory := mem, gasLeft := gl + g,
                     pc := pcv + 1, halted := false } := by
    simp only [Evm.Frontier.Vm.Instructions.keccak256, bind, Except.bind,
               hp2, hch2, chargeMemory_shifted g hcm, pure, Except.pure]
    rw [hpush]
  unfold Effect.liftPure
  rw [hK]
  simp

/-- CALLDATACOPY (0x37): split-charge shape like KECCAK256 — static
    `Gas.veryLow` pre-charged, per-word copy cost + memory expansion
    charged by the IR op; `Instructions.copyToMemory` charges
    `veryLow + copy·words` in one `Gas.charge`. -/
theorem step1_calldatacopy_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x37)
    (hIR : IR.execOp i .calldatacopy = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp3 : Stack.pop3 i.stack with _ | ⟨dest, off, len, s⟩
  · rw [hp3] at hIR; simp at hIR
  rw [hp3] at hIR
  simp only at hIR
  rcases hch : Gas.charge i.gasLeft (Gas.copy * ((len.toNat + 31) / 32))
      with _ | gl1
  · rw [hch] at hIR; simp at hIR
  rw [hch] at hIR
  simp only at hIR
  rcases hcm : Instructions.chargeMemory gl1 i.memory dest.toNat len.toNat
      with _ | ⟨gl, mem⟩
  · rw [hcm] at hIR; simp at hIR
  rw [hcm] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  obtain ⟨hdle, rfl⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
  refine ⟨?_, rfl, rfl⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.calldatacopy
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false } = _
  have hch2 : Gas.charge (i.gasLeft + (Gas.veryLow + g))
      (Gas.veryLow + Gas.copy * ((len.toNat + 31) / 32))
      = .ok (i.gasLeft - Gas.copy * ((len.toNat + 31) / 32) + g) :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mpr
      ⟨nat_le_add_mid2 _ _ _ _ hdle, (nat_add_sub_mid2 _ _ _ g hdle).symm⟩
  have hCopy : Evm.Frontier.Vm.Instructions.calldatacopy
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false }
      = .ok { i with stack := s,
                     memory := Memory.write mem dest.toNat
                       (Evm.Bytes.sliceZeroPad i.message.data off.toNat len.toNat),
                     gasLeft := gl + g, pc := pcv + 1, halted := false } := by
    simp only [Evm.Frontier.Vm.Instructions.calldatacopy,
               Evm.Frontier.Vm.Instructions.copyToMemory, bind, Except.bind,
               hp3, hch2, chargeMemory_shifted g hcm, pure, Except.pure]
  unfold Effect.liftPure
  rw [hCopy]
  simp

/-- CODECOPY (0x39): identical to CALLDATACOPY with the source buffer
    `message.code` instead of `message.data`. -/
theorem step1_codecopy_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x39)
    (hIR : IR.execOp i .codecopy = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp3 : Stack.pop3 i.stack with _ | ⟨dest, off, len, s⟩
  · rw [hp3] at hIR; simp at hIR
  rw [hp3] at hIR
  simp only at hIR
  rcases hch : Gas.charge i.gasLeft (Gas.copy * ((len.toNat + 31) / 32))
      with _ | gl1
  · rw [hch] at hIR; simp at hIR
  rw [hch] at hIR
  simp only at hIR
  rcases hcm : Instructions.chargeMemory gl1 i.memory dest.toNat len.toNat
      with _ | ⟨gl, mem⟩
  · rw [hcm] at hIR; simp at hIR
  rw [hcm] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  obtain ⟨hdle, rfl⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
  refine ⟨?_, rfl, rfl⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.codecopy
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false } = _
  have hch2 : Gas.charge (i.gasLeft + (Gas.veryLow + g))
      (Gas.veryLow + Gas.copy * ((len.toNat + 31) / 32))
      = .ok (i.gasLeft - Gas.copy * ((len.toNat + 31) / 32) + g) :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mpr
      ⟨nat_le_add_mid2 _ _ _ _ hdle, (nat_add_sub_mid2 _ _ _ g hdle).symm⟩
  have hCopy : Evm.Frontier.Vm.Instructions.codecopy
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false }
      = .ok { i with stack := s,
                     memory := Memory.write mem dest.toNat
                       (Evm.Bytes.sliceZeroPad i.message.code off.toNat len.toNat),
                     gasLeft := gl + g, pc := pcv + 1, halted := false } := by
    simp only [Evm.Frontier.Vm.Instructions.codecopy,
               Evm.Frontier.Vm.Instructions.copyToMemory, bind, Except.bind,
               hp3, hch2, chargeMemory_shifted g hcm, pure, Except.pure]
  unfold Effect.liftPure
  rw [hCopy]
  simp

/-! ### Nullary-push shifted core (Phase 2c tranche A)

    One core for the 15 `runNullaryPush`-shaped ops (ADDRESS …
    GASLIMIT, PC, MSIZE, GAS). The pushed value is abstracted twice:
    `value` is the handler/spec lambda, `v` is the literal the IR op
    pushes, and `hval` connects them on the shifted frame — `rfl`
    for everything except GAS, whose IR literal `gasLeft + rem`
    needs `nat_add_sub_mid` to match the spec's post-charge read. -/

private theorem liftPure_nullaryPush_shifted (i i2 : Evm) (g pcv : Nat)
    (gas : Gas.Gas) (value : Evm → Evm.U256) (v : Evm.U256)
    (hval : value { i with gasLeft := i.gasLeft + (gas + g), pc := pcv,
                           halted := false } = v)
    (hHalt : i.halted = false)
    (hIR : (do
        let s ← Stack.push i.stack v
        pure { i with stack := s } : Except Exception Evm) = .ok i2) :
    Effect.liftPure (Instructions.runNullaryPush gas value)
      { i with gasLeft := i.gasLeft + (gas + g), pc := pcv, halted := false }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  simp only [bind, Except.bind] at hIR
  rcases hpush : Stack.push i.stack v with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  refine ⟨?_, rfl, rfl⟩
  have hIs : Evm.Frontier.Spec.IsNullaryPushStep value gas
      { i with gasLeft := i.gasLeft + (gas + g), pc := pcv,
               halted := false }
      { i with stack := v :: i.stack,
               gasLeft := i.gasLeft + g,
               pc := pcv + 1, halted := false } := by
    refine ⟨hlt, nat_le_add_mid _ _ _, ?_⟩
    rw [hval]
    simp [nat_add_sub_mid]
  have hRun := _root_.Evm.Frontier.Spec.Refinement.runNullaryPush_complete
    gas value _ _ hIs
  unfold Effect.liftPure
  rw [hRun]
  simp [hHalt]

theorem step1_address_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x30)
    (hIR : IR.execOp i .address = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_nullaryPush_shifted i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.message.currentTarget.toNat)
      (Evm.U256.ofNat i.message.currentTarget.toNat)
      rfl hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_origin_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x32)
    (hIR : IR.execOp i .origin = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_nullaryPush_shifted i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.env.origin.toNat)
      (Evm.U256.ofNat i.env.origin.toNat)
      rfl hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_caller_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x33)
    (hIR : IR.execOp i .caller = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_nullaryPush_shifted i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.message.caller.toNat)
      (Evm.U256.ofNat i.message.caller.toNat)
      rfl hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_callvalue_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x34)
    (hIR : IR.execOp i .callvalue = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_nullaryPush_shifted i i2 g pcv Gas.base
      (fun evm => evm.message.value)
      (i.message.value)
      rfl hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_calldatasize_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x36)
    (hIR : IR.execOp i .calldatasize = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_nullaryPush_shifted i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.message.data.size)
      (Evm.U256.ofNat i.message.data.size)
      rfl hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_codesize_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x38)
    (hIR : IR.execOp i .codesize = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_nullaryPush_shifted i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.message.code.size)
      (Evm.U256.ofNat i.message.code.size)
      rfl hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_gasprice_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x3a)
    (hIR : IR.execOp i .gasprice = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_nullaryPush_shifted i i2 g pcv Gas.base
      (fun evm => evm.env.gasPrice)
      (i.env.gasPrice)
      rfl hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_coinbase_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x41)
    (hIR : IR.execOp i .coinbase = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_nullaryPush_shifted i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.env.coinbase.toNat)
      (Evm.U256.ofNat i.env.coinbase.toNat)
      rfl hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_timestamp_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x42)
    (hIR : IR.execOp i .timestamp = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_nullaryPush_shifted i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.env.timestamp)
      (Evm.U256.ofNat i.env.timestamp)
      rfl hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_number_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x43)
    (hIR : IR.execOp i .number = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_nullaryPush_shifted i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.env.number)
      (Evm.U256.ofNat i.env.number)
      rfl hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_difficulty_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x44)
    (hIR : IR.execOp i .prevrandao = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_nullaryPush_shifted i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.env.difficulty)
      (Evm.U256.ofNat i.env.difficulty)
      rfl hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_gaslimit_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x45)
    (hIR : IR.execOp i .gaslimit = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_nullaryPush_shifted i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.env.gasLimit)
      (Evm.U256.ofNat i.env.gasLimit)
      rfl hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_pc_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x58)
    (hIR : IR.execOp i (.pc pcv) = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_nullaryPush_shifted i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.pc)
      (Evm.U256.ofNat pcv)
      rfl hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_msize_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x59)
    (hIR : IR.execOp i .msize = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_nullaryPush_shifted i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.memory.size)
      (Evm.U256.ofNat i.memory.size)
      rfl hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_gas_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x5a)
    (hIR : IR.execOp i (.gas g) = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hRun, hmsg, hhalt⟩ :=
    liftPure_nullaryPush_shifted i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat (evm.gasLeft - Gas.base))
      (Evm.U256.ofNat (i.gasLeft + g))
      (congrArg Evm.U256.ofNat (nat_add_sub_mid i.gasLeft Gas.base g)) hHalt hIR
  refine ⟨?_, hmsg, hhalt⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  exact hRun

theorem step1_calldataload_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x35)
    (hIR : IR.execOp i .calldataload = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp : Stack.pop i.stack with _ | ⟨a, s⟩
  · rw [hp] at hIR; simp at hIR
  rw [hp] at hIR
  simp only at hIR
  rcases hpush : Stack.push s
      (Evm.U256.ofBytesBE (Evm.Bytes.sliceZeroPad i.message.data a.toNat 32))
      with _ | s2
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.calldataload
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false } = _
  have hCdl : Evm.Frontier.Vm.Instructions.calldataload
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false }
      = .ok { i with stack := s2, gasLeft := i.gasLeft + g, pc := pcv + 1,
                     halted := false } := by
    simp [Evm.Frontier.Vm.Instructions.calldataload, bind, Except.bind,
          charge_shifted i.gasLeft Gas.veryLow g, hp, hpush,
          pure, Except.pure]
  unfold Effect.liftPure
  rw [hCdl]
  simp

theorem step1_mstore8_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x53)
    (hIR : IR.execOp i .mstore8 = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨off, value, s⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hcm : Instructions.chargeMemory i.gasLeft i.memory off.toNat 1
      with _ | ⟨gl, mem⟩
  · rw [hcm] at hIR; simp at hIR
  rw [hcm] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.mstore8
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false } = _
  have hMstore8 : Evm.Frontier.Vm.Instructions.mstore8
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv,
               halted := false }
      = .ok { i with stack := s,
                     memory := Memory.writeByte mem off.toNat
                                 (UInt8.ofNat (value.toNat &&& 0xff)),
                     gasLeft := gl + g, pc := pcv + 1,
                     halted := false } := by
    simp [Evm.Frontier.Vm.Instructions.mstore8, bind, Except.bind,
          charge_shifted i.gasLeft Gas.veryLow g, hp2,
          chargeMemory_shifted g hcm, pure, Except.pure]
  unfold Effect.liftPure
  rw [hMstore8]
  simp

theorem step1_jumpdest_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x5b)
    (hIR : IR.execOp i .jumpdest = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.jumpDest + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.jumpdest
      { i with gasLeft := i.gasLeft + (Gas.jumpDest + g), pc := pcv,
               halted := false } = _
  have hJd : Evm.Frontier.Vm.Instructions.jumpdest
      { i with gasLeft := i.gasLeft + (Gas.jumpDest + g), pc := pcv,
               halted := false }
      = .ok { i with gasLeft := i.gasLeft + g, pc := pcv + 1,
                     halted := false } := by
    simp [Evm.Frontier.Vm.Instructions.jumpdest, bind, Except.bind,
          charge_shifted i.gasLeft Gas.jumpDest g, pure, Except.pure]
  unfold Effect.liftPure
  rw [hJd]
  simp

/-! ## PUSH dispatch + shifted lemma

    PUSH is `step1`'s catch-all arm, so reducing the dispatch needs
    the opcode as a literal — `interval_cases` bashes the 32 cases
    once, and everything downstream uses the abstract form. -/

theorem step1_dispatch_push (evm : Evm) (nop : Nat)
    (hHalt : evm.halted = false)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : (evm.message.code.get! evm.pc).toNat = nop)
    (hlo : 0x60 ≤ nop) (hhi : nop ≤ 0x7f) :
    Effect.step1 evm
      = Effect.liftPure (Instructions.push (nop - 0x5f)) evm := by
  interval_cases nop <;>
  · simp only [Effect.step1, hHalt, hCode, ite_false,
               show ¬ (evm.pc ≥ evm.message.code.size) from
                 Nat.not_le.mpr hSize]
    rfl

theorem step1_push_shifted (i i2 : Evm) (g pcv nop : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : (i.message.code.get! pcv).toNat = nop)
    (hlo : 0x60 ≤ nop) (hhi : nop ≤ 0x7f)
    (hIR : IR.execOp i
        (.push (nop - 0x5f) (readImmediate i.message.code pcv (nop - 0x5f)))
      = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g,
                            pc := pcv + 1 + (nop - 0x5f) } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hpush : Stack.push i.stack
      (readImmediate i.message.code pcv (nop - 0x5f)) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  rw [step1_dispatch_push
        { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
        nop hHalt hSize hCode hlo hhi]
  have hPush : Evm.Frontier.Vm.Instructions.push (nop - 0x5f)
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .ok { i with stack := s', gasLeft := i.gasLeft + g,
                     pc := pcv + 1 + (nop - 0x5f) } := by
    unfold Evm.Frontier.Vm.Instructions.push
    rw [show IR.readImmediate i.message.code pcv (nop - 0x5f)
          = Evm.U256.ofBytesBE
              (Evm.Bytes.sliceZeroPad i.message.code (pcv + 1) (nop - 0x5f))
        from rfl] at hpush
    simp [bind, Except.bind, charge_shifted i.gasLeft Gas.veryLow g,
          hpush, pure, Except.pure]
  show Effect.liftPure (Instructions.push (nop - 0x5f))
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv } = _
  unfold Effect.liftPure
  rw [hPush]
  simp [hHalt]

/-! ## DUP / SWAP dispatch + shifted lemmas

    DUP and SWAP live in `step1`'s catch-all arm alongside PUSH, so
    the dispatch lemmas case-bash their 16-opcode ranges the same
    way. -/

theorem step1_dispatch_dup (evm : Evm) (nop : Nat)
    (hHalt : evm.halted = false)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : (evm.message.code.get! evm.pc).toNat = nop)
    (hlo : 0x80 ≤ nop) (hhi : nop ≤ 0x8f) :
    Effect.step1 evm
      = Effect.liftPure (Instructions.dup (nop - 0x7f)) evm := by
  interval_cases nop <;>
  · simp only [Effect.step1, hHalt, hCode, ite_false,
               show ¬ (evm.pc ≥ evm.message.code.size) from
                 Nat.not_le.mpr hSize]
    rfl

theorem step1_dispatch_swap (evm : Evm) (nop : Nat)
    (hHalt : evm.halted = false)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : (evm.message.code.get! evm.pc).toNat = nop)
    (hlo : 0x90 ≤ nop) (hhi : nop ≤ 0x9f) :
    Effect.step1 evm
      = Effect.liftPure (Instructions.swap (nop - 0x8f)) evm := by
  interval_cases nop <;>
  · simp only [Effect.step1, hHalt, hCode, ite_false,
               show ¬ (evm.pc ≥ evm.message.code.size) from
                 Nat.not_le.mpr hSize]
    rfl

theorem step1_dup_shifted (i i2 : Evm) (g pcv nop : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : (i.message.code.get! pcv).toNat = nop)
    (hlo : 0x80 ≤ nop) (hhi : nop ≤ 0x8f)
    (hIR : IR.execOp i (.dup (nop - 0x7f)) = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hd : Stack.dup i.stack (nop - 0x7f) with _ | s'
  · rw [hd] at hIR; simp at hIR
  rw [hd] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  rw [step1_dispatch_dup
        { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
        nop hHalt hSize hCode hlo hhi]
  have hDup : Evm.Frontier.Vm.Instructions.dup (nop - 0x7f)
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .ok { i with stack := s', gasLeft := i.gasLeft + g,
                     pc := pcv + 1 } := by
    simp [Evm.Frontier.Vm.Instructions.dup, bind, Except.bind,
          charge_shifted i.gasLeft Gas.veryLow g, hd, pure, Except.pure]
  unfold Effect.liftPure
  rw [hDup]
  simp [hHalt]

theorem step1_swap_shifted (i i2 : Evm) (g pcv nop : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : (i.message.code.get! pcv).toNat = nop)
    (hlo : 0x90 ≤ nop) (hhi : nop ≤ 0x9f)
    (hIR : IR.execOp i (.swap (nop - 0x8f)) = .ok i2) :
    Effect.step1 { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .continue { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hs : Stack.swap i.stack (nop - 0x8f) with _ | s'
  · rw [hs] at hIR; simp at hIR
  rw [hs] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  rw [step1_dispatch_swap
        { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
        nop hHalt hSize hCode hlo hhi]
  have hSwap : Evm.Frontier.Vm.Instructions.swap (nop - 0x8f)
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      = .ok { i with stack := s', gasLeft := i.gasLeft + g,
                     pc := pcv + 1 } := by
    simp [Evm.Frontier.Vm.Instructions.swap, bind, Except.bind,
          charge_shifted i.gasLeft Gas.veryLow g, hs, pure, Except.pure]
  unfold Effect.liftPure
  rw [hSwap]
  simp [hHalt]

/-! ## LOG dispatch

    LOG0-4 live in `step1`'s catch-all arm as a range test, so the
    dispatch lemma case-bashes the 5-opcode range like PUSH/DUP/SWAP.
    Unlike the literal arms it does NOT rebuild the frame, so the
    shifted lemma must carry `hHalt` through its own simp set. -/

theorem step1_dispatch_log (evm : Evm) (nop : Nat)
    (hHalt : evm.halted = false)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : (evm.message.code.get! evm.pc).toNat = nop)
    (hlo : 0xa0 ≤ nop) (hhi : nop ≤ 0xa4) :
    Effect.step1 evm = Effect.doLog (nop - 0xa0) evm := by
  interval_cases nop <;>
  · simp only [Effect.step1, hHalt, hCode, ite_false,
               show ¬ (evm.pc ≥ evm.message.code.size) from
                 Nat.not_le.mpr hSize]
    rfl

/-! ## Terminator lemmas

    The chunk gas at a terminator is 0 (terminators charge nothing
    statically in this slice), so these are stated without the
    gas offset — the chunk proof normalizes `+ 0` away first. -/

theorem step1_stop_halts (i : Evm) (pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x00) :
    Effect.step1 { i with pc := pcv }
      = .halt { i with halted := true, pc := pcv } i.output := by
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  rfl

theorem step1_endOfCode_halts (i : Evm) (pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv ≥ i.message.code.size) :
    Effect.step1 { i with pc := pcv }
      = .halt { i with halted := true, pc := pcv } i.output := by
  simp only [Effect.step1, hHalt,
             show (pcv ≥ i.message.code.size) from hSize, ite_true]
  rfl

theorem step1_ret_halts (i i' : Evm) (pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0xf3)
    (hTerm : IR.execTerm i (pcv + 1) .ret = .ok i') :
    Effect.step1 { i with pc := pcv } = .halt i' i'.output := by
  unfold IR.execTerm at hTerm
  simp only [bind, Except.bind] at hTerm
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨off, len, s⟩
  · rw [hp2] at hTerm; simp at hTerm
  rw [hp2] at hTerm
  simp only at hTerm
  rcases hcm : Instructions.chargeMemory i.gasLeft i.memory off.toNat len.toNat
      with _ | ⟨gl, mem⟩
  · rw [hcm] at hTerm; simp at hTerm
  rw [hcm] at hTerm
  simp only [pure, Except.pure, Except.ok.injEq] at hTerm
  subst hTerm
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.return_
      { i with pc := pcv, halted := false } = _
  have hRet : Evm.Frontier.Vm.Instructions.return_
      { i with pc := pcv, halted := false }
      = .ok { i with gasLeft := gl, memory := mem, stack := s,
                     output := Memory.read mem off.toNat len.toNat,
                     halted := true, pc := pcv + 1 } := by
    simp [Evm.Frontier.Vm.Instructions.return_, bind, Except.bind,
          hp2, hcm, pure, Except.pure]
  unfold Effect.liftPure
  rw [hRet]
  simp

/-- `runFrameR` one-step unfolding (structural recursion, so `rfl`). -/
private theorem runFrameR_succ (fuel : Nat) (evm : Evm) :
    Effect.runFrameR (fuel + 1) evm =
      match Effect.step1 evm with
      | .continue evm'    => Effect.runFrameR fuel evm'
      | .yield frame eff  =>
        if eff.isState then
          match Effect.handleYield frame eff
              (fun _ => .error .outOfGas) with
          | .ok cont => Effect.runFrameR fuel cont
          | .error e => .error frame e
        else .yield frame eff
      | .halt evm' output => .halt evm' output
      | .error evm' e     => .error evm' e := rfl


/-- `step1` on an already-halted frame: immediate `.halt`. Peels the
    right-hand `runFrame` of the generalized chunk conclusion once the
    IR result is known to be halted. -/
private theorem step1_halted (evm : Evm) (h : evm.halted = true) :
    Effect.step1 evm = .halt evm evm.output := by
  simp [Effect.step1, h]

/-! ## State-yield shifted lemmas

    SLOAD / SSTORE / BALANCE / EXTCODESIZE / EXTCODECOPY / BLOCKHASH /
    LOG0-4 yield in `Effect.step1` and are resolved by `handleYield`
    purely from the frame's own env; `runFrameR` folds that resolution
    in. Each lemma states: ONE fuel tick on the shifted frame lands on
    the shifted IR successor — the same shape as the `.continue` ops'
    `step1_*_shifted` lemmas, just one yield-resolution layer deeper,
    so the conclusion is a `runFrameR` equation rather than a `step1`
    equation. -/

theorem runFrameR_sload_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x54)
    (hIR : IR.execOp i .sload = .ok i2) :
    (∀ fl, Effect.runFrameR (fl + 1)
        { i with gasLeft := i.gasLeft + (Gas.sLoad + g), pc := pcv }
      = Effect.runFrameR fl
        { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 }) ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hIR
  obtain ⟨⟨key, s⟩, hp, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨s2, hpush, hIR⟩ := hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨fun fl => ?_, rfl, rfl⟩
  have hs1 : Effect.step1
      { i with gasLeft := i.gasLeft + (Gas.sLoad + g), pc := pcv }
      = .yield { i with gasLeft := i.gasLeft + g, stack := s, pc := pcv,
                        halted := false } (.sload key) := by
    simp only [Effect.step1, hHalt, hCode, ite_false,
               show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
    show Effect.doSload
        { i with gasLeft := i.gasLeft + (Gas.sLoad + g), pc := pcv,
                 halted := false } = _
    simp only [Effect.doSload, charge_shifted, hp]
  rw [runFrameR_succ, hs1]
  simp only [Effect.YieldEffect.isState, Effect.handleYield,
             Effect.resumeSload, bind, Except.bind, hpush, pure,
             Except.pure, hHalt, ite_true]

theorem runFrameR_sstore_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x55)
    (hIR : IR.execOp i .sstore = .ok i2) :
    (∀ fl, Effect.runFrameR (fl + 1)
        { i with gasLeft := i.gasLeft + (0 + g), pc := pcv }
      = Effect.runFrameR fl
        { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 }) ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  by_cases hSt : i.message.isStatic = true
  · rw [ite_eq_left hSt] at hIR; simp at hIR
  rw [ite_eq_right hSt] at hIR
  have hStf : i.message.isStatic = false := by simpa using hSt
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hIR
  obtain ⟨⟨key, value, s⟩, hp2, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨gl, hch, hIR⟩ := hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  obtain ⟨hdle, hgl⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
  subst hgl
  refine ⟨fun fl => ?_, rfl, rfl⟩
  have hs1 : Effect.step1
      { i with gasLeft := i.gasLeft + (0 + g), pc := pcv }
      = .yield { i with gasLeft := i.gasLeft + (0 + g), stack := s,
                        pc := pcv, halted := false } (.sstore key value) := by
    simp only [Effect.step1, hHalt, hCode, ite_false,
               show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
    show Effect.doSstore
        { i with gasLeft := i.gasLeft + (0 + g), pc := pcv,
                 halted := false } = _
    simp only [Effect.doSstore, hStf, Bool.false_eq_true, ite_false, hp2]
  have hch2 : Gas.charge (i.gasLeft + (0 + g))
      (if i.env.state.getStorage i.message.currentTarget key
            = (0 : Evm.U256) ∧ value ≠ (0 : Evm.U256)
       then Gas.sSet else Gas.sReset)
      = .ok (i.gasLeft -
          (if i.env.state.getStorage i.message.currentTarget key
                = (0 : Evm.U256) ∧ value ≠ (0 : Evm.U256)
           then Gas.sSet else Gas.sReset) + g) :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mpr
      ⟨Nat.le_add_right_of_le hdle,
       by rw [nat_sub_add_comm _ hdle, Nat.zero_add]⟩
  rw [runFrameR_succ, hs1]
  simp only [Effect.YieldEffect.isState, Effect.handleYield,
             Effect.resumeSstore, bind, Except.bind, hch2, pure,
             Except.pure, hHalt, ite_true]

theorem runFrameR_balance_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x31)
    (hIR : IR.execOp i .balance = .ok i2) :
    (∀ fl, Effect.runFrameR (fl + 1)
        { i with gasLeft := i.gasLeft + (Gas.balance + g), pc := pcv }
      = Effect.runFrameR fl
        { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 }) ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hIR
  obtain ⟨⟨addrW, s⟩, hp, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨s2, hpush, hIR⟩ := hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨fun fl => ?_, rfl, rfl⟩
  have hs1 : Effect.step1
      { i with gasLeft := i.gasLeft + (Gas.balance + g), pc := pcv }
      = .yield { i with gasLeft := i.gasLeft + g, stack := s, pc := pcv,
                        halted := false }
          (.balance (Effect.u256ToAddr addrW)) := by
    simp only [Effect.step1, hHalt, hCode, ite_false,
               show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
    show Effect.doBalance
        { i with gasLeft := i.gasLeft + (Gas.balance + g), pc := pcv,
                 halted := false } = _
    simp only [Effect.doBalance, charge_shifted, hp]
  rw [runFrameR_succ, hs1]
  simp only [Effect.YieldEffect.isState, Effect.handleYield,
             Effect.resumeBalance, Effect.u256ToAddr, bind, Except.bind,
             hpush, pure, Except.pure, hHalt, ite_true]

theorem runFrameR_extcodesize_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x3b)
    (hIR : IR.execOp i .extcodesize = .ok i2) :
    (∀ fl, Effect.runFrameR (fl + 1)
        { i with gasLeft := i.gasLeft + (Gas.extCode + g), pc := pcv }
      = Effect.runFrameR fl
        { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 }) ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hIR
  obtain ⟨⟨addrW, s⟩, hp, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨s2, hpush, hIR⟩ := hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨fun fl => ?_, rfl, rfl⟩
  have hs1 : Effect.step1
      { i with gasLeft := i.gasLeft + (Gas.extCode + g), pc := pcv }
      = .yield { i with gasLeft := i.gasLeft + g, stack := s, pc := pcv,
                        halted := false }
          (.extcodesize (Effect.u256ToAddr addrW)) := by
    simp only [Effect.step1, hHalt, hCode, ite_false,
               show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
    show Effect.doExtcodesize
        { i with gasLeft := i.gasLeft + (Gas.extCode + g), pc := pcv,
                 halted := false } = _
    simp only [Effect.doExtcodesize, charge_shifted, hp]
  rw [runFrameR_succ, hs1]
  simp only [Effect.YieldEffect.isState, Effect.handleYield,
             Effect.resumeExtcodesize, Effect.u256ToAddr, bind, Except.bind,
             hpush, pure, Except.pure, hHalt, ite_true]

theorem runFrameR_extcodecopy_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x3c)
    (hIR : IR.execOp i .extcodecopy = .ok i2) :
    (∀ fl, Effect.runFrameR (fl + 1)
        { i with gasLeft := i.gasLeft + (Gas.extCode + g), pc := pcv }
      = Effect.runFrameR fl
        { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 }) ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hIR
  obtain ⟨⟨addrW, s⟩, hp, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨⟨memOff, codeOff, size, s'⟩, hp3, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨⟨gl1, mem⟩, hcm, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨gl2, hch, hIR⟩ := hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  obtain ⟨hdle, hgl⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
  subst hgl
  refine ⟨fun fl => ?_, rfl, rfl⟩
  have hch2 : Gas.charge (gl1 + (Gas.extCode + g))
      (Gas.extCode + Gas.copy * ((size.toNat + 31) / 32))
      = .ok (gl1 - Gas.copy * ((size.toNat + 31) / 32) + g) :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mpr
      ⟨nat_le_add_mid2 _ _ _ _ hdle, (nat_add_sub_mid2 _ _ _ g hdle).symm⟩
  have hs1 : Effect.step1
      { i with gasLeft := i.gasLeft + (Gas.extCode + g), pc := pcv }
      = .yield { i with gasLeft := gl1 - Gas.copy * ((size.toNat + 31) / 32) + g,
                        memory := mem, stack := s', pc := pcv,
                        halted := false }
          (.extcodecopy (Effect.u256ToAddr addrW) memOff.toNat
             codeOff.toNat size.toNat) := by
    simp only [Effect.step1, hHalt, hCode, ite_false,
               show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
    show Effect.doExtcodecopy
        { i with gasLeft := i.gasLeft + (Gas.extCode + g), pc := pcv,
                 halted := false } = _
    simp only [Effect.doExtcodecopy, hp, hp3,
               chargeMemory_shifted (Gas.extCode + g) hcm, hch2]
  rw [runFrameR_succ, hs1]
  simp only [Effect.YieldEffect.isState, Effect.handleYield,
             Effect.resumeExtcodecopy, Effect.u256ToAddr, pure, Except.pure, hHalt, ite_true]

theorem runFrameR_blockhash_shifted (i i2 : Evm) (g pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x40)
    (hIR : IR.execOp i .blockhash = .ok i2) :
    (∀ fl, Effect.runFrameR (fl + 1)
        { i with gasLeft := i.gasLeft + (Gas.blockHash + g), pc := pcv }
      = Effect.runFrameR fl
        { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 }) ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hIR
  obtain ⟨⟨n, s⟩, hp, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨s2, hpush, hIR⟩ := hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨fun fl => ?_, rfl, rfl⟩
  have hs1 : Effect.step1
      { i with gasLeft := i.gasLeft + (Gas.blockHash + g), pc := pcv }
      = .yield { i with gasLeft := i.gasLeft + g, stack := s, pc := pcv,
                        halted := false } (.blockhash n.toNat) := by
    simp only [Effect.step1, hHalt, hCode, ite_false,
               show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
    show Effect.doBlockhash
        { i with gasLeft := i.gasLeft + (Gas.blockHash + g), pc := pcv,
                 halted := false } = _
    simp only [Effect.doBlockhash, charge_shifted, hp]
  rw [runFrameR_succ, hs1]
  simp only [Effect.YieldEffect.isState, Effect.handleYield,
             Effect.resumeBlockhash, bind, Except.bind, hpush, pure,
             Except.pure, hHalt, ite_true]

theorem runFrameR_log_shifted (i i2 : Evm) (g pcv nop : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : (i.message.code.get! pcv).toNat = nop)
    (hlo : 0xa0 ≤ nop) (hhi : nop ≤ 0xa4)
    (hIR : IR.execOp i (.log (nop - 0xa0)) = .ok i2) :
    (∀ fl, Effect.runFrameR (fl + 1)
        { i with gasLeft := i.gasLeft
                   + (Gas.log + Gas.logTopic * (nop - 0xa0) + g),
                 pc := pcv }
      = Effect.runFrameR fl
        { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 }) ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  -- `unfold` leaves the opcode match unreduced for the parameterized
  -- `.log n` arm; the equation lemma via `simp only [IR.execOp]` does
  -- reduce it, and normalizes the trailing `<$>` into bind + pure so a
  -- single `bind_eq_ok` round rewrites the whole chain at once.
  simp only [IR.execOp] at hIR
  by_cases hSt : i.message.isStatic = true
  · rw [ite_eq_left hSt] at hIR; simp at hIR
  rw [ite_eq_right hSt] at hIR
  have hStf : i.message.isStatic = false := by simpa using hSt
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hIR
  obtain ⟨⟨offset, len, s⟩, hp2, hIR⟩ := hIR
  obtain ⟨⟨topics, s'⟩, hpt, hIR⟩ := hIR
  obtain ⟨gl1, hch, hIR⟩ := hIR
  obtain ⟨⟨gl, mem⟩, hcm, hIR⟩ := hIR
  simp only at hpt hch hcm hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  obtain ⟨hdle, hgl1⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
  subst hgl1
  refine ⟨fun fl => ?_, rfl, rfl⟩
  have hch2 : Gas.charge
      (i.gasLeft + (Gas.log + Gas.logTopic * (nop - 0xa0) + g))
      (Gas.log + Gas.logTopic * (nop - 0xa0) + Gas.logData * len.toNat)
      = .ok (i.gasLeft - Gas.logData * len.toNat + g) :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mpr
      ⟨nat_le_add_mid2 _ _ _ _ hdle, (nat_add_sub_mid2 _ _ _ g hdle).symm⟩
  have hs1 : Effect.step1
      { i with gasLeft := i.gasLeft
                 + (Gas.log + Gas.logTopic * (nop - 0xa0) + g),
               pc := pcv }
      = .yield { i with gasLeft := gl + g, memory := mem, stack := s',
                        pc := pcv, halted := false }
          (.logEmit { address := i.message.currentTarget, topics := topics,
                      data := Memory.read mem offset.toNat len.toNat }) := by
    rw [step1_dispatch_log
          { i with gasLeft := i.gasLeft
                     + (Gas.log + Gas.logTopic * (nop - 0xa0) + g),
                   pc := pcv }
          nop hHalt hSize hCode hlo hhi]
    simp only [Effect.doLog, hStf, Bool.false_eq_true, ite_false, hp2, hpt,
               hch2, chargeMemory_shifted g hcm, hHalt]
  rw [runFrameR_succ, hs1]
  simp only [Effect.YieldEffect.isState, Effect.handleYield,
             Effect.resumeLog, pure, Except.pure, hHalt,
             ite_true]

/-- A successful `.ret` terminator always yields a halted frame. -/
private theorem execTerm_ret_halted (i i' : Evm) (endPc : Nat)
    (hTerm : IR.execTerm i endPc .ret = .ok i') : i'.halted = true := by
  unfold IR.execTerm at hTerm
  simp only [bind, Except.bind] at hTerm
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨off, len, s⟩
  · rw [hp2] at hTerm; simp at hTerm
  rw [hp2] at hTerm
  simp only at hTerm
  rcases hcm : Instructions.chargeMemory i.gasLeft i.memory off.toNat len.toNat
      with _ | ⟨gl, mem⟩
  · rw [hcm] at hTerm; simp at hTerm
  rw [hcm] at hTerm
  simp only [pure, Except.pure, Except.ok.injEq] at hTerm
  subst hTerm
  rfl

/-- A successful `.selfdestruct` terminator always yields a halted
    frame. -/
private theorem execTerm_selfdestruct_halted (i i' : Evm) (endPc : Nat)
    (hTerm : IR.execTerm i endPc .selfdestruct = .ok i') :
    i'.halted = true := by
  simp only [IR.execTerm] at hTerm
  unfold Evm.Frontier.Vm.selfdestruct at hTerm
  simp only [bind, Except.bind, pure, Except.pure] at hTerm
  by_cases hSt : i.message.isStatic = true
  · rw [ite_eq_left hSt] at hTerm; simp at hTerm
  rw [ite_eq_right hSt] at hTerm
  rcases hp : Stack.pop i.stack with _ | ⟨bW, s⟩
  · rw [hp] at hTerm; simp at hTerm
  rw [hp] at hTerm
  simp only [Except.ok.injEq] at hTerm
  subst hTerm
  rfl

/-- 0xff SELFDESTRUCT: a successful `.selfdestruct` terminator
    matches one `step1` that `.halt`s — `step1` wires 0xff to the
    total `Vm.selfdestruct` handler via `liftPure`, exactly the
    function `execTerm` binds, so agreement is definitional. -/
private theorem step1_selfdestruct_halts (i i' : Evm) (pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0xff)
    (hTerm : IR.execTerm i pcv .selfdestruct = .ok i') :
    Effect.step1 { i with pc := pcv } = .halt i' i'.output := by
  have hHalted := execTerm_selfdestruct_halted i i' pcv hTerm
  simp only [IR.execTerm] at hTerm
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.selfdestruct
      { i with pc := pcv, halted := false } = _
  unfold Effect.liftPure
  rw [show ({ i with pc := pcv, halted := false } : Evm)
        = { i with pc := pcv } from by rw [← hHalt],
      hTerm]
  simp [hHalted]

/-- 0x56 JUMP: a successful `.jumpDynamic` terminator matches one
    `step1` that `.continue`s into the (non-halted) transfer frame.
    Jump validity is the shared `Instructions.isValidJumpDest`, so
    handler/IR agreement on the branch taken is definitional. -/
private theorem step1_jump_continue (i i' : Evm) (pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x56)
    (hTerm : IR.execTerm i (pcv + 1) .jumpDynamic = .ok i') :
    Effect.step1 { i with pc := pcv } = .continue i' := by
  unfold IR.execTerm at hTerm
  simp only [bind, Except.bind] at hTerm
  rcases hch : Gas.charge i.gasLeft Gas.mid with _ | gl
  · rw [hch] at hTerm; simp at hTerm
  rw [hch] at hTerm
  simp only at hTerm
  rcases hp : Stack.pop i.stack with _ | ⟨dest, s⟩
  · rw [hp] at hTerm; simp at hTerm
  rw [hp] at hTerm
  simp only at hTerm
  split at hTerm
  case isTrue hvj =>
    simp only [pure, Except.pure, Except.ok.injEq] at hTerm
    subst hTerm
    have hvj' : Instructions.isValidJumpDest
        { i with pc := pcv, halted := false } dest.toNat = true := hvj
    simp only [Effect.step1, hHalt, hCode, ite_false,
               show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
    show Effect.liftPure Evm.Frontier.Vm.Instructions.jump
        { i with pc := pcv, halted := false } = _
    have hJump : Evm.Frontier.Vm.Instructions.jump
        { i with pc := pcv, halted := false }
        = .ok { i with gasLeft := gl, stack := s, pc := dest.toNat,
                       halted := false } := by
      unfold Evm.Frontier.Vm.Instructions.jump
      simp [bind, Except.bind, hch, hp, hvj', pure, Except.pure]
    unfold Effect.liftPure
    rw [hJump]
    simp
  case isFalse hvj => simp at hTerm

/-- 0x57 JUMPI: a successful `.jumpiDynamic` terminator (either
    branch) matches one `step1` that `.continue`s into the transfer
    frame. The false branch lands on `pcv + 1`, which is the `endPc`
    the compiler emitted. -/
private theorem step1_jumpi_continue (i i' : Evm) (pcv : Nat)
    (hHalt : i.halted = false)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x57)
    (hTerm : IR.execTerm i (pcv + 1) .jumpiDynamic = .ok i') :
    Effect.step1 { i with pc := pcv } = .continue i' := by
  unfold IR.execTerm at hTerm
  simp only [bind, Except.bind] at hTerm
  rcases hch : Gas.charge i.gasLeft Gas.high with _ | gl
  · rw [hch] at hTerm; simp at hTerm
  rw [hch] at hTerm
  simp only at hTerm
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨dest, cond, s⟩
  · rw [hp2] at hTerm; simp at hTerm
  rw [hp2] at hTerm
  simp only at hTerm
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (pcv ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show Effect.liftPure Evm.Frontier.Vm.Instructions.jumpi
      { i with pc := pcv, halted := false } = _
  by_cases hc : cond = (0 : Evm.U256)
  · rw [ite_eq_left hc] at hTerm
    simp only [pure, Except.pure, Except.ok.injEq] at hTerm
    subst hTerm
    have hJumpi : Evm.Frontier.Vm.Instructions.jumpi
        { i with pc := pcv, halted := false }
        = .ok { i with gasLeft := gl, stack := s, pc := pcv + 1,
                       halted := false } := by
      unfold Evm.Frontier.Vm.Instructions.jumpi
      simp [bind, Except.bind, hch, hp2, hc, pure, Except.pure]
    unfold Effect.liftPure
    rw [hJumpi]
    simp [hHalt]
  · rw [ite_eq_right hc] at hTerm
    split at hTerm
    next hvj =>
      simp only [pure, Except.pure, Except.ok.injEq] at hTerm
      subst hTerm
      have hvj' : Instructions.isValidJumpDest
          { i with pc := pcv, halted := false } dest.toNat = true := hvj
      have hJumpi : Evm.Frontier.Vm.Instructions.jumpi
          { i with pc := pcv, halted := false }
          = .ok { i with gasLeft := gl, stack := s, pc := dest.toNat,
                         halted := false } := by
        unfold Evm.Frontier.Vm.Instructions.jumpi
        -- simp normalizes the `cond = 0` test to `cond = 0#256`, so
        -- `hc` no longer fires syntactically; the dead true branch
        -- survives as an implication, discharged by `hc` directly.
        simp [bind, Except.bind, hch, hp2, hvj', pure, Except.pure]
        exact fun h => absurd h hc
      unfold Effect.liftPure
      rw [hJumpi]
      simp [hHalt]
    next hvj => simp at hTerm

/-! ## Chunk-level soundness

    `compileLoop_sound` is the induction workhorse: if `compileLoop`
    succeeds at `pc` and the IR interpreter runs the resulting ops
    and terminator to a halted frame `i'`, then the Effect
    interpreter — started at `pc` on the same frame with the
    static gas of the remaining ops added back — halts at exactly
    `i'`. The gas offset is the loop invariant: the IR pre-charged
    the whole chunk up front, so mid-chunk the Effect frame is
    always "ahead" by the static gas of what's left. -/

set_option maxHeartbeats 1000000 in
/-- `compileLoop` at a PUSH opcode: one `Op.push` plus the recursive
    tail at `pc + 1 + immBytes`. Stated with an abstract opcode value
    `nop` so the chunk induction can use it directly; the proof
    case-bashes the 32 PUSH opcodes internally. -/
private theorem compileLoop_push_eq (fork : Evm.Fork) (code : Evm.Bytes)
    (pc nop : Nat)
    (hlt : ¬ pc ≥ code.size) (hop : (code.get! pc).toNat = nop)
    (hlo : 0x60 ≤ nop) (hhi : nop ≤ 0x7f) :
    IR.compileLoop fork code pc = do
      let (ops, gas, term, e) ← IR.compileLoop fork code (pc + 1 + (nop - 0x5f))
      return (Op.push (nop - 0x5f) (IR.readImmediate code pc (nop - 0x5f)) :: ops,
              Gas.veryLow + gas, term, e) := by
  interval_cases nop <;>
  · rw [IR.compileLoop.eq_def, dite_eq_right hlt]
    simp only [hop]
    rw [ite_eq_left (by omega)]
    rfl

/-- `compileLoop` at a DUP opcode: one `Op.dup` plus the recursive
    tail at `pc + 1`. -/
private theorem compileLoop_dup_eq (fork : Evm.Fork) (code : Evm.Bytes)
    (pc nop : Nat)
    (hlt : ¬ pc ≥ code.size) (hop : (code.get! pc).toNat = nop)
    (hlo : 0x80 ≤ nop) (hhi : nop ≤ 0x8f) :
    IR.compileLoop fork code pc = do
      let (ops, gas, term, e) ← IR.compileLoop fork code (pc + 1)
      return (Op.dup (nop - 0x7f) :: ops, Gas.veryLow + gas, term, e) := by
  interval_cases nop <;>
  · rw [IR.compileLoop.eq_def, dite_eq_right hlt]
    simp only [hop]
    rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    rfl

/-- `compileLoop` at a SWAP opcode: one `Op.swap` plus the recursive
    tail at `pc + 1`. -/
private theorem compileLoop_swap_eq (fork : Evm.Fork) (code : Evm.Bytes)
    (pc nop : Nat)
    (hlt : ¬ pc ≥ code.size) (hop : (code.get! pc).toNat = nop)
    (hlo : 0x90 ≤ nop) (hhi : nop ≤ 0x9f) :
    IR.compileLoop fork code pc = do
      let (ops, gas, term, e) ← IR.compileLoop fork code (pc + 1)
      return (Op.swap (nop - 0x8f) :: ops, Gas.veryLow + gas, term, e) := by
  interval_cases nop <;>
  · rw [IR.compileLoop.eq_def, dite_eq_right hlt]
    simp only [hop]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
    rfl

/-- `compileLoop` at a LOG opcode: one `Op.log` plus the recursive
    tail at `pc + 1`. The static gas (`log + logTopic·n`) is baked in
    so the chunk proof never needs to unfold `staticGasFor` on a
    non-literal `Op.log` argument. -/
private theorem compileLoop_log_eq (fork : Evm.Fork) (code : Evm.Bytes)
    (pc nop : Nat)
    (hlt : ¬ pc ≥ code.size) (hop : (code.get! pc).toNat = nop)
    (hlo : 0xa0 ≤ nop) (hhi : nop ≤ 0xa4) :
    IR.compileLoop fork code pc = do
      let (ops, gas, term, e) ← IR.compileLoop fork code (pc + 1)
      return (Op.log (nop - 0xa0) :: ops,
              (Gas.log + Gas.logTopic * (nop - 0xa0)) + gas, term, e) := by
  interval_cases nop <;>
  · rw [IR.compileLoop.eq_def, dite_eq_right hlt]
    simp only [hop]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left (by omega)]
    rfl

set_option maxHeartbeats 1000000 in
theorem compileLoop_sound (code : Evm.Bytes) (pc : Nat) :
    ∀ (ops : List Op) (gas : Nat) (term : Terminator) (endPc : Nat),
    IR.compileLoop .frontier code pc = .ok (ops, gas, term, endPc) →
    ∀ (i i2 i' : Evm),
      i.message.code = code → i.halted = false →
      IR.execOps i ops = .ok i2 →
      IR.execTerm i2 endPc term = .ok i' →
      ∃ n, ∀ (f : Nat), Effect.runFrameR (n + (f + 1))
        { i with gasLeft := i.gasLeft + gas, pc := pc }
      = Effect.runFrameR (f + 1) i' := by
  induction pc using IR.compileLoop.induct (fork := .frontier) (code := code) with
  | case1 x hge =>
    -- pc ≥ code.size : endOfCode
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    rw [IR.compileLoop.eq_def, dite_eq_left hge] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, pure, Except.pure, Except.ok.injEq] at hOps
    subst hOps
    simp only [IR.execTerm, pure, Except.pure, Except.ok.injEq] at hTerm
    subst hTerm
    refine ⟨0, fun f => ?_⟩
    simp only [Nat.add_zero, Nat.zero_add]
    rw [runFrameR_succ, runFrameR_succ,
        step1_endOfCode_halts i x hHalt (by rw [hcc]; exact hge),
        step1_halted { i with halted := true, pc := x } rfl]
  | case2 x hlt opc hop =>
    -- 0x00 : STOP
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x00 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, pure, Except.pure, Except.ok.injEq] at hOps
    subst hOps
    simp only [IR.execTerm, pure, Except.pure, Except.ok.injEq] at hTerm
    subst hTerm
    refine ⟨0, fun f => ?_⟩
    simp only [Nat.add_zero, Nat.zero_add]
    rw [runFrameR_succ, runFrameR_succ,
        step1_stop_halts i x hHalt (by rw [hcc]; omega)
          (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)),
        step1_halted { i with halted := true, pc := x } rfl]
  | case3 x hlt opc hop =>
    -- 0xf3 : RETURN
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xf3 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, pure, Except.pure, Except.ok.injEq] at hOps
    subst hOps
    refine ⟨0, fun f => ?_⟩
    simp only [Nat.add_zero, Nat.zero_add]
    rw [runFrameR_succ, runFrameR_succ,
        step1_ret_halts i i' x hHalt (by rw [hcc]; omega)
          (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop))
          hTerm,
        step1_halted i' (execTerm_ret_halted i i' (x + 1) hTerm)]
  | case4 x hlt opc hop ih =>
    -- 0x01 : ADD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x01 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_add_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.add = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case5 x hlt opc hop ih =>
    -- 0x02 : MUL
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x02 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_mul_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.mul = Gas.low from rfl, hstep]
    exact hrun f
  | case6 x hlt opc hop ih =>
    -- 0x03 : SUB
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x03 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_sub_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.sub = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case7 x hlt opc hop ih =>
    -- 0x50 : POP
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x50 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_pop_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.pop = Gas.base from rfl, hstep]
    exact hrun f
  | case8 x hlt opc hop ih =>
    -- 0x51 : MLOAD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x51 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_mload_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.mload = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case9 x hlt opc hop ih =>
    -- 0x52 : MSTORE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x52 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_mstore_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.mstore = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case10 x hlt opc hop ih =>
    -- 0x04 : DIV
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x04 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_div_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.div = Gas.low from rfl, hstep]
    exact hrun f
  | case11 x hlt opc hop ih =>
    -- 0x05 : SDIV
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x05 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_sdiv_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.sdiv = Gas.low from rfl, hstep]
    exact hrun f
  | case12 x hlt opc hop ih =>
    -- 0x06 : MOD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x06 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_mod_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.mod = Gas.low from rfl, hstep]
    exact hrun f
  | case13 x hlt opc hop ih =>
    -- 0x07 : SMOD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x07 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_smod_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.smod = Gas.low from rfl, hstep]
    exact hrun f
  | case14 x hlt opc hop ih =>
    -- 0x08 : ADDMOD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x08 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_addmod_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.addmod = Gas.mid from rfl, hstep]
    exact hrun f
  | case15 x hlt opc hop ih =>
    -- 0x09 : MULMOD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x09 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_mulmod_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.mulmod = Gas.mid from rfl, hstep]
    exact hrun f
  | case16 x hlt opc hop ih =>
    -- 0x0b : SIGNEXTEND
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x0b := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_signextend_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.signextend = Gas.low from rfl, hstep]
    exact hrun f
  | case17 x hlt opc hop ih =>
    -- 0x10 : LT
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x10 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_lt_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.lt = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case18 x hlt opc hop ih =>
    -- 0x11 : GT
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x11 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_gt_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.gt = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case19 x hlt opc hop ih =>
    -- 0x12 : SLT
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x12 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_slt_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.slt = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case20 x hlt opc hop ih =>
    -- 0x13 : SGT
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x13 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_sgt_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.sgt = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case21 x hlt opc hop ih =>
    -- 0x14 : EQ
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x14 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_eq_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.eq = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case22 x hlt opc hop ih =>
    -- 0x15 : ISZERO
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x15 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_iszero_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.iszero = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case23 x hlt opc hop ih =>
    -- 0x16 : AND
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x16 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_and_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.and_ = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case24 x hlt opc hop ih =>
    -- 0x17 : OR
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x17 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_or_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.or_ = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case25 x hlt opc hop ih =>
    -- 0x18 : XOR
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x18 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_xor_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.xor_ = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case26 x hlt opc hop ih =>
    -- 0x19 : NOT
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x19 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_not_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.not_ = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case27 x hlt opc hop ih =>
    -- 0x1a : BYTE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x1a := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_byte_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.byte = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case28 x hlt opc hop ih =>
    -- 0x0a : EXP
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x0a := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_exp_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.exp = Gas.exp from rfl, hstep]
    exact hrun f
  | case29 x hlt opc hop ih =>
    -- 0x30 : ADDRESS
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x30 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_address_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.address = Gas.base from rfl, hstep]
    exact hrun f
  | case30 x hlt opc hop ih =>
    -- 0x32 : ORIGIN
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x32 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_origin_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.origin = Gas.base from rfl, hstep]
    exact hrun f
  | case31 x hlt opc hop ih =>
    -- 0x33 : CALLER
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x33 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_caller_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.caller = Gas.base from rfl, hstep]
    exact hrun f
  | case32 x hlt opc hop ih =>
    -- 0x34 : CALLVALUE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x34 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_callvalue_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.callvalue = Gas.base from rfl, hstep]
    exact hrun f
  | case33 x hlt opc hop ih =>
    -- 0x35 : CALLDATALOAD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x35 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_calldataload_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.calldataload = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case34 x hlt opc hop ih =>
    -- 0x36 : CALLDATASIZE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x36 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_calldatasize_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.calldatasize = Gas.base from rfl, hstep]
    exact hrun f
  | case35 x hlt opc hop ih =>
    -- 0x38 : CODESIZE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x38 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_codesize_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.codesize = Gas.base from rfl, hstep]
    exact hrun f
  | case36 x hlt opc hop ih =>
    -- 0x3a : GASPRICE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x3a := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_gasprice_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.gasprice = Gas.base from rfl, hstep]
    exact hrun f
  | case37 x hlt opc hop ih =>
    -- 0x41 : COINBASE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x41 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_coinbase_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.coinbase = Gas.base from rfl, hstep]
    exact hrun f
  | case38 x hlt opc hop ih =>
    -- 0x42 : TIMESTAMP
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x42 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_timestamp_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.timestamp = Gas.base from rfl, hstep]
    exact hrun f
  | case39 x hlt opc hop ih =>
    -- 0x43 : NUMBER
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x43 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_number_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.number = Gas.base from rfl, hstep]
    exact hrun f
  | case40 x hlt opc hop ih =>
    -- 0x44 : DIFFICULTY
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x44 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_difficulty_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.prevrandao = Gas.base from rfl, hstep]
    exact hrun f
  | case41 x hlt opc hop ih =>
    -- 0x45 : GASLIMIT
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x45 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_gaslimit_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.gaslimit = Gas.base from rfl, hstep]
    exact hrun f
  | case42 x hlt opc hop ih =>
    -- 0x53 : MSTORE8
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x53 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_mstore8_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.mstore8 = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case43 x hlt opc hop ih =>
    -- 0x58 : PC
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x58 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_pc_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier (Op.pc x) = Gas.base from rfl, hstep]
    exact hrun f
  | case44 x hlt opc hop ih =>
    -- 0x59 : MSIZE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x59 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_msize_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.msize = Gas.base from rfl, hstep]
    exact hrun f
  | case45 x hlt opc hop ih =>
    -- 0x5a : GAS
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x5a := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_gas_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier (Op.gas gas') = Gas.base from rfl, hstep]
    exact hrun f
  | case46 x hlt opc hop ih =>
    -- 0x5b : JUMPDEST
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x5b := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_jumpdest_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, show IR.staticGasFor .frontier Op.jumpdest = Gas.jumpDest from rfl, hstep]
    exact hrun f
  | case47 x hlt opc hop =>
    -- 0x56 : JUMP — dynamic-target terminator; transfers, does not halt
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x56 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, pure, Except.pure, Except.ok.injEq] at hOps
    subst hOps
    refine ⟨1, fun f => ?_⟩
    simp only [Nat.add_zero]
    rw [show 1 + (f + 1) = (f + 1) + 1 from by omega, runFrameR_succ,
        step1_jump_continue i i' x hHalt (by rw [hcc]; omega)
          (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop))
          hTerm]
  | case48 x hlt opc hop =>
    -- 0x57 : JUMPI — transfers or falls through to x + 1
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x57 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, pure, Except.pure, Except.ok.injEq] at hOps
    subst hOps
    refine ⟨1, fun f => ?_⟩
    simp only [Nat.add_zero]
    rw [show 1 + (f + 1) = (f + 1) + 1 from by omega, runFrameR_succ,
        step1_jumpi_continue i i' x hHalt (by rw [hcc]; omega)
          (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop))
          hTerm]
  | case49 x hlt opc hop =>
    -- 0xfe : INVALID — `execTerm .invalid` errors; hypothesis is vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xfe := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case50 x hlt opc hop ih =>
    -- 0x20 : KECCAK256
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x20 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_keccak256_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ,
        show IR.staticGasFor .frontier Op.keccak256 = Gas.keccak256 from rfl, hstep]
    exact hrun f
  | case51 x hlt opc hop ih =>
    -- 0x37 : CALLDATACOPY
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x37 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_calldatacopy_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ,
        show IR.staticGasFor .frontier Op.calldatacopy = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case52 x hlt opc hop ih =>
    -- 0x39 : CODECOPY
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x39 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_codecopy_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ,
        show IR.staticGasFor .frontier Op.codecopy = Gas.veryLow from rfl, hstep]
    exact hrun f
  | case53 x hlt opc hop ih =>
    -- 0x31 : BALANCE (state yield, resolved in-frame by runFrameR)
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x31 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      runFrameR_balance_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega,
        show IR.staticGasFor .frontier Op.balance = Gas.balance from rfl,
        hstep (n + (f + 1))]
    exact hrun f
  | case54 x hlt opc hop ih =>
    -- 0x3b : EXTCODESIZE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x3b := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      runFrameR_extcodesize_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega,
        show IR.staticGasFor .frontier Op.extcodesize = Gas.extCode from rfl,
        hstep (n + (f + 1))]
    exact hrun f
  | case55 x hlt opc hop ih =>
    -- 0x3c : EXTCODECOPY
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x3c := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      runFrameR_extcodecopy_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega,
        show IR.staticGasFor .frontier Op.extcodecopy = Gas.extCode from rfl,
        hstep (n + (f + 1))]
    exact hrun f
  | case56 x hlt opc hop ih =>
    -- 0x40 : BLOCKHASH
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x40 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      runFrameR_blockhash_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega,
        show IR.staticGasFor .frontier Op.blockhash = Gas.blockHash from rfl,
        hstep (n + (f + 1))]
    exact hrun f
  | case57 x hlt opc hop ih =>
    -- 0x54 : SLOAD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x54 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      runFrameR_sload_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega,
        show IR.staticGasFor .frontier Op.sload = Gas.sLoad from rfl,
        hstep (n + (f + 1))]
    exact hrun f
  | case58 x hlt opc hop ih =>
    -- 0x55 : SSTORE (no static pre-charge; cost depends on old value)
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x55 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      runFrameR_sstore_shifted i ia gas' x hHalt (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega,
        show IR.staticGasFor .frontier Op.sstore = 0 from rfl,
        hstep (n + (f + 1))]
    exact hrun f
  | case59 x hlt opc hop =>
    -- 0xf0 : CREATE terminator — a sub-frame yield is not
    -- expressible in the Except-valued track (`execTerm` errors BY
    -- DESIGN), so the `.ok` hypothesis is vacuous. The yielding
    -- track is `IR.executeStep`.
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xf0 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case60 x hlt opc hop =>
    -- 0xf1 : CALL terminator — vacuous (see the 0xf0 case)
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xf1 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case61 x hlt opc hop =>
    -- 0xf2 : CALLCODE terminator — vacuous (see the 0xf0 case)
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xf2 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case62 x hlt opc hop =>
    -- 0xff : SELFDESTRUCT — frame-ending and total at Frontier
    -- (`execTerm` binds `Vm.selfdestruct`, the handler `step1` wires
    -- via `liftPure`), so it closes like STOP/RETURN.
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xff := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, pure, Except.pure, Except.ok.injEq] at hOps
    subst hOps
    refine ⟨0, fun f => ?_⟩
    simp only [Nat.add_zero, Nat.zero_add]
    rw [runFrameR_succ, runFrameR_succ,
        step1_selfdestruct_halts i i' x hHalt (by rw [hcc]; omega)
          (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop))
          hTerm,
        step1_halted i' (execTerm_selfdestruct_halted i i' x hTerm)]
  | case63 x hlt opc hop hgate ih =>
    -- 0x1b SHL gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case64 x hlt opc hop hgate =>
    -- 0x1b SHL gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x1b := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case65 x hlt opc hop hgate ih =>
    -- 0x1c SHR gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case66 x hlt opc hop hgate =>
    -- 0x1c SHR gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x1c := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case67 x hlt opc hop hgate ih =>
    -- 0x1d SAR gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case68 x hlt opc hop hgate =>
    -- 0x1d SAR gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x1d := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case69 x hlt opc hop hgate ih =>
    -- 0x3d RETURNDATASIZE gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case70 x hlt opc hop hgate =>
    -- 0x3d RETURNDATASIZE gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x3d := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case71 x hlt opc hop hgate ih =>
    -- 0x3e RETURNDATACOPY gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case72 x hlt opc hop hgate =>
    -- 0x3e RETURNDATACOPY gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x3e := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case73 x hlt opc hop hgate ih =>
    -- 0x3f EXTCODEHASH gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case74 x hlt opc hop hgate =>
    -- 0x3f EXTCODEHASH gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x3f := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case75 x hlt opc hop hgate ih =>
    -- 0x46 CHAINID gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case76 x hlt opc hop hgate =>
    -- 0x46 CHAINID gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x46 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case77 x hlt opc hop hgate ih =>
    -- 0x47 SELFBALANCE gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case78 x hlt opc hop hgate =>
    -- 0x47 SELFBALANCE gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x47 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case79 x hlt opc hop hgate ih =>
    -- 0x48 BASEFEE gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case80 x hlt opc hop hgate =>
    -- 0x48 BASEFEE gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x48 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case81 x hlt opc hop hgate ih =>
    -- 0x49 BLOBHASH gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case82 x hlt opc hop hgate =>
    -- 0x49 BLOBHASH gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x49 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case83 x hlt opc hop hgate ih =>
    -- 0x4a BLOBBASEFEE gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case84 x hlt opc hop hgate =>
    -- 0x4a BLOBBASEFEE gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x4a := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case85 x hlt opc hop hgate ih =>
    -- 0x5c TLOAD gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case86 x hlt opc hop hgate =>
    -- 0x5c TLOAD gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x5c := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case87 x hlt opc hop hgate ih =>
    -- 0x5d TSTORE gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case88 x hlt opc hop hgate =>
    -- 0x5d TSTORE gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x5d := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case89 x hlt opc hop hgate ih =>
    -- 0x5e MCOPY gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case90 x hlt opc hop hgate =>
    -- 0x5e MCOPY gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x5e := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case91 x hlt opc hop hgate ih =>
    -- 0x5f PUSH0 gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case92 x hlt opc hop hgate =>
    -- 0x5f PUSH0 gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x5f := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case93 x hlt opc hop hgate =>
    -- 0xfd REVERT gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case94 x hlt opc hop hgate =>
    -- 0xfd REVERT gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xfd := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case95 x hlt opc hop hgate =>
    -- 0xf4 DELEGATECALL gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case96 x hlt opc hop hgate =>
    -- 0xf4 DELEGATECALL gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xf4 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case97 x hlt opc hop hgate =>
    -- 0xfa STATICCALL gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case98 x hlt opc hop hgate =>
    -- 0xfa STATICCALL gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xfa := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case99 x hlt opc hop hgate =>
    -- 0xf5 CREATE2 gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case100 x hlt opc hop hgate =>
    -- 0xf5 CREATE2 gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xf5 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case101 x hlt opc hop hgate ih =>
    -- 0x1e CLZ gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case102 x hlt opc hop hgate =>
    -- 0x1e CLZ gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x1e := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case103 x hlt opc h0 h243 h1 h2 h3 h80 h81 h82 _h4 _h5 _h6 _h7
      _h8 _h9 _hb _q10 _q11 _q12 _q13 _q14 _q15 _q16 _q17 _q18 _q19
      _q1a _ha _a30 _a32 _a33 _a34 _a35 _a36 _a38 _a3a _a41 _a42 _a43
      _a44 _a45 _a53 _a58 _a59 _a5a _a5b _a56 _a57 _afe _a20 _a37 _a39
      _a31 _a3b _a3c _a40 _a54 _a55 _af0 _af1 _af2 _aff
      _a1b _a1c _a1d _a3d _a3e _a3f _a46 _a47 _a48 _a49 _a4a _a5c
      _a5d _a5e _a5f _afd _af4 _afa _af5 _a1e
      hrange imm ih =>
    -- 0x60–0x7f : PUSH1..PUSH32
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hrange : 0x60 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0x7f :=
      hrange
    rw [compileLoop_push_eq .frontier code x ((code.get! x).toNat) hlt rfl
          hrange.1 hrange.2] at hC
    simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_push_shifted i ia gas' x ((code.get! x).toNat) hHalt
        (by rw [hcc]; omega) (by rw [hcc]) hrange.1 hrange.2
        (by rw [hcc]; exact hop1)
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, hstep]
    exact hrun f
  | case104 x hlt opc _h0 _h243 _h1 _h2 _h3 _h80 _h81 _h82 _h4 _h5 _h6 _h7
      _h8 _h9 _hb _q10 _q11 _q12 _q13 _q14 _q15 _q16 _q17 _q18 _q19
      _q1a _ha _a30 _a32 _a33 _a34 _a35 _a36 _a38 _a3a _a41 _a42 _a43
      _a44 _a45 _a53 _a58 _a59 _a5a _a5b _a56 _a57 _afe _a20 _a37 _a39
      _a31 _a3b _a3c _a40 _a54 _a55 _af0 _af1 _af2 _aff
      _a1b _a1c _a1d _a3d _a3e _a3f _a46 _a47 _a48 _a49 _a4a _a5c
      _a5d _a5e _a5f _afd _af4 _afa _af5 _a1e
      _hnp hrange ih =>
    -- 0x80–0x8f : DUP1..DUP16
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hrange : 0x80 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0x8f :=
      hrange
    rw [compileLoop_dup_eq .frontier code x ((code.get! x).toNat) hlt rfl
          hrange.1 hrange.2] at hC
    simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_dup_shifted i ia gas' x ((code.get! x).toNat) hHalt
        (by rw [hcc]; omega) (by rw [hcc]) hrange.1 hrange.2 hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, hstep]
    exact hrun f
  | case105 x hlt opc _h0 _h243 _h1 _h2 _h3 _h80 _h81 _h82 _h4 _h5 _h6 _h7
      _h8 _h9 _hb _q10 _q11 _q12 _q13 _q14 _q15 _q16 _q17 _q18 _q19
      _q1a _ha _a30 _a32 _a33 _a34 _a35 _a36 _a38 _a3a _a41 _a42 _a43
      _a44 _a45 _a53 _a58 _a59 _a5a _a5b _a56 _a57 _afe _a20 _a37 _a39
      _a31 _a3b _a3c _a40 _a54 _a55 _af0 _af1 _af2 _aff
      _a1b _a1c _a1d _a3d _a3e _a3f _a46 _a47 _a48 _a49 _a4a _a5c
      _a5d _a5e _a5f _afd _af4 _afa _af5 _a1e
      _hnp _hnd hrange ih =>
    -- 0x90–0x9f : SWAP1..SWAP16
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hrange : 0x90 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0x9f :=
      hrange
    rw [compileLoop_swap_eq .frontier code x ((code.get! x).toNat) hlt rfl
          hrange.1 hrange.2] at hC
    simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      step1_swap_shifted i ia gas' x ((code.get! x).toNat) hHalt
        (by rw [hcc]; omega) (by rw [hcc]) hrange.1 hrange.2 hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega]
    rw [runFrameR_succ, hstep]
    exact hrun f
  | case106 x hlt opc _h0 _h243 _h1 _h2 _h3 _h80 _h81 _h82 _h4 _h5 _h6 _h7
      _h8 _h9 _hb _q10 _q11 _q12 _q13 _q14 _q15 _q16 _q17 _q18 _q19
      _q1a _ha _a30 _a32 _a33 _a34 _a35 _a36 _a38 _a3a _a41 _a42 _a43
      _a44 _a45 _a53 _a58 _a59 _a5a _a5b _a56 _a57 _afe _a20 _a37 _a39
      _a31 _a3b _a3c _a40 _a54 _a55 _af0 _af1 _af2 _aff
      _a1b _a1c _a1d _a3d _a3e _a3f _a46 _a47 _a48 _a49 _a4a _a5c
      _a5d _a5e _a5f _afd _af4 _afa _af5 _a1e
      _hnp _hnd _hns hrange ih =>
    -- 0xa0–0xa4 : LOG0..LOG4 (state yield, resolved in-frame)
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hrange : 0xa0 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0xa4 :=
      hrange
    rw [compileLoop_log_eq .frontier code x ((code.get! x).toNat) hlt rfl
          hrange.1 hrange.2] at hC
    simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hstep, hmsg, hhalt⟩ :=
      runFrameR_log_shifted i ia gas' x ((code.get! x).toNat) hHalt
        (by rw [hcc]; omega) (by rw [hcc]) hrange.1 hrange.2 hop1
    obtain ⟨n, hrun⟩ :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    refine ⟨n + 1, fun f => ?_⟩
    rw [show n + 1 + (f + 1) = n + (f + 1) + 1 from by omega,
        hstep (n + (f + 1))]
    exact hrun f
  | case107 x hlt opc h0 h243 h1 h2 h3 h80 h81 h82 h4 h5 h6 h7
      h8 h9 hb q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q1a ha
      a30 a32 a33 a34 a35 a36 a38 a3a a41 a42 a43 a44 a45 a53
      a58 a59 a5a a5b a56 a57 afe a20 a37 a39
      a31 a3b a3c a40 a54 a55 af0 af1 af2 aff
      a1b a1c a1d a3d a3e a3f a46 a47 a48 a49 a4a a5c a5d a5e a5f
      afd af4 afa af5 a1e hnp hnd hns hnl =>
    -- unknown opcode : compileLoop errors, hypothesis is vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have h0' : (code.get! x).toNat = 0x00 → False := h0
    have h243' : (code.get! x).toNat = 0xf3 → False := h243
    have h1' : (code.get! x).toNat = 0x01 → False := h1
    have h2' : (code.get! x).toNat = 0x02 → False := h2
    have h3' : (code.get! x).toNat = 0x03 → False := h3
    have h80' : (code.get! x).toNat = 0x50 → False := h80
    have h81' : (code.get! x).toNat = 0x51 → False := h81
    have h82' : (code.get! x).toNat = 0x52 → False := h82
    have h4' : (code.get! x).toNat = 0x04 → False := h4
    have h5' : (code.get! x).toNat = 0x05 → False := h5
    have h6' : (code.get! x).toNat = 0x06 → False := h6
    have h7' : (code.get! x).toNat = 0x07 → False := h7
    have h8' : (code.get! x).toNat = 0x08 → False := h8
    have h9' : (code.get! x).toNat = 0x09 → False := h9
    have hb' : (code.get! x).toNat = 0x0b → False := hb
    have q10' : (code.get! x).toNat = 0x10 → False := q10
    have q11' : (code.get! x).toNat = 0x11 → False := q11
    have q12' : (code.get! x).toNat = 0x12 → False := q12
    have q13' : (code.get! x).toNat = 0x13 → False := q13
    have q14' : (code.get! x).toNat = 0x14 → False := q14
    have q15' : (code.get! x).toNat = 0x15 → False := q15
    have q16' : (code.get! x).toNat = 0x16 → False := q16
    have q17' : (code.get! x).toNat = 0x17 → False := q17
    have q18' : (code.get! x).toNat = 0x18 → False := q18
    have q19' : (code.get! x).toNat = 0x19 → False := q19
    have q1a' : (code.get! x).toNat = 0x1a → False := q1a
    have ha' : (code.get! x).toNat = 0x0a → False := ha
    have a30' : (code.get! x).toNat = 0x30 → False := a30
    have a32' : (code.get! x).toNat = 0x32 → False := a32
    have a33' : (code.get! x).toNat = 0x33 → False := a33
    have a34' : (code.get! x).toNat = 0x34 → False := a34
    have a35' : (code.get! x).toNat = 0x35 → False := a35
    have a36' : (code.get! x).toNat = 0x36 → False := a36
    have a38' : (code.get! x).toNat = 0x38 → False := a38
    have a3a' : (code.get! x).toNat = 0x3a → False := a3a
    have a41' : (code.get! x).toNat = 0x41 → False := a41
    have a42' : (code.get! x).toNat = 0x42 → False := a42
    have a43' : (code.get! x).toNat = 0x43 → False := a43
    have a44' : (code.get! x).toNat = 0x44 → False := a44
    have a45' : (code.get! x).toNat = 0x45 → False := a45
    have a53' : (code.get! x).toNat = 0x53 → False := a53
    have a58' : (code.get! x).toNat = 0x58 → False := a58
    have a59' : (code.get! x).toNat = 0x59 → False := a59
    have a5a' : (code.get! x).toNat = 0x5a → False := a5a
    have a5b' : (code.get! x).toNat = 0x5b → False := a5b
    have a56' : (code.get! x).toNat = 0x56 → False := a56
    have a57' : (code.get! x).toNat = 0x57 → False := a57
    have afe' : (code.get! x).toNat = 0xfe → False := afe
    have a20' : (code.get! x).toNat = 0x20 → False := a20
    have a37' : (code.get! x).toNat = 0x37 → False := a37
    have a39' : (code.get! x).toNat = 0x39 → False := a39
    have a31' : (code.get! x).toNat = 0x31 → False := a31
    have a3b' : (code.get! x).toNat = 0x3b → False := a3b
    have a3c' : (code.get! x).toNat = 0x3c → False := a3c
    have a40' : (code.get! x).toNat = 0x40 → False := a40
    have a54' : (code.get! x).toNat = 0x54 → False := a54
    have a55' : (code.get! x).toNat = 0x55 → False := a55
    have af0' : (code.get! x).toNat = 0xf0 → False := af0
    have af1' : (code.get! x).toNat = 0xf1 → False := af1
    have af2' : (code.get! x).toNat = 0xf2 → False := af2
    have aff' : (code.get! x).toNat = 0xff → False := aff
    have a1b' : (code.get! x).toNat = 0x1b → False := a1b
    have a1c' : (code.get! x).toNat = 0x1c → False := a1c
    have a1d' : (code.get! x).toNat = 0x1d → False := a1d
    have a3d' : (code.get! x).toNat = 0x3d → False := a3d
    have a3e' : (code.get! x).toNat = 0x3e → False := a3e
    have a3f' : (code.get! x).toNat = 0x3f → False := a3f
    have a46' : (code.get! x).toNat = 0x46 → False := a46
    have a47' : (code.get! x).toNat = 0x47 → False := a47
    have a48' : (code.get! x).toNat = 0x48 → False := a48
    have a49' : (code.get! x).toNat = 0x49 → False := a49
    have a4a' : (code.get! x).toNat = 0x4a → False := a4a
    have a5c' : (code.get! x).toNat = 0x5c → False := a5c
    have a5d' : (code.get! x).toNat = 0x5d → False := a5d
    have a5e' : (code.get! x).toNat = 0x5e → False := a5e
    have a5f' : (code.get! x).toNat = 0x5f → False := a5f
    have afd' : (code.get! x).toNat = 0xfd → False := afd
    have af4' : (code.get! x).toNat = 0xf4 → False := af4
    have afa' : (code.get! x).toNat = 0xfa → False := afa
    have af5' : (code.get! x).toNat = 0xf5 → False := af5
    have a1e' : (code.get! x).toNat = 0x1e → False := a1e
    have hnp' : ¬ (0x60 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0x7f) :=
      hnp
    have hnd' : ¬ (0x80 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0x8f) :=
      hnd
    have hns' : ¬ (0x90 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0x9f) :=
      hns
    have hnl' : ¬ (0xa0 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0xa4) :=
      hnl
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    -- `simp only []` reduces the opcode match to its default arm
    -- (the literal arms are ruled out by h0'..h82'); the `split`s
    -- then case on the PUSH/DUP/SWAP range `if`s, all branches
    -- contradictory.
    simp only [] at hC
    split at hC
    · exact absurd ‹_› hnp'
    all_goals first
      | exact absurd ‹_› hnd'
      | exact absurd ‹_› hns'
      | exact absurd ‹_› hnl'
      -- fall-through arm: an all-forks-undefined byte compiles to
      -- `.invalid`, whose `execTerm` errors — hypothesis is vacuous
      | (simp at hC
         obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
         simp [IR.execTerm] at hTerm)

/-- Halt-shaped corollary of `compileLoop_sound`: when the IR result
    frame is halted, the Effect run `.halt`s with it — the Phase 3
    statement, derived from the generalized transfer conclusion by
    peeling one step of the right-hand `runFrame`. -/
theorem compileLoop_sound_halt (code : Evm.Bytes) (pc : Nat)
    (ops : List Op) (gas : Nat) (term : Terminator) (endPc : Nat)
    (hC : IR.compileLoop .frontier code pc = .ok (ops, gas, term, endPc))
    (i i2 i' : Evm)
    (hcc : i.message.code = code) (hHalt : i.halted = false)
    (hOps : IR.execOps i ops = .ok i2)
    (hTerm : IR.execTerm i2 endPc term = .ok i')
    (hHalted : i'.halted = true) :
    ∃ fuel, Effect.runFrameR fuel
      { i with gasLeft := i.gasLeft + gas, pc := pc } = .halt i' i'.output := by
  obtain ⟨n, hrun⟩ :=
    compileLoop_sound code pc ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
  refine ⟨n + (0 + 1), ?_⟩
  rw [hrun 0, runFrameR_succ, step1_halted i' hHalted]

/-- Chunk-level soundness vs the Effect interpreter (no-jump slice).

    If compiling `code` yields a chunk and `IR.execute` runs it to a
    halted frame `evm'`, then `Effect.runFrameR` — given adequate
    fuel — halts with exactly `evm'` from the same starting frame.

    The `evm.pc = 0` hypothesis pins the frame to the chunk entry
    (the no-jump slice compiles a single chunk from pc 0). -/
theorem compile_sound_vs_effect
    (code : Evm.Bytes) (chunk : Chunk) (evm evm' : Evm)
    (hcc : evm.message.code = code)
    (hpc : evm.pc = 0)
    (hHalt : evm.halted = false)
    (hcompile : IR.compile .frontier code = .ok chunk)
    (hexec : IR.execute chunk evm = .ok evm')
    (hHalted : evm'.halted = true) :
    ∃ fuel, Effect.runFrameR fuel evm = .halt evm' evm'.output := by
  unfold IR.compile at hcompile
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hcompile
  obtain ⟨⟨ops, gas, term, endPc⟩, hloop, hchunk⟩ := hcompile
  simp only [pure, Except.pure, Except.ok.injEq] at hchunk
  subst hchunk
  unfold IR.execute at hexec
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hexec
  obtain ⟨g0, hcharge, i2, hOps, hTerm⟩ := hexec
  obtain ⟨hle, rfl⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hcharge
  obtain ⟨fuel, hrun⟩ :=
    compileLoop_sound_halt code 0 ops gas term endPc hloop
      { evm with gasLeft := evm.gasLeft - gas } i2 evm' hcc hHalt hOps hTerm
      hHalted
  refine ⟨fuel, ?_⟩
  have hEq : evm = { evm with gasLeft := evm.gasLeft - gas + gas, pc := 0 } := by
    rw [Nat.sub_add_cancel hle, ← hpc]
  rw [hEq]
  exact hrun

/-! ## Yield soundness — CALL / CALLCODE / CREATE chunks

    The yielding terminators are inexpressible in the Except-valued
    `IR.execute` track, so their soundness statement lives at the
    `StepResult` level: `IR.executeStep` on a chunk compiled at the
    opcode equals `Effect.step1` on the frame positioned there. Both
    sides ARE `Effect.doCall` / `doCallcode` / `doCreate` — the chunk
    has no ops and zero static gas, and
    `Trampoline.Terminator.stepHandler` binds the very handlers
    `step1` dispatches to (binding-not-reencoding) — so each proof is
    `rfl` once the frame's `halted := false` is folded away. The
    downstream yield processing is shared by definition:
    `Trampoline.runYield = Effect.handleYield`
    (`runYield_is_handleYield`), so everything proven about the
    Effect trampoline's resume path covers `IR.runProgram`. -/

private theorem executeStep_call (i : Evm) (x : Nat)
    (hHalt : i.halted = false)
    (hSize : x < i.message.code.size)
    (hCode : i.message.code.get! x = 0xf1) :
    IR.executeStep .frontier ⟨x, x, 0, [], .call .call⟩ i
      = Effect.step1 { i with pc := x } := by
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (x ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show IR.executeStep .frontier ⟨x, x, 0, [], .call .call⟩ i
      = Effect.doCall { i with pc := x, halted := false }
  rw [show ({ i with pc := x, halted := false } : Evm)
        = { i with pc := x } from by rw [← hHalt]]
  rfl

private theorem executeStep_callcode (i : Evm) (x : Nat)
    (hHalt : i.halted = false)
    (hSize : x < i.message.code.size)
    (hCode : i.message.code.get! x = 0xf2) :
    IR.executeStep .frontier ⟨x, x, 0, [], .call .callcode⟩ i
      = Effect.step1 { i with pc := x } := by
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (x ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show IR.executeStep .frontier ⟨x, x, 0, [], .call .callcode⟩ i
      = Effect.doCallcode { i with pc := x, halted := false }
  rw [show ({ i with pc := x, halted := false } : Evm)
        = { i with pc := x } from by rw [← hHalt]]
  rfl

private theorem executeStep_create (i : Evm) (x : Nat)
    (hHalt : i.halted = false)
    (hSize : x < i.message.code.size)
    (hCode : i.message.code.get! x = 0xf0) :
    IR.executeStep .frontier ⟨x, x, 0, [], .create .create⟩ i
      = Effect.step1 { i with pc := x } := by
  simp only [Effect.step1, hHalt, hCode, ite_false,
             show ¬ (x ≥ i.message.code.size) from Nat.not_le.mpr hSize]
  show IR.executeStep .frontier ⟨x, x, 0, [], .create .create⟩ i
      = Effect.doCreate { i with pc := x, halted := false }
  rw [show ({ i with pc := x, halted := false } : Evm)
        = { i with pc := x } from by rw [← hHalt]]
  rfl

/-- CALL chunk soundness: the chunk `compileLoop` emits at a 0xf1
    opcode steps (via `IR.executeStep`) to exactly what one
    `Effect.step1` produces from the frame positioned at the opcode
    — including the `.yield` carrying the sub-frame request. -/
theorem executeStep_call_sound (code : Evm.Bytes) (x : Nat)
    (ops : List Op) (gas : Nat) (term : Terminator) (endPc : Nat)
    (hlt : ¬ x ≥ code.size)
    (hop : (code.get! x).toNat = 0xf1)
    (hC : IR.compileLoop .frontier code x = .ok (ops, gas, term, endPc))
    (i : Evm) (hcc : i.message.code = code) (hHalt : i.halted = false) :
    IR.executeStep .frontier ⟨x, endPc, gas, ops, term⟩ i
      = Effect.step1 { i with pc := x } := by
  rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
  simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
  exact executeStep_call i x hHalt (by rw [hcc]; omega)
    (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop))

/-- CALLCODE chunk soundness — see `executeStep_call_sound`. -/
theorem executeStep_callcode_sound (code : Evm.Bytes) (x : Nat)
    (ops : List Op) (gas : Nat) (term : Terminator) (endPc : Nat)
    (hlt : ¬ x ≥ code.size)
    (hop : (code.get! x).toNat = 0xf2)
    (hC : IR.compileLoop .frontier code x = .ok (ops, gas, term, endPc))
    (i : Evm) (hcc : i.message.code = code) (hHalt : i.halted = false) :
    IR.executeStep .frontier ⟨x, endPc, gas, ops, term⟩ i
      = Effect.step1 { i with pc := x } := by
  rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
  simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
  exact executeStep_callcode i x hHalt (by rw [hcc]; omega)
    (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop))

/-- CREATE chunk soundness — see `executeStep_call_sound`. -/
theorem executeStep_create_sound (code : Evm.Bytes) (x : Nat)
    (ops : List Op) (gas : Nat) (term : Terminator) (endPc : Nat)
    (hlt : ¬ x ≥ code.size)
    (hop : (code.get! x).toNat = 0xf0)
    (hC : IR.compileLoop .frontier code x = .ok (ops, gas, term, endPc))
    (i : Evm) (hcc : i.message.code = code) (hHalt : i.halted = false) :
    IR.executeStep .frontier ⟨x, endPc, gas, ops, term⟩ i
      = Effect.step1 { i with pc := x } := by
  rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
  simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
  exact executeStep_create i x hHalt (by rw [hcc]; omega)
    (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop))

/-! ## (2) IR.execute vs the spec (`IsFrameRun`)

    Same chunk induction as (1), but the conclusion is the spec's
    frame-run relation instead of the Effect interpreter: each
    compiled op becomes one `IsFrameRun.step` whose `IsAnyStep`
    dispatch fires the corresponding `IsXxxStep`, and the
    terminator becomes the final step into a halted frame closed
    by `IsFrameRun.done`. The gas-offset invariant is identical —
    the spec charges per-op, the IR pre-charged the chunk. -/

/-- `code[pc]?` agrees with `code.get!` in bounds — the bridge from
    the executable's `get!`-based dispatch to `IsAnyStep`'s
    `getElem?`-based dispatch. -/
private theorem bytes_getElem?_eq_get! (code : Evm.Bytes) (pc : Nat)
    (h : pc < code.size) : code[pc]? = some (code.get! pc) := by
  rw [getElem?_pos code pc h]
  show _ = some code.data[pc]!
  rw [getElem!_pos code.data pc h]
  rfl

/-- `chargeMemory` success in the spec's vocabulary: the cost is
    `memExpansionGas` and the resulting memory is `memAfterExpand`.
    Wraps `chargeMemory_ok`, folding away its `max`-form via
    `memoryExpansionCost_max`. -/
private theorem chargeMemory_spec {g : Nat} {m : Memory} {off size g' : Nat}
    {m' : Memory}
    (h : Instructions.chargeMemory g m off size = .ok (g', m')) :
    Evm.Frontier.Spec.memExpansionGas m off size ≤ g ∧
    g' = g - Evm.Frontier.Spec.memExpansionGas m off size ∧
    m' = Evm.Frontier.Spec.memAfterExpand m off size := by
  obtain ⟨hle, hg, _, hm⟩ := Evm.Frontier.Spec.chargeMemory_ok h
  by_cases hsz : size = 0
  · subst hsz
    simp only [reduceIte, Evm.Frontier.Spec.memoryExpansionCost_self] at hg hm
    simp only [Evm.Frontier.Spec.memExpansionGas,
               Evm.Frontier.Spec.memAfterExpand, reduceIte]
    exact ⟨Nat.zero_le _, by omega, hm⟩
  · simp only [ite_eq_right hsz] at hle hg hm
    rw [Evm.Frontier.Spec.memoryExpansionCost_max] at hle hg
    simp only [Evm.Frontier.Spec.memExpansionGas,
               Evm.Frontier.Spec.memAfterExpand, ite_eq_right hsz]
    exact ⟨hle, hg, hm⟩

/-- `popTopicsAux` success splits the stack: the popped topics are a
    prefix of length `n` and the leftover is the suffix. Connects the
    Effect/IR-side topic popping to `IsLogStep`'s
    `stack = offset :: len :: (topics ++ rest)` clause. -/
private theorem popTopicsAux_eq_ok (s s' : Stack) (n : Nat)
    (topics : List Evm.U256)
    (h : Effect.popTopicsAux s n = .ok (topics, s')) :
    s = topics ++ s' ∧ topics.length = n := by
  induction n generalizing s topics with
  | zero =>
    simp only [Effect.popTopicsAux, pure, Except.pure, Except.ok.injEq,
               Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | succ k ihk =>
    simp only [Effect.popTopicsAux, bind,
               Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
    obtain ⟨⟨t, s1⟩, hp, h⟩ := h
    simp only at h
    obtain ⟨⟨ts, s2⟩, hrec, h⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hsplit, hlen⟩ := ihk s1 ts hrec
    have hs1 := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
    subst hs1; subst hsplit
    exact ⟨rfl, by simp [hlen]⟩

/-! ### IsAnyStep introduction — one lemma per dispatch arm

    Each reduces `IsAnyStep`'s match to the right `IsXxxStep` given
    the opcode at `pc`. Stated over an abstract `evm` so the `rw`s
    match syntactically; chunk-level callers instantiate `evm` with
    a record literal and the hypotheses pass by defeq. -/

private theorem anyStep_endOfCode (evm evm' : Evm)
    (hSize : evm.pc ≥ evm.message.code.size)
    (h : evm' = { evm with halted := true }) :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [getElem?_neg evm.message.code evm.pc (by omega)]
  exact h

private theorem anyStep_stop (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x00)
    (h : Evm.Frontier.Spec.IsStopStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_add (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x01)
    (h : Evm.Frontier.Spec.IsAddStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_mul (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x02)
    (h : Evm.Frontier.Spec.IsMulStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_sub (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x03)
    (h : Evm.Frontier.Spec.IsSubStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_pop (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x50)
    (h : Evm.Frontier.Spec.IsPopStep Gas.base evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_mload (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x51)
    (h : Evm.Frontier.Spec.IsMloadStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_mstore (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x52)
    (h : Evm.Frontier.Spec.IsMstoreStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_ret (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0xf3)
    (h : Evm.Frontier.Spec.IsReturnStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_selfdestruct (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0xff)
    (h : Evm.Frontier.Spec.IsSelfdestructStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_jump (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x56)
    (h : Evm.Frontier.Spec.IsJumpStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_jumpi (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x57)
    (h : Evm.Frontier.Spec.IsJumpiStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_push (evm evm' : Evm) (nop : Nat)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : (evm.message.code.get! evm.pc).toNat = nop)
    (hlo : 0x60 ≤ nop) (hhi : nop ≤ 0x7f)
    (h : Evm.Frontier.Spec.IsPushStep (nop - 0x5f) Gas.veryLow evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize]
  interval_cases nop <;>
  · simp only [hCode]
    exact h

private theorem anyStep_keccak256 (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x20)
    (h : Evm.Frontier.Spec.IsKeccak256Step evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_calldatacopy (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x37)
    (h : Evm.Frontier.Spec.IsCalldatacopyStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_codecopy (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x39)
    (h : Evm.Frontier.Spec.IsCodecopyStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_dup (evm evm' : Evm) (nop : Nat)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : (evm.message.code.get! evm.pc).toNat = nop)
    (hlo : 0x80 ≤ nop) (hhi : nop ≤ 0x8f)
    (h : Evm.Frontier.Spec.IsDupStep (nop - 0x7f) Gas.veryLow evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize]
  interval_cases nop <;>
  · simp only [hCode]
    exact h

private theorem anyStep_swap (evm evm' : Evm) (nop : Nat)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : (evm.message.code.get! evm.pc).toNat = nop)
    (hlo : 0x90 ≤ nop) (hhi : nop ≤ 0x9f)
    (h : Evm.Frontier.Spec.IsSwapStep (nop - 0x8f) Gas.veryLow evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize]
  interval_cases nop <;>
  · simp only [hCode]
    exact h

private theorem anyStep_balance (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x31)
    (h : Evm.Frontier.Spec.IsBalanceStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_extcodesize (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x3b)
    (h : Evm.Frontier.Spec.IsExtcodesizeStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_extcodecopy (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x3c)
    (h : Evm.Frontier.Spec.IsExtcodecopyStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_blockhash (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x40)
    (h : Evm.Frontier.Spec.IsBlockhashStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_sload (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x54)
    (h : Evm.Frontier.Spec.IsSloadStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_sstore (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x55)
    (h : Evm.Frontier.Spec.IsSstoreStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_log (evm evm' : Evm) (nop : Nat)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : (evm.message.code.get! evm.pc).toNat = nop)
    (hlo : 0xa0 ≤ nop) (hhi : nop ≤ 0xa4)
    (h : Evm.Frontier.Spec.IsLogStep (nop - 0xa0) evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize]
  interval_cases nop <;>
  · simp only [hCode]
    exact h

private theorem anyStep_div (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x04)
    (h : Evm.Frontier.Spec.IsDivStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_sdiv (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x05)
    (h : Evm.Frontier.Spec.IsSdivStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_mod (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x06)
    (h : Evm.Frontier.Spec.IsModStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_smod (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x07)
    (h : Evm.Frontier.Spec.IsSmodStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_addmod (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x08)
    (h : Evm.Frontier.Spec.IsAddmodStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_mulmod (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x09)
    (h : Evm.Frontier.Spec.IsMulmodStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_signextend (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x0b)
    (h : Evm.Frontier.Spec.IsSignextendStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_lt (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x10)
    (h : Evm.Frontier.Spec.IsLtStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_gt (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x11)
    (h : Evm.Frontier.Spec.IsGtStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_slt (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x12)
    (h : Evm.Frontier.Spec.IsSltStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_sgt (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x13)
    (h : Evm.Frontier.Spec.IsSgtStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_eq (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x14)
    (h : Evm.Frontier.Spec.IsEqStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_iszero (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x15)
    (h : Evm.Frontier.Spec.IsIszeroStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_and (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x16)
    (h : Evm.Frontier.Spec.IsAndStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_or (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x17)
    (h : Evm.Frontier.Spec.IsOrStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_xor (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x18)
    (h : Evm.Frontier.Spec.IsXorStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_not (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x19)
    (h : Evm.Frontier.Spec.IsNotStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_byte (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x1a)
    (h : Evm.Frontier.Spec.IsByteStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_exp (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x0a)
    (h : Evm.Frontier.Spec.IsExpStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_address (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x30)
    (h : Evm.Frontier.Spec.IsAddressStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_origin (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x32)
    (h : Evm.Frontier.Spec.IsOriginStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_caller (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x33)
    (h : Evm.Frontier.Spec.IsCallerStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_callvalue (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x34)
    (h : Evm.Frontier.Spec.IsCallvalueStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_calldataload (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x35)
    (h : Evm.Frontier.Spec.IsCalldataloadStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_calldatasize (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x36)
    (h : Evm.Frontier.Spec.IsCalldatasizeStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_codesize (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x38)
    (h : Evm.Frontier.Spec.IsCodesizeStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_gasprice (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x3a)
    (h : Evm.Frontier.Spec.IsGaspriceStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_coinbase (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x41)
    (h : Evm.Frontier.Spec.IsCoinbaseStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_timestamp (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x42)
    (h : Evm.Frontier.Spec.IsTimestampStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_number (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x43)
    (h : Evm.Frontier.Spec.IsNumberStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_difficulty (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x44)
    (h : Evm.Frontier.Spec.IsDifficultyStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_gaslimit (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x45)
    (h : Evm.Frontier.Spec.IsGaslimitStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_mstore8 (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x53)
    (h : Evm.Frontier.Spec.IsMstore8Step evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_pc (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x58)
    (h : Evm.Frontier.Spec.IsPcStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_msize (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x59)
    (h : Evm.Frontier.Spec.IsMsizeStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_gas (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x5a)
    (h : Evm.Frontier.Spec.IsGasStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

private theorem anyStep_jumpdest (evm evm' : Evm)
    (hSize : evm.pc < evm.message.code.size)
    (hCode : evm.message.code.get! evm.pc = 0x5b)
    (h : Evm.Frontier.Spec.IsJumpdestStep evm evm') :
    Evm.Frontier.Spec.IsAnyStep evm evm' := by
  unfold Evm.Frontier.Spec.IsAnyStep
  rw [bytes_getElem?_eq_get! _ _ hSize, hCode]
  exact h

/-! ### Per-Op spec-shifted lemmas

    Spec-side twins of `step1_*_shifted`: from `IR.execOp` success,
    conclude that the gas-shifted frames are related by `IsAnyStep`
    (instead of one `Effect.step1`). -/

theorem spec_add_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x01)
    (hIR : IR.execOp i .add = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨a, b, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (a + b) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  refine ⟨?_, rfl, rfl⟩
  refine anyStep_add _ _ hSize hCode ?_
  refine ⟨a, b, rest, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩
  simp [nat_add_sub_mid]

theorem spec_mul_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x02)
    (hIR : IR.execOp i .mul = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.low + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨a, b, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (a * b) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  refine ⟨?_, rfl, rfl⟩
  refine anyStep_mul _ _ hSize hCode ?_
  refine ⟨a, b, rest, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩
  simp [nat_add_sub_mid]

theorem spec_sub_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x03)
    (hIR : IR.execOp i .sub = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨a, b, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (a - b) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  refine ⟨?_, rfl, rfl⟩
  refine anyStep_sub _ _ hSize hCode ?_
  refine ⟨a, b, rest, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩
  simp [nat_add_sub_mid]

theorem spec_pop_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x50)
    (hIR : IR.execOp i .pop = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp : Stack.pop i.stack with _ | ⟨a, s⟩
  · rw [hp] at hIR; simp at hIR
  rw [hp] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  have hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  refine anyStep_pop _ _ hSize hCode ?_
  refine ⟨a, s, hStack, nat_le_add_mid _ _ _, ?_⟩
  simp [nat_add_sub_mid]

theorem spec_mload_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x51)
    (hIR : IR.execOp i .mload = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp : Stack.pop i.stack with _ | ⟨off, s⟩
  · rw [hp] at hIR; simp at hIR
  rw [hp] at hIR
  simp only at hIR
  rcases hcm : Instructions.chargeMemory i.gasLeft i.memory off.toNat 32
      with _ | ⟨gl, mem⟩
  · rw [hcm] at hIR; simp at hIR
  rw [hcm] at hIR
  simp only at hIR
  rcases hpush : Stack.push s (Evm.U256.ofBytesBE (Memory.read mem off.toNat 32))
      with _ | s2
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  have hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq
  obtain ⟨hcle, hgl, hmem⟩ := chargeMemory_spec hcm
  subst hgl; subst hmem
  refine anyStep_mload _ _ hSize hCode ?_
  refine ⟨off, s, hStack, hlt, nat_le_add_mid2 _ _ _ _ hcle, ?_⟩
  simp [nat_add_sub_mid2 _ _ _ g hcle]

theorem spec_mstore_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x52)
    (hIR : IR.execOp i .mstore = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨off, value, s⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hcm : Instructions.chargeMemory i.gasLeft i.memory off.toNat 32
      with _ | ⟨gl, mem⟩
  · rw [hcm] at hIR; simp at hIR
  rw [hcm] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hcle, hgl, hmem⟩ := chargeMemory_spec hcm
  subst hgl; subst hmem
  refine anyStep_mstore _ _ hSize hCode ?_
  refine ⟨off, value, s, hStack, nat_le_add_mid2 _ _ _ _ hcle, ?_⟩
  simp [nat_add_sub_mid2 _ _ _ g hcle]

theorem spec_push_shifted (i i2 : Evm) (g pcv nop : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : (i.message.code.get! pcv).toNat = nop)
    (hlo : 0x60 ≤ nop) (hhi : nop ≤ 0x7f)
    (hIR : IR.execOp i
        (.push (nop - 0x5f) (readImmediate i.message.code pcv (nop - 0x5f)))
      = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 + (nop - 0x5f) } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hpush : Stack.push i.stack
      (readImmediate i.message.code pcv (nop - 0x5f)) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq
  refine anyStep_push _ _ nop hSize hCode hlo hhi ?_
  rw [show pcv + 1 + (nop - 0x5f) = pcv + (nop - 0x5f) + 1 from by omega]
  refine ⟨hlt, nat_le_add_mid _ _ _, ?_⟩
  simp [nat_add_sub_mid,
        show Evm.Frontier.Spec.pushImmediate i.message.code pcv (nop - 0x5f)
            = IR.readImmediate i.message.code pcv (nop - 0x5f) from rfl]

/-- `Stack.dup` success unpacked into the `IsDupStep` vocabulary. -/
private theorem stack_dup_ok {s s' : Stack} {n : Nat}
    (h : Stack.dup s n = .ok s') :
    ∃ v, s[n - 1]? = some v ∧ s.length < stackLimit ∧ s' = v :: s := by
  unfold Stack.dup Stack.peek at h
  simp only [bind, Except.bind] at h
  rcases hv : s[n - 1]? with _ | v
  · rw [hv] at h; simp at h
  rw [hv] at h
  simp only at h
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp h
  exact ⟨v, rfl, hlt, hsEq⟩

/-- `Stack.swap` success unpacked into the `IsSwapStep` vocabulary. -/
private theorem stack_swap_ok {s s' : Stack} {n : Nat}
    (h : Stack.swap s n = .ok s') :
    ∃ top other rest, s = top :: rest ∧ rest[n - 1]? = some other ∧
      s' = other :: rest.set (n - 1) top := by
  unfold Stack.swap at h
  rcases s with _ | ⟨top, rest⟩
  · simp at h
  simp only at h
  rcases hv : rest[n - 1]? with _ | other
  · rw [hv] at h; simp at h
  rw [hv] at h
  simp only [Except.ok.injEq] at h
  exact ⟨top, other, rest, rfl, hv, h.symm⟩

theorem spec_dup_shifted (i i2 : Evm) (g pcv nop : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : (i.message.code.get! pcv).toNat = nop)
    (hlo : 0x80 ≤ nop) (hhi : nop ≤ 0x8f)
    (hIR : IR.execOp i (.dup (nop - 0x7f)) = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hd : Stack.dup i.stack (nop - 0x7f) with _ | s'
  · rw [hd] at hIR; simp at hIR
  rw [hd] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  obtain ⟨v, hv, hlt, hsEq⟩ := stack_dup_ok hd
  subst hsEq
  refine anyStep_dup _ _ nop hSize hCode hlo hhi ?_
  refine ⟨v, by omega, by omega, hv, hlt, nat_le_add_mid _ _ _, ?_⟩
  simp [nat_add_sub_mid]

theorem spec_swap_shifted (i i2 : Evm) (g pcv nop : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : (i.message.code.get! pcv).toNat = nop)
    (hlo : 0x90 ≤ nop) (hhi : nop ≤ 0x9f)
    (hIR : IR.execOp i (.swap (nop - 0x8f)) = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hs : Stack.swap i.stack (nop - 0x8f) with _ | s'
  · rw [hs] at hIR; simp at hIR
  rw [hs] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  obtain ⟨top, other, rest, hsEq, hv, hs'Eq⟩ := stack_swap_ok hs
  subst hs'Eq
  refine anyStep_swap _ _ nop hSize hCode hlo hhi ?_
  refine ⟨top, other, rest, hsEq, hv, nat_le_add_mid _ _ _, ?_⟩
  simp [nat_add_sub_mid]

/-! ### Generic spec-shifted cores (no `hHalt`, no `halted := false`)

    Spec-side twins of the `liftPure_*_shifted` cores: from the
    do-block form of `IR.execOp` success, conclude the gas-shifted
    `Is*Step` directly. Wrappers compose with the `anyStep_*`
    intros above. -/

private theorem spec_binary_shifted_core (i i2 : Evm) (g pcv : Nat)
    (gas : Gas.Gas) (f : Evm.U256 → Evm.U256 → Evm.U256)
    (hIR : (do
        let (a, b, s) ← Stack.pop2 i.stack
        let s ← Stack.push s (f a b)
        pure { i with stack := s } : Except Exception Evm) = .ok i2) :
    Evm.Frontier.Spec.IsBinaryStep f gas
      { i with gasLeft := i.gasLeft + (gas + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨a, b, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (f a b) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  refine ⟨⟨a, b, rest, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩, rfl, rfl⟩
  simp [nat_add_sub_mid]

private theorem spec_unary_shifted_core (i i2 : Evm) (g pcv : Nat)
    (gas : Gas.Gas) (f : Evm.U256 → Evm.U256)
    (hIR : (do
        let (a, s) ← Stack.pop i.stack
        let s ← Stack.push s (f a)
        pure { i with stack := s } : Except Exception Evm) = .ok i2) :
    Evm.Frontier.Spec.IsUnaryStep f gas
      { i with gasLeft := i.gasLeft + (gas + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  simp only [bind, Except.bind] at hIR
  rcases hp : Stack.pop i.stack with _ | ⟨a, rest⟩
  · rw [hp] at hIR; simp at hIR
  rw [hp] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (f a) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  refine ⟨⟨a, rest, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩, rfl, rfl⟩
  simp [nat_add_sub_mid]

private theorem spec_ternary_shifted_core (i i2 : Evm) (g pcv : Nat)
    (gas : Gas.Gas) (f : Evm.U256 → Evm.U256 → Evm.U256 → Evm.U256)
    (hIR : (do
        let (a, b, c, s) ← Stack.pop3 i.stack
        let s ← Stack.push s (f a b c)
        pure { i with stack := s } : Except Exception Evm) = .ok i2) :
    Evm.Frontier.Spec.IsTernaryStep f gas
      { i with gasLeft := i.gasLeft + (gas + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  simp only [bind, Except.bind] at hIR
  rcases hp3 : Stack.pop3 i.stack with _ | ⟨a, b, c, rest⟩
  · rw [hp3] at hIR; simp at hIR
  rw [hp3] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest (f a b c) with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop3_eq_ok_iff _ _ _ _ _).mp hp3
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  refine ⟨⟨a, b, c, rest, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩, rfl, rfl⟩
  simp [nat_add_sub_mid]

theorem spec_div_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x04)
    (hIR : IR.execOp i .div = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.low + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_binary_shifted_core i i2 g pcv Gas.low
      (fun a b => if b = 0 then 0 else BitVec.udiv a b) hIR
  exact ⟨anyStep_div _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_sdiv_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x05)
    (hIR : IR.execOp i .sdiv = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.low + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_binary_shifted_core i i2 g pcv Gas.low
      (fun a b => if b = 0 then 0 else BitVec.sdiv a b) hIR
  exact ⟨anyStep_sdiv _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_mod_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x06)
    (hIR : IR.execOp i .mod = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.low + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_binary_shifted_core i i2 g pcv Gas.low
      (fun a b => if b = 0 then 0 else BitVec.umod a b) hIR
  exact ⟨anyStep_mod _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_smod_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x07)
    (hIR : IR.execOp i .smod = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.low + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_binary_shifted_core i i2 g pcv Gas.low
      (fun a b => if b = 0 then 0 else BitVec.srem a b) hIR
  exact ⟨anyStep_smod _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_addmod_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x08)
    (hIR : IR.execOp i .addmod = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.mid + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_ternary_shifted_core i i2 g pcv Gas.mid
      (fun a b n =>
        if n = 0 then 0 else Evm.U256.ofNat ((a.toNat + b.toNat) % n.toNat)) hIR
  exact ⟨anyStep_addmod _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_mulmod_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x09)
    (hIR : IR.execOp i .mulmod = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.mid + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_ternary_shifted_core i i2 g pcv Gas.mid
      (fun a b n =>
        if n = 0 then 0 else Evm.U256.ofNat ((a.toNat * b.toNat) % n.toNat)) hIR
  exact ⟨anyStep_mulmod _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_signextend_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x0b)
    (hIR : IR.execOp i .signextend = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.low + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_binary_shifted_core i i2 g pcv Gas.low
      Instructions.signExtend hIR
  exact ⟨anyStep_signextend _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_lt_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x10)
    (hIR : IR.execOp i .lt = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_binary_shifted_core i i2 g pcv Gas.veryLow
      (fun a b => if a < b then 1 else 0) hIR
  exact ⟨anyStep_lt _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_gt_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x11)
    (hIR : IR.execOp i .gt = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_binary_shifted_core i i2 g pcv Gas.veryLow
      (fun a b => if a > b then 1 else 0) hIR
  exact ⟨anyStep_gt _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_slt_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x12)
    (hIR : IR.execOp i .slt = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_binary_shifted_core i i2 g pcv Gas.veryLow
      (fun a b => if BitVec.slt a b then 1 else 0) hIR
  exact ⟨anyStep_slt _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_sgt_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x13)
    (hIR : IR.execOp i .sgt = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_binary_shifted_core i i2 g pcv Gas.veryLow
      (fun a b => if BitVec.slt b a then 1 else 0) hIR
  exact ⟨anyStep_sgt _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_eq_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x14)
    (hIR : IR.execOp i .eq = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_binary_shifted_core i i2 g pcv Gas.veryLow
      (fun a b => if a = b then 1 else 0) hIR
  exact ⟨anyStep_eq _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_iszero_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x15)
    (hIR : IR.execOp i .iszero = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_unary_shifted_core i i2 g pcv Gas.veryLow
      (fun a => if a = 0 then 1 else 0) hIR
  exact ⟨anyStep_iszero _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_and_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x16)
    (hIR : IR.execOp i .and_ = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_binary_shifted_core i i2 g pcv Gas.veryLow
      (fun a b => a &&& b) hIR
  exact ⟨anyStep_and _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_or_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x17)
    (hIR : IR.execOp i .or_ = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_binary_shifted_core i i2 g pcv Gas.veryLow
      (fun a b => a ||| b) hIR
  exact ⟨anyStep_or _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_xor_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x18)
    (hIR : IR.execOp i .xor_ = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_binary_shifted_core i i2 g pcv Gas.veryLow
      (fun a b => a ^^^ b) hIR
  exact ⟨anyStep_xor _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_not_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x19)
    (hIR : IR.execOp i .not_ = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_unary_shifted_core i i2 g pcv Gas.veryLow
      (fun a => ~~~ a) hIR
  exact ⟨anyStep_not _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_byte_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x1a)
    (hIR : IR.execOp i .byte = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_binary_shifted_core i i2 g pcv Gas.veryLow
      Instructions.byteOf hIR
  exact ⟨anyStep_byte _ _ hSize hCode hStep, hmsg, hhalt⟩

/-- Spec-side twin of `step1_exp_shifted` — bespoke for the same
    split-gas reason. -/
theorem spec_exp_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x0a)
    (hIR : IR.execOp i .exp = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.exp + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨base, e, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hch : Gas.charge i.gasLeft
      (Gas.expByte * Instructions.expByteSize e.toNat) with _ | gl
  · rw [hch] at hIR; simp at hIR
  rw [hch] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest
      (Evm.U256.ofNat (Instructions.powMod base.toNat e.toNat (1 <<< 256)))
      with _ | s2
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  obtain ⟨hdle, rfl⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
  refine ⟨?_, rfl, rfl⟩
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq
  refine anyStep_exp _ _ hSize hCode ?_
  refine ⟨base, e, rest, hStack, hlt, nat_le_add_mid2 _ _ _ _ hdle, ?_⟩
  simp [nat_add_sub_mid2 _ _ _ g hdle]

theorem spec_keccak256_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x20)
    (hIR : IR.execOp i .keccak256 = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.keccak256 + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨offset, len, rest⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hch : Gas.charge i.gasLeft
      (Gas.keccak256Word * ((len.toNat + 31) / 32)) with _ | gl1
  · rw [hch] at hIR; simp at hIR
  rw [hch] at hIR
  simp only at hIR
  rcases hcm : Instructions.chargeMemory gl1 i.memory offset.toNat len.toNat
      with _ | ⟨gl, mem⟩
  · rw [hcm] at hIR; simp at hIR
  rw [hcm] at hIR
  simp only at hIR
  rcases hpush : Stack.push rest
      (Evm.Crypto.keccak256 (Memory.read mem offset.toNat len.toNat))
      with _ | s2
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  obtain ⟨hdle, rfl⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
  refine ⟨?_, rfl, rfl⟩
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq
  obtain ⟨hcle, hgl, hmem⟩ := chargeMemory_spec hcm
  subst hgl; subst hmem
  refine anyStep_keccak256 _ _ hSize hCode ?_
  refine ⟨offset, len, rest, hStack, hlt,
          nat_le_add_mid3 _ _ _ _ _ hdle hcle, ?_⟩
  simp [nat_add_sub_mid3 _ _ _ _ g hdle hcle]

theorem spec_calldatacopy_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x37)
    (hIR : IR.execOp i .calldatacopy = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp3 : Stack.pop3 i.stack with _ | ⟨dest, off, len, rest⟩
  · rw [hp3] at hIR; simp at hIR
  rw [hp3] at hIR
  simp only at hIR
  rcases hch : Gas.charge i.gasLeft (Gas.copy * ((len.toNat + 31) / 32))
      with _ | gl1
  · rw [hch] at hIR; simp at hIR
  rw [hch] at hIR
  simp only at hIR
  rcases hcm : Instructions.chargeMemory gl1 i.memory dest.toNat len.toNat
      with _ | ⟨gl, mem⟩
  · rw [hcm] at hIR; simp at hIR
  rw [hcm] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  obtain ⟨hdle, rfl⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
  refine ⟨?_, rfl, rfl⟩
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop3_eq_ok_iff _ _ _ _ _).mp hp3
  obtain ⟨hcle, hgl, hmem⟩ := chargeMemory_spec hcm
  subst hgl; subst hmem
  refine anyStep_calldatacopy _ _ hSize hCode ?_
  refine ⟨dest, off, len, rest, hStack,
          nat_le_add_mid3 _ _ _ _ _ hdle hcle, ?_⟩
  simp [nat_add_sub_mid3 _ _ _ _ g hdle hcle]

theorem spec_codecopy_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x39)
    (hIR : IR.execOp i .codecopy = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp3 : Stack.pop3 i.stack with _ | ⟨dest, off, len, rest⟩
  · rw [hp3] at hIR; simp at hIR
  rw [hp3] at hIR
  simp only at hIR
  rcases hch : Gas.charge i.gasLeft (Gas.copy * ((len.toNat + 31) / 32))
      with _ | gl1
  · rw [hch] at hIR; simp at hIR
  rw [hch] at hIR
  simp only at hIR
  rcases hcm : Instructions.chargeMemory gl1 i.memory dest.toNat len.toNat
      with _ | ⟨gl, mem⟩
  · rw [hcm] at hIR; simp at hIR
  rw [hcm] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  obtain ⟨hdle, rfl⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
  refine ⟨?_, rfl, rfl⟩
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop3_eq_ok_iff _ _ _ _ _).mp hp3
  obtain ⟨hcle, hgl, hmem⟩ := chargeMemory_spec hcm
  subst hgl; subst hmem
  refine anyStep_codecopy _ _ hSize hCode ?_
  refine ⟨dest, off, len, rest, hStack,
          nat_le_add_mid3 _ _ _ _ _ hdle hcle, ?_⟩
  simp [nat_add_sub_mid3 _ _ _ _ g hdle hcle]

theorem spec_balance_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x31)
    (hIR : IR.execOp i .balance = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.balance + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hIR
  obtain ⟨⟨addrW, s⟩, hp, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨s2, hpush, hIR⟩ := hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  have hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq
  refine anyStep_balance _ _ hSize hCode ?_
  refine ⟨addrW, s, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩
  simp [nat_add_sub_mid]

theorem spec_extcodesize_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x3b)
    (hIR : IR.execOp i .extcodesize = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.extCode + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hIR
  obtain ⟨⟨addrW, s⟩, hp, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨s2, hpush, hIR⟩ := hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  have hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq
  refine anyStep_extcodesize _ _ hSize hCode ?_
  refine ⟨addrW, s, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩
  simp [nat_add_sub_mid]

theorem spec_extcodecopy_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x3c)
    (hIR : IR.execOp i .extcodecopy = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.extCode + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hIR
  obtain ⟨⟨addrW, s⟩, hp, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨⟨memOff, codeOff, size, s'⟩, hp3, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨⟨gl1, mem⟩, hcm, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨gl, hch, hIR⟩ := hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  obtain ⟨hcle, hgl, hmem⟩ := chargeMemory_spec hcm
  subst hgl; subst hmem
  obtain ⟨hdle, rfl⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
  refine ⟨?_, rfl, rfl⟩
  have hStack : i.stack = addrW :: memOff :: codeOff :: size :: s' := by
    rw [(Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp,
        (Evm.Frontier.Vm.Spec.Stack.pop3_eq_ok_iff _ _ _ _ _).mp hp3]
  refine anyStep_extcodecopy _ _ hSize hCode ?_
  refine ⟨addrW, memOff, codeOff, size, s', hStack,
          nat_le_add_mid3' _ _ _ _ _ hcle hdle, ?_⟩
  simp [nat_add_sub_mid3' _ _ _ _ g hcle hdle]

theorem spec_blockhash_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x40)
    (hIR : IR.execOp i .blockhash = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.blockHash + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hIR
  obtain ⟨⟨n, s⟩, hp, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨s2, hpush, hIR⟩ := hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  have hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq
  refine anyStep_blockhash _ _ hSize hCode ?_
  refine ⟨n, s, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩
  simp [nat_add_sub_mid]

theorem spec_sload_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x54)
    (hIR : IR.execOp i .sload = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.sLoad + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hIR
  obtain ⟨⟨key, s⟩, hp, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨s2, hpush, hIR⟩ := hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  have hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq
  refine anyStep_sload _ _ hSize hCode ?_
  refine ⟨key, s, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩
  simp [nat_add_sub_mid]

theorem spec_sstore_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x55)
    (hIR : IR.execOp i .sstore = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (0 + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  by_cases hSt : i.message.isStatic = true
  · rw [ite_eq_left hSt] at hIR; simp at hIR
  rw [ite_eq_right hSt] at hIR
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hIR
  obtain ⟨⟨key, value, s⟩, hp2, hIR⟩ := hIR
  simp only at hIR
  obtain ⟨gl, hch, hIR⟩ := hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  obtain ⟨hdle, rfl⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
  refine ⟨?_, rfl, rfl⟩
  have hStack := (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  refine anyStep_sstore _ _ hSize hCode ?_
  refine ⟨key, value, s, hStack, Nat.le_add_right_of_le hdle, ?_⟩
  -- Full `simp` would normalize the U256 numerals inside the sSet/sReset
  -- ite (0 → 0#256), making it no longer match `hdle`'s ite; rewrite the
  -- gas arithmetic directly instead.
  simp only [Nat.zero_add]
  rw [nat_sub_add_comm g hdle]

theorem spec_log_shifted (i i2 : Evm) (g pcv nop : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : (i.message.code.get! pcv).toNat = nop)
    (hlo : 0xa0 ≤ nop) (hhi : nop ≤ 0xa4)
    (hIR : IR.execOp i (.log (nop - 0xa0)) = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft
                 + (Gas.log + Gas.logTopic * (nop - 0xa0) + g),
               pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  -- Same `.log n` caveat as `runFrameR_log_shifted`: reduce via the
  -- equation lemma, then one `bind_eq_ok` round rewrites the chain.
  simp only [IR.execOp] at hIR
  by_cases hSt : i.message.isStatic = true
  · rw [ite_eq_left hSt] at hIR; simp at hIR
  rw [ite_eq_right hSt] at hIR
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hIR
  obtain ⟨⟨offset, len, s⟩, hp2, hIR⟩ := hIR
  obtain ⟨⟨topics, s'⟩, hpt, hIR⟩ := hIR
  obtain ⟨gl1, hch, hIR⟩ := hIR
  obtain ⟨⟨gl, mem⟩, hcm, hIR⟩ := hIR
  simp only at hpt hch hcm hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  obtain ⟨hdle, rfl⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
  obtain ⟨hcle, hgl, hmem⟩ := chargeMemory_spec hcm
  subst hgl; subst hmem
  obtain ⟨hsplit, hlen⟩ := popTopicsAux_eq_ok _ _ _ _ hpt
  refine ⟨?_, rfl, rfl⟩
  have hStack : i.stack = offset :: len :: (topics ++ s') := by
    rw [(Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2, hsplit]
  refine anyStep_log _ _ nop hSize hCode hlo hhi ?_
  refine ⟨offset, len, topics, s', hStack, hlen,
          nat_le_add_mid3 _ _ _ _ _ hdle hcle, ?_⟩
  simp [nat_add_sub_mid3 _ _ _ _ g hdle hcle]

private theorem spec_nullaryPush_shifted_core (i i2 : Evm) (g pcv : Nat)
    (gas : Gas.Gas) (value : Evm → Evm.U256) (v : Evm.U256)
    (hval : value { i with gasLeft := i.gasLeft + (gas + g), pc := pcv } = v)
    (hIR : (do
        let s ← Stack.push i.stack v
        pure { i with stack := s } : Except Exception Evm) = .ok i2) :
    Evm.Frontier.Spec.IsNullaryPushStep value gas
      { i with gasLeft := i.gasLeft + (gas + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  simp only [bind, Except.bind] at hIR
  rcases hpush : Stack.push i.stack v with _ | s'
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq; subst hIR
  refine ⟨⟨hlt, nat_le_add_mid _ _ _, ?_⟩, rfl, rfl⟩
  rw [hval]
  simp [nat_add_sub_mid]

theorem spec_address_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x30)
    (hIR : IR.execOp i .address = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_nullaryPush_shifted_core i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.message.currentTarget.toNat)
      (Evm.U256.ofNat i.message.currentTarget.toNat)
      rfl hIR
  exact ⟨anyStep_address _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_origin_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x32)
    (hIR : IR.execOp i .origin = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_nullaryPush_shifted_core i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.env.origin.toNat)
      (Evm.U256.ofNat i.env.origin.toNat)
      rfl hIR
  exact ⟨anyStep_origin _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_caller_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x33)
    (hIR : IR.execOp i .caller = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_nullaryPush_shifted_core i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.message.caller.toNat)
      (Evm.U256.ofNat i.message.caller.toNat)
      rfl hIR
  exact ⟨anyStep_caller _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_callvalue_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x34)
    (hIR : IR.execOp i .callvalue = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_nullaryPush_shifted_core i i2 g pcv Gas.base
      (fun evm => evm.message.value)
      (i.message.value)
      rfl hIR
  exact ⟨anyStep_callvalue _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_calldatasize_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x36)
    (hIR : IR.execOp i .calldatasize = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_nullaryPush_shifted_core i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.message.data.size)
      (Evm.U256.ofNat i.message.data.size)
      rfl hIR
  exact ⟨anyStep_calldatasize _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_codesize_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x38)
    (hIR : IR.execOp i .codesize = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_nullaryPush_shifted_core i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.message.code.size)
      (Evm.U256.ofNat i.message.code.size)
      rfl hIR
  exact ⟨anyStep_codesize _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_gasprice_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x3a)
    (hIR : IR.execOp i .gasprice = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_nullaryPush_shifted_core i i2 g pcv Gas.base
      (fun evm => evm.env.gasPrice)
      (i.env.gasPrice)
      rfl hIR
  exact ⟨anyStep_gasprice _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_coinbase_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x41)
    (hIR : IR.execOp i .coinbase = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_nullaryPush_shifted_core i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.env.coinbase.toNat)
      (Evm.U256.ofNat i.env.coinbase.toNat)
      rfl hIR
  exact ⟨anyStep_coinbase _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_timestamp_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x42)
    (hIR : IR.execOp i .timestamp = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_nullaryPush_shifted_core i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.env.timestamp)
      (Evm.U256.ofNat i.env.timestamp)
      rfl hIR
  exact ⟨anyStep_timestamp _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_number_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x43)
    (hIR : IR.execOp i .number = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_nullaryPush_shifted_core i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.env.number)
      (Evm.U256.ofNat i.env.number)
      rfl hIR
  exact ⟨anyStep_number _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_difficulty_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x44)
    (hIR : IR.execOp i .prevrandao = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_nullaryPush_shifted_core i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.env.difficulty)
      (Evm.U256.ofNat i.env.difficulty)
      rfl hIR
  exact ⟨anyStep_difficulty _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_gaslimit_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x45)
    (hIR : IR.execOp i .gaslimit = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_nullaryPush_shifted_core i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.env.gasLimit)
      (Evm.U256.ofNat i.env.gasLimit)
      rfl hIR
  exact ⟨anyStep_gaslimit _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_pc_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x58)
    (hIR : IR.execOp i (.pc pcv) = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_nullaryPush_shifted_core i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.pc)
      (Evm.U256.ofNat pcv)
      rfl hIR
  exact ⟨anyStep_pc _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_msize_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x59)
    (hIR : IR.execOp i .msize = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_nullaryPush_shifted_core i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat evm.memory.size)
      (Evm.U256.ofNat i.memory.size)
      rfl hIR
  exact ⟨anyStep_msize _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_gas_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x5a)
    (hIR : IR.execOp i (.gas g) = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.base + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  obtain ⟨hStep, hmsg, hhalt⟩ :=
    spec_nullaryPush_shifted_core i i2 g pcv Gas.base
      (fun evm => Evm.U256.ofNat (evm.gasLeft - Gas.base))
      (Evm.U256.ofNat (i.gasLeft + g))
      (congrArg Evm.U256.ofNat (nat_add_sub_mid i.gasLeft Gas.base g)) hIR
  exact ⟨anyStep_gas _ _ hSize hCode hStep, hmsg, hhalt⟩

theorem spec_calldataload_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x35)
    (hIR : IR.execOp i .calldataload = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp : Stack.pop i.stack with _ | ⟨a, s⟩
  · rw [hp] at hIR; simp at hIR
  rw [hp] at hIR
  simp only at hIR
  rcases hpush : Stack.push s
      (Evm.U256.ofBytesBE (Evm.Bytes.sliceZeroPad i.message.data a.toNat 32))
      with _ | s2
  · rw [hpush] at hIR; simp at hIR
  rw [hpush] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  have hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  obtain ⟨hlt, hsEq⟩ :=
    (Evm.Frontier.Vm.Spec.Stack.push_eq_ok_iff _ _ _).mp hpush
  subst hsEq
  refine anyStep_calldataload _ _ hSize hCode ?_
  refine ⟨a, s, hStack, hlt, nat_le_add_mid _ _ _, ?_⟩
  simp [nat_add_sub_mid]

theorem spec_mstore8_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x53)
    (hIR : IR.execOp i .mstore8 = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.veryLow + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [bind, Except.bind] at hIR
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨off, value, s⟩
  · rw [hp2] at hIR; simp at hIR
  rw [hp2] at hIR
  simp only at hIR
  rcases hcm : Instructions.chargeMemory i.gasLeft i.memory off.toNat 1
      with _ | ⟨gl, mem⟩
  · rw [hcm] at hIR; simp at hIR
  rw [hcm] at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hcle, hgl, hmem⟩ := chargeMemory_spec hcm
  subst hgl; subst hmem
  refine anyStep_mstore8 _ _ hSize hCode ?_
  refine ⟨off, value, s, hStack, nat_le_add_mid2 _ _ _ _ hcle, ?_⟩
  simp [nat_add_sub_mid2 _ _ _ g hcle]

theorem spec_jumpdest_shifted (i i2 : Evm) (g pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x5b)
    (hIR : IR.execOp i .jumpdest = .ok i2) :
    Evm.Frontier.Spec.IsAnyStep
      { i with gasLeft := i.gasLeft + (Gas.jumpDest + g), pc := pcv }
      { i2 with gasLeft := i2.gasLeft + g, pc := pcv + 1 } ∧
    i2.message = i.message ∧ i2.halted = i.halted := by
  unfold IR.execOp at hIR
  simp only [pure, Except.pure, Except.ok.injEq] at hIR
  subst hIR
  refine ⟨?_, rfl, rfl⟩
  refine anyStep_jumpdest _ _ hSize hCode ?_
  refine ⟨nat_le_add_mid _ _ _, ?_⟩
  simp [nat_add_sub_mid]

/-- RETURN as a spec step: `IR.execTerm .ret` success yields an
    `IsAnyStep` (via `IsReturnStep`) into a halted frame. -/
theorem spec_ret_step (i i' : Evm) (pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0xf3)
    (hTerm : IR.execTerm i (pcv + 1) .ret = .ok i') :
    Evm.Frontier.Spec.IsAnyStep { i with pc := pcv } i' ∧ i'.halted = true := by
  unfold IR.execTerm at hTerm
  simp only [bind, Except.bind] at hTerm
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨off, len, s⟩
  · rw [hp2] at hTerm; simp at hTerm
  rw [hp2] at hTerm
  simp only at hTerm
  rcases hcm : Instructions.chargeMemory i.gasLeft i.memory off.toNat len.toNat
      with _ | ⟨gl, mem⟩
  · rw [hcm] at hTerm; simp at hTerm
  rw [hcm] at hTerm
  simp only [pure, Except.pure, Except.ok.injEq] at hTerm
  subst hTerm
  have hStack :=
    (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  obtain ⟨hcle, hgl, hmem⟩ := chargeMemory_spec hcm
  subst hgl; subst hmem
  refine ⟨?_, rfl⟩
  refine anyStep_ret _ _ hSize hCode ?_
  exact ⟨off, len, s, hStack, hcle, rfl⟩

/-- 0xff SELFDESTRUCT: a successful `.selfdestruct` terminator is
    one halting spec step (`IsSelfdestructStep`) from the frame
    positioned at the opcode. -/
theorem spec_selfdestruct_step (i i' : Evm) (pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0xff)
    (hTerm : IR.execTerm i pcv .selfdestruct = .ok i') :
    Evm.Frontier.Spec.IsAnyStep { i with pc := pcv } i' ∧
      i'.halted = true := by
  simp only [IR.execTerm] at hTerm
  unfold Evm.Frontier.Vm.selfdestruct at hTerm
  simp only [bind, Except.bind, pure, Except.pure] at hTerm
  by_cases hSt : i.message.isStatic = true
  · rw [ite_eq_left hSt] at hTerm; simp at hTerm
  rw [ite_eq_right hSt] at hTerm
  rcases hp : Stack.pop i.stack with _ | ⟨bW, s⟩
  · rw [hp] at hTerm; simp at hTerm
  rw [hp] at hTerm
  simp only [Except.ok.injEq] at hTerm
  subst hTerm
  refine ⟨?_, rfl⟩
  refine anyStep_selfdestruct _ _ hSize hCode ?_
  have hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
  exact ⟨bW, s, hStack, by simpa using hSt, rfl⟩


/-- 0x56 JUMP: a successful `.jumpDynamic` terminator is one spec
    step (`IsJumpStep`) from the frame positioned at the JUMP. -/
private theorem spec_jump_step (i i' : Evm) (pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x56)
    (hTerm : IR.execTerm i (pcv + 1) .jumpDynamic = .ok i') :
    Evm.Frontier.Spec.IsAnyStep { i with pc := pcv } i' := by
  unfold IR.execTerm at hTerm
  simp only [bind, Except.bind] at hTerm
  rcases hch : Gas.charge i.gasLeft Gas.mid with _ | gl
  · rw [hch] at hTerm; simp at hTerm
  rw [hch] at hTerm
  simp only at hTerm
  rcases hp : Stack.pop i.stack with _ | ⟨dest, s⟩
  · rw [hp] at hTerm; simp at hTerm
  rw [hp] at hTerm
  simp only at hTerm
  split at hTerm
  case isTrue hvj =>
    simp only [pure, Except.pure, Except.ok.injEq] at hTerm
    subst hTerm
    obtain ⟨hle, rfl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
    have hStack := (Evm.Frontier.Vm.Spec.Stack.pop_eq_ok_iff _ _ _).mp hp
    refine anyStep_jump _ _ hSize hCode ?_
    exact ⟨dest, s, hStack, hle, hvj, rfl⟩
  case isFalse hvj => simp at hTerm

/-- 0x57 JUMPI: a successful `.jumpiDynamic` terminator (either
    branch) is one spec step (`IsJumpiStep`). -/
private theorem spec_jumpi_step (i i' : Evm) (pcv : Nat)
    (hSize : pcv < i.message.code.size)
    (hCode : i.message.code.get! pcv = 0x57)
    (hTerm : IR.execTerm i (pcv + 1) .jumpiDynamic = .ok i') :
    Evm.Frontier.Spec.IsAnyStep { i with pc := pcv } i' := by
  unfold IR.execTerm at hTerm
  simp only [bind, Except.bind] at hTerm
  rcases hch : Gas.charge i.gasLeft Gas.high with _ | gl
  · rw [hch] at hTerm; simp at hTerm
  rw [hch] at hTerm
  simp only at hTerm
  rcases hp2 : Stack.pop2 i.stack with _ | ⟨dest, cond, s⟩
  · rw [hp2] at hTerm; simp at hTerm
  rw [hp2] at hTerm
  simp only at hTerm
  obtain ⟨hle, hgl⟩ := (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hch
  subst hgl
  have hStack := (Evm.Frontier.Vm.Spec.Stack.pop2_eq_ok_iff _ _ _ _).mp hp2
  by_cases hc : cond = (0 : Evm.U256)
  · rw [ite_eq_left hc] at hTerm
    simp only [pure, Except.pure, Except.ok.injEq] at hTerm
    subst hTerm
    refine anyStep_jumpi _ _ hSize hCode ?_
    exact ⟨dest, cond, s, hStack, hle, .inl ⟨hc, rfl⟩⟩
  · rw [ite_eq_right hc] at hTerm
    split at hTerm
    next hvj =>
      simp only [pure, Except.pure, Except.ok.injEq] at hTerm
      subst hTerm
      refine anyStep_jumpi _ _ hSize hCode ?_
      exact ⟨dest, cond, s, hStack, hle, .inr ⟨hc, hvj, rfl⟩⟩
    next hvj => simp at hTerm

set_option maxHeartbeats 1000000 in
theorem compileLoop_sound_spec (code : Evm.Bytes) (pc : Nat) :
    ∀ (ops : List Op) (gas : Nat) (term : Terminator) (endPc : Nat),
    IR.compileLoop .frontier code pc = .ok (ops, gas, term, endPc) →
    ∀ (i i2 i' : Evm),
      i.message.code = code → i.halted = false →
      IR.execOps i ops = .ok i2 →
      IR.execTerm i2 endPc term = .ok i' →
      ∀ (cause : Evm.Frontier.Spec.HaltCause) (k : Evm),
      Evm.Frontier.Spec.IsFrameRun i' cause k →
      Evm.Frontier.Spec.IsFrameRun
        { i with gasLeft := i.gasLeft + gas, pc := pc } cause k := by
  induction pc using IR.compileLoop.induct (fork := .frontier) (code := code) with
  | case1 x hge =>
    -- pc ≥ code.size : endOfCode
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    rw [IR.compileLoop.eq_def, dite_eq_left hge] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, pure, Except.pure, Except.ok.injEq] at hOps
    subst hOps
    simp only [IR.execTerm, pure, Except.pure, Except.ok.injEq] at hTerm
    subst hTerm
    intro cause k hk
    simp only [Nat.add_zero]
    exact .step _ _ _ _
      (anyStep_endOfCode _ _
        (show x ≥ i.message.code.size by rw [hcc]; exact hge) rfl)
      hk
  | case2 x hlt opc hop =>
    -- 0x00 : STOP
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x00 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, pure, Except.pure, Except.ok.injEq] at hOps
    subst hOps
    simp only [IR.execTerm, pure, Except.pure, Except.ok.injEq] at hTerm
    subst hTerm
    intro cause k hk
    simp only [Nat.add_zero]
    exact .step _ _ _ _
      (anyStep_stop _ _ (show x < i.message.code.size by rw [hcc]; omega)
        (show i.message.code.get! x = 0x00 by
          rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) rfl)
      hk
  | case3 x hlt opc hop =>
    -- 0xf3 : RETURN
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xf3 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, pure, Except.pure, Except.ok.injEq] at hOps
    subst hOps
    obtain ⟨hAny, _hHalted⟩ :=
      spec_ret_step i i' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hTerm
    intro cause k hk
    simp only [Nat.add_zero]
    exact .step _ _ _ _ hAny hk
  | case4 x hlt opc hop ih =>
    -- 0x01 : ADD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x01 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_add_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.add = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case5 x hlt opc hop ih =>
    -- 0x02 : MUL
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x02 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_mul_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.mul = Gas.low from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case6 x hlt opc hop ih =>
    -- 0x03 : SUB
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x03 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_sub_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.sub = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case7 x hlt opc hop ih =>
    -- 0x50 : POP
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x50 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_pop_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.pop = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case8 x hlt opc hop ih =>
    -- 0x51 : MLOAD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x51 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_mload_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.mload = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case9 x hlt opc hop ih =>
    -- 0x52 : MSTORE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x52 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_mstore_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.mstore = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case10 x hlt opc hop ih =>
    -- 0x04 : DIV
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x04 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_div_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.div = Gas.low from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case11 x hlt opc hop ih =>
    -- 0x05 : SDIV
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x05 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_sdiv_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.sdiv = Gas.low from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case12 x hlt opc hop ih =>
    -- 0x06 : MOD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x06 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_mod_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.mod = Gas.low from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case13 x hlt opc hop ih =>
    -- 0x07 : SMOD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x07 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_smod_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.smod = Gas.low from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case14 x hlt opc hop ih =>
    -- 0x08 : ADDMOD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x08 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_addmod_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.addmod = Gas.mid from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case15 x hlt opc hop ih =>
    -- 0x09 : MULMOD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x09 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_mulmod_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.mulmod = Gas.mid from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case16 x hlt opc hop ih =>
    -- 0x0b : SIGNEXTEND
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x0b := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_signextend_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.signextend = Gas.low from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case17 x hlt opc hop ih =>
    -- 0x10 : LT
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x10 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_lt_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.lt = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case18 x hlt opc hop ih =>
    -- 0x11 : GT
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x11 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_gt_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.gt = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case19 x hlt opc hop ih =>
    -- 0x12 : SLT
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x12 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_slt_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.slt = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case20 x hlt opc hop ih =>
    -- 0x13 : SGT
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x13 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_sgt_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.sgt = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case21 x hlt opc hop ih =>
    -- 0x14 : EQ
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x14 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_eq_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.eq = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case22 x hlt opc hop ih =>
    -- 0x15 : ISZERO
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x15 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_iszero_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.iszero = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case23 x hlt opc hop ih =>
    -- 0x16 : AND
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x16 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_and_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.and_ = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case24 x hlt opc hop ih =>
    -- 0x17 : OR
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x17 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_or_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.or_ = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case25 x hlt opc hop ih =>
    -- 0x18 : XOR
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x18 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_xor_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.xor_ = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case26 x hlt opc hop ih =>
    -- 0x19 : NOT
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x19 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_not_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.not_ = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case27 x hlt opc hop ih =>
    -- 0x1a : BYTE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x1a := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_byte_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.byte = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case28 x hlt opc hop ih =>
    -- 0x0a : EXP
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x0a := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_exp_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.exp = Gas.exp from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case29 x hlt opc hop ih =>
    -- 0x30 : ADDRESS
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x30 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_address_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.address = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case30 x hlt opc hop ih =>
    -- 0x32 : ORIGIN
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x32 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_origin_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.origin = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case31 x hlt opc hop ih =>
    -- 0x33 : CALLER
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x33 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_caller_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.caller = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case32 x hlt opc hop ih =>
    -- 0x34 : CALLVALUE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x34 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_callvalue_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.callvalue = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case33 x hlt opc hop ih =>
    -- 0x35 : CALLDATALOAD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x35 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_calldataload_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.calldataload = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case34 x hlt opc hop ih =>
    -- 0x36 : CALLDATASIZE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x36 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_calldatasize_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.calldatasize = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case35 x hlt opc hop ih =>
    -- 0x38 : CODESIZE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x38 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_codesize_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.codesize = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case36 x hlt opc hop ih =>
    -- 0x3a : GASPRICE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x3a := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_gasprice_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.gasprice = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case37 x hlt opc hop ih =>
    -- 0x41 : COINBASE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x41 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_coinbase_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.coinbase = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case38 x hlt opc hop ih =>
    -- 0x42 : TIMESTAMP
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x42 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_timestamp_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.timestamp = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case39 x hlt opc hop ih =>
    -- 0x43 : NUMBER
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x43 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_number_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.number = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case40 x hlt opc hop ih =>
    -- 0x44 : DIFFICULTY
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x44 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_difficulty_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.prevrandao = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case41 x hlt opc hop ih =>
    -- 0x45 : GASLIMIT
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x45 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_gaslimit_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.gaslimit = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case42 x hlt opc hop ih =>
    -- 0x53 : MSTORE8
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x53 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_mstore8_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.mstore8 = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case43 x hlt opc hop ih =>
    -- 0x58 : PC
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x58 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_pc_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier (Op.pc x) = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case44 x hlt opc hop ih =>
    -- 0x59 : MSIZE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x59 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_msize_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.msize = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case45 x hlt opc hop ih =>
    -- 0x5a : GAS
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x5a := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_gas_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier (Op.gas gas') = Gas.base from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case46 x hlt opc hop ih =>
    -- 0x5b : JUMPDEST
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x5b := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_jumpdest_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.jumpdest = Gas.jumpDest from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case47 x hlt opc hop =>
    -- 0x56 : JUMP — dynamic-target terminator; transfers, does not halt
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x56 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, pure, Except.pure, Except.ok.injEq] at hOps
    subst hOps
    intro cause k hk
    simp only [Nat.add_zero]
    exact .step _ _ _ _
      (spec_jump_step i i' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hTerm)
      hk
  | case48 x hlt opc hop =>
    -- 0x57 : JUMPI — transfers or falls through to x + 1
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x57 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, pure, Except.pure, Except.ok.injEq] at hOps
    subst hOps
    intro cause k hk
    simp only [Nat.add_zero]
    exact .step _ _ _ _
      (spec_jumpi_step i i' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hTerm)
      hk
  | case49 x hlt opc hop =>
    -- 0xfe : INVALID — `execTerm .invalid` errors; hypothesis is vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xfe := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case50 x hlt opc hop ih =>
    -- 0x20 : KECCAK256
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x20 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_keccak256_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.keccak256 = Gas.keccak256 from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case51 x hlt opc hop ih =>
    -- 0x37 : CALLDATACOPY
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x37 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_calldatacopy_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.calldatacopy = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case52 x hlt opc hop ih =>
    -- 0x39 : CODECOPY
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x39 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_codecopy_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.codecopy = Gas.veryLow from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case53 x hlt opc hop ih =>
    -- 0x31 : BALANCE (state yield in the Effect track; pure step here)
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x31 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_balance_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.balance = Gas.balance from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case54 x hlt opc hop ih =>
    -- 0x3b : EXTCODESIZE
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x3b := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_extcodesize_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.extcodesize = Gas.extCode from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case55 x hlt opc hop ih =>
    -- 0x3c : EXTCODECOPY
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x3c := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_extcodecopy_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.extcodecopy = Gas.extCode from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case56 x hlt opc hop ih =>
    -- 0x40 : BLOCKHASH
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x40 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_blockhash_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.blockhash = Gas.blockHash from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case57 x hlt opc hop ih =>
    -- 0x54 : SLOAD
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x54 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_sload_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.sload = Gas.sLoad from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case58 x hlt opc hop ih =>
    -- 0x55 : SSTORE (no static pre-charge; cost depends on old value)
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x55 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_sstore_shifted i ia gas' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    rw [show IR.staticGasFor .frontier Op.sstore = 0 from rfl]
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case59 x hlt opc hop =>
    -- 0xf0 : CREATE terminator — a sub-frame yield is not
    -- expressible in the Except-valued track (`execTerm` errors BY
    -- DESIGN), so the `.ok` hypothesis is vacuous. The yielding
    -- track is `IR.executeStep`.
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xf0 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case60 x hlt opc hop =>
    -- 0xf1 : CALL terminator — vacuous, see 0xf0.
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xf1 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case61 x hlt opc hop =>
    -- 0xf2 : CALLCODE terminator — vacuous, see 0xf0.
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xf2 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case62 x hlt opc hop =>
    -- 0xff : SELFDESTRUCT — one halting spec step at the opcode's
    -- own pc.
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xff := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, pure, Except.pure, Except.ok.injEq] at hOps
    subst hOps
    obtain ⟨hAny, _hHalted⟩ :=
      spec_selfdestruct_step i i' x (by rw [hcc]; omega)
        (by rw [hcc]; exact UInt8.toNat_inj.mp (by simpa using hop)) hTerm
    intro cause k hk
    simp only [Nat.add_zero]
    exact .step _ _ _ _ hAny hk
  | case63 x hlt opc hop hgate ih =>
    -- 0x1b SHL gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case64 x hlt opc hop hgate =>
    -- 0x1b SHL gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x1b := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case65 x hlt opc hop hgate ih =>
    -- 0x1c SHR gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case66 x hlt opc hop hgate =>
    -- 0x1c SHR gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x1c := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case67 x hlt opc hop hgate ih =>
    -- 0x1d SAR gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case68 x hlt opc hop hgate =>
    -- 0x1d SAR gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x1d := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case69 x hlt opc hop hgate ih =>
    -- 0x3d RETURNDATASIZE gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case70 x hlt opc hop hgate =>
    -- 0x3d RETURNDATASIZE gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x3d := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case71 x hlt opc hop hgate ih =>
    -- 0x3e RETURNDATACOPY gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case72 x hlt opc hop hgate =>
    -- 0x3e RETURNDATACOPY gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x3e := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case73 x hlt opc hop hgate ih =>
    -- 0x3f EXTCODEHASH gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case74 x hlt opc hop hgate =>
    -- 0x3f EXTCODEHASH gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x3f := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case75 x hlt opc hop hgate ih =>
    -- 0x46 CHAINID gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case76 x hlt opc hop hgate =>
    -- 0x46 CHAINID gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x46 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case77 x hlt opc hop hgate ih =>
    -- 0x47 SELFBALANCE gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case78 x hlt opc hop hgate =>
    -- 0x47 SELFBALANCE gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x47 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case79 x hlt opc hop hgate ih =>
    -- 0x48 BASEFEE gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case80 x hlt opc hop hgate =>
    -- 0x48 BASEFEE gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x48 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case81 x hlt opc hop hgate ih =>
    -- 0x49 BLOBHASH gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case82 x hlt opc hop hgate =>
    -- 0x49 BLOBHASH gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x49 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case83 x hlt opc hop hgate ih =>
    -- 0x4a BLOBBASEFEE gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case84 x hlt opc hop hgate =>
    -- 0x4a BLOBBASEFEE gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x4a := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case85 x hlt opc hop hgate ih =>
    -- 0x5c TLOAD gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case86 x hlt opc hop hgate =>
    -- 0x5c TLOAD gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x5c := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case87 x hlt opc hop hgate ih =>
    -- 0x5d TSTORE gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case88 x hlt opc hop hgate =>
    -- 0x5d TSTORE gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x5d := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case89 x hlt opc hop hgate ih =>
    -- 0x5e MCOPY gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case90 x hlt opc hop hgate =>
    -- 0x5e MCOPY gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x5e := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case91 x hlt opc hop hgate ih =>
    -- 0x5f PUSH0 gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case92 x hlt opc hop hgate =>
    -- 0x5f PUSH0 gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x5f := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case93 x hlt opc hop hgate =>
    -- 0xfd REVERT gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case94 x hlt opc hop hgate =>
    -- 0xfd REVERT gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xfd := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case95 x hlt opc hop hgate =>
    -- 0xf4 DELEGATECALL gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case96 x hlt opc hop hgate =>
    -- 0xf4 DELEGATECALL gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xf4 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case97 x hlt opc hop hgate =>
    -- 0xfa STATICCALL gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case98 x hlt opc hop hgate =>
    -- 0xfa STATICCALL gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xfa := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case99 x hlt opc hop hgate =>
    -- 0xf5 CREATE2 gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case100 x hlt opc hop hgate =>
    -- 0xf5 CREATE2 gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0xf5 := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case101 x hlt opc hop hgate ih =>
    -- 0x1e CLZ gate-true : impossible at .frontier
    exact absurd hgate (by decide)
  | case102 x hlt opc hop hgate =>
    -- 0x1e CLZ gated off at .frontier : compiles to .invalid, execTerm errors, vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hop : (code.get! x).toNat = 0x1e := hop
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [hop] at hC
    rw [ite_eq_right hgate] at hC
    simp only [Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp [IR.execTerm] at hTerm
  | case103 x hlt opc h0 h243 h1 h2 h3 h80 h81 h82 _h4 _h5 _h6 _h7
      _h8 _h9 _hb _q10 _q11 _q12 _q13 _q14 _q15 _q16 _q17 _q18 _q19
      _q1a _ha _a30 _a32 _a33 _a34 _a35 _a36 _a38 _a3a _a41 _a42 _a43
      _a44 _a45 _a53 _a58 _a59 _a5a _a5b _a56 _a57 _afe _a20 _a37 _a39
      _a31 _a3b _a3c _a40 _a54 _a55 _af0 _af1 _af2 _aff
      _a1b _a1c _a1d _a3d _a3e _a3f _a46 _a47 _a48 _a49 _a4a _a5c
      _a5d _a5e _a5f _afd _af4 _afa _af5 _a1e
      hrange imm ih =>
    -- 0x60–0x7f : PUSH1..PUSH32
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hrange : 0x60 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0x7f :=
      hrange
    rw [compileLoop_push_eq .frontier code x ((code.get! x).toNat) hlt rfl
          hrange.1 hrange.2] at hC
    simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_push_shifted i ia gas' x ((code.get! x).toNat)
        (by rw [hcc]; omega) (by rw [hcc]) hrange.1 hrange.2
        (by rw [hcc]; exact hop1)
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case104 x hlt opc _h0 _h243 _h1 _h2 _h3 _h80 _h81 _h82 _h4 _h5 _h6 _h7
      _h8 _h9 _hb _q10 _q11 _q12 _q13 _q14 _q15 _q16 _q17 _q18 _q19
      _q1a _ha _a30 _a32 _a33 _a34 _a35 _a36 _a38 _a3a _a41 _a42 _a43
      _a44 _a45 _a53 _a58 _a59 _a5a _a5b _a56 _a57 _afe _a20 _a37 _a39
      _a31 _a3b _a3c _a40 _a54 _a55 _af0 _af1 _af2 _aff
      _a1b _a1c _a1d _a3d _a3e _a3f _a46 _a47 _a48 _a49 _a4a _a5c
      _a5d _a5e _a5f _afd _af4 _afa _af5 _a1e
      _hnp hrange ih =>
    -- 0x80–0x8f : DUP1..DUP16
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hrange : 0x80 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0x8f :=
      hrange
    rw [compileLoop_dup_eq .frontier code x ((code.get! x).toNat) hlt rfl
          hrange.1 hrange.2] at hC
    simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_dup_shifted i ia gas' x ((code.get! x).toNat)
        (by rw [hcc]; omega) (by rw [hcc]) hrange.1 hrange.2 hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case105 x hlt opc _h0 _h243 _h1 _h2 _h3 _h80 _h81 _h82 _h4 _h5 _h6 _h7
      _h8 _h9 _hb _q10 _q11 _q12 _q13 _q14 _q15 _q16 _q17 _q18 _q19
      _q1a _ha _a30 _a32 _a33 _a34 _a35 _a36 _a38 _a3a _a41 _a42 _a43
      _a44 _a45 _a53 _a58 _a59 _a5a _a5b _a56 _a57 _afe _a20 _a37 _a39
      _a31 _a3b _a3c _a40 _a54 _a55 _af0 _af1 _af2 _aff
      _a1b _a1c _a1d _a3d _a3e _a3f _a46 _a47 _a48 _a49 _a4a _a5c
      _a5d _a5e _a5f _afd _af4 _afa _af5 _a1e
      _hnp _hnd hrange ih =>
    -- 0x90–0x9f : SWAP1..SWAP16
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hrange : 0x90 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0x9f :=
      hrange
    rw [compileLoop_swap_eq .frontier code x ((code.get! x).toNat) hlt rfl
          hrange.1 hrange.2] at hC
    simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_swap_shifted i ia gas' x ((code.get! x).toNat)
        (by rw [hcc]; omega) (by rw [hcc]) hrange.1 hrange.2 hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case106 x hlt opc _h0 _h243 _h1 _h2 _h3 _h80 _h81 _h82 _h4 _h5 _h6 _h7
      _h8 _h9 _hb _q10 _q11 _q12 _q13 _q14 _q15 _q16 _q17 _q18 _q19
      _q1a _ha _a30 _a32 _a33 _a34 _a35 _a36 _a38 _a3a _a41 _a42 _a43
      _a44 _a45 _a53 _a58 _a59 _a5a _a5b _a56 _a57 _afe _a20 _a37 _a39
      _a31 _a3b _a3c _a40 _a54 _a55 _af0 _af1 _af2 _aff
      _a1b _a1c _a1d _a3d _a3e _a3f _a46 _a47 _a48 _a49 _a4a _a5c
      _a5d _a5e _a5f _afd _af4 _afa _af5 _a1e
      _hnp _hnd _hns hrange ih =>
    -- 0xa0–0xa4 : LOG0..LOG4
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have hrange : 0xa0 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0xa4 :=
      hrange
    rw [compileLoop_log_eq .frontier code x ((code.get! x).toNat) hlt rfl
          hrange.1 hrange.2] at hC
    simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hC
    obtain ⟨⟨ops', gas', term', endPc'⟩, hrec, hC⟩ := hC
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hC
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
    simp only [IR.execOps, bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hOps
    obtain ⟨ia, hop1, hOps'⟩ := hOps
    obtain ⟨hAny, hmsg, hhalt⟩ :=
      spec_log_shifted i ia gas' x ((code.get! x).toNat)
        (by rw [hcc]; omega) (by rw [hcc]) hrange.1 hrange.2 hop1
    have hrun :=
      ih _ _ _ _ hrec ia i2 i'
        (by rw [hmsg, hcc]) (by rw [hhalt, hHalt]) hOps' hTerm
    intro cause k hk
    exact .step _ _ _ _ hAny (hrun cause k hk)
  | case107 x hlt opc h0 h243 h1 h2 h3 h80 h81 h82 h4 h5 h6 h7
      h8 h9 hb q10 q11 q12 q13 q14 q15 q16 q17 q18 q19 q1a ha
      a30 a32 a33 a34 a35 a36 a38 a3a a41 a42 a43 a44 a45 a53
      a58 a59 a5a a5b a56 a57 afe a20 a37 a39
      a31 a3b a3c a40 a54 a55 af0 af1 af2 aff
      a1b a1c a1d a3d a3e a3f a46 a47 a48 a49 a4a a5c a5d a5e a5f
      afd af4 afa af5 a1e hnp hnd hns hnl =>
    -- unknown opcode : compileLoop errors, hypothesis is vacuous
    intro ops gas term endPc hC i i2 i' hcc hHalt hOps hTerm
    have h0' : (code.get! x).toNat = 0x00 → False := h0
    have h243' : (code.get! x).toNat = 0xf3 → False := h243
    have h1' : (code.get! x).toNat = 0x01 → False := h1
    have h2' : (code.get! x).toNat = 0x02 → False := h2
    have h3' : (code.get! x).toNat = 0x03 → False := h3
    have h80' : (code.get! x).toNat = 0x50 → False := h80
    have h81' : (code.get! x).toNat = 0x51 → False := h81
    have h82' : (code.get! x).toNat = 0x52 → False := h82
    have h4' : (code.get! x).toNat = 0x04 → False := h4
    have h5' : (code.get! x).toNat = 0x05 → False := h5
    have h6' : (code.get! x).toNat = 0x06 → False := h6
    have h7' : (code.get! x).toNat = 0x07 → False := h7
    have h8' : (code.get! x).toNat = 0x08 → False := h8
    have h9' : (code.get! x).toNat = 0x09 → False := h9
    have hb' : (code.get! x).toNat = 0x0b → False := hb
    have q10' : (code.get! x).toNat = 0x10 → False := q10
    have q11' : (code.get! x).toNat = 0x11 → False := q11
    have q12' : (code.get! x).toNat = 0x12 → False := q12
    have q13' : (code.get! x).toNat = 0x13 → False := q13
    have q14' : (code.get! x).toNat = 0x14 → False := q14
    have q15' : (code.get! x).toNat = 0x15 → False := q15
    have q16' : (code.get! x).toNat = 0x16 → False := q16
    have q17' : (code.get! x).toNat = 0x17 → False := q17
    have q18' : (code.get! x).toNat = 0x18 → False := q18
    have q19' : (code.get! x).toNat = 0x19 → False := q19
    have q1a' : (code.get! x).toNat = 0x1a → False := q1a
    have ha' : (code.get! x).toNat = 0x0a → False := ha
    have a30' : (code.get! x).toNat = 0x30 → False := a30
    have a32' : (code.get! x).toNat = 0x32 → False := a32
    have a33' : (code.get! x).toNat = 0x33 → False := a33
    have a34' : (code.get! x).toNat = 0x34 → False := a34
    have a35' : (code.get! x).toNat = 0x35 → False := a35
    have a36' : (code.get! x).toNat = 0x36 → False := a36
    have a38' : (code.get! x).toNat = 0x38 → False := a38
    have a3a' : (code.get! x).toNat = 0x3a → False := a3a
    have a41' : (code.get! x).toNat = 0x41 → False := a41
    have a42' : (code.get! x).toNat = 0x42 → False := a42
    have a43' : (code.get! x).toNat = 0x43 → False := a43
    have a44' : (code.get! x).toNat = 0x44 → False := a44
    have a45' : (code.get! x).toNat = 0x45 → False := a45
    have a53' : (code.get! x).toNat = 0x53 → False := a53
    have a58' : (code.get! x).toNat = 0x58 → False := a58
    have a59' : (code.get! x).toNat = 0x59 → False := a59
    have a5a' : (code.get! x).toNat = 0x5a → False := a5a
    have a5b' : (code.get! x).toNat = 0x5b → False := a5b
    have a56' : (code.get! x).toNat = 0x56 → False := a56
    have a57' : (code.get! x).toNat = 0x57 → False := a57
    have afe' : (code.get! x).toNat = 0xfe → False := afe
    have a20' : (code.get! x).toNat = 0x20 → False := a20
    have a37' : (code.get! x).toNat = 0x37 → False := a37
    have a39' : (code.get! x).toNat = 0x39 → False := a39
    have a31' : (code.get! x).toNat = 0x31 → False := a31
    have a3b' : (code.get! x).toNat = 0x3b → False := a3b
    have a3c' : (code.get! x).toNat = 0x3c → False := a3c
    have a40' : (code.get! x).toNat = 0x40 → False := a40
    have a54' : (code.get! x).toNat = 0x54 → False := a54
    have a55' : (code.get! x).toNat = 0x55 → False := a55
    have af0' : (code.get! x).toNat = 0xf0 → False := af0
    have af1' : (code.get! x).toNat = 0xf1 → False := af1
    have af2' : (code.get! x).toNat = 0xf2 → False := af2
    have aff' : (code.get! x).toNat = 0xff → False := aff
    have a1b' : (code.get! x).toNat = 0x1b → False := a1b
    have a1c' : (code.get! x).toNat = 0x1c → False := a1c
    have a1d' : (code.get! x).toNat = 0x1d → False := a1d
    have a3d' : (code.get! x).toNat = 0x3d → False := a3d
    have a3e' : (code.get! x).toNat = 0x3e → False := a3e
    have a3f' : (code.get! x).toNat = 0x3f → False := a3f
    have a46' : (code.get! x).toNat = 0x46 → False := a46
    have a47' : (code.get! x).toNat = 0x47 → False := a47
    have a48' : (code.get! x).toNat = 0x48 → False := a48
    have a49' : (code.get! x).toNat = 0x49 → False := a49
    have a4a' : (code.get! x).toNat = 0x4a → False := a4a
    have a5c' : (code.get! x).toNat = 0x5c → False := a5c
    have a5d' : (code.get! x).toNat = 0x5d → False := a5d
    have a5e' : (code.get! x).toNat = 0x5e → False := a5e
    have a5f' : (code.get! x).toNat = 0x5f → False := a5f
    have afd' : (code.get! x).toNat = 0xfd → False := afd
    have af4' : (code.get! x).toNat = 0xf4 → False := af4
    have afa' : (code.get! x).toNat = 0xfa → False := afa
    have af5' : (code.get! x).toNat = 0xf5 → False := af5
    have a1e' : (code.get! x).toNat = 0x1e → False := a1e
    have hnp' : ¬ (0x60 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0x7f) :=
      hnp
    have hnd' : ¬ (0x80 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0x8f) :=
      hnd
    have hns' : ¬ (0x90 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0x9f) :=
      hns
    have hnl' : ¬ (0xa0 ≤ (code.get! x).toNat ∧ (code.get! x).toNat ≤ 0xa4) :=
      hnl
    rw [IR.compileLoop.eq_def, dite_eq_right hlt] at hC
    simp only [] at hC
    split at hC
    · exact absurd ‹_› hnp'
    all_goals first
      | exact absurd ‹_› hnd'
      | exact absurd ‹_› hns'
      | exact absurd ‹_› hnl'
      -- fall-through arm: an all-forks-undefined byte compiles to
      -- `.invalid`, whose `execTerm` errors — hypothesis is vacuous
      | (simp at hC
         obtain ⟨rfl, rfl, rfl, rfl⟩ := hC
         simp [IR.execTerm] at hTerm)


/-- Halt-shaped corollary of `compileLoop_sound_spec` (the Phase 3
    statement): a halted IR result closes the run with `.done`.
    `IsFrameRun.done` accepts any cause, so `.stop` is chosen. -/
theorem compileLoop_sound_spec_halt (code : Evm.Bytes) (pc : Nat)
    (ops : List Op) (gas : Nat) (term : Terminator) (endPc : Nat)
    (hC : IR.compileLoop .frontier code pc = .ok (ops, gas, term, endPc))
    (i i2 i' : Evm)
    (hcc : i.message.code = code) (hHalt : i.halted = false)
    (hOps : IR.execOps i ops = .ok i2)
    (hTerm : IR.execTerm i2 endPc term = .ok i')
    (hHalted : i'.halted = true) :
    ∃ cause, Evm.Frontier.Spec.IsFrameRun
      { i with gasLeft := i.gasLeft + gas, pc := pc } cause i' :=
  ⟨.stop, compileLoop_sound_spec code pc ops gas term endPc hC i i2 i'
      hcc hHalt hOps hTerm .stop i' (.done _ _ hHalted)⟩

/-- Chunk-level soundness vs the spec (no-jump slice).

    If compiling `code` yields a chunk and `IR.execute` runs it to a
    halted frame `evm'`, then the spec's frame-run relation accepts
    the transition: `IsFrameRun evm cause evm'` for some halt cause.
    Together with `compile_sound_vs_effect` this puts the IR pipeline
    between the executable and the spec. -/
theorem compile_sound_vs_spec
    (code : Evm.Bytes) (chunk : Chunk) (evm evm' : Evm)
    (hcc : evm.message.code = code)
    (hpc : evm.pc = 0)
    (hHalt : evm.halted = false)
    (hcompile : IR.compile .frontier code = .ok chunk)
    (hexec : IR.execute chunk evm = .ok evm')
    (hHalted : evm'.halted = true) :
    ∃ cause, Evm.Frontier.Spec.IsFrameRun evm cause evm' := by
  unfold IR.compile at hcompile
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hcompile
  obtain ⟨⟨ops, gas, term, endPc⟩, hloop, hchunk⟩ := hcompile
  simp only [pure, Except.pure, Except.ok.injEq] at hchunk
  subst hchunk
  unfold IR.execute at hexec
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hexec
  obtain ⟨g0, hcharge, i2, hOps, hTerm⟩ := hexec
  obtain ⟨hle, rfl⟩ :=
    (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hcharge
  obtain ⟨cause, hrun⟩ :=
    compileLoop_sound_spec_halt code 0 ops gas term endPc hloop
      { evm with gasLeft := evm.gasLeft - gas } i2 evm' hcc hHalt hOps hTerm
      hHalted
  refine ⟨cause, ?_⟩
  have hEq : evm = { evm with gasLeft := evm.gasLeft - gas + gas, pc := 0 } := by
    rw [Nat.sub_add_cancel hle, ← hpc]
  rw [hEq]
  exact hrun

/-! ## (3) Program-level soundness (Phase 4)

    Lift the chunk-level theorems to `IR.executeProgram`, the
    multi-chunk trampoline. The trampoline transfers control between
    chunks on JUMP/JUMPI; each round is one chunk execution, so the
    proof is a fuel induction composing the generalized chunk-level
    conclusions across rounds.

    `ProgramWF` captures exactly what the trampoline needs from the
    compiler: every chunk reachable by `Program.lookup` is the result
    of `compileLoop` at its entry pc. `compileProgram_wf` shows
    `IR.compileProgram` establishes it. -/

/-- `execOp` never touches the frame's message or halt flag: every
    arm is a record update over stack/gas/memory only. -/
private theorem execOp_frame (evm evm' : Evm) (op : Op)
    (h : IR.execOp evm op = .ok evm') :
    evm'.message = evm.message ∧ evm'.halted = evm.halted := by
  cases op <;> simp only [IR.execOp] at h <;>
    (try simp only [bind, Except.bind] at h) <;>
    (repeat' split at h) <;>
    (try simp only [pure, Except.pure] at h) <;>
    first
      | (injection h with h; subst h; exact ⟨rfl, rfl⟩)
      | injection h

private theorem execOps_frame (evm evm' : Evm) (ops : List Op)
    (h : IR.execOps evm ops = .ok evm') :
    evm'.message = evm.message ∧ evm'.halted = evm.halted := by
  induction ops generalizing evm with
  | nil =>
    simp only [IR.execOps, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨rfl, rfl⟩
  | cons op rest ih =>
    simp only [IR.execOps, bind,
      Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
    obtain ⟨mid, hop, hrest⟩ := h
    obtain ⟨hm1, hh1⟩ := execOp_frame evm mid op hop
    obtain ⟨hm2, hh2⟩ := ih mid hrest
    exact ⟨hm2.trans hm1, hh2.trans hh1⟩

/-- `execTerm` never changes the message (it only sets pc, gas,
    stack, memory, output, and the halt flag). -/
private theorem execTerm_message (evm evm' : Evm) (endPc : Nat)
    (term : Terminator)
    (h : IR.execTerm evm endPc term = .ok evm') :
    evm'.message = evm.message := by
  cases term
  case selfdestruct =>
    -- `Vm.selfdestruct` only touches env, halted (and reads stack);
    -- the generic injection chain below can't see through it.
    simp only [IR.execTerm] at h
    unfold Evm.Frontier.Vm.selfdestruct at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    by_cases hSt : evm.message.isStatic = true
    · rw [ite_eq_left hSt] at h; simp at h
    rw [ite_eq_right hSt] at h
    rcases hp : Stack.pop evm.stack with _ | ⟨bW, s⟩
    · rw [hp] at h; simp at h
    rw [hp] at h
    simp only [Except.ok.injEq] at h
    subst h
    rfl
  all_goals
    simp only [IR.execTerm] at h
    try simp only [bind, Except.bind] at h
    (repeat' split at h) <;>
      (try simp only [pure, Except.pure] at h) <;>
      first
        | (injection h with h; subst h; rfl)
        | injection h

private theorem execute_message (ch : Chunk) (evm evm' : Evm)
    (h : IR.execute ch evm = .ok evm') :
    evm'.message = evm.message := by
  unfold IR.execute at h
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
  obtain ⟨g0, _hcharge, i2, hOps, hTerm⟩ := h
  rw [execTerm_message i2 evm' ch.endPc ch.term hTerm,
      (execOps_frame _ i2 ch.ops hOps).1]

/-- Program well-formedness: every chunk reachable through
    `Program.lookup` is the faithful `compileLoop` output at its
    entry pc. This is the only property the trampoline soundness
    proofs need from the compiler. -/
def ProgramWF (fork : Evm.Fork) (code : Evm.Bytes) (prog : Program) : Prop :=
  ∀ pc ch, prog.lookup pc = some ch →
    IR.compileLoop fork code pc = .ok (ch.ops, ch.staticGas, ch.term, ch.endPc)

private theorem mapM_mem {α β : Type} (f : α → Except CompileError β)
    (l : List α) (l' : List β) (h : l.mapM f = .ok l') :
    ∀ b ∈ l', ∃ a, a ∈ l ∧ f a = .ok b := by
  induction l generalizing l' with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; intro b hb; cases hb
  | cons a rest ih =>
    simp only [List.mapM_cons, bind,
      Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
    obtain ⟨b0, hb0, h⟩ := h
    obtain ⟨rest', hrest', h⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hmem
    · exact ⟨a, .head _, hb0⟩
    · obtain ⟨a', ha', hfa'⟩ := ih rest' hrest' b hmem
      exact ⟨a', .tail _ ha', hfa'⟩

/-- `compileProgram` establishes `ProgramWF`: every chunk in the
    table came from `compileChunkAt` (i.e. `compileLoop`) at its
    entry pc. -/
theorem compileProgram_wf (fork : Evm.Fork) (code : Evm.Bytes) (prog : Program)
    (h : IR.compileProgram fork code = .ok prog) : ProgramWF fork code prog := by
  unfold IR.compileProgram at h
  simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at h
  obtain ⟨chunks, hmap, hprog⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at hprog
  subst hprog
  intro pc ch hlook
  unfold IR.Program.lookup at hlook
  split at hlook
  case h_1 e heq =>
    simp only [Option.some.injEq] at hlook
    subst hlook
    obtain ⟨e1, e2⟩ := e
    have hpc : pc = e1 := by
      have := List.find?_some heq
      exact (of_decide_eq_true this).symm
    subst hpc
    have hmem := List.mem_of_find?_eq_some heq
    obtain ⟨en, _hen, hfe⟩ := mapM_mem _ _ _ hmap (pc, e2) hmem
    simp only [Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hfe
    obtain ⟨ch0, hch0, hfe⟩ := hfe
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hfe
    obtain ⟨rfl, rfl⟩ := hfe
    unfold IR.compileChunkAt at hch0
    simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hch0
    obtain ⟨⟨ops, gas, term, endPc⟩, hloop, hret⟩ := hch0
    simp only [pure, Except.pure, Except.ok.injEq] at hret
    subst hret
    exact hloop
  case h_2 => cases hlook

/-- Trampoline soundness vs the Effect interpreter: a fueled
    `executeProgram` run over a well-formed program is matched by
    `Effect.runFrameR` with some step fuel. Fuel induction; each round
    composes the generalized chunk-level conclusion
    (`compileLoop_sound`) with the IH. -/
theorem executeProgram_sound_vs_effect (fuel : Nat) (code : Evm.Bytes)
    (prog : Program) (hwf : ProgramWF .frontier code prog) :
    ∀ (evm evm' : Evm), evm.message.code = code → evm.halted = false →
      IR.executeProgram fuel prog evm = .ok evm' →
      ∃ n, Effect.runFrameR n evm = .halt evm' evm'.output := by
  induction fuel with
  | zero => intro evm evm' _ _ hrun; simp [IR.executeProgram] at hrun
  | succ fuel ih =>
    intro evm evm' hcc hHalt hrun
    unfold IR.executeProgram at hrun
    rcases hlook : prog.lookup evm.pc with _ | ch
    · rw [hlook] at hrun; simp at hrun
    simp only [hlook] at hrun
    rcases hexec : IR.execute ch evm with e | evmMid
    · simp only [hexec] at hrun; cases hrun
    simp only [hexec] at hrun
    have hloop := hwf evm.pc ch hlook
    have hmsg := execute_message ch evm evmMid hexec
    unfold IR.execute at hexec
    simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hexec
    obtain ⟨g0, hcharge, i2, hOps, hTerm⟩ := hexec
    obtain ⟨hle, rfl⟩ :=
      (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hcharge
    obtain ⟨n, hrunF⟩ := compileLoop_sound code evm.pc ch.ops
      ch.staticGas ch.term ch.endPc hloop
      { evm with gasLeft := evm.gasLeft - ch.staticGas } i2 evmMid
      hcc hHalt hOps hTerm
    have hEq : { evm with
        gasLeft := evm.gasLeft - ch.staticGas + ch.staticGas,
        pc := evm.pc } = evm := by
      rw [Nat.sub_add_cancel hle]
    rw [hEq] at hrunF
    by_cases hH : evmMid.halted
    · rw [ite_eq_left hH] at hrun
      simp only [Except.ok.injEq] at hrun
      subst hrun
      refine ⟨n + (0 + 1), ?_⟩
      rw [hrunF 0, runFrameR_succ, step1_halted evmMid hH]
    · rw [ite_eq_right hH] at hrun
      obtain ⟨m, hm⟩ := ih evmMid evm'
        (by rw [hmsg, hcc]) (by simpa using hH) hrun
      cases m with
      | zero => simp [Effect.runFrameR] at hm
      | succ m' =>
        refine ⟨n + (m' + 1), ?_⟩
        rw [hrunF m']
        exact hm

/-- Trampoline soundness vs the spec: a fueled `executeProgram` run
    over a well-formed program is a spec frame run for some halt
    cause. Same fuel induction, composing
    `compileLoop_sound_spec` round by round. -/
theorem executeProgram_sound_vs_spec (fuel : Nat) (code : Evm.Bytes)
    (prog : Program) (hwf : ProgramWF .frontier code prog) :
    ∀ (evm evm' : Evm), evm.message.code = code → evm.halted = false →
      IR.executeProgram fuel prog evm = .ok evm' →
      ∃ cause, Evm.Frontier.Spec.IsFrameRun evm cause evm' := by
  induction fuel with
  | zero => intro evm evm' _ _ hrun; simp [IR.executeProgram] at hrun
  | succ fuel ih =>
    intro evm evm' hcc hHalt hrun
    unfold IR.executeProgram at hrun
    rcases hlook : prog.lookup evm.pc with _ | ch
    · rw [hlook] at hrun; simp at hrun
    simp only [hlook] at hrun
    rcases hexec : IR.execute ch evm with e | evmMid
    · simp only [hexec] at hrun; cases hrun
    simp only [hexec] at hrun
    have hloop := hwf evm.pc ch hlook
    have hmsg := execute_message ch evm evmMid hexec
    unfold IR.execute at hexec
    simp only [bind, Evm.Frontier.Vm.Spec.Except.bind_eq_ok] at hexec
    obtain ⟨g0, hcharge, i2, hOps, hTerm⟩ := hexec
    obtain ⟨hle, rfl⟩ :=
      (Evm.Frontier.Vm.Spec.Gas.charge_eq_ok_iff _ _ _).mp hcharge
    have hrunF := compileLoop_sound_spec code evm.pc ch.ops
      ch.staticGas ch.term ch.endPc hloop
      { evm with gasLeft := evm.gasLeft - ch.staticGas } i2 evmMid
      hcc hHalt hOps hTerm
    have hEq : { evm with
        gasLeft := evm.gasLeft - ch.staticGas + ch.staticGas,
        pc := evm.pc } = evm := by
      rw [Nat.sub_add_cancel hle]
    rw [hEq] at hrunF
    by_cases hH : evmMid.halted
    · rw [ite_eq_left hH] at hrun
      simp only [Except.ok.injEq] at hrun
      subst hrun
      exact ⟨.stop, hrunF .stop evmMid (.done _ _ hH)⟩
    · rw [ite_eq_right hH] at hrun
      obtain ⟨cause, hk⟩ := ih evmMid evm'
        (by rw [hmsg, hcc]) (by simpa using hH) hrun
      exact ⟨cause, hrunF cause evm' hk⟩

/-- Top-level Phase 4 theorem (effect side): compile bytecode with
    `compileProgram`, run the trampoline, and `Effect.runFrameR`
    agrees on the final frame and output. -/
theorem compileProgram_sound_vs_effect (fuel : Nat) (code : Evm.Bytes)
    (prog : Program) (evm evm' : Evm)
    (hcompile : IR.compileProgram .frontier code = .ok prog)
    (hcc : evm.message.code = code) (hHalt : evm.halted = false)
    (hrun : IR.executeProgram fuel prog evm = .ok evm') :
    ∃ n, Effect.runFrameR n evm = .halt evm' evm'.output :=
  executeProgram_sound_vs_effect fuel code prog
    (compileProgram_wf .frontier code prog hcompile) evm evm' hcc hHalt hrun

/-- Top-level Phase 4 theorem (spec side): compile bytecode with
    `compileProgram`, run the trampoline, and the spec's frame-run
    relation accepts the transition. -/
theorem compileProgram_sound_vs_spec (fuel : Nat) (code : Evm.Bytes)
    (prog : Program) (evm evm' : Evm)
    (hcompile : IR.compileProgram .frontier code = .ok prog)
    (hcc : evm.message.code = code) (hHalt : evm.halted = false)
    (hrun : IR.executeProgram fuel prog evm = .ok evm') :
    ∃ cause, Evm.Frontier.Spec.IsFrameRun evm cause evm' :=
  executeProgram_sound_vs_spec fuel code prog
    (compileProgram_wf .frontier code prog hcompile) evm evm' hcc hHalt hrun

end Evm.IR.Soundness
