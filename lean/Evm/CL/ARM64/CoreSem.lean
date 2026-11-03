/-
  Evm.CL.ARM64.CoreSem — the u256 limb cores of the region flush
  (`ARM64.JIT.addCoreT`, `subCoreT`, `bitCoreT`, `notCoreA`, `isZeroCoreA`,
  `eqCoreT`, `cmpCoreT`) run under `AsmRun` to the 256-bit operation on the
  four limbs: `ofLimbs x6 x7 x8 x9 := x9 ++ x8 ++ x7 ++ x6`.

  Each core is a straight line of data instructions; the carry chain is the
  65-bit `addc`/`subc` of `AsmRun`, `adds`/`subs` set the first carry through
  `AsmSem`'s `addFlags`/`subFlags`. The joint is `bv_decide` on the resulting
  256-bit identity — a 256-bit adder, subtractor, comparator built from four
  64-bit stages, which is exactly what the chained instructions are.
-/

import Evm.CL.AsmRunMem
import Evm.CL.ARM64.JIT

namespace Evm.CL.ARM64.CoreSem

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun Evm.CL.ARM64.JIT

/-- The left operand (x6-x9) and the right quad (ARM64: x10-x13) in a state. -/
def lhs (s : RS) : Evm.U256 := ofLimbs (s.regs .x6) (s.regs .x7) (s.regs .x8) (s.regs .x9)
def rhs (rq : Reg × Reg × Reg × Reg) (s : RS) : Evm.U256 :=
  ofLimbs (s.regs rq.1) (s.regs rq.2.1) (s.regs rq.2.2.1) (s.regs rq.2.2.2)

/-! ## The flags of `adds`/`subs`, in bitvector form (for `bv_decide`) -/

theorem addFlags_c (a b : BitVec 64) :
    (addFlags a b).c = (a.zeroExtend 65 + b.zeroExtend 65).msb := by
  simp only [addFlags, BitVec.msb_eq_decide, BitVec.toNat_add, BitVec.zeroExtend, BitVec.toNat_setWidth]
  have ha := a.isLt; have hb := b.isLt
  rw [Nat.mod_eq_of_lt (by omega : a.toNat < 2 ^ 65), Nat.mod_eq_of_lt (by omega : b.toNat < 2 ^ 65),
      Nat.mod_eq_of_lt (by omega : a.toNat + b.toNat < 2 ^ 65)]

theorem subFlags_c (a b : BitVec 64) :
    (subFlags a b).c = decide (b ≤ a) := rfl

/-! ## The ARM64 right quad -/

def armRq : Reg × Reg × Reg × Reg := (.x10, .x11, .x12, .x13)

/-- `addCoreT armRq`: x6-x9 become the limbs of `lhs + rhs`; x10-x13 and
    everything but the flags survive. -/
theorem addCore_run (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (addCoreT armRq ++ rest) s = run H rest s' ∧
      lhs s' = lhs s + rhs armRq s ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  simp only [addCoreT, armRq, List.cons_append, List.nil_append, run_cons_data, ctrl_adds, ctrl_adcs,
             ctrl_adc, step_adds, step_adcs, step_adc]
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · simp only [lhs, rhs, ofLimbs, AsmRun.set_regs, AsmRun.withFlags_regs, AsmRun.withFlags_flags,
               reduceCtorEq, ite_true, ite_false, addFlags_c, addc, bit]
    bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

/-- The u256 value a `cset`-style core leaves: the predicate in limb 0, zeros above. -/
theorem ofLimbs_b2v (b : Bool) : ofLimbs (b2v b) 0 0 0 = (if b then 1 else 0 : Evm.U256) := by
  cases b <;> simp only [ofLimbs, b2v, ite_true] <;> dsimp only [Evm.U256] <;> bv_decide

/-- The simp set that executes a core and exposes the limb arithmetic. -/
syntax "core_run" : tactic
macro_rules
  | `(tactic| core_run) =>
    `(tactic| (simp only [addCoreT, subCoreT, bitCoreT, notCoreA, isZeroCoreA, eqCoreT, cmpCoreT, zeroHiA, armRq,
                 List.cons_append, List.nil_append, List.append_assoc, run_cons_data,
                 ctrl_adds, ctrl_adcs, ctrl_adc, ctrl_subsReg, ctrl_sbcs, ctrl_sbc, ctrl_subsZr, ctrl_sbcsZr,
                 ctrl_cset, ctrl_and3, ctrl_orr3, ctrl_eor3, ctrl_mvn, ctrl_movImm, ctrl_cmpImm,
                 step_adds, step_adcs, step_adc, step_subsReg, step_sbcs, step_sbc, step_subsZr, step_sbcsZr,
                 step_cset, step_and3, step_orr3, step_eor3, step_mvn, step_movImm, step_cmpImm]))

syntax "core_limbs" : tactic
macro_rules
  | `(tactic| core_limbs) =>
    `(tactic| (simp only [lhs, rhs, ofLimbs, AsmRun.set_regs, AsmRun.withFlags_regs, AsmRun.withFlags_flags,
                 AsmRun.set_flags, reduceCtorEq, ite_true, ite_false, addFlags_c, subFlags, addc, subc, bit,
                 bcHolds, scHolds, b2v, BitVec.ofNat_eq_ofNat];
               -- `bv_decide` abstracts `-`/`|||` at the ABBREVIATION `Evm.U256`
               -- (it accepts `+`); unfolding the abbreviation makes them bitvector ops
               dsimp only [Evm.U256]))

theorem subCore_run (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (subCoreT armRq ++ rest) s = run H rest s' ∧
      lhs s' = lhs s - rhs armRq s ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_run
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

theorem andCore_run (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (bitCoreT armRq .and3 ++ rest) s = run H rest s' ∧
      lhs s' = lhs s &&& rhs armRq s ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_run
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

theorem orCore_run (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (bitCoreT armRq .orr3 ++ rest) s = run H rest s' ∧
      lhs s' = lhs s ||| rhs armRq s ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_run
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

theorem xorCore_run (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (bitCoreT armRq .eor3 ++ rest) s = run H rest s' ∧
      lhs s' = lhs s ^^^ rhs armRq s ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_run
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

theorem notCore_run (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (notCoreA ++ rest) s = run H rest s' ∧
      lhs s' = ~~~ lhs s ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_run
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

/-- `isZero`: x14, x15 are scratch. -/
theorem isZeroCore_run (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (isZeroCoreA ++ rest) s = run H rest s' ∧
      lhs s' = (if lhs s = 0 then 1 else 0) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → s'.regs r = s.regs r) := by
  core_run
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9 h14 h15; simp [RS.set, h6, h7, h8, h9, h14, h15]

/-- `eq`: x14, x15 are scratch. -/
theorem eqCore_run (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (eqCoreT armRq ++ rest) s = run H rest s' ∧
      lhs s' = (if lhs s = rhs armRq s then 1 else 0) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → s'.regs r = s.regs r) := by
  core_run
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9 h14 h15; simp [RS.set, h6, h7, h8, h9, h14, h15]

theorem ltCore_run (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (cmpCoreT armRq false .lo ++ rest) s = run H rest s' ∧
      lhs s' = (if lhs s < rhs armRq s then 1 else 0) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_run
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

theorem gtCore_run (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (cmpCoreT armRq true .lo ++ rest) s = run H rest s' ∧
      lhs s' = (if rhs armRq s < lhs s then 1 else 0) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_run
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

theorem sltCore_run (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (cmpCoreT armRq false .lt ++ rest) s = run H rest s' ∧
      lhs s' = (if BitVec.slt (lhs s) (rhs armRq s) then 1 else 0) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_run
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

theorem sgtCore_run (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (cmpCoreT armRq true .lt ++ rest) s = run H rest s' ∧
      lhs s' = (if BitVec.slt (rhs armRq s) (lhs s) then 1 else 0) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_run
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

end Evm.CL.ARM64.CoreSem
