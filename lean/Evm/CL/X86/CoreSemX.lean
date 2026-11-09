/-
  Evm.CL.X86.CoreSemX — the u256 limb cores over the x86-64 right quad
  (`X86JIT.x86Flush.rq = (x15, x17, x16, x0)`): the same statements as
  `ARM64.CoreSem` (there over x10-x13), by the same bit-blasting. `eqCoreT`
  reads its first right limb (x15) before it uses x15 as scratch; the proof
  checks that ordering rather than assuming it.
-/

import Evm.CL.ARM64.CoreSem
import Evm.CL.X86JIT

namespace Evm.CL.X86.CoreSemX

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun Evm.CL.ARM64.JIT Evm.CL.ARM64.CoreSem

/-- The x86-64 right quad. -/
def x86Rq : Reg × Reg × Reg × Reg := (.x15, .x17, .x16, .x0)

theorem x86Flush_rq : Evm.CL.X86JIT.x86Flush.rq = x86Rq := rfl

syntax "core_runX" : tactic
macro_rules
  | `(tactic| core_runX) =>
    `(tactic| (simp only [addCoreT, subCoreT, bitCoreT, notCoreA, isZeroCoreA, eqCoreT, cmpCoreT, zeroHiA, x86Rq,
                 List.cons_append, List.nil_append, List.append_assoc, run_cons_data,
                 ctrl_adds, ctrl_adcs, ctrl_adc, ctrl_subsReg, ctrl_sbcs, ctrl_sbc, ctrl_subsZr, ctrl_sbcsZr,
                 ctrl_cset, ctrl_and3, ctrl_orr3, ctrl_eor3, ctrl_mvn, ctrl_movImm, ctrl_cmpImm,
                 step_adds, step_adcs, step_adc, step_subsReg, step_sbcs, step_sbc, step_subsZr, step_sbcsZr,
                 step_cset, step_and3, step_orr3, step_eor3, step_mvn, step_movImm, step_cmpImm]))

set_option backward.isDefEq.respectTransparency false in
theorem addCore_runX (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (addCoreT x86Rq ++ rest) s = run H rest s' ∧
      lhs s' = lhs s + rhs x86Rq s ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_runX
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

set_option backward.isDefEq.respectTransparency false in
theorem subCore_runX (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (subCoreT x86Rq ++ rest) s = run H rest s' ∧
      lhs s' = lhs s - rhs x86Rq s ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_runX
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

set_option backward.isDefEq.respectTransparency false in
theorem andCore_runX (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (bitCoreT x86Rq .and3 ++ rest) s = run H rest s' ∧
      lhs s' = lhs s &&& rhs x86Rq s ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_runX
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

set_option backward.isDefEq.respectTransparency false in
theorem orCore_runX (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (bitCoreT x86Rq .orr3 ++ rest) s = run H rest s' ∧
      lhs s' = lhs s ||| rhs x86Rq s ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_runX
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

set_option backward.isDefEq.respectTransparency false in
theorem xorCore_runX (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (bitCoreT x86Rq .eor3 ++ rest) s = run H rest s' ∧
      lhs s' = lhs s ^^^ rhs x86Rq s ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_runX
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

set_option backward.isDefEq.respectTransparency false in
/-- `eq`: x14, x15 are scratch (x15 is read as the first right limb first). -/
theorem eqCore_runX (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (eqCoreT x86Rq ++ rest) s = run H rest s' ∧
      lhs s' = (if lhs s = rhs x86Rq s then 1 else 0) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → r ≠ .x14 → r ≠ .x15 → s'.regs r = s.regs r) := by
  core_runX
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9 h14 h15; simp [RS.set, h6, h7, h8, h9, h14, h15]

set_option backward.isDefEq.respectTransparency false in
theorem ltCore_runX (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (cmpCoreT x86Rq false .lo ++ rest) s = run H rest s' ∧
      lhs s' = (if lhs s < rhs x86Rq s then 1 else 0) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_runX
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

set_option backward.isDefEq.respectTransparency false in
theorem gtCore_runX (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (cmpCoreT x86Rq true .lo ++ rest) s = run H rest s' ∧
      lhs s' = (if rhs x86Rq s < lhs s then 1 else 0) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_runX
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

set_option backward.isDefEq.respectTransparency false in
theorem sltCore_runX (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (cmpCoreT x86Rq false .lt ++ rest) s = run H rest s' ∧
      lhs s' = (if BitVec.slt (lhs s) (rhs x86Rq s) then 1 else 0) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_runX
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

set_option backward.isDefEq.respectTransparency false in
theorem sgtCore_runX (H : Helpers) (rest : List AInstr) (s : RS) :
    ∃ s', run H (cmpCoreT x86Rq true .lt ++ rest) s = run H rest s' ∧
      lhs s' = (if BitVec.slt (rhs x86Rq s) (lhs s) then 1 else 0) ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.regs r = s.regs r) := by
  core_runX
  refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
  · core_limbs; bv_decide
  · intro r h6 h7 h8 h9; simp [RS.set, h6, h7, h8, h9]

end Evm.CL.X86.CoreSemX
