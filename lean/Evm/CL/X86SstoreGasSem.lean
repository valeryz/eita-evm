/-
  Evm.CL.X86SstoreGasSem — the x86-64 `_eita_sstore_gas_*` PROGRAMS run under
  `AsmSem` store exactly the `SstoreGasDenote` plans — `ARM64.SstoreGasSem`
  for the packed-predicate programs of `X86SstoreGas`.

  The one new piece is the join between the prologue and the trees: ARM64
  leaves six predicate REGISTERS, x86-64 leaves one register of BITS
  (`packBits`), and the trees test bits (`tst x9, #k`); `pack_bit*` are the
  seven facts that turn a bit test into the predicate. The folds are the
  left-nested two-register chains (`limbs_zero_iff'`, `limbs_eq_iff'`), the
  same `PredFold` theorems in the shape simp leaves them. Everything else —
  prologue run once as `runSL`, 64/128-way case split before the run, the
  plan generalised to an atom, propositional rewrites only — is the ARM64
  proof verbatim, with `X86SstoreGas`'s registers.
-/

import Evm.CL.AsmSem
import Evm.CL.X86SstoreGas
import Evm.CL.ARM64.SstoreGasSem

namespace Evm.CL.X86SstoreGasSem

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.ARM64 Evm.CL.ARM64.PredFold
open Evm.CL.ARM64.SstoreGasSem (loads pz pe orFold_eq_zero xorFold_eq_zero msb_true_iff msb_false_iff
  addz subz iteT iteF bnt bnf bat baf bta bfa bfet btef eqT runSL exec_symLabel)
open Evm.CL.X86SstoreGas

/-- The two words the routine leaves at `out` (x3 = rdi). -/
def outWords (m : RM) (m' : RM) : BitVec 64 × BitVec 64 :=
  (m'.mem (m.regs .x3), m'.mem (m.regs .x3 + 8#64))

/-! ### The folds in the two-register chain's shape -/

@[simp] theorem limbs_zero_iff' (x : Evm.U256) :
    (((limb0 x = 0#64 ∧ limb1 x = 0#64) ∧ limb2 x = 0#64) ∧ limb3 x = 0#64) ↔ pz x = true := by
  rw [pz, decide_eq_true_eq, ← orFold_eq_zero]; simp [and_assoc]

@[simp] theorem limbs_eq_iff' (x y : Evm.U256) :
    (((limb0 x = limb0 y ∧ limb1 x = limb1 y) ∧ limb2 x = limb2 y) ∧ limb3 x = limb3 y)
      ↔ pe x y = true := by
  rw [pe, decide_eq_true_eq, ← xorFold_eq_zero]; simp [and_assoc]

/-! ### The packed predicates -/

/-- What the prologue leaves in x9, in the order it packs: cold first. -/
def packBits (oz cz nz oc cn on cold : Bool) : BitVec 64 :=
  (((((((b2v cold <<< 6) ||| b2v oz) ||| (b2v cz <<< 1)) ||| (b2v nz <<< 2)) ||| (b2v oc <<< 3))
      ||| (b2v cn <<< 4)) ||| (b2v on <<< 5))

@[simp] theorem pack_bit1 (a b c d e f g : Bool) :
    (packBits a b c d e f g &&& 1#64 = 0#64) ↔ a = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> decide
@[simp] theorem pack_bit2 (a b c d e f g : Bool) :
    (packBits a b c d e f g &&& 2#64 = 0#64) ↔ b = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> decide
@[simp] theorem pack_bit4 (a b c d e f g : Bool) :
    (packBits a b c d e f g &&& 4#64 = 0#64) ↔ c = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> decide
@[simp] theorem pack_bit8 (a b c d e f g : Bool) :
    (packBits a b c d e f g &&& 8#64 = 0#64) ↔ d = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> decide
@[simp] theorem pack_bit16 (a b c d e f g : Bool) :
    (packBits a b c d e f g &&& 16#64 = 0#64) ↔ e = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> decide
@[simp] theorem pack_bit32 (a b c d e f g : Bool) :
    (packBits a b c d e f g &&& 32#64 = 0#64) ↔ f = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> decide
@[simp] theorem pack_bit64 (a b c d e f g : Bool) :
    (packBits a b c d e f g &&& 64#64 = 0#64) ↔ g = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> cases g <;> decide

@[simp] theorem b2v_not_not (b : Bool) : b2v (!!b) = b2v b := by cases b <;> rfl

/-! ### The prologue, once -/

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem exec_prologueX (m : RM) (rest : List AInstr) :
    exec (prologueX ++ rest) m = exec rest (runSL prologueX m) := by
  simp [prologueX, isZeroX, isEqX, packBit, exec, step, runSL]

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- What the prologue leaves: x9 the packed predicates, x14 zero, x2/x3 and
    memory untouched. -/
theorem prologueX_facts (m : RM) (cold : Bool) (o c n : Evm.U256)
    (h7 : m.regs .x7 = b2v cold)
    (ho : loads m .x1 o) (hc : loads m .x14 c) (hn : loads m .x6 n) :
    (runSL prologueX m).regs .x9 = packBits (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n) cold ∧
    (runSL prologueX m).regs .x14 = 0#64 ∧
    (runSL prologueX m).regs .x2 = m.regs .x2 ∧
    (runSL prologueX m).regs .x3 = m.regs .x3 ∧
    (runSL prologueX m).mem = m.mem := by
  obtain ⟨ho0, ho1, ho2, ho3⟩ := ho
  obtain ⟨hc0, hc1, hc2, hc3⟩ := hc
  obtain ⟨hn0, hn1, hn2, hn3⟩ := hn
  simp [runSL, prologueX, isZeroX, isEqX, packBit, step, h7,
        ho0, ho1, ho2, ho3, hc0, hc1, hc2, hc3, hn0, hn1, hn2, hn3, scHolds, subFlags, packBits]

/-- One path, as `SstoreGasSem.sstore_case` with the bit tests' flags. -/
syntax "sstorex_case" ident ident : tactic
macro_rules
  | `(tactic| sstorex_case $h:ident $ce:ident) => `(tactic| (
      simp [*, exec, step, skipTo, bcHolds, scHolds, subFlags, logicFlags, outWords] <;>
      (simp only [SstoreGasDenote.planEip1283, SstoreGasDenote.planEip2200,
        SstoreGasDenote.plan2929, SstoreGasDenote.cost1283, SstoreGasDenote.add1283,
        SstoreGasDenote.sub1283, SstoreGasDenote.cost2200] at $h:ident) <;>
      (try simp only [iteT, iteF, bnt, bnf, bat, baf, bta, bfa, bfet, btef, eqT] at $h:ident) <;>
      (simp only [SstoreGasDenote.chainPlan,
        SstoreGasDenote.noopCost1283_eq, SstoreGasDenote.setCost1283_eq,
        SstoreGasDenote.resetCost1283_eq, SstoreGasDenote.dirtyCost1283_eq,
        SstoreGasDenote.resetZeroR1283_eq, SstoreGasDenote.resetNzR1283_eq,
        SstoreGasDenote.sloadCost2200_eq, SstoreGasDenote.setCost2200_eq,
        SstoreGasDenote.resetCost2200_eq, SstoreGasDenote.resetZeroR2200_eq,
        SstoreGasDenote.resetNzR2200_eq,
        SstoreGasDenote.berlin_warm_eq, SstoreGasDenote.berlin_set_eq,
        SstoreGasDenote.berlin_reset_eq, SstoreGasDenote.berlin_coldSurch_eq,
        SstoreGasDenote.berlin_resetZeroA_eq, SstoreGasDenote.berlin_resetNzA_eq,
        SstoreGasDenote.london_warm_eq, SstoreGasDenote.london_set_eq,
        SstoreGasDenote.london_reset_eq, SstoreGasDenote.london_coldSurch_eq,
        SstoreGasDenote.london_resetZeroA_eq, SstoreGasDenote.london_resetNzA_eq,
        iteT, iteF, bnt, bnf, bat, baf, bta, bfa, bfet, btef, eqT, addz, subz,
        Nat.not_lt_zero, Prod.ext_iff] at $h:ident) <;>
      (have hc := $ce) <;>
      (obtain ⟨hP1, hP2⟩ := $h) <;>
      (repeat' split) <;> (repeat' apply And.intro) <;>
      (try split at hP2) <;> (try split at hP1) <;>
      (try simp only [msb_true_iff, msb_false_iff, Bool.not_eq_true] at *) <;> bv_omega))

syntax "sstorex_unfold" : tactic
macro_rules
  | `(tactic| sstorex_unfold) => `(tactic| (
      simp only [X86SstoreGas.instrs, X86SstoreGas.routines, X86SstoreGas.legacyBody,
        X86SstoreGas.eip1283Body, X86SstoreGas.eip2200Body, X86SstoreGas.eip2929Body,
        X86SstoreGas.isZeroX, X86SstoreGas.packBit, Evm.CL.Frame.header,
        List.flatMap_cons, List.flatMap_nil,
        bOrigZero, bCurZero, bNewZero, bOrigEqCur, bCurEqNew, bOrigEqNew, bCold,
        SstoreGasSem.setCost_eq, SstoreGasSem.resetCost_eq, SstoreGasSem.clearRefund_eq,
        SstoreGasDenote.noopCost1283_eq, SstoreGasDenote.setCost1283_eq,
        SstoreGasDenote.resetCost1283_eq, SstoreGasDenote.dirtyCost1283_eq,
        SstoreGasDenote.clearRef1283_eq, SstoreGasDenote.resetZeroR1283_eq,
        SstoreGasDenote.resetNzR1283_eq,
        SstoreGasDenote.sloadCost2200_eq, SstoreGasDenote.setCost2200_eq,
        SstoreGasDenote.resetCost2200_eq, SstoreGasDenote.clearRef2200_eq,
        SstoreGasDenote.resetZeroR2200_eq, SstoreGasDenote.resetNzR2200_eq,
        SstoreGasDenote.berlin_warm_eq, SstoreGasDenote.berlin_set_eq,
        SstoreGasDenote.berlin_reset_eq, SstoreGasDenote.berlin_coldSurch_eq,
        SstoreGasDenote.berlin_clearRef_eq, SstoreGasDenote.berlin_resetZeroA_eq,
        SstoreGasDenote.berlin_resetNzA_eq,
        SstoreGasDenote.london_warm_eq, SstoreGasDenote.london_set_eq,
        SstoreGasDenote.london_reset_eq, SstoreGasDenote.london_coldSurch_eq,
        SstoreGasDenote.london_clearRef_eq, SstoreGasDenote.london_resetZeroA_eq,
        SstoreGasDenote.london_resetNzA_eq]
      simp (disch := decide) only [movImmInstrs_small, List.cons_append, List.nil_append,
        List.append_assoc]
      simp only [entry, BEq.beq, String.reduceEq, String.reduceAppend, decide_true, decide_false,
        ite_true, ite_false, reduceCtorEq]))

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `_eita_sstore_gas_legacy` (x86-64) stores `planLegacy`. -/
theorem legacy_sem (m : RM) (rest : List AInstr) (r : BitVec 64) (c n : Evm.U256)
    (h2 : m.regs .x2 = r) (_hr : r.toNat + 65536 < 2^63)
    (hc : loads m .x14 c) (hn : loads m .x6 n) :
    (exec (entry "_eita_sstore_gas_legacy" (Evm.CL.Frame.header "_eita_sstore_gas_legacy" ++ legacyBody ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (SstoreGasDenote.planLegacy r.toNat (pz c) (pz n)).1,
              BitVec.ofNat 64 (SstoreGasDenote.planLegacy r.toNat (pz c) (pz n)).2) := by
  obtain ⟨hc0, hc1, hc2, hc3⟩ := hc
  obtain ⟨hn0, hn1, hn2, hn3⟩ := hn
  sstorex_unfold
  simp [exec, step, skipTo, h2, hc0, hc1, hc2, hc3, hn0, hn1, hn2, hn3, bcHolds, scHolds,
        subFlags, logicFlags, outWords, SstoreGasDenote.planLegacy,
        SstoreGasSem.setCost_eq, SstoreGasSem.resetCost_eq, SstoreGasSem.clearRefund_eq]
  generalize pz c = cz
  generalize pz n = nz
  cases cz <;> cases nz <;> simp <;> bv_omega

/-- The tree theorems share this prelude: the prologue once, its facts, the
    predicates and the plan as atoms. -/
syntax "sstorex_tree" : tactic
macro_rules
  | `(tactic| sstorex_tree) => `(tactic| (
      sstorex_unfold
      rw [exec_symLabel, exec_prologueX]))

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `_eita_sstore_gas_eip1283` (x86-64) stores `planEip1283`. -/
theorem eip1283_sem (m : RM) (rest : List AInstr) (r : BitVec 64) (cold : Bool) (o c n : Evm.U256)
    (h2 : m.regs .x2 = r) (hr : r.toNat + 65536 < 2^63) (h7 : m.regs .x7 = b2v cold)
    (ho : loads m .x1 o) (hc : loads m .x14 c) (hn : loads m .x6 n) :
    (exec (entry "_eita_sstore_gas_eip1283" (Evm.CL.Frame.header "_eita_sstore_gas_eip1283" ++ eip1283Body ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (SstoreGasDenote.planEip1283 r.toNat
                (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).1,
              BitVec.ofNat 64 (SstoreGasDenote.planEip1283 r.toNat
                (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).2) := by
  have hf := prologueX_facts m cold o c n h7 ho hc hn
  obtain ⟨h9, h14, hx2, hx3, hmem⟩ := hf
  rw [h2] at hx2
  clear ho hc hn
  sstorex_tree
  generalize runSL prologueX m = m1 at h9 h14 hx2 hx3 hmem ⊢
  generalize pz o = oz at h9 ⊢
  generalize pz c = cz at h9 ⊢
  generalize pz n = nz at h9 ⊢
  generalize pe o c = oc at h9 ⊢
  generalize pe c n = cn at h9 ⊢
  generalize pe o n = on at h9 ⊢
  generalize hP : SstoreGasDenote.planEip1283 r.toNat oz cz nz oc cn on = P
  cases oz <;> cases cz <;> cases nz <;> cases oc <;> cases cn <;> cases on <;>
    sstorex_case hP SstoreGasDenote.clearRef1283_eq

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `_eita_sstore_gas_eip2200` (x86-64) stores `planEip2200`. -/
theorem eip2200_sem (m : RM) (rest : List AInstr) (r : BitVec 64) (cold : Bool) (o c n : Evm.U256)
    (h2 : m.regs .x2 = r) (hr : r.toNat + 65536 < 2^63) (h7 : m.regs .x7 = b2v cold)
    (ho : loads m .x1 o) (hc : loads m .x14 c) (hn : loads m .x6 n) :
    (exec (entry "_eita_sstore_gas_eip2200" (Evm.CL.Frame.header "_eita_sstore_gas_eip2200" ++ eip2200Body ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (SstoreGasDenote.planEip2200 r.toNat
                (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).1,
              BitVec.ofNat 64 (SstoreGasDenote.planEip2200 r.toNat
                (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).2) := by
  have hf := prologueX_facts m cold o c n h7 ho hc hn
  obtain ⟨h9, h14, hx2, hx3, hmem⟩ := hf
  rw [h2] at hx2
  clear ho hc hn
  sstorex_tree
  generalize runSL prologueX m = m1 at h9 h14 hx2 hx3 hmem ⊢
  generalize pz o = oz at h9 ⊢
  generalize pz c = cz at h9 ⊢
  generalize pz n = nz at h9 ⊢
  generalize pe o c = oc at h9 ⊢
  generalize pe c n = cn at h9 ⊢
  generalize pe o n = on at h9 ⊢
  generalize hP : SstoreGasDenote.planEip2200 r.toNat oz cz nz oc cn on = P
  cases oz <;> cases cz <;> cases nz <;> cases oc <;> cases cn <;> cases on <;>
    sstorex_case hP SstoreGasDenote.clearRef2200_eq

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `_eita_sstore_gas_berlin` (x86-64) stores `plan2929 berlinConsts`. -/
theorem berlin_sem (m : RM) (rest : List AInstr) (r : BitVec 64) (cold : Bool) (o c n : Evm.U256)
    (h2 : m.regs .x2 = r) (hr : r.toNat + 65536 < 2^63) (h7 : m.regs .x7 = b2v cold)
    (ho : loads m .x1 o) (hc : loads m .x14 c) (hn : loads m .x6 n) :
    (exec (entry "_eita_sstore_gas_berlin" (Evm.CL.Frame.header "_eita_sstore_gas_berlin" ++ eip2929Body SstoreGasDenote.berlinConsts ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (SstoreGasDenote.plan2929 SstoreGasDenote.berlinConsts r.toNat cold
                (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).1,
              BitVec.ofNat 64 (SstoreGasDenote.plan2929 SstoreGasDenote.berlinConsts r.toNat cold
                (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).2) := by
  have hf := prologueX_facts m cold o c n h7 ho hc hn
  obtain ⟨h9, h14, hx2, hx3, hmem⟩ := hf
  rw [h2] at hx2
  clear ho hc hn
  sstorex_tree
  generalize runSL prologueX m = m1 at h9 h14 hx2 hx3 hmem ⊢
  generalize pz o = oz at h9 ⊢
  generalize pz c = cz at h9 ⊢
  generalize pz n = nz at h9 ⊢
  generalize pe o c = oc at h9 ⊢
  generalize pe c n = cn at h9 ⊢
  generalize pe o n = on at h9 ⊢
  generalize hP : SstoreGasDenote.plan2929 SstoreGasDenote.berlinConsts r.toNat cold oz cz nz oc cn on = P
  cases cold <;> cases oz <;> cases cz <;> cases nz <;> cases oc <;> cases cn <;> cases on <;>
    sstorex_case hP SstoreGasDenote.berlin_clearRef_eq

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `_eita_sstore_gas_london` (x86-64) stores `plan2929 londonConsts`. -/
theorem london_sem (m : RM) (rest : List AInstr) (r : BitVec 64) (cold : Bool) (o c n : Evm.U256)
    (h2 : m.regs .x2 = r) (hr : r.toNat + 65536 < 2^63) (h7 : m.regs .x7 = b2v cold)
    (ho : loads m .x1 o) (hc : loads m .x14 c) (hn : loads m .x6 n) :
    (exec (entry "_eita_sstore_gas_london" (Evm.CL.Frame.header "_eita_sstore_gas_london" ++ eip2929Body SstoreGasDenote.londonConsts ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (SstoreGasDenote.plan2929 SstoreGasDenote.londonConsts r.toNat cold
                (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).1,
              BitVec.ofNat 64 (SstoreGasDenote.plan2929 SstoreGasDenote.londonConsts r.toNat cold
                (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).2) := by
  have hf := prologueX_facts m cold o c n h7 ho hc hn
  obtain ⟨h9, h14, hx2, hx3, hmem⟩ := hf
  rw [h2] at hx2
  clear ho hc hn
  sstorex_tree
  generalize runSL prologueX m = m1 at h9 h14 hx2 hx3 hmem ⊢
  generalize pz o = oz at h9 ⊢
  generalize pz c = cz at h9 ⊢
  generalize pz n = nz at h9 ⊢
  generalize pe o c = oc at h9 ⊢
  generalize pe c n = cn at h9 ⊢
  generalize pe o n = on at h9 ⊢
  generalize hP : SstoreGasDenote.plan2929 SstoreGasDenote.londonConsts r.toNat cold oz cz nz oc cn on = P
  cases cold <;> cases oz <;> cases cz <;> cases nz <;> cases oc <;> cases cn <;> cases on <;>
    sstorex_case hP SstoreGasDenote.london_clearRef_eq


/-! ## Program → spec

Each routine, as the x86-64 file prints it (`X86Interp`: a header, then the
body), IS its fork's `sstoreGas`, by the plan theorems of `SstoreGasDenote`. -/

theorem legacy_is_sstoreGas (m : RM) (rest : List AInstr) (r : BitVec 64) (c n : Evm.U256)
    (h2 : m.regs .x2 = r) (hr : r.toNat + 65536 < 2^63)
    (hc : loads m .x14 c) (hn : loads m .x6 n) :
    (exec (entry "_eita_sstore_gas_legacy"
        (Evm.CL.Frame.header "_eita_sstore_gas_legacy" ++ legacyBody ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (Evm.Frontier.Vm.Instructions.sstoreGas r.toNat c n).1,
              BitVec.ofNat 64 (Evm.Frontier.Vm.Instructions.sstoreGas r.toNat c n).2) := by
  rw [legacy_sem m rest r c n h2 hr hc hn]
  simp only [pz, SstoreGasDenote.legacy_eq_spec]

theorem eip1283_is_sstoreGas (m : RM) (rest : List AInstr) (r : BitVec 64) (cold : Bool) (o c n : Evm.U256)
    (h2 : m.regs .x2 = r) (hr : r.toNat + 65536 < 2^63) (h7 : m.regs .x7 = b2v cold)
    (ho : loads m .x1 o) (hc : loads m .x14 c) (hn : loads m .x6 n) :
    (exec (entry "_eita_sstore_gas_eip1283"
        (Evm.CL.Frame.header "_eita_sstore_gas_eip1283" ++ eip1283Body ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (Evm.Constantinople.Vm.Instructions.sstoreGas r.toNat o c n).1,
              BitVec.ofNat 64 (Evm.Constantinople.Vm.Instructions.sstoreGas r.toNat o c n).2) := by
  rw [eip1283_sem m rest r cold o c n h2 hr h7 ho hc hn]
  simp only [pz, pe, SstoreGasDenote.eip1283_eq_spec]

theorem eip2200_is_sstoreGas (m : RM) (rest : List AInstr) (r : BitVec 64) (cold : Bool) (o c n : Evm.U256)
    (h2 : m.regs .x2 = r) (hr : r.toNat + 65536 < 2^63) (h7 : m.regs .x7 = b2v cold)
    (ho : loads m .x1 o) (hc : loads m .x14 c) (hn : loads m .x6 n) :
    (exec (entry "_eita_sstore_gas_eip2200"
        (Evm.CL.Frame.header "_eita_sstore_gas_eip2200" ++ eip2200Body ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (Evm.Istanbul.Vm.Instructions.sstoreGas r.toNat o c n).1,
              BitVec.ofNat 64 (Evm.Istanbul.Vm.Instructions.sstoreGas r.toNat o c n).2) := by
  rw [eip2200_sem m rest r cold o c n h2 hr h7 ho hc hn]
  simp only [pz, pe, SstoreGasDenote.eip2200_eq_spec]

theorem berlin_is_sstoreGas (m : RM) (rest : List AInstr) (r : BitVec 64) (cold : Bool) (o c n : Evm.U256)
    (h2 : m.regs .x2 = r) (hr : r.toNat + 65536 < 2^63) (h7 : m.regs .x7 = b2v cold)
    (ho : loads m .x1 o) (hc : loads m .x14 c) (hn : loads m .x6 n) :
    (exec (entry "_eita_sstore_gas_berlin"
        (Evm.CL.Frame.header "_eita_sstore_gas_berlin" ++ eip2929Body SstoreGasDenote.berlinConsts ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (Evm.Berlin.Vm.Instructions.Storage.sstoreGas r.toNat cold o c n).1,
              BitVec.ofNat 64 (Evm.Berlin.Vm.Instructions.Storage.sstoreGas r.toNat cold o c n).2) := by
  rw [berlin_sem m rest r cold o c n h2 hr h7 ho hc hn]
  simp only [pz, pe, SstoreGasDenote.berlin_eq_spec]

theorem london_is_sstoreGas (m : RM) (rest : List AInstr) (r : BitVec 64) (cold : Bool) (o c n : Evm.U256)
    (h2 : m.regs .x2 = r) (hr : r.toNat + 65536 < 2^63) (h7 : m.regs .x7 = b2v cold)
    (ho : loads m .x1 o) (hc : loads m .x14 c) (hn : loads m .x6 n) :
    (exec (entry "_eita_sstore_gas_london"
        (Evm.CL.Frame.header "_eita_sstore_gas_london" ++ eip2929Body SstoreGasDenote.londonConsts ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (Evm.London.Vm.Effect.sstoreGas r.toNat cold o c n).1,
              BitVec.ofNat 64 (Evm.London.Vm.Effect.sstoreGas r.toNat cold o c n).2) := by
  rw [london_sem m rest r cold o c n h2 hr h7 ho hc hn]
  simp only [pz, pe, SstoreGasDenote.london_eq_spec]

end Evm.CL.X86SstoreGasSem
