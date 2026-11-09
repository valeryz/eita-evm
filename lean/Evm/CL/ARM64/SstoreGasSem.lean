/-
  Evm.CL.ARM64.SstoreGasSem — the `_eita_sstore_gas_*` PROGRAMS run under
  `AsmSem` store exactly the `SstoreGasDenote` plans.

  The precondition is `refund + 65536 < 2^63` (on the 64-bit counter the
  caller passes in x1), not the `refund < 2^63` the routines' header used to
  state: EIP-1283's single clamp reads the SIGN BIT
  of `refund + delta` (`cmp #0 ; csel lt`), so the counter needs headroom for
  the largest positive delta (19 800). The symbolic execution found the gap;
  the counter is bounded by gas spent, so it is unreachable, but the stated
  precondition is now the one that is true.

  This is the joint `SstoreGasDenote`'s header said was missing: the limb-fold
  prologue (`PredFold`) and the branch tree (the plan functions) were each
  proven against the spec, but nothing related the `AInstr` program to either.
  Here the program is executed symbolically — every `ldp`, `orr`, `cset`,
  `cbz`, `csel`, the clamps — and what it stores at `out` is the plan. With
  `*_eq_spec` that is program → plan → `sstoreGas`.
-/

import Evm.CL.AsmSem
import Evm.CL.ARM64.SstoreGas
import Evm.CL.ARM64.SstoreGasDenote
import Evm.CL.ARM64.PredFold

namespace Evm.CL.ARM64.SstoreGasSem

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.ARM64 Evm.CL.ARM64.PredFold

/-- A u256 at `[p]`, four little-endian limbs as `ldp` reads them. -/
def loads (m : RM) (p : Reg) (v : Evm.U256) : Prop :=
  m.mem (m.regs p) = limb0 v ∧ m.mem (m.regs p + 8#64) = limb1 v ∧
  m.mem (m.regs p + 16#64) = limb2 v ∧ m.mem (m.regs p + 24#64) = limb3 v

/-- The two words the routine leaves at `out`. -/
def outWords (m : RM) (m' : RM) : BitVec 64 × BitVec 64 :=
  (m'.mem (m.regs .x0), m'.mem (m.regs .x0 + 8#64))

/-! ### The folds, as simp leaves them

`simp` splits `a ||| b = 0` into `a = 0 ∧ b = 0` and `a ^^^ b = 0` into `a = b`
before any fold lemma can see the tree, so the join with `PredFold` is stated in
that normal form. The predicates are wrapped (`pz`, `pe`) so that, once the
program has been executed, they can be generalised to the six Booleans the plan
theorems quantify over. -/

/-- `decide (x = 0)`, kept opaque to simp. -/
def pz (x : Evm.U256) : Bool := decide (x = 0)
/-- `decide (x = y)`, kept opaque to simp. -/
def pe (x y : Evm.U256) : Bool := decide (x = y)

theorem orFold_eq_zero (x : Evm.U256) :
    ((limb0 x ||| limb1 x) ||| (limb2 x ||| limb3 x) = 0#64) ↔ x = 0 := by
  have h := isZeroFold_eq x
  simp only [isZeroFold, csetEqZero, orFold] at h
  exact (decide_eq_decide).1 h

theorem xorFold_eq_zero (x y : Evm.U256) :
    (((limb0 x ^^^ limb0 y) ||| (limb1 x ^^^ limb1 y)) |||
      ((limb2 x ^^^ limb2 y) ||| (limb3 x ^^^ limb3 y)) = 0#64) ↔ x = y := by
  have h := isEqFold_eq x y
  simp only [isEqFold, csetEqZero, xorFold] at h
  exact (decide_eq_decide).1 h

/-- The OR tree, limb by limb: zero iff the u256 is. -/
@[simp] theorem limbs_zero_iff (x : Evm.U256) :
    ((limb0 x = 0#64 ∧ limb1 x = 0#64) ∧ (limb2 x = 0#64 ∧ limb3 x = 0#64)) ↔ pz x = true := by
  rw [pz, decide_eq_true_eq, ← orFold_eq_zero]; simp

/-- The XOR/OR tree, limb by limb: equal iff the u256s are. -/
@[simp] theorem limbs_eq_iff (x y : Evm.U256) :
    ((limb0 x = limb0 y ∧ limb1 x = limb1 y) ∧ (limb2 x = limb2 y ∧ limb3 x = limb3 y))
      ↔ pe x y = true := by
  rw [pe, decide_eq_true_eq, ← xorFold_eq_zero]; simp

@[simp] theorem limbs_xor_iff (x y : Evm.U256) :
    ((limb0 x ^^^ limb0 y = 0#64 ∧ limb1 x ^^^ limb1 y = 0#64) ∧
      (limb2 x ^^^ limb2 y = 0#64 ∧ limb3 x ^^^ limb3 y = 0#64)) ↔ pe x y = true := by
  rw [pe, decide_eq_true_eq, ← xorFold_eq_zero]; simp

/-- The legacy constants as numbers (the probes in `SstoreGasDenote`). -/
theorem setCost_eq : SstoreGasDenote.setCost = 20000 := by native_decide
theorem resetCost_eq : SstoreGasDenote.resetCost = 5000 := by native_decide
theorem clearRefund_eq : SstoreGasDenote.clearRefund = 15000 := by native_decide

syntax "sstore_unfold" : tactic
macro_rules
  | `(tactic| sstore_unfold) => `(tactic| (
      simp only [SstoreGas.legacyA, SstoreGas.eip1283A, SstoreGas.eip2200A,
        SstoreGas.eip2929A, SstoreGas.isZeroA, SstoreGas.isEqA, Evm.CL.Frame.header,
        setCost_eq, resetCost_eq, clearRefund_eq,
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

/-! ### The prologue, once

The six predicates are computed by the same 60 instructions in four routines.
Running them inside each routine's proof made the proof terms deeper than the
kernel will check, so the prologue is run once here, as a straight-line
machine function, and each tree proof starts from its output. -/

/-- Straight-line run: every instruction is a data step (no branches, no `ret`). -/
def runSL : List AInstr → RM → RM
  | [], m => m
  | i :: r, m => runSL r ((step m i).getD m)

@[simp] theorem exec_symLabel (s : String) (rest : List AInstr) (m : RM) :
    exec (.symLabel s :: rest) m = exec rest m := by
  simp [exec, step]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The prologue is straight-line: executing it is `runSL`. -/
theorem exec_prologue (m : RM) (rest : List AInstr) :
    exec (SstoreGas.prologueA ++ rest) m = exec rest (runSL SstoreGas.prologueA m) := by
  simp [SstoreGas.prologueA, SstoreGas.isZeroA, SstoreGas.isEqA, exec, step, runSL]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- What the prologue leaves: x10..x15 are the six predicates; x0/x1/x5 and
    memory are untouched (x6–x9, x16, x17 are scratch the trees write before
    they read). -/
theorem prologue_facts (m : RM) (o c n : Evm.U256)
    (ho : loads m .x2 o) (hc : loads m .x3 c) (hn : loads m .x4 n) :
    (runSL SstoreGas.prologueA m).regs .x10 = b2v (pz o) ∧
    (runSL SstoreGas.prologueA m).regs .x11 = b2v (pz c) ∧
    (runSL SstoreGas.prologueA m).regs .x12 = b2v (pz n) ∧
    (runSL SstoreGas.prologueA m).regs .x13 = b2v (pe o c) ∧
    (runSL SstoreGas.prologueA m).regs .x14 = b2v (pe c n) ∧
    (runSL SstoreGas.prologueA m).regs .x15 = b2v (pe o n) ∧
    (runSL SstoreGas.prologueA m).regs .x0 = m.regs .x0 ∧
    (runSL SstoreGas.prologueA m).regs .x1 = m.regs .x1 ∧
    (runSL SstoreGas.prologueA m).regs .x5 = m.regs .x5 ∧
    (runSL SstoreGas.prologueA m).mem = m.mem := by
  obtain ⟨ho0, ho1, ho2, ho3⟩ := ho
  obtain ⟨hc0, hc1, hc2, hc3⟩ := hc
  obtain ⟨hn0, hn1, hn2, hn3⟩ := hn
  simp [runSL, SstoreGas.prologueA, SstoreGas.isZeroA, SstoreGas.isEqA, step,
        ho0, ho1, ho2, ho3, hc0, hc1, hc2, hc3, hn0, hn1, hn2, hn3, scHolds, subFlags]

/-- The sign bit as a Prop on `toNat` — NOT `BitVec.msb_eq_decide`: its
    `decide (2^63 ≤ …)` makes the kernel evaluate `Nat.ble` against the literal
    `2^63`, which is a recursion `2^63` deep. -/
theorem msb_true_iff (x : BitVec 64) : x.msb = true ↔ 2^63 ≤ x.toNat := by
  rw [BitVec.msb_eq_decide]; simp

theorem msb_false_iff (x : BitVec 64) : x.msb = false ↔ x.toNat < 2^63 := by
  rw [BitVec.msb_eq_decide]; simp

/-! ### Propositional rewrites for the plan

Every lemma simp uses to evaluate the plan's Booleans and `if`s is stated
here with a CONSTANT body rather than `rfl`. Simp applies a `rfl` lemma
definitionally and then has the whole hypothesis re-checked by `whnf`; on the
EIP-2200 chain that walk reaches `x - 15000 + 0` and unfolds `Nat.sub` by
15 000 successor steps — in the elaborator (stack overflow) and in the kernel
("deep recursion detected"). A propositional rewrite is a `congrArg` the
checker verifies syntactically. For the same reason the subtracted constant
(the fork's clears-refund) is never rewritten to its number inside the plan;
omega receives it as the fact `clearRef = 15000`. -/

theorem addz (n : Nat) : n + 0 = n := Nat.add_zero n
theorem subz (n : Nat) : n - 0 = n := Nat.sub_zero n
theorem iteT {α : Sort _} (a b : α) : (if True then a else b) = a := ite_eq_left trivial
theorem iteF {α : Sort _} (a b : α) : (if False then a else b) = b := ite_eq_right id
theorem bnt : (!true) = false := Bool.not_true
theorem bnf : (!false) = true := Bool.not_false
theorem bat (b : Bool) : (b && true) = b := Bool.and_true b
theorem baf (b : Bool) : (b && false) = false := Bool.and_false b
theorem bta (b : Bool) : (true && b) = b := Bool.true_and b
theorem bfa (b : Bool) : (false && b) = false := Bool.false_and b
theorem bfet : (false = true) = False := Bool.false_eq_true
theorem btef : (true = false) = False := Bool.true_eq_false
theorem eqT {α : Sort _} (a : α) : (a = a) = True := eq_self a

/-- One path of a tree: with the six predicates (and `cold`) concrete, run the
    program — every `cbz`/`cbnz`/`csel` resolves — then unfold the PLAN inside
    its own hypothesis `h : plan … = P` (plan, then the dead branch of the
    outer `if`, then the live arithmetic), and close the clamps' `if`s and the
    64-bit arithmetic with the two components of `P` as facts. `ce` is the
    fork's clears-refund equation, handed to omega as a hypothesis. -/
syntax "sstore_case" ident ident : tactic
macro_rules
  | `(tactic| sstore_case $h:ident $ce:ident) => `(tactic| (
      simp [*, exec, step, skipTo, bcHolds, scHolds, subFlags, outWords] <;>
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

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
/-- `_eita_sstore_gas_legacy` stores `planLegacy` — Frontier's unconditional add. -/
theorem legacy_sem (m : RM) (rest : List AInstr) (r : BitVec 64) (c n : Evm.U256)
    (h1 : m.regs .x1 = r) (_hr : r.toNat + 65536 < 2^63)
    (hc : loads m .x3 c) (hn : loads m .x4 n) :
    (exec (entry "_eita_sstore_gas_legacy" (SstoreGas.legacyA ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (SstoreGasDenote.planLegacy r.toNat (pz c) (pz n)).1,
              BitVec.ofNat 64 (SstoreGasDenote.planLegacy r.toNat (pz c) (pz n)).2) := by
  obtain ⟨hc0, hc1, hc2, hc3⟩ := hc
  obtain ⟨hn0, hn1, hn2, hn3⟩ := hn
  sstore_unfold
  simp [exec, step, h1, hc0, hc1, hc2, hc3, hn0, hn1, hn2, hn3, bcHolds, scHolds,
        subFlags, outWords, SstoreGasDenote.planLegacy, setCost_eq, resetCost_eq, clearRefund_eq]
  generalize pz c = cz
  generalize pz n = nz
  cases cz <;> cases nz <;> simp <;> bv_omega

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `_eita_sstore_gas_eip1283` stores `planEip1283` — one signed delta in x9,
    clamped once by `cmp #0 ; csel lt` (the sign bit of a 64-bit sum, sound
    because `refund + 65536 < 2^63`). -/
theorem eip1283_sem (m : RM) (rest : List AInstr) (r : BitVec 64) (o c n : Evm.U256)
    (h1 : m.regs .x1 = r) (hr : r.toNat + 65536 < 2^63)
    (ho : loads m .x2 o) (hc : loads m .x3 c) (hn : loads m .x4 n) :
    (exec (entry "_eita_sstore_gas_eip1283" (SstoreGas.eip1283A ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (SstoreGasDenote.planEip1283 r.toNat (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).1,
              BitVec.ofNat 64 (SstoreGasDenote.planEip1283 r.toNat (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).2) := by
  have hf := prologue_facts m o c n ho hc hn
  obtain ⟨h10, h11, h12, h13, h14, h15, hx0, hx1, hx5, hmem⟩ := hf
  rw [h1] at hx1
  clear ho hc hn
  sstore_unfold
  rw [exec_symLabel, exec_prologue]
  generalize runSL SstoreGas.prologueA m = m1 at h10 h11 h12 h13 h14 h15 hx0 hx1 hx5 hmem ⊢
  generalize pz o = oz at h10 ⊢
  generalize pz c = cz at h11 ⊢
  generalize pz n = nz at h12 ⊢
  generalize pe o c = oc at h13 ⊢
  generalize pe c n = cn at h14 ⊢
  generalize pe o n = on at h15 ⊢
  generalize hP : SstoreGasDenote.planEip1283 r.toNat oz cz nz oc cn on = P
  cases oz <;> cases cz <;> cases nz <;> cases oc <;> cases cn <;> cases on <;>
    sstore_case hP SstoreGasDenote.clearRef1283_eq

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `_eita_sstore_gas_eip2200` stores `planEip2200` — the sequential discipline:
    an `add`, a saturating `subs`+`csel lo`, an `add`. -/
theorem eip2200_sem (m : RM) (rest : List AInstr) (r : BitVec 64) (o c n : Evm.U256)
    (h1 : m.regs .x1 = r) (hr : r.toNat + 65536 < 2^63)
    (ho : loads m .x2 o) (hc : loads m .x3 c) (hn : loads m .x4 n) :
    (exec (entry "_eita_sstore_gas_eip2200" (SstoreGas.eip2200A ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (SstoreGasDenote.planEip2200 r.toNat (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).1,
              BitVec.ofNat 64 (SstoreGasDenote.planEip2200 r.toNat (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).2) := by
  have hf := prologue_facts m o c n ho hc hn
  obtain ⟨h10, h11, h12, h13, h14, h15, hx0, hx1, hx5, hmem⟩ := hf
  rw [h1] at hx1
  clear ho hc hn
  sstore_unfold
  rw [exec_symLabel, exec_prologue]
  generalize runSL SstoreGas.prologueA m = m1 at h10 h11 h12 h13 h14 h15 hx0 hx1 hx5 hmem ⊢
  generalize pz o = oz at h10 ⊢
  generalize pz c = cz at h11 ⊢
  generalize pz n = nz at h12 ⊢
  generalize pe o c = oc at h13 ⊢
  generalize pe c n = cn at h14 ⊢
  generalize pe o n = on at h15 ⊢
  generalize hP : SstoreGasDenote.planEip2200 r.toNat oz cz nz oc cn on = P
  cases oz <;> cases cz <;> cases nz <;> cases oc <;> cases cn <;> cases on <;>
    sstore_case hP SstoreGasDenote.clearRef2200_eq

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `_eita_sstore_gas_berlin` stores `plan2929 berlinConsts` — add first, then
    one clamped subtract, plus the cold surcharge on the cost. -/
theorem berlin_sem (m : RM) (rest : List AInstr) (r : BitVec 64) (cold : Bool) (o c n : Evm.U256)
    (h1 : m.regs .x1 = r) (hr : r.toNat + 65536 < 2^63) (h5 : m.regs .x5 = b2v cold)
    (ho : loads m .x2 o) (hc : loads m .x3 c) (hn : loads m .x4 n) :
    (exec (entry "_eita_sstore_gas_berlin" (SstoreGas.eip2929A "berlin" SstoreGasDenote.berlinConsts ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (SstoreGasDenote.plan2929 SstoreGasDenote.berlinConsts r.toNat cold (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).1,
              BitVec.ofNat 64 (SstoreGasDenote.plan2929 SstoreGasDenote.berlinConsts r.toNat cold (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).2) := by
  have hf := prologue_facts m o c n ho hc hn
  obtain ⟨h10, h11, h12, h13, h14, h15, hx0, hx1, hx5, hmem⟩ := hf
  rw [h1] at hx1
  rw [h5] at hx5
  clear ho hc hn
  sstore_unfold
  rw [exec_symLabel, exec_prologue]
  generalize runSL SstoreGas.prologueA m = m1 at h10 h11 h12 h13 h14 h15 hx0 hx1 hx5 hmem ⊢
  generalize pz o = oz at h10 ⊢
  generalize pz c = cz at h11 ⊢
  generalize pz n = nz at h12 ⊢
  generalize pe o c = oc at h13 ⊢
  generalize pe c n = cn at h14 ⊢
  generalize pe o n = on at h15 ⊢
  generalize hP : SstoreGasDenote.plan2929 SstoreGasDenote.berlinConsts r.toNat cold oz cz nz oc cn on = P
  cases cold <;> cases oz <;> cases cz <;> cases nz <;> cases oc <;> cases cn <;> cases on <;>
    sstore_case hP SstoreGasDenote.berlin_clearRef_eq

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- `_eita_sstore_gas_london` stores `plan2929 londonConsts` (EIP-3529 clear refund). -/
theorem london_sem (m : RM) (rest : List AInstr) (r : BitVec 64) (cold : Bool) (o c n : Evm.U256)
    (h1 : m.regs .x1 = r) (hr : r.toNat + 65536 < 2^63) (h5 : m.regs .x5 = b2v cold)
    (ho : loads m .x2 o) (hc : loads m .x3 c) (hn : loads m .x4 n) :
    (exec (entry "_eita_sstore_gas_london" (SstoreGas.eip2929A "london" SstoreGasDenote.londonConsts ++ rest)) m).map (outWords m)
      = some (BitVec.ofNat 64 (SstoreGasDenote.plan2929 SstoreGasDenote.londonConsts r.toNat cold (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).1,
              BitVec.ofNat 64 (SstoreGasDenote.plan2929 SstoreGasDenote.londonConsts r.toNat cold (pz o) (pz c) (pz n) (pe o c) (pe c n) (pe o n)).2) := by
  have hf := prologue_facts m o c n ho hc hn
  obtain ⟨h10, h11, h12, h13, h14, h15, hx0, hx1, hx5, hmem⟩ := hf
  rw [h1] at hx1
  rw [h5] at hx5
  clear ho hc hn
  sstore_unfold
  rw [exec_symLabel, exec_prologue]
  generalize runSL SstoreGas.prologueA m = m1 at h10 h11 h12 h13 h14 h15 hx0 hx1 hx5 hmem ⊢
  generalize pz o = oz at h10 ⊢
  generalize pz c = cz at h11 ⊢
  generalize pz n = nz at h12 ⊢
  generalize pe o c = oc at h13 ⊢
  generalize pe c n = cn at h14 ⊢
  generalize pe o n = on at h15 ⊢
  generalize hP : SstoreGasDenote.plan2929 SstoreGasDenote.londonConsts r.toNat cold oz cz nz oc cn on = P
  cases cold <;> cases oz <;> cases cz <;> cases nz <;> cases oc <;> cases cn <;> cases on <;>
    sstore_case hP SstoreGasDenote.london_clearRef_eq

/-! ## From the file to the routine

`instrs` is the five routines and the table in one list; the entry for a
symbol is that routine followed by whatever comes after it, and no routine
executes past its `ret`. -/

theorem entry_legacy :
    entry "_eita_sstore_gas_legacy" SstoreGas.instrs
      = entry "_eita_sstore_gas_legacy"
          (SstoreGas.legacyA ++ (SstoreGas.eip1283A ++ (SstoreGas.eip2200A ++
            (SstoreGas.eip2929A "berlin" SstoreGasDenote.berlinConsts ++
              (SstoreGas.eip2929A "london" SstoreGasDenote.londonConsts ++
                SstoreGas.accessTableA))))) := by
  simp only [SstoreGas.instrs, List.append_assoc, List.cons_append, List.nil_append]
  simp only [entry]

theorem entry_eip1283 :
    entry "_eita_sstore_gas_eip1283" SstoreGas.instrs
      = entry "_eita_sstore_gas_eip1283"
          (SstoreGas.eip1283A ++ (SstoreGas.eip2200A ++
            (SstoreGas.eip2929A "berlin" SstoreGasDenote.berlinConsts ++
              (SstoreGas.eip2929A "london" SstoreGasDenote.londonConsts ++
                SstoreGas.accessTableA)))) := by
  simp only [SstoreGas.instrs, List.append_assoc, List.cons_append, List.nil_append]
  simp only [entry]
  rw [entry_append_left]
  intro t ht
  simp [SstoreGas.legacyA, SstoreGas.isZeroA, Evm.CL.Frame.header] at ht
  subst ht; decide

theorem entry_eip2200 :
    entry "_eita_sstore_gas_eip2200" SstoreGas.instrs
      = entry "_eita_sstore_gas_eip2200"
          (SstoreGas.eip2200A ++
            (SstoreGas.eip2929A "berlin" SstoreGasDenote.berlinConsts ++
              (SstoreGas.eip2929A "london" SstoreGasDenote.londonConsts ++
                SstoreGas.accessTableA))) := by
  simp only [SstoreGas.instrs, List.append_assoc, List.cons_append, List.nil_append]
  simp only [entry]
  rw [entry_append_left, entry_append_left]
  · intro t ht
    simp [SstoreGas.eip1283A, SstoreGas.prologueA, SstoreGas.isZeroA, SstoreGas.isEqA,
          Evm.CL.Frame.header] at ht
    subst ht; decide
  · intro t ht
    simp [SstoreGas.legacyA, SstoreGas.isZeroA, Evm.CL.Frame.header] at ht
    subst ht; decide

theorem entry_berlin :
    entry "_eita_sstore_gas_berlin" SstoreGas.instrs
      = entry "_eita_sstore_gas_berlin"
          (SstoreGas.eip2929A "berlin" SstoreGasDenote.berlinConsts ++
            (SstoreGas.eip2929A "london" SstoreGasDenote.londonConsts ++
              SstoreGas.accessTableA)) := by
  simp only [SstoreGas.instrs, List.append_assoc, List.cons_append, List.nil_append]
  simp only [entry]
  rw [entry_append_left, entry_append_left, entry_append_left]
  · intro t ht
    simp [SstoreGas.eip2200A, SstoreGas.prologueA, SstoreGas.isZeroA, SstoreGas.isEqA,
          Evm.CL.Frame.header] at ht
    subst ht; decide
  · intro t ht
    simp [SstoreGas.eip1283A, SstoreGas.prologueA, SstoreGas.isZeroA, SstoreGas.isEqA,
          Evm.CL.Frame.header] at ht
    subst ht; decide
  · intro t ht
    simp [SstoreGas.legacyA, SstoreGas.isZeroA, Evm.CL.Frame.header] at ht
    subst ht; decide

theorem entry_london :
    entry "_eita_sstore_gas_london" SstoreGas.instrs
      = entry "_eita_sstore_gas_london"
          (SstoreGas.eip2929A "london" SstoreGasDenote.londonConsts ++ SstoreGas.accessTableA) := by
  simp only [SstoreGas.instrs, List.append_assoc, List.cons_append, List.nil_append]
  simp only [entry]
  rw [entry_append_left, entry_append_left, entry_append_left, entry_append_left]
  · intro t ht
    simp [SstoreGas.eip2929A, SstoreGas.prologueA, SstoreGas.isZeroA, SstoreGas.isEqA,
          Evm.CL.Frame.header] at ht
    subst ht; decide
  · intro t ht
    simp [SstoreGas.eip2200A, SstoreGas.prologueA, SstoreGas.isZeroA, SstoreGas.isEqA,
          Evm.CL.Frame.header] at ht
    subst ht; decide
  · intro t ht
    simp [SstoreGas.eip1283A, SstoreGas.prologueA, SstoreGas.isZeroA, SstoreGas.isEqA,
          Evm.CL.Frame.header] at ht
    subst ht; decide
  · intro t ht
    simp [SstoreGas.legacyA, SstoreGas.isZeroA, Evm.CL.Frame.header] at ht
    subst ht; decide

/-! ## Program → spec

With the plan theorems of `SstoreGasDenote`, each emitted routine IS its fork's
`sstoreGas`: nothing between the `AInstr` list and the spec is by inspection. -/

theorem legacy_is_sstoreGas (m : RM) (r : BitVec 64) (c n : Evm.U256)
    (h1 : m.regs .x1 = r) (hr : r.toNat + 65536 < 2^63)
    (hc : loads m .x3 c) (hn : loads m .x4 n) :
    (exec (entry "_eita_sstore_gas_legacy" SstoreGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 (Evm.Frontier.Vm.Instructions.sstoreGas r.toNat c n).1,
              BitVec.ofNat 64 (Evm.Frontier.Vm.Instructions.sstoreGas r.toNat c n).2) := by
  rw [entry_legacy, legacy_sem m _ r c n h1 hr hc hn]
  simp only [pz, SstoreGasDenote.legacy_eq_spec]

theorem eip1283_is_sstoreGas (m : RM) (r : BitVec 64) (o c n : Evm.U256)
    (h1 : m.regs .x1 = r) (hr : r.toNat + 65536 < 2^63)
    (ho : loads m .x2 o) (hc : loads m .x3 c) (hn : loads m .x4 n) :
    (exec (entry "_eita_sstore_gas_eip1283" SstoreGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 (Evm.Constantinople.Vm.Instructions.sstoreGas r.toNat o c n).1,
              BitVec.ofNat 64 (Evm.Constantinople.Vm.Instructions.sstoreGas r.toNat o c n).2) := by
  rw [entry_eip1283, eip1283_sem m _ r o c n h1 hr ho hc hn]
  simp only [pz, pe, SstoreGasDenote.eip1283_eq_spec]

theorem eip2200_is_sstoreGas (m : RM) (r : BitVec 64) (o c n : Evm.U256)
    (h1 : m.regs .x1 = r) (hr : r.toNat + 65536 < 2^63)
    (ho : loads m .x2 o) (hc : loads m .x3 c) (hn : loads m .x4 n) :
    (exec (entry "_eita_sstore_gas_eip2200" SstoreGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 (Evm.Istanbul.Vm.Instructions.sstoreGas r.toNat o c n).1,
              BitVec.ofNat 64 (Evm.Istanbul.Vm.Instructions.sstoreGas r.toNat o c n).2) := by
  rw [entry_eip2200, eip2200_sem m _ r o c n h1 hr ho hc hn]
  simp only [pz, pe, SstoreGasDenote.eip2200_eq_spec]

theorem berlin_is_sstoreGas (m : RM) (r : BitVec 64) (cold : Bool) (o c n : Evm.U256)
    (h1 : m.regs .x1 = r) (hr : r.toNat + 65536 < 2^63)
    (h5 : m.regs .x5 = b2v cold)
    (ho : loads m .x2 o) (hc : loads m .x3 c) (hn : loads m .x4 n) :
    (exec (entry "_eita_sstore_gas_berlin" SstoreGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 (Evm.Berlin.Vm.Instructions.Storage.sstoreGas r.toNat cold o c n).1,
              BitVec.ofNat 64 (Evm.Berlin.Vm.Instructions.Storage.sstoreGas r.toNat cold o c n).2) := by
  rw [entry_berlin, berlin_sem m _ r cold o c n h1 hr h5 ho hc hn]
  simp only [pz, pe, SstoreGasDenote.berlin_eq_spec]

theorem london_is_sstoreGas (m : RM) (r : BitVec 64) (cold : Bool) (o c n : Evm.U256)
    (h1 : m.regs .x1 = r) (hr : r.toNat + 65536 < 2^63)
    (h5 : m.regs .x5 = b2v cold)
    (ho : loads m .x2 o) (hc : loads m .x3 c) (hn : loads m .x4 n) :
    (exec (entry "_eita_sstore_gas_london" SstoreGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 (Evm.London.Vm.Effect.sstoreGas r.toNat cold o c n).1,
              BitVec.ofNat 64 (Evm.London.Vm.Effect.sstoreGas r.toNat cold o c n).2) := by
  rw [entry_london, london_sem m _ r cold o c n h1 hr h5 ho hc hn]
  simp only [pz, pe, SstoreGasDenote.london_eq_spec]

end Evm.CL.ARM64.SstoreGasSem
