/-
  Evm.CL.OpSem — `Op.denote` as a theorem about the op's instructions.

  `Op.toAInstrs` is the one source of a handler op's machine code; `Op.denote`
  is a separate, hand-written description of what the op does to the abstract
  machine `Mach`. A coarse denotation passes every proof stated over `Mach`
  while the instructions do something else — the JUMP low-limb compare
  (`pc := tos.l0` for a destination of 2^64 + k) and the CALL family's
  "gas is a host effect" both survived that way.

  This module closes the gap for the ops that hid bugs: it runs the op's
  instructions under the fragment semantics (`AsmRun.run`) from a register
  state that holds the `Mach` the denotation reads (`JumpView`, `MemView`),
  and proves the two agree — the instructions fault exactly when the
  denotation traps, and when they fall through, the registers and the
  struct hold what the denotation computed. A denotation that disagreed
  with the instructions would not prove.

  Pilot (B7a step 3): `jumpValidate`, `jumpiCheck` (JUMP / JUMPI) and
  `memExpandIfLen` (the RETURN/REVERT memory-expansion prologue, built from
  the same `memRangeInstrs` + `memExpandInstrs` gadgets as the CALL family's).
-/

import Evm.CL.ARM64.MemCommitSem

namespace Evm.CL.OpSem

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun
open Evm.CL.ARM64.MemCommitSem (toNat_ofNat64 words_bv oldWords_bv
  aligned_bv mcost_bv mcost_mono wordsOf wordsOf_le mcost ecost msAt capAt run_cons_blsLbl)

/-! ## Bit-vector facts -/

theorem ofNat64_eq_zero (n : Nat) (h : n < 2 ^ 64) : BitVec.ofNat 64 n = (0 : BitVec 64) ↔ n = 0 := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; rwa [toNat_ofNat64 n h] at this
  · rintro rfl; rfl

theorem or_or_eq_zero (a b c : BitVec 64) : a ||| b ||| c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  simp [BitVec.or_eq_zero_iff, and_assoc]

theorem sub_eq_zero' (a b : BitVec 64) : a - b = 0 ↔ a = b := by
  constructor
  · intro h; rw [← BitVec.sub_add_cancel a b, h]; simp
  · rintro rfl; simp

/-! The condition codes after `cmp a, b`, as `Nat` comparisons (no `bv_decide`:
the pilot's closure stays propext/Quot.sound/Classical.choice). -/

theorem hs_subFlags' (a b : BitVec 64) : bcHolds .hs (subFlags a b) = decide (b.toNat ≤ a.toNat) := by
  simp [bcHolds, subFlags, BitVec.le_def]
theorem lo_subFlags (a b : BitVec 64) : bcHolds .lo (subFlags a b) = decide (a.toNat < b.toNat) := by
  simp only [bcHolds, subFlags, BitVec.le_def]
  by_cases h : a.toNat < b.toNat <;> simp [h] <;> omega
theorem hi_subFlags (a b : BitVec 64) : bcHolds .hi (subFlags a b) = decide (b.toNat < a.toNat) := by
  simp only [bcHolds, subFlags, sub_eq_zero', BitVec.le_def]
  by_cases h : a = b
  · subst h; simp
  · have : a.toNat ≠ b.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    by_cases h2 : b.toNat < a.toNat <;> simp [h, h2] <;> omega
theorem ls_subFlags (a b : BitVec 64) : bcHolds .ls (subFlags a b) = decide (a.toNat ≤ b.toNat) := by
  simp only [bcHolds, subFlags, sub_eq_zero', BitVec.le_def]
  by_cases h : a = b
  · subst h; simp
  · have : a.toNat ≠ b.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    by_cases h2 : a.toNat ≤ b.toNat <;> simp [h, h2] <;> omega

/-- `ldrb` then `cmp w, #1 ; b.ne`: the branch is taken iff the byte is not 1. -/
theorem ne_byte_one (b : BitVec 8) :
    bcHolds .ne (subFlags (b.zeroExtend 64) (BitVec.ofNat 64 1)) = true ↔ b ≠ 1#8 := by
  simp only [bcHolds, subFlags, sub_eq_zero', Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · intro h e; apply h; subst e; rfl
  · intro h e; apply h
    have := congrArg BitVec.toNat e
    simp [BitVec.toNat_setWidth] at this
    apply BitVec.eq_of_toNat_eq; simp; have := b.isLt; omega

@[simp] theorem step_cmpImmWHex (s : RS) (a : Reg) (i : Nat) :
    AsmRun.step s (.cmpImmWHex a i) = some (s.withFlags (subFlags (s.regs a) (BitVec.ofNat 64 i))) := rfl
@[simp] theorem step_ldrbReg (s : RS) (d b i : Reg) :
    AsmRun.step s (.ldrbReg d b i) = some (s.set d ((s.mem (s.regs b + s.regs i)).zeroExtend 64)) := rfl

/-! ## JUMP: `jumpValidate` -/

/-- What the JUMP ops read, held in a register state: TOS in x6-x9 (limbs below
    2^64), `code_size` at EvmState #72, and the valid-JUMPDEST map behind the
    pointer at #136 (byte `d` is 1 iff `d` is a valid destination). -/
structure JumpView (m : Mach) (s : RS) : Prop where
  x6 : s.regs .x6 = BitVec.ofNat 64 m.tos.l0
  x7 : s.regs .x7 = BitVec.ofNat 64 m.tos.l1
  x8 : s.regs .x8 = BitVec.ofNat 64 m.tos.l2
  x9 : s.regs .x9 = BitVec.ofNat 64 m.tos.l3
  l0 : m.tos.l0 < 2 ^ 64
  l1 : m.tos.l1 < 2 ^ 64
  l2 : m.tos.l2 < 2 ^ 64
  l3 : m.tos.l3 < 2 ^ 64
  codeSize : ld64 s.mem (s.regs .x20 + BitVec.ofNat 64 72) = BitVec.ofNat 64 m.codeSize
  codeSizeLt : m.codeSize < 2 ^ 64
  jumpMap : ∀ d, d < 2 ^ 64 →
    (s.mem (ld64 s.mem (s.regs .x20 + BitVec.ofNat 64 136) + BitVec.ofNat 64 d) = 1#8 ↔ m.jumpDest d = true)

/-- The destination test both the denotation and the instructions make. -/
def jumpOk (m : Mach) : Prop :=
  m.tos.l1 = 0 ∧ m.tos.l2 = 0 ∧ m.tos.l3 = 0 ∧ m.tos.l0 < m.codeSize ∧ m.jumpDest m.tos.l0 = true

instance (m : Mach) : Decidable (jumpOk m) := by unfold jumpOk; infer_instance

/-- The destination check as the instructions make it, from the state the
    jump ops see: either the run falls through with pc (x21) = the destination,
    or it exits to `_eita_invalid_jump` — and which one is `jumpOk`. Only x14,
    x21 and the flags change. -/
theorem destCheck_run (H : Helpers) (m : Mach) (s : RS) (v : JumpView m s) :
    (jumpOk m → ∃ s', run H ([ .orr3 .x14 .x7 .x8, .orr3 .x14 .x14 .x9, .cbnzSym .x14 "_eita_invalid_jump",
        .ldrOff .x14 .x20 72, .cmpReg .x6 .x14, .bSym .hs "_eita_invalid_jump" ] ++ jumpDestInstrs ++
        [ .movReg .x21 .x6 ]) s = .done s' ∧ s'.regs .x21 = BitVec.ofNat 64 m.tos.l0 ∧
        s'.mem = s.mem ∧ s'.sp = s.sp ∧ ∀ r, r ≠ .x14 → r ≠ .x21 → s'.regs r = s.regs r) ∧
    (¬ jumpOk m → ∃ s', run H ([ .orr3 .x14 .x7 .x8, .orr3 .x14 .x14 .x9, .cbnzSym .x14 "_eita_invalid_jump",
        .ldrOff .x14 .x20 72, .cmpReg .x6 .x14, .bSym .hs "_eita_invalid_jump" ] ++ jumpDestInstrs ++
        [ .movReg .x21 .x6 ]) s = .fault "_eita_invalid_jump" s') := by
  have hhi : (s.regs .x7 ||| s.regs .x8 ||| s.regs .x9 = (0 : BitVec 64)) ↔
      (m.tos.l1 = 0 ∧ m.tos.l2 = 0 ∧ m.tos.l3 = 0) := by
    rw [or_or_eq_zero, v.x7, v.x8, v.x9, ofNat64_eq_zero _ v.l1, ofNat64_eq_zero _ v.l2,
        ofNat64_eq_zero _ v.l3]
  have hlt : bcHolds .hs (subFlags (s.regs .x6) (ld64 s.mem (s.regs .x20 + BitVec.ofNat 64 72))) = true ↔
      ¬ m.tos.l0 < m.codeSize := by
    rw [hs_subFlags', v.x6, v.codeSize, toNat_ofNat64 _ v.l0, toNat_ofNat64 _ v.codeSizeLt]; simp
  have hmap := v.jumpMap m.tos.l0 v.l0
  rw [← v.x6] at hmap
  simp only [jumpDestInstrs, List.cons_append, List.nil_append]
  rw [run_cons_step H _ _ _ _ rfl rfl, run_cons_step H _ _ _ _ rfl rfl,
      run_cons_condFar H _ _ _ _ _ rfl]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have hz := hhi.mpr ⟨h1, h2, h3⟩
    rw [if_neg (by simp [hz]), run_cons_step H _ _ _ _ rfl rfl, run_cons_step H _ _ _ _ rfl rfl,
        run_cons_condFar H _ _ _ _ _ rfl, if_neg (by simpa using fun h => (hlt.mp h) h4),
        run_cons_step H _ _ _ _ rfl rfl, run_cons_step H _ _ _ _ rfl (step_ldrbReg ..),
        run_cons_step H _ _ _ _ rfl (step_cmpImmWHex ..), run_cons_condFar H _ _ _ _ _ rfl,
        if_neg (by simp only [AsmRun.set_regs, AsmRun.set_mem, AsmRun.withFlags_flags,
          AsmRun.withFlags_regs, AsmRun.withFlags_mem, ite_true, reduceCtorEq,
          ite_false]; rw [ne_byte_one]; exact fun h => h (hmap.mpr h5)),
        run_cons_step H _ _ _ _ rfl rfl, run_nil]
    refine ⟨_, rfl, ?_, rfl, rfl, ?_⟩
    · simp [v.x6]
    · intro r h14 h21; simp [h14, h21]
  · intro hno
    by_cases h1 : m.tos.l1 = 0 ∧ m.tos.l2 = 0 ∧ m.tos.l3 = 0
    · have hz := hhi.mpr h1
      rw [if_neg (by simp [hz]), run_cons_step H _ _ _ _ rfl rfl, run_cons_step H _ _ _ _ rfl rfl,
          run_cons_condFar H _ _ _ _ _ rfl]
      by_cases h4 : m.tos.l0 < m.codeSize
      · have h5 : ¬ m.jumpDest m.tos.l0 = true := fun h5 => hno ⟨h1.1, h1.2.1, h1.2.2, h4, h5⟩
        rw [if_neg (by simpa using fun h => (hlt.mp h) h4),
            run_cons_step H _ _ _ _ rfl rfl, run_cons_step H _ _ _ _ rfl (step_ldrbReg ..),
            run_cons_step H _ _ _ _ rfl (step_cmpImmWHex ..), run_cons_condFar H _ _ _ _ _ rfl,
            if_pos (by simp only [AsmRun.set_regs, AsmRun.set_mem, AsmRun.withFlags_flags,
              AsmRun.withFlags_regs, AsmRun.withFlags_mem, ite_true, reduceCtorEq,
              ite_false]; rw [ne_byte_one]; exact fun h => h5 (hmap.mp h))]
        exact ⟨_, rfl⟩
      · rw [if_pos (by simpa using hlt.mpr h4)]
        exact ⟨_, rfl⟩
    · rw [if_pos (by simp only [AsmRun.set_regs, ite_true]; exact decide_eq_true (fun h => h1 (hhi.mp h)))]
      exact ⟨_, rfl⟩

/-- **JUMP's destination check is what its instructions do.** From a state that
    holds the `Mach` (`JumpView`, an untrapped machine), the instructions fall
    through exactly when `Op.denote .jumpValidate` does not trap, with pc (x21)
    the denotation's pc; otherwise they exit to `_eita_invalid_jump`. The
    denotation `pc := tos.l0` that passed every proof while the instructions
    compared only the low limb cannot be stated here: it would not prove. -/
theorem jumpValidate_sem (H : Helpers) (m : Mach) (s : RS) (v : JumpView m s) (ht : m.trap = false) :
    (∃ s', run H (Op.toAInstrs .jumpValidate) s = .done s' ∧
       (Op.denote .jumpValidate m).trap = false ∧
       s'.regs .x21 = BitVec.ofNat 64 (Op.denote .jumpValidate m).pcReg) ∨
    (∃ s', run H (Op.toAInstrs .jumpValidate) s = .fault "_eita_invalid_jump" s' ∧
       (Op.denote .jumpValidate m).trap = true) := by
  have hd := destCheck_run H m s v
  by_cases h : jumpOk m
  · obtain ⟨s', hr, h21, -⟩ := hd.1 h
    have h' := h; unfold jumpOk at h'
    left; refine ⟨s', hr, ?_, ?_⟩
    · simp only [Op.denote]; rw [if_pos h']; exact ht
    · simp only [Op.denote]; rw [if_pos h']; exact h21
  · obtain ⟨s', hr⟩ := hd.2 h
    have h' := h; unfold jumpOk at h'
    right; refine ⟨s', hr, ?_⟩
    simp only [Op.denote]; rw [if_neg h']

/-! ## JUMPI: `jumpiCheck` -/

/-- JUMPI also reads the condition, NOS, in x10-x13. -/
structure JumpiView (m : Mach) (s : RS) : Prop extends JumpView m s where
  x10 : s.regs .x10 = BitVec.ofNat 64 m.nos.l0
  x11 : s.regs .x11 = BitVec.ofNat 64 m.nos.l1
  x12 : s.regs .x12 = BitVec.ofNat 64 m.nos.l2
  x13 : s.regs .x13 = BitVec.ofNat 64 m.nos.l3
  n0 : m.nos.l0 < 2 ^ 64
  n1 : m.nos.l1 < 2 ^ 64
  n2 : m.nos.l2 < 2 ^ 64
  n3 : m.nos.l3 < 2 ^ 64

theorem or_or_or_eq_zero (a b c d : BitVec 64) :
    a ||| b ||| (c ||| d) = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  simp [BitVec.or_eq_zero_iff, and_assoc]

theorem destCheck_closed :
    closed ([ .orr3 .x14 .x7 .x8, .orr3 .x14 .x14 .x9, .cbnzSym .x14 "_eita_invalid_jump",
      .ldrOff .x14 .x20 72, .cmpReg .x6 .x14, .bSym .hs "_eita_invalid_jump" ] ++ jumpDestInstrs ++
      [ AInstr.movReg .x21 .x6 ]) := by
  simp [closed, refLabel, ctrl, jumpDestInstrs]

/-- A state that differs from a `JumpView` one only in registers the check
    does not read still holds the view. -/
theorem JumpView.congr {m : Mach} {s t : RS} (v : JumpView m s) (hm : t.mem = s.mem)
    (hr : ∀ r, r = .x6 ∨ r = .x7 ∨ r = .x8 ∨ r = .x9 ∨ r = .x20 → t.regs r = s.regs r) :
    JumpView m t where
  x6 := by rw [hr _ (by simp)]; exact v.x6
  x7 := by rw [hr _ (by simp)]; exact v.x7
  x8 := by rw [hr _ (by simp)]; exact v.x8
  x9 := by rw [hr _ (by simp)]; exact v.x9
  l0 := v.l0
  l1 := v.l1
  l2 := v.l2
  l3 := v.l3
  codeSize := by rw [hm, hr _ (by simp)]; exact v.codeSize
  codeSizeLt := v.codeSizeLt
  jumpMap := by rw [hm, hr _ (by simp)]; exact v.jumpMap

def nosZero (m : Mach) : Prop := m.nos.l0 = 0 ∧ m.nos.l1 = 0 ∧ m.nos.l2 = 0 ∧ m.nos.l3 = 0

/-- **JUMPI's check is what its instructions do.** A zero condition (all four
    limbs) leaves the machine alone: the instructions branch to
    `_eita_jumpi_fallthrough`, a label outside this op (`jumpiTailGas` places
    it as `b _eita_jumpi_pop`, the label this op ends on), so the fragment ends
    there with pc (x21) untouched. A nonzero condition faces JUMP's
    destination check: fall through with pc = the destination exactly when
    `Op.denote .jumpiCheck` does not trap, else `_eita_invalid_jump`. -/
theorem jumpiCheck_sem (H : Helpers) (m : Mach) (s : RS) (v : JumpiView m s) (ht : m.trap = false) :
    (nosZero m → ∃ s', run H (Op.toAInstrs .jumpiCheck) s = .done s' ∧
       Op.denote .jumpiCheck m = m ∧ s'.regs .x21 = s.regs .x21) ∧
    (¬ nosZero m →
      (∃ s', run H (Op.toAInstrs .jumpiCheck) s = .done s' ∧
         (Op.denote .jumpiCheck m).trap = false ∧
         s'.regs .x21 = BitVec.ofNat 64 (Op.denote .jumpiCheck m).pcReg) ∨
      (∃ s', run H (Op.toAInstrs .jumpiCheck) s = .fault "_eita_invalid_jump" s' ∧
         (Op.denote .jumpiCheck m).trap = true)) := by
  have hz : (s.regs .x10 ||| s.regs .x11 ||| (s.regs .x12 ||| s.regs .x13) = 0) ↔ nosZero m := by
    rw [or_or_or_eq_zero, v.x10, v.x11, v.x12, v.x13, ofNat64_eq_zero _ v.n0,
        ofNat64_eq_zero _ v.n1, ofNat64_eq_zero _ v.n2, ofNat64_eq_zero _ v.n3]; rfl
  have hsplit : Op.toAInstrs .jumpiCheck =
      .orr3 .x14 .x10 .x11 :: .orr3 .x15 .x12 .x13 :: .orr3 .x14 .x14 .x15 ::
        .cbzLbl .x14 "_eita_jumpi_fallthrough" ::
      (([ .orr3 .x14 .x7 .x8, .orr3 .x14 .x14 .x9, .cbnzSym .x14 "_eita_invalid_jump",
        .ldrOff .x14 .x20 72, .cmpReg .x6 .x14, .bSym .hs "_eita_invalid_jump" ] ++ jumpDestInstrs ++
        [ AInstr.movReg .x21 .x6 ]) ++ [ .label "_eita_jumpi_pop" ]) := by
    simp [Op.toAInstrs, jumpDestInstrs]
  rw [hsplit, run_cons_step H _ _ _ _ rfl (step_orr3 ..), run_cons_step H _ _ _ _ rfl (step_orr3 ..),
      run_cons_step H _ _ _ _ rfl (step_orr3 ..)]
  rw [show ∀ (t : RS) (rest : List AInstr), run H (.cbzLbl .x14 "_eita_jumpi_fallthrough" :: rest) t =
      if t.regs .x14 = 0 then run H (AsmRun.skipTo "_eita_jumpi_fallthrough" rest) t else run H rest t from
      fun t rest => by simp [run, ctrl]]
  simp only [AsmRun.set_regs, ite_true, reduceCtorEq, ite_false]
  constructor
  · intro h0
    rw [if_pos (hz.mpr h0)]
    rw [show AsmRun.skipTo "_eita_jumpi_fallthrough"
        (([ .orr3 .x14 .x7 .x8, .orr3 .x14 .x14 .x9, .cbnzSym .x14 "_eita_invalid_jump",
          .ldrOff .x14 .x20 72, .cmpReg .x6 .x14, .bSym .hs "_eita_invalid_jump" ] ++ jumpDestInstrs ++
          [ AInstr.movReg .x21 .x6 ]) ++ [ .label "_eita_jumpi_pop" ]) = [] from by
        simp [AsmRun.skipTo, jumpDestInstrs], run_nil]
    refine ⟨_, rfl, ?_, by simp⟩
    have h0' := h0; unfold nosZero at h0'
    simp only [Op.denote]; rw [if_pos h0']
  · intro h0
    have h0' := h0; unfold nosZero at h0'
    rw [if_neg (fun h => h0 (hz.mp h)), run_append H _ _ _ destCheck_closed]
    have v' : JumpView m _ := v.toJumpView.congr (t := ((s.set .x14 (s.regs .x10 ||| s.regs .x11)).set .x15
        (s.regs .x12 ||| s.regs .x13)).set .x14 ((s.regs .x10 ||| s.regs .x11) ||| (s.regs .x12 ||| s.regs .x13)))
      rfl (by intro r hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp)
    have hd := destCheck_run H m _ v'
    by_cases h : jumpOk m
    · obtain ⟨s', hr, h21, -⟩ := hd.1 h
      have h' := h; unfold jumpOk at h'
      left; rw [hr]; refine ⟨s', by simp [run_cons_label], ?_, ?_⟩
      · simp only [Op.denote]; rw [if_neg h0', if_pos h']; exact ht
      · simp only [Op.denote]; rw [if_neg h0', if_pos h']; exact h21
    · obtain ⟨s', hr⟩ := hd.2 h
      have h' := h; unfold jumpOk at h'
      right; rw [hr]; refine ⟨s', rfl, ?_⟩
      simp only [Op.denote]; rw [if_neg h0', if_neg h']

/-! ## The memory-expansion gadget (`memExpandInstrs`)

The interpreter's form of the gadget the CALL family, CREATE, the COPY family,
KECCAK256, LOG and RETURN/REVERT share: new end in x0, the quadratic delta
added into the accumulator x17, `memory_size` (#48) raised, `_eita_oog` past
the capacity (#56). The JIT's flush form (`memExpandFlushT`, proved in
`MemCommitSem.memExpand_run`) charges x22 directly; this one accumulates. -/

theorem run_cons_bhiOog (H : Helpers) (rest : List AInstr) (s : RS) :
    run H (.bhiOog :: rest) s = if bcHolds .hi s.flags then .fault "_eita_oog" s else run H rest s := by
  simp [run, ctrl]

/-- The cost block of `memExpandInstrs`, skipped when no word is added. -/
theorem skipTo_7_interp (r : List AInstr) :
    AsmRun.skipTo "7f" (.mulReg .x16 .x14 .x14 :: .addLsr .x16 .x14 .x16 9 :: .addLsl .x16 .x16 .x14 1 ::
      .mulReg .x14 .x15 .x15 :: .addLsr .x14 .x15 .x14 9 :: .addLsl .x14 .x14 .x15 1 ::
      .subReg .x16 .x16 .x14 :: .addReg .x17 .x17 .x16 ::
      .addImm .x14 .x0 31 :: .lsrImm .x14 .x14 5 :: .lslImm .x14 .x14 5 :: .strOff .x14 .x20 48 ::
      .label "7" :: r) = .label "7" :: r := by
  simp [AsmRun.skipTo]

/-- `memExpandInstrs` from a new end `e` in x0: `_eita_oog` past the capacity,
    else EELS's expansion delta (`ecost`, = `Gas.memoryExpansionCost`) added into
    x17 and `memory_size` raised to the aligned new end when it grows. -/
theorem memExpandInstrs_run (H : Helpers) (st : BitVec 64) (e : Nat) (rest : List AInstr) (s : RS)
    (h20 : s.regs .x20 = st) (h0 : s.regs .x0 = BitVec.ofNat 64 e) (he : e < 2 ^ 64)
    (hcap : (capAt s.mem st).toNat < 2 ^ 32) (hms : (msAt s.mem st).toNat ≤ (capAt s.mem st).toNat)
    (h17 : (s.regs .x17).toNat < 2 ^ 63) :
    ((capAt s.mem st).toNat < e → ∃ sf, run H (memExpandInstrs ++ rest) s = .fault "_eita_oog" sf) ∧
    (e ≤ (capAt s.mem st).toNat →
      ∃ s', run H (memExpandInstrs ++ rest) s = run H rest s' ∧ s'.sp = s.sp ∧
        (s'.regs .x17).toNat = (s.regs .x17).toNat + ecost ((msAt s.mem st).toNat / 32) (wordsOf e) ∧
        (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → s'.regs r = s.regs r) ∧
        (msAt s'.mem st).toNat =
          (if wordsOf e ≤ (msAt s.mem st).toNat / 32 then (msAt s.mem st).toNat else 32 * wordsOf e)) := by
  have hcapE : capAt s.mem st = ld64 s.mem (st + BitVec.ofNat 64 56) := rfl
  have hmsE : msAt s.mem st = ld64 s.mem (st + BitVec.ofNat 64 48) := rfl
  simp only [memExpandInstrs, List.cons_append, List.nil_append]
  rw [run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..),
      run_cons_step H _ _ _ _ (ctrl_cmpReg ..) (step_cmpReg ..), run_cons_bhiOog]
  rs_simp
  rw [h20, h0, hi_subFlags, toNat_ofNat64 _ he, ← hcapE]
  refine ⟨fun hlt => ⟨_, by rw [if_pos (by simpa using hlt)]⟩, fun hle => ?_⟩
  rw [if_neg (by simp; omega),
      run_cons_step H _ _ _ _ (ctrl_addImm ..) (step_addImm ..),
      run_cons_step H _ _ _ _ (ctrl_lsrImm ..) (step_lsrImm ..),
      run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..),
      run_cons_step H _ _ _ _ (ctrl_lsrImm ..) (step_lsrImm ..),
      run_cons_step H _ _ _ _ (ctrl_cmpReg ..) (step_cmpReg ..),
      run_cons_blsLbl]
  rs_simp
  rw [h20, h0, ls_subFlags, words_bv e (by omega), oldWords_bv, ← hmsE]
  by_cases hw : wordsOf e ≤ (msAt s.mem st).toNat / 32
  · rw [if_pos (by simpa using hw), skipTo_7_interp, run_cons_label]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
    · rs_simp
    · rs_simp; unfold ecost; rw [if_pos hw]; simp
    · intro r h14 h15 h16 h17; rs_simp; simp [h14, h15]
    · rs_simp; rw [if_pos hw]
  · rw [if_neg (by simpa using hw),
        run_cons_step H _ _ _ _ (ctrl_mulReg ..) (step_mulReg ..),
        run_cons_step H _ _ _ _ (ctrl_addLsr ..) (step_addLsr ..),
        run_cons_step H _ _ _ _ (ctrl_addLsl ..) (step_addLsl ..),
        run_cons_step H _ _ _ _ (ctrl_mulReg ..) (step_mulReg ..),
        run_cons_step H _ _ _ _ (ctrl_addLsr ..) (step_addLsr ..),
        run_cons_step H _ _ _ _ (ctrl_addLsl ..) (step_addLsl ..),
        run_cons_step H _ _ _ _ (ctrl_subReg ..) (step_subReg ..),
        run_cons_step H _ _ _ _ (ctrl_addReg ..) (step_addReg ..),
        run_cons_step H _ _ _ _ (ctrl_addImm ..) (step_addImm ..),
        run_cons_step H _ _ _ _ (ctrl_lsrImm ..) (step_lsrImm ..),
        run_cons_step H _ _ _ _ (ctrl_lslImm ..) (step_lslImm ..),
        run_cons_step H _ _ _ _ (ctrl_strOff ..) (step_strOff ..),
        run_cons_label]
    have hnw : ((BitVec.ofNat 64 e + BitVec.ofNat 64 31) >>> 5).toNat < 2 ^ 28 := by
      rw [words_bv e (by omega)]; exact wordsOf_le e _ hle hcap
    have how : ((msAt s.mem st) >>> 5).toNat < 2 ^ 28 := by
      rw [oldWords_bv]; omega
    have hle' : (msAt s.mem st >>> 5 + (msAt s.mem st >>> 5 * (msAt s.mem st >>> 5)) >>> 9 + msAt s.mem st >>> 5 <<< 1) ≤
        ((BitVec.ofNat 64 e + BitVec.ofNat 64 31) >>> 5 +
          ((BitVec.ofNat 64 e + BitVec.ofNat 64 31) >>> 5 * ((BitVec.ofNat 64 e + BitVec.ofNat 64 31) >>> 5)) >>> 9 +
          (BitVec.ofNat 64 e + BitVec.ofNat 64 31) >>> 5 <<< 1) := by
      rw [BitVec.le_def, mcost_bv _ hnw, mcost_bv _ how, words_bv e (by omega), oldWords_bv]
      exact mcost_mono (by omega)
    have hcostv : (((BitVec.ofNat 64 e + BitVec.ofNat 64 31) >>> 5 +
          ((BitVec.ofNat 64 e + BitVec.ofNat 64 31) >>> 5 * ((BitVec.ofNat 64 e + BitVec.ofNat 64 31) >>> 5)) >>> 9 +
          (BitVec.ofNat 64 e + BitVec.ofNat 64 31) >>> 5 <<< 1) -
        (msAt s.mem st >>> 5 + (msAt s.mem st >>> 5 * (msAt s.mem st >>> 5)) >>> 9 + msAt s.mem st >>> 5 <<< 1)).toNat =
        ecost ((msAt s.mem st).toNat / 32) (wordsOf e) := by
      rw [BitVec.toNat_sub_of_le hle', mcost_bv _ hnw, mcost_bv _ how, words_bv e (by omega), oldWords_bv]
      unfold ecost; rw [if_neg hw]
    have hsmall : ecost ((msAt s.mem st).toNat / 32) (wordsOf e) < 2 ^ 62 := by
      have : wordsOf e < 2 ^ 28 := wordsOf_le e _ hle hcap
      unfold ecost mcost; rw [if_neg hw]
      have : wordsOf e * wordsOf e < 2 ^ 56 := by
        have := Nat.mul_lt_mul_of_lt_of_lt this this; omega
      omega
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
    · rs_simp
    · rs_simp
      generalize hX : ((BitVec.ofNat 64 e + BitVec.ofNat 64 31) >>> 5 +
          ((BitVec.ofNat 64 e + BitVec.ofNat 64 31) >>> 5 * ((BitVec.ofNat 64 e + BitVec.ofNat 64 31) >>> 5)) >>> 9 +
          (BitVec.ofNat 64 e + BitVec.ofNat 64 31) >>> 5 <<< 1) -
        (msAt s.mem st >>> 5 + (msAt s.mem st >>> 5 * (msAt s.mem st >>> 5)) >>> 9 + msAt s.mem st >>> 5 <<< 1) = X at hcostv ⊢
      rw [BitVec.toNat_add, hcostv, Nat.mod_eq_of_lt (by omega)]
    · intro r h14 h15 h16 h17; rs_simp; simp [h14, h15, h16, h17]
    · rs_simp
      rw [h20, if_neg hw]
      try rw [h0]
      show (ld64 (st64 _ (off st 48) _) (off st 48)).toNat = _
      rw [ld64_st64_same, aligned_bv e (by omega) (by unfold wordsOf; omega)]

/-! ## One (offset, length) range: `memRangeInstrs` -/

/-- The address of stack word `sp − k` (x24 + 32·(x23 − k)). -/
def slot (s : RS) (k : Nat) : BitVec 64 := s.regs .x24 + ((s.regs .x23 - BitVec.ofNat 64 k) <<< 5)

/-- Stack word `sp − k` holds `w` (four limbs below 2^64, little-endian). -/
structure SlotHolds (s : RS) (k : Nat) (w : AsmCore.U256) : Prop where
  h0 : ld64 s.mem (slot s k + BitVec.ofNat 64 0) = BitVec.ofNat 64 w.l0
  h1 : ld64 s.mem (slot s k + BitVec.ofNat 64 8) = BitVec.ofNat 64 w.l1
  h2 : ld64 s.mem (slot s k + BitVec.ofNat 64 16) = BitVec.ofNat 64 w.l2
  h3 : ld64 s.mem (slot s k + BitVec.ofNat 64 24) = BitVec.ofNat 64 w.l3
  b0 : w.l0 < 2 ^ 64
  b1 : w.l1 < 2 ^ 64
  b2 : w.l2 < 2 ^ 64
  b3 : w.l3 < 2 ^ 64

theorem SlotHolds.hi_zero {s : RS} {k : Nat} {w : AsmCore.U256} (h : SlotHolds s k w) :
    (ld64 s.mem (slot s k + BitVec.ofNat 64 8) ||| ld64 s.mem (slot s k + BitVec.ofNat 64 16) |||
      ld64 s.mem (slot s k + BitVec.ofNat 64 24) = (0 : BitVec 64)) ↔ (w.l1 = 0 ∧ w.l2 = 0 ∧ w.l3 = 0) := by
  rw [h.h1, h.h2, h.h3, or_or_eq_zero, ofNat64_eq_zero _ h.b1, ofNat64_eq_zero _ h.b2, ofNat64_eq_zero _ h.b3]

theorem run_cons_cbnzOog (H : Helpers) (r : Reg) (rest : List AInstr) (s : RS) :
    run H (.cbnzOog r :: rest) s = if s.regs r ≠ 0 then .fault "_eita_oog" s else run H rest s := by
  simp [run, ctrl]
theorem run_cons_bcsOog (H : Helpers) (rest : List AInstr) (s : RS) :
    run H (.bcsOog :: rest) s = if bcHolds .hs s.flags then .fault "_eita_oog" s else run H rest s := by
  simp [run, ctrl]
theorem run_cons_cbzLbl (H : Helpers) (r : Reg) (l : String) (rest : List AInstr) (s : RS) :
    run H (.cbzLbl r l :: rest) s = if s.regs r = 0 then run H (AsmRun.skipTo l rest) s else run H rest s := by
  simp [run, ctrl]
theorem run_cons_bLbl (H : Helpers) (l : String) (rest : List AInstr) (s : RS) :
    run H (.bLbl l :: rest) s = run H (AsmRun.skipTo l rest) s := by
  simp [run, ctrl]

/-- `memRangeInstrs` over the range (offset at `sp − offP`, length at `sp − lenP`):
    `_eita_oog` exactly when `memRangeEnd` is `none` (the true end is past 2^64),
    else the end in `dst`, with memory, sp and every register but the four
    scratch registers and `dst` unchanged. -/
theorem memRange_run (H : Helpers) (lenP offP : Nat) (dst : Reg) (L0 L1 : String) (rest : List AInstr)
    (s : RS) (off len : AsmCore.U256) (hl : SlotHolds s lenP len) (ho : SlotHolds s offP off)
    (hd : dst ≠ .x14 ∧ dst ≠ .x15 ∧ dst ≠ .x16 ∧ dst ≠ .x17 ∧ dst ≠ .x23 ∧ dst ≠ .x24)
    (hL : (L1 == L0 || L1 == L0 ++ "f") = false) :
    (memRangeEnd off len = none →
      ∃ sf, run H (memRangeInstrs lenP offP dst L0 L1 ++ rest) s = .fault "_eita_oog" sf) ∧
    (∀ e, memRangeEnd off len = some e →
      ∃ s', run H (memRangeInstrs lenP offP dst L0 L1 ++ rest) s = run H rest s' ∧
        s'.regs dst = BitVec.ofNat 64 e ∧ s'.mem = s.mem ∧ s'.sp = s.sp ∧ e < 2 ^ 64 ∧
        (∀ r, r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x17 → r ≠ dst → s'.regs r = s.regs r)) := by
  obtain ⟨d14, d15, d16, d17, d23, d24⟩ := hd
  have hsl : ∀ k, s.regs .x24 + ((s.regs .x23 - BitVec.ofNat 64 k) <<< 5) = slot s k := fun _ => rfl
  simp only [memRangeInstrs, List.cons_append, List.nil_append]
  rw [run_cons_step H _ _ _ _ (ctrl_subImm ..) (step_subImm ..),
      run_cons_step H _ _ _ _ (ctrl_addLsl5 ..) (step_addLsl5 ..),
      run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..),
      run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..),
      run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..),
      run_cons_step H _ _ _ _ (ctrl_orr3 ..) (step_orr3 ..),
      run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..),
      run_cons_step H _ _ _ _ (ctrl_orr3 ..) (step_orr3 ..),
      run_cons_cbnzOog]
  rs_simp
  rw [hsl]
  have hcarry : ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 →
      bcHolds .hs (addFlags (BitVec.ofNat 64 a) (BitVec.ofNat 64 b)) = decide (2 ^ 64 ≤ a + b) := by
    intro a b ha hb
    simp only [bcHolds, addFlags, toNat_ofNat64 _ ha, toNat_ofNat64 _ hb]
  by_cases hlh : len.l1 = 0 ∧ len.l2 = 0 ∧ len.l3 = 0
  · rw [if_neg (by simpa [and_assoc] using hl.hi_zero.mpr hlh),
        run_cons_step H _ _ _ _ (ctrl_subImm ..) (step_subImm ..),
        run_cons_step H _ _ _ _ (ctrl_addLsl5 ..) (step_addLsl5 ..), run_cons_cbzLbl]
    rs_simp
    rw [hsl, hl.h0]
    simp only [ofNat64_eq_zero _ hl.b0]
    by_cases hl0 : len.l0 = 0
    · -- zero length: end 0, any offset
      have hE : memRangeEnd off len = some 0 := by simp [memRangeEnd, hlh, hl0]
      rw [if_pos hl0]
      simp only [AsmRun.skipTo, beq_self_eq_true, Bool.true_or, ite_true, reduceCtorEq, ite_false,
        Bool.false_eq_true]
      rw [run_cons_label, run_cons_step H _ _ _ _ (ctrl_movImm ..) (step_movImm ..), run_cons_label]
      refine ⟨fun h => (by rw [hE] at h; cases h), fun e he' => ?_⟩
      rw [hE] at he'; cases he'
      refine ⟨_, rfl, by rs_simp, by rs_simp, by rs_simp, by decide, ?_⟩
      intro r h14 h15 h16 h17 hdr; rs_simp; simp [h14, h15, h16, h17, hdr]
    · rw [if_neg hl0,
          run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..),
          run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..),
          run_cons_step H _ _ _ _ (ctrl_orr3 ..) (step_orr3 ..),
          run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..),
          run_cons_step H _ _ _ _ (ctrl_orr3 ..) (step_orr3 ..),
          run_cons_cbnzOog]
      rs_simp
      try rw [hsl]
      by_cases hoh : off.l1 = 0 ∧ off.l2 = 0 ∧ off.l3 = 0
      · rw [if_neg (by simpa [and_assoc] using ho.hi_zero.mpr hoh),
            run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..),
            run_cons_step H _ _ _ _ (ctrl_adds ..) (step_adds ..), run_cons_bcsOog]
        rs_simp
        try rw [hsl]
        simp only [ho.h0, hl.h0]
        rw [hcarry _ _ ho.b0 hl.b0]
        by_cases hc : 2 ^ 64 ≤ off.l0 + len.l0
        · have hE : memRangeEnd off len = none := by simp [memRangeEnd, hlh, hl0, hoh, hc]
          refine ⟨fun _ => ⟨_, by rw [if_pos (by simpa using hc)]⟩, fun e he' => (by rw [hE] at he'; cases he')⟩
        · have hE : memRangeEnd off len = some (off.l0 + len.l0) := by
            simp [memRangeEnd, hlh, hl0, hoh, hc]
          rw [if_neg (by simpa using hc), run_cons_bLbl]
          simp only [AsmRun.skipTo, hL, Bool.false_eq_true, ite_false, beq_self_eq_true, Bool.true_or,
            ite_true]
          rw [run_cons_label]
          refine ⟨fun h => (by rw [hE] at h; cases h), fun e he' => ?_⟩
          rw [hE] at he'; cases he'
          refine ⟨_, rfl, ?_, by rs_simp, by rs_simp, by omega, ?_⟩
          · rs_simp
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_add, toNat_ofNat64 _ ho.b0, toNat_ofNat64 _ hl.b0, toNat_ofNat64 _ (by omega),
                Nat.mod_eq_of_lt (by omega)]
          · intro r h14 h15 h16 h17 hdr; rs_simp; simp [h14, h15, h16, h17, hdr]
      · have hE : memRangeEnd off len = none := by
          simp [memRangeEnd, hlh, hl0]; intro a b c; exact (hoh ⟨a, b, c⟩).elim
        refine ⟨fun _ => ⟨_, by rw [if_pos (by simpa [and_assoc] using fun h => hoh (ho.hi_zero.mp h))]⟩,
          fun e he' => (by rw [hE] at he'; cases he')⟩
  · have hE : memRangeEnd off len = none := by
      simp only [memRangeEnd]; rw [if_pos (by simp only [not_and_or] at hlh; simpa using hlh)]
    refine ⟨fun _ => ⟨_, by rw [if_pos (by simpa [and_assoc] using fun h => hlh (hl.hi_zero.mp h))]⟩,
      fun e he' => (by rw [hE] at he'; cases he')⟩

/-! ## RETURN / REVERT: `memExpandIfLen` -/

/-- What the RETURN/REVERT prologue reads: offset (TOS) and length (NOS) in
    their stack words — the register cache is written back there, which is
    what lets the denotation read `tos`/`nos` while the instructions read
    memory —, the capacity (#56) and `memory_size` (#48) of the struct at x20,
    and gas in x22. The capacity bound (2^32) is the gadget's own precondition:
    `w²` for the word count must not wrap. -/
structure MemView (m : Mach) (s : RS) : Prop where
  tos : SlotHolds s 1 m.tos
  nos : SlotHolds s 2 m.nos
  cap : capAt s.mem (s.regs .x20) = BitVec.ofNat 64 m.memCap
  capLt : m.memCap < 2 ^ 32
  ms : msAt s.mem (s.regs .x20) = BitVec.ofNat 64 m.memSize
  msLe : m.memSize ≤ m.memCap
  gas : s.regs .x22 = BitVec.ofNat 64 m.gas
  gasLt : m.gas < 2 ^ 64

theorem skipTo_4_memExpand (r : List AInstr) :
    AsmRun.skipTo "4f" (memExpandInstrs ++ .subsReg .x22 .x22 .x17 :: .bloOog :: .label "4" :: r) =
      .label "4" :: r := by
  simp [memExpandInstrs, AsmRun.skipTo]

theorem run_cons_bloOog (H : Helpers) (rest : List AInstr) (s : RS) :
    run H (.bloOog :: rest) s = if bcHolds .lo s.flags then .fault "_eita_oog" s else run H rest s := by
  simp [run, ctrl]

/-- **RETURN/REVERT's memory expansion is what its instructions do.** From a
    state holding the `Mach` (`MemView`, no OOG yet), the instructions exit to
    `_eita_oog` exactly when `Op.denote (.memExpandIfLen tag)` sets `oog`, and
    otherwise fall through with x22 and `memory_size` holding the denotation's
    gas and memory size: the range over the full u256 (`memRangeEnd`), the
    capacity check, and EELS's expansion delta. -/
theorem memExpandIfLen_sem (H : Helpers) (tag : String) (m : Mach) (s : RS) (v : MemView m s)
    (hoog : m.oog = false)
    (hL : (s!".Lro{tag}1" == s!".Lro{tag}0" || s!".Lro{tag}1" == s!".Lro{tag}0" ++ "f") = false) :
    (∃ s', run H (Op.toAInstrs (.memExpandIfLen tag)) s = .done s' ∧
       (Op.denote (.memExpandIfLen tag) m).oog = false ∧
       s'.regs .x22 = BitVec.ofNat 64 (Op.denote (.memExpandIfLen tag) m).gas ∧
       msAt s'.mem (s.regs .x20) = BitVec.ofNat 64 (Op.denote (.memExpandIfLen tag) m).memSize) ∨
    (∃ s', run H (Op.toAInstrs (.memExpandIfLen tag)) s = .fault "_eita_oog" s' ∧
       (Op.denote (.memExpandIfLen tag) m).oog = true) := by
  have hr := memRange_run H 2 1 .x0 s!".Lro{tag}0" s!".Lro{tag}1"
    ([.movImm .x17 0, .cbzLbl .x0 "4f"] ++ memExpandInstrs ++ [.subsReg .x22 .x22 .x17, .bloOog, .label "4"])
    s m.tos m.nos v.nos v.tos (by decide) hL
  have hprog : Op.toAInstrs (.memExpandIfLen tag) = memRangeInstrs 2 1 .x0 s!".Lro{tag}0" s!".Lro{tag}1" ++
      ([.movImm .x17 0, .cbzLbl .x0 "4f"] ++ memExpandInstrs ++ [.subsReg .x22 .x22 .x17, .bloOog, .label "4"]) := by
    simp [Op.toAInstrs]
  rw [hprog]
  cases hE : memRangeEnd m.tos m.nos with
  | none =>
    obtain ⟨sf, hf⟩ := hr.1 hE
    right; refine ⟨sf, hf, ?_⟩
    simp only [Op.denote, hE]
  | some e =>
    obtain ⟨s1, h1, h1x0, h1m, h1sp, he, h1r⟩ := hr.2 e hE
    rw [h1]
    simp only [List.cons_append, List.nil_append]
    rw [run_cons_step H _ _ _ _ (ctrl_movImm ..) (step_movImm ..), run_cons_cbzLbl]
    rs_simp
    rw [h1x0]
    simp only [ofNat64_eq_zero _ he]
    have h20 : s1.regs .x20 = s.regs .x20 := h1r _ (by decide) (by decide) (by decide) (by decide) (by decide)
    have h22 : s1.regs .x22 = s.regs .x22 := h1r _ (by decide) (by decide) (by decide) (by decide) (by decide)
    by_cases he0 : e = 0
    · subst he0
      rw [if_pos rfl, skipTo_4_memExpand, run_cons_label, run_nil]
      left; refine ⟨_, rfl, ?_, ?_, ?_⟩
      · simp only [Op.denote, hE]; exact hoog
      · rs_simp; rw [h22, v.gas]; simp only [Op.denote, hE]
      · rs_simp; rw [h1m, v.ms]; simp only [Op.denote, hE]
    · rw [if_neg he0]
      have hmem : (s1.set .x17 (BitVec.ofNat 64 0)).mem = s.mem := by rs_simp; exact h1m
      have hcapN : (capAt (s1.set .x17 (BitVec.ofNat 64 0)).mem (s.regs .x20)).toNat = m.memCap := by
        rw [hmem, v.cap, toNat_ofNat64 _ (by have := v.capLt; omega)]
      have hmsN : (msAt (s1.set .x17 (BitVec.ofNat 64 0)).mem (s.regs .x20)).toNat = m.memSize := by
        rw [hmem, v.ms, toNat_ofNat64 _ (by have := v.capLt; have := v.msLe; omega)]
      have hx := memExpandInstrs_run H (s.regs .x20) e [.subsReg .x22 .x22 .x17, .bloOog, .label "4"]
        (s1.set .x17 (BitVec.ofNat 64 0)) (by rs_simp; exact h20) (by rs_simp; exact h1x0) he
        (by rw [hcapN]; exact v.capLt) (by rw [hcapN, hmsN]; exact v.msLe) (by rs_simp; decide)
      rw [hcapN, hmsN] at hx
      -- the denotation's branch, with newEnd = e ≠ 0
      obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
      have hden : Op.denote (.memExpandIfLen tag) m =
          (let m0 := { m with acc := 0 }
           if m.memCap < k + 1 then { m0 with oog := true }
           else
             let nw := (k + 1 + 31) / 32
             let ow := m.memSize / 32
             let a := if nw ≤ ow then 0 else (3*nw + nw*nw/512) - (3*ow + ow*ow/512)
             let ms := if nw ≤ ow then m.memSize else nw * 32
             if m.gas < a then { m0 with oog := true, memSize := ms }
             else { m0 with gas := m.gas - a, memSize := ms }) := by
        simp only [Op.denote, hE]
      rw [hden]
      by_cases hc : m.memCap < k + 1
      · obtain ⟨sf, hf⟩ := hx.1 hc
        right; exact ⟨sf, hf, by simp [hc]⟩
      · obtain ⟨s3, h3, -, h3x17, h3r, h3ms⟩ := hx.2 (by omega)
        rw [h3, run_cons_step H _ _ _ _ (ctrl_subsReg ..) (step_subsReg ..), run_cons_bloOog]
        rs_simp
        have h3x22 : s3.regs .x22 = BitVec.ofNat 64 m.gas := by
          rw [h3r _ (by decide) (by decide) (by decide) (by decide)]; rs_simp; rw [h22, v.gas]
        have hecost : ecost (m.memSize / 32) (wordsOf (k + 1)) =
            (if (k + 1 + 31) / 32 ≤ m.memSize / 32 then 0
             else (3 * ((k + 1 + 31) / 32) + (k + 1 + 31) / 32 * ((k + 1 + 31) / 32) / 512) -
                  (3 * (m.memSize / 32) + m.memSize / 32 * (m.memSize / 32) / 512)) := by
          unfold ecost mcost wordsOf; rfl
        have h17' : (s3.regs .x17).toNat = ecost (m.memSize / 32) (wordsOf (k + 1)) := by
          rw [h3x17]; rs_simp; simp
        simp only [lo_subFlags, h3x22, toNat_ofNat64 _ v.gasLt, h17']
        by_cases hg : m.gas < ecost (m.memSize / 32) (wordsOf (k + 1))
        · rw [if_pos (by simpa using hg)]
          right; refine ⟨_, rfl, ?_⟩
          rw [hecost] at hg; simp [hc, hg]
        · rw [if_neg (by simpa using hg), run_cons_label, run_nil]
          left; refine ⟨_, rfl, ?_, ?_, ?_⟩
          · rw [hecost] at hg; simp [hc, hg, hoog]
          · rs_simp
            try rw [h3x22]
            apply BitVec.eq_of_toNat_eq
            rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, toNat_ofNat64 _ v.gasLt, h17']; omega),
                toNat_ofNat64 _ v.gasLt, h17']
            rw [hecost] at hg ⊢
            simp only [hc, hg, if_false]
            rw [toNat_ofNat64 _ (by have := v.gasLt; omega)]
          · rs_simp
            rw [hecost] at hg
            apply BitVec.eq_of_toNat_eq
            rw [h3ms]
            simp only [hc, hg, if_false]
            have := v.capLt; have := v.msLe
            rw [toNat_ofNat64]
            · unfold wordsOf; split <;> omega
            · split <;> omega

-- The two bodies' instances (RETURN tags its labels `r`, REVERT `v`): the label side
-- condition is decided.
example (H : Helpers) (m : Mach) (s : RS) (v : MemView m s) (h : m.oog = false) :=
  memExpandIfLen_sem H "r" m s v h (by decide)
example (H : Helpers) (m : Mach) (s : RS) (v : MemView m s) (h : m.oog = false) :=
  memExpandIfLen_sem H "v" m s v h (by decide)

end Evm.CL.OpSem
