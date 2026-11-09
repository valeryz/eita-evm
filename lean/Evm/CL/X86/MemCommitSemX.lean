/-
  Evm.CL.X86.MemCommitSemX — the memory commit of a region flush at the x86-64
  target (`memCommitT x86Flush`): the x86-64 twin of `ARM64.MemCommitSem`.
  Immediates are one `mov`, far exits go through the chunk's trampolines
  (`bTramp`), the word/byte stores are `strOff`/`strbOff` at offset 0;
  everything else — the struct fields, the cost arithmetic, the big-endian
  store, the write list — is reused from the ARM64 module.
-/

import Evm.CL.ARM64.MemCommitSem
import Evm.CL.X86.FlushSemX

namespace Evm.CL.X86.MemCommitSemX

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun Evm.CL.ARM64.JIT Evm.CL.ARM64.FlushSem Evm.CL.ARM64.CoreSem
open Evm.CL.ARM64.MemCommitSem
open Evm.CL.X86.FlushSemX (run_cons_bTramp loadSlotX_x6_run)
open Evm.IR.SymExpr (Expr eval)

/-! ## Label skipping inside the gadget -/

theorem skipTo_5X (r : List AInstr) :
    AsmRun.skipTo "5f" (.bTramp "_eita_oog" :: .label "5" :: r) = .label "5" :: r := by simp [AsmRun.skipTo]
theorem skipTo_6X (r : List AInstr) :
    AsmRun.skipTo "6f" (.bTramp "_eita_oog" :: .label "6" :: r) = .label "6" :: r := by simp [AsmRun.skipTo]
/-- The cost block, skipped when no expansion is needed. -/
def costBlockX : List AInstr :=
  [ .mulReg .x16 .x14 .x14, .addLsr .x16 .x14 .x16 9, .addLsl .x16 .x16 .x14 1,
    .mulReg .x14 .x15 .x15, .addLsr .x14 .x15 .x14 9, .addLsl .x14 .x14 .x15 1,
    .subReg .x16 .x16 .x14,
    .subsReg .x22 .x22 .x16, .bcLbl .hs "6f", .bTramp "_eita_oog", .label "6",
    .addImm .x14 .x0 31, .lsrImm .x14 .x14 5, .lslImm .x14 .x14 5, .strOff .x14 .x20 48 ]

theorem skipTo_7X (r : List AInstr) :
    AsmRun.skipTo "7f" (costBlockX ++ .label "7" :: r) = .label "7" :: r := by
  simp only [costBlockX, List.cons_append, List.nil_append]
  rw [AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo,
      AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, ite_eq_right (by decide),
      AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, ite_eq_left (by decide)]
  all_goals (intro t h; cases h)

theorem memExpandFlushT_eqX (maxEnd : Nat) :
    memExpandFlushT Evm.CL.X86JIT.x86Flush maxEnd =
      [.movImm .x0 maxEnd] ++
      [ .ldrOff .x14 .x20 56, .cmpReg .x0 .x14, .blsLbl "5f", .bTramp "_eita_oog", .label "5",
        .addImm .x14 .x0 31, .lsrImm .x14 .x14 5,
        .ldrOff .x15 .x20 48, .lsrImm .x15 .x15 5,
        .cmpReg .x14 .x15, .blsLbl "7f" ] ++ costBlockX ++ [.label "7"] := by
  simp [memExpandFlushT, Evm.CL.X86JIT.x86Flush, costBlockX]

/-! ## The expansion gadget -/

/-- `memExpandFlushT`: EELS's expansion charge, or `_eita_oog`. -/
theorem memExpand_runX (H : Helpers) (st : BitVec 64) (maxEnd : Nat) (rest : List AInstr) (s : RS)
    (h20 : s.regs .x20 = st) (hmax : maxEnd < 2 ^ 64)
    (hcap : (capAt s.mem st).toNat < 2 ^ 32) (hms : (msAt s.mem st).toNat ≤ (capAt s.mem st).toNat) :
    ((capAt s.mem st).toNat < maxEnd →
      ∃ sf, run H (memExpandFlushT Evm.CL.X86JIT.x86Flush maxEnd ++ rest) s = .fault "_eita_oog" sf) ∧
    (maxEnd ≤ (capAt s.mem st).toNat →
      (s.regs .x22).toNat < ecost ((msAt s.mem st).toNat / 32) (wordsOf maxEnd) →
      ∃ sf, run H (memExpandFlushT Evm.CL.X86JIT.x86Flush maxEnd ++ rest) s = .fault "_eita_oog" sf) ∧
    (maxEnd ≤ (capAt s.mem st).toNat →
      ecost ((msAt s.mem st).toNat / 32) (wordsOf maxEnd) ≤ (s.regs .x22).toNat →
      ∃ s', run H (memExpandFlushT Evm.CL.X86JIT.x86Flush maxEnd ++ rest) s = run H rest s' ∧
        s'.sp = s.sp ∧
        (s'.regs .x22).toNat = (s.regs .x22).toNat - ecost ((msAt s.mem st).toNat / 32) (wordsOf maxEnd) ∧
        (∀ r, r ≠ .x0 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x22 → s'.regs r = s.regs r) ∧
        (msAt s'.mem st).toNat =
          (if wordsOf maxEnd ≤ (msAt s.mem st).toNat / 32 then (msAt s.mem st).toNat else 32 * wordsOf maxEnd) ∧
        (∀ x, (∀ i < 8, x ≠ off (off st 48) i) → s'.mem x = s.mem x)) := by
  -- the common prefix up to the capacity check
  rw [memExpandFlushT_eqX]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [run_cons_step H _ _ _ _ (ctrl_movImm ..) (step_movImm ..),
      run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..),
      run_cons_step H _ _ _ _ (ctrl_cmpReg ..) (step_cmpReg ..),
      run_cons_blsLbl]
  rs_simp
  rw [h20, ls_subFlags, toNat_ofNat64 _ hmax]
  have hcapE : capAt s.mem st = ld64 s.mem (st + BitVec.ofNat 64 56) := rfl
  have hmsE : msAt s.mem st = ld64 s.mem (st + BitVec.ofNat 64 48) := rfl
  rw [← hcapE]
  refine ⟨?_, ?_, ?_⟩
  · -- past the capacity: the far branch
    intro hlt
    rw [ite_eq_right (by simp; omega), run_cons_bTramp]
    exact ⟨_, rfl⟩
  · -- the charge is past the gas left
    intro hle hgas
    rw [ite_eq_left (by simp; omega), skipTo_5X, run_cons_label,
        run_cons_step H _ _ _ _ (ctrl_addImm ..) (step_addImm ..),
        run_cons_step H _ _ _ _ (ctrl_lsrImm ..) (step_lsrImm ..),
        run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..),
        run_cons_step H _ _ _ _ (ctrl_lsrImm ..) (step_lsrImm ..),
        run_cons_step H _ _ _ _ (ctrl_cmpReg ..) (step_cmpReg ..),
        run_cons_blsLbl]
    rs_simp
    rw [h20, ls_subFlags, words_bv maxEnd (by omega), oldWords_bv, ← hmsE]
    have hnot : ¬ wordsOf maxEnd ≤ (msAt s.mem st).toNat / 32 := by
      intro hw; unfold ecost at hgas; rw [ite_eq_left hw] at hgas; omega
    rw [ite_eq_right (by simpa using hnot)]
    simp only [costBlockX, List.cons_append, List.nil_append]
    rw [run_cons_step H _ _ _ _ (ctrl_mulReg ..) (step_mulReg ..),
        run_cons_step H _ _ _ _ (ctrl_addLsr ..) (step_addLsr ..),
        run_cons_step H _ _ _ _ (ctrl_addLsl ..) (step_addLsl ..),
        run_cons_step H _ _ _ _ (ctrl_mulReg ..) (step_mulReg ..),
        run_cons_step H _ _ _ _ (ctrl_addLsr ..) (step_addLsr ..),
        run_cons_step H _ _ _ _ (ctrl_addLsl ..) (step_addLsl ..),
        run_cons_step H _ _ _ _ (ctrl_subReg ..) (step_subReg ..),
        run_cons_step H _ _ _ _ (ctrl_subsReg ..) (step_subsReg ..),
        run_cons_bcLbl]
    rs_simp
    rw [hs_subFlags']
    -- the charge in x16
    have hnw : ((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5).toNat < 2 ^ 28 := by
      rw [words_bv maxEnd (by omega)]; exact wordsOf_le maxEnd _ hle hcap
    have how : ((msAt s.mem st) >>> 5).toNat < 2 ^ 28 := by
      rw [oldWords_bv]; omega
    have hle' : (msAt s.mem st >>> 5 + (msAt s.mem st >>> 5 * (msAt s.mem st >>> 5)) >>> 9 + msAt s.mem st >>> 5 <<< 1) ≤
        ((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5 +
          ((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5 * ((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5)) >>> 9 +
          (BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5 <<< 1) := by
      rw [BitVec.le_def, mcost_bv _ hnw, mcost_bv _ how, words_bv maxEnd (by omega), oldWords_bv]
      exact mcost_mono (by omega)
    have hcostv : (((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5 +
          ((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5 * ((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5)) >>> 9 +
          (BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5 <<< 1) -
        (msAt s.mem st >>> 5 + (msAt s.mem st >>> 5 * (msAt s.mem st >>> 5)) >>> 9 + msAt s.mem st >>> 5 <<< 1)).toNat =
        ecost ((msAt s.mem st).toNat / 32) (wordsOf maxEnd) := by
      rw [BitVec.toNat_sub_of_le hle', mcost_bv _ hnw, mcost_bv _ how, words_bv maxEnd (by omega), oldWords_bv]
      unfold ecost; rw [ite_eq_right hnot]
    rw [hcostv, ite_eq_right (by simp; omega), run_cons_bTramp]
    exact ⟨_, rfl⟩
  · -- success
    intro hle hgas
    rw [ite_eq_left (by simp; omega), skipTo_5X, run_cons_label,
        run_cons_step H _ _ _ _ (ctrl_addImm ..) (step_addImm ..),
        run_cons_step H _ _ _ _ (ctrl_lsrImm ..) (step_lsrImm ..),
        run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..),
        run_cons_step H _ _ _ _ (ctrl_lsrImm ..) (step_lsrImm ..),
        run_cons_step H _ _ _ _ (ctrl_cmpReg ..) (step_cmpReg ..),
        run_cons_blsLbl]
    rs_simp
    rw [h20, ls_subFlags, words_bv maxEnd (by omega), oldWords_bv, ← hmsE]
    by_cases hw : wordsOf maxEnd ≤ (msAt s.mem st).toNat / 32
    · -- no expansion: skip the cost block
      rw [ite_eq_left (by simpa using hw), skipTo_7X, run_cons_label]
      refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rs_simp
      · rs_simp; unfold ecost; rw [ite_eq_left hw]; simp
      · intro r h0 h14 h15 h16 h22; rs_simp; simp [h0, h14, h15]
      · rs_simp; rw [ite_eq_left hw]
      · intro x _; rs_simp
    · rw [ite_eq_right (by simpa using hw)]
      simp only [costBlockX, List.cons_append, List.nil_append]
      rw [run_cons_step H _ _ _ _ (ctrl_mulReg ..) (step_mulReg ..),
          run_cons_step H _ _ _ _ (ctrl_addLsr ..) (step_addLsr ..),
          run_cons_step H _ _ _ _ (ctrl_addLsl ..) (step_addLsl ..),
          run_cons_step H _ _ _ _ (ctrl_mulReg ..) (step_mulReg ..),
          run_cons_step H _ _ _ _ (ctrl_addLsr ..) (step_addLsr ..),
          run_cons_step H _ _ _ _ (ctrl_addLsl ..) (step_addLsl ..),
          run_cons_step H _ _ _ _ (ctrl_subReg ..) (step_subReg ..),
          run_cons_step H _ _ _ _ (ctrl_subsReg ..) (step_subsReg ..),
          run_cons_bcLbl]
      rs_simp
      rw [hs_subFlags']
      have hnw : ((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5).toNat < 2 ^ 28 := by
        rw [words_bv maxEnd (by omega)]; exact wordsOf_le maxEnd _ hle hcap
      have how : ((msAt s.mem st) >>> 5).toNat < 2 ^ 28 := by
        rw [oldWords_bv]; omega
      have hle' : (msAt s.mem st >>> 5 + (msAt s.mem st >>> 5 * (msAt s.mem st >>> 5)) >>> 9 + msAt s.mem st >>> 5 <<< 1) ≤
          ((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5 +
            ((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5 * ((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5)) >>> 9 +
            (BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5 <<< 1) := by
        rw [BitVec.le_def, mcost_bv _ hnw, mcost_bv _ how, words_bv maxEnd (by omega), oldWords_bv]
        exact mcost_mono (by omega)
      have hcostv : (((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5 +
            ((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5 * ((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5)) >>> 9 +
            (BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5 <<< 1) -
          (msAt s.mem st >>> 5 + (msAt s.mem st >>> 5 * (msAt s.mem st >>> 5)) >>> 9 + msAt s.mem st >>> 5 <<< 1)).toNat =
          ecost ((msAt s.mem st).toNat / 32) (wordsOf maxEnd) := by
        rw [BitVec.toNat_sub_of_le hle', mcost_bv _ hnw, mcost_bv _ how, words_bv maxEnd (by omega), oldWords_bv]
        unfold ecost; rw [ite_eq_right hw]
      rw [hcostv, ite_eq_left (by simp; omega), skipTo_6X, run_cons_label,
          run_cons_step H _ _ _ _ (ctrl_addImm ..) (step_addImm ..),
          run_cons_step H _ _ _ _ (ctrl_lsrImm ..) (step_lsrImm ..),
          run_cons_step H _ _ _ _ (ctrl_lslImm ..) (step_lslImm ..),
          run_cons_step H _ _ _ _ (ctrl_strOff ..) (step_strOff ..),
          run_cons_label]
      refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rs_simp
      · rs_simp
        generalize hX : ((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5 +
            ((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5 * ((BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5)) >>> 9 +
            (BitVec.ofNat 64 maxEnd + BitVec.ofNat 64 31) >>> 5 <<< 1) -
          (msAt s.mem st >>> 5 + (msAt s.mem st >>> 5 * (msAt s.mem st >>> 5)) >>> 9 + msAt s.mem st >>> 5 <<< 1) = X at hcostv ⊢
        rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hcostv]; exact hgas), hcostv]
      · intro r h0 h14 h15 h16 h22; rs_simp; simp [h0, h14, h15, h16, h22]
      · rs_simp
        rw [h20, ite_eq_right hw]
        show (ld64 (st64 _ (off st 48) _) (off st 48)).toNat = _
        rw [ld64_st64_same, aligned_bv maxEnd (by omega) (by unfold wordsOf; omega)]
      · intro x hx; rs_simp; rw [h20]; exact st64_out _ _ _ _ hx

/-! ## One buffered write -/

/-- `memBaseAtT`: x14 ← the buffer pointer plus the constant offset. -/
theorem memBaseAt_runX (H : Helpers) (st : BitVec 64) (o : Nat) (ho : o < 2 ^ 64) (rest : List AInstr) (s : RS)
    (h20 : s.regs .x20 = st) :
    ∃ s', run H (memBaseAtT Evm.CL.X86JIT.x86Flush o ++ rest) s = run H rest s' ∧
      s'.regs .x14 = off (mbAt s.mem st) o ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → s'.regs r = s.regs r) := by
  simp only [memBaseAtT, Evm.CL.X86JIT.x86Flush, List.cons_append]
  rw [run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..)]
  split
  · rename_i h0
    simp only [beq_iff_eq] at h0; subst h0
    rw [List.nil_append]
    refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
    · rs_simp; rw [h20, off_zero]; rfl
    · intro r h14 _; rs_simp; simp [h14]
  · split
    · rw [List.singleton_append, run_cons_step H _ _ _ _ (ctrl_addImm ..) (step_addImm ..)]
      refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
      · rs_simp; rw [h20]; rfl
      · intro r h14 _; rs_simp; simp [h14]
    · simp only [List.nil_append, List.cons_append]
      rw [run_cons_step H _ _ _ _ (ctrl_movImm ..) (step_movImm ..),
          run_cons_step H _ _ _ _ (ctrl_addReg ..) (step_addReg ..)]
      refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
      · rs_simp; rw [h20]; rfl
      · intro r h14 h15; rs_simp; simp [h14, h15]

/-- `emitMemWriteT`: the slot's value lands in the buffer at the constant offset. -/
theorem memWrite_runX (H : Helpers) (st : BitVec 64) (idx : Expr → Nat) (w : MemWrite) (es : List Evm.U256)
    (rest : List AInstr) (s : RS) (h20 : s.regs .x20 = st) (ho : w.off < 2 ^ 64)
    (hslot : ld256 s.mem (slotAddr s.sp (idx w.val)) = eval w.val es) (_hn : 32 * idx w.val < 2 ^ 64) :
    ∃ s', run H (emitMemWriteT Evm.CL.X86JIT.x86Flush idx w ++ rest) s = run H rest s' ∧
      s'.mem = applyW (mbAt s.mem st) es s.mem w ∧ s'.sp = s.sp ∧
      (∀ r, keep r = true → s'.regs r = s.regs r) := by
  simp only [emitMemWriteT, List.append_assoc]
  obtain ⟨s1, h1, hv1, hsp1, hmem1, _, hregs1⟩ := loadSlotX_x6_run H (idx w.val) _ s
  rw [show loadSlotT Evm.CL.X86JIT.x86Flush .x6 (idx w.val) = Evm.CL.X86.FlushSemX.loadSlotX .x6 (idx w.val) from rfl, h1]
  have h20' : s1.regs .x20 = st := by
    rw [hregs1 _ (by decide) (by decide) (by decide) (by decide) (by decide), h20]
  obtain ⟨s2, h2, h14, hsp2, hmem2, _, hregs2⟩ := memBaseAt_runX H st w.off ho _ s1 h20'
  rw [h2]
  rw [hmem1] at h14
  have hx6 : s2.regs .x6 = (eval w.val es).extractLsb' 0 64 := by
    rw [hregs2 _ (by decide) (by decide), ← hslot, ← hv1, lhs, extract0_ofLimbs]
  have hx7 : s2.regs .x7 = (eval w.val es).extractLsb' 64 64 := by
    rw [hregs2 _ (by decide) (by decide), ← hslot, ← hv1, lhs, extract1_ofLimbs]
  have hx8 : s2.regs .x8 = (eval w.val es).extractLsb' 128 64 := by
    rw [hregs2 _ (by decide) (by decide), ← hslot, ← hv1, lhs, extract2_ofLimbs]
  have hx9 : s2.regs .x9 = (eval w.val es).extractLsb' 192 64 := by
    rw [hregs2 _ (by decide) (by decide), ← hslot, ← hv1, lhs, extract3_ofLimbs]
  have hkeep : ∀ r, keep r = true → s2.regs r = s.regs r := by
    intro r hr
    obtain ⟨_, _, _, _, h6, h7, h8, h9, _, _, _, _, h14, h15, _, _⟩ := keep_ne r hr
    rw [hregs2 r h14 h15, hregs1 r h6 h7 h8 h9 h14]
  have hsp2' : s2.sp = s.sp := by rw [hsp2, hsp1]
  have hmem2' : s2.mem = s.mem := by rw [hmem2, hmem1]
  unfold applyW
  split
  · rename_i hb
    simp only [Evm.CL.X86JIT.x86Flush, List.singleton_append]
    rw [run_cons_step H _ _ _ _ (ctrl_strbOff ..) rfl]
    refine ⟨_, rfl, ?_, by rs_simp; exact hsp2', ?_⟩
    · rs_simp; simp only [BitVec.add_zero]; rw [h14, hx6, hmem2', extract_extract _ _ _ _ (by omega), Nat.zero_add]
    · intro r hr; rs_simp; exact hkeep r hr
  · rename_i hb
    simp only [Evm.CL.X86JIT.x86Flush, List.cons_append, List.nil_append]
    rw [run_cons_step H _ _ _ _ (ctrl_rev ..) (step_rev ..),
        run_cons_step H _ _ _ _ (ctrl_rev ..) (step_rev ..),
        run_cons_step H _ _ _ _ (ctrl_rev ..) (step_rev ..),
        run_cons_step H _ _ _ _ (ctrl_rev ..) (step_rev ..)]
    rs_simp
    rw [hx6, hx7, hx8, hx9]
    rw [run_cons_step H _ _ _ _ (ctrl_strOff ..) (step_strOff ..),
        run_cons_step H _ _ _ _ (ctrl_strOff ..) (step_strOff ..),
        run_cons_step H _ _ _ _ (ctrl_strOff ..) (step_strOff ..),
        run_cons_step H _ _ _ _ (ctrl_strOff ..) (step_strOff ..)]
    refine ⟨_, rfl, ?_, by rs_simp; exact hsp2', ?_⟩
    · rs_simp; simp only [BitVec.add_zero]; rw [h14, hmem2']; rfl
    · intro r hr
      obtain ⟨h0, h1', h2', h3, _, _, _, _, _, _, _, _, _, _, _, _⟩ := keep_ne r hr
      rs_simp; simp only [h0, h1', h2', h3, ite_false]; exact hkeep r hr

/-! ## The high-water update -/

theorem mpUpdate_runX (H : Helpers) (st : BitVec 64) (maxEnd : Nat) (hmax : maxEnd < 2 ^ 64) (rest : List AInstr)
    (s : RS) (h20 : s.regs .x20 = st) :
    ∃ s', run H (mpUpdateFlushT Evm.CL.X86JIT.x86Flush maxEnd ++ rest) s = run H rest s' ∧
      s'.sp = s.sp ∧ (∀ r, r ≠ .x15 → r ≠ .x16 → s'.regs r = s.regs r) ∧
      (mpAt s'.mem st).toNat = max (mpAt s.mem st).toNat maxEnd ∧
      (∀ x, (∀ i < 8, x ≠ off (off st 24) i) → s'.mem x = s.mem x) := by
  simp only [mpUpdateFlushT, Evm.CL.X86JIT.x86Flush, List.cons_append, List.nil_append]
  rw [run_cons_step H _ _ _ _ (ctrl_movImm ..) (step_movImm ..),
      run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..),
      run_cons_step H _ _ _ _ (ctrl_cmpReg ..) (step_cmpReg ..),
      run_cons_step H _ _ _ _ (ctrl_cselHi ..) (step_cselHi ..),
      run_cons_step H _ _ _ _ (ctrl_strOff ..) (step_strOff ..)]
  refine ⟨_, rfl, by rs_simp, ?_, ?_, ?_⟩
  · intro r h15 h16; rs_simp; simp [h15, h16]
  · rs_simp
    rw [h20, hi_subFlags, toNat_ofNat64 _ hmax]
    show (ld64 (st64 _ (st + BitVec.ofNat 64 24) _) (st + BitVec.ofNat 64 24)).toNat =
      max (ld64 s.mem (st + BitVec.ofNat 64 24)).toNat maxEnd
    rw [ld64_st64_same]
    split
    · rename_i h; simp only [decide_eq_true_eq] at h; rw [toNat_ofNat64 _ hmax]; omega
    · rename_i h; simp only [decide_eq_true_eq] at h; omega
  · intro x hx; rs_simp; rw [h20]; exact st64_out _ _ _ _ hx

/-! ## The writes, in order -/

/-- Every write of the list, each reading its slot and landing in the buffer. -/
theorem writes_runX (H : Helpers) (fp mb st : BitVec 64) (idx : Expr → Nat) (es : List Evm.U256)
    (rest : List AInstr) : ∀ (ws : List MemWrite) (s : RS),
    s.sp = fp → s.regs .x20 = st → mbAt s.mem st = mb →
    (∀ w ∈ ws, w.off < 2 ^ 64) → (∀ w ∈ ws, 32 * idx w.val < 2 ^ 64) →
    (∀ w ∈ ws, ld256 s.mem (slotAddr fp (idx w.val)) = eval w.val es) →
    (∀ w ∈ ws, ∀ i < wWidth w,
      (∀ w' ∈ ws, ∀ j < 32, off (off mb w.off) i ≠ off (slotAddr fp (idx w'.val)) j) ∧
      (∀ j < 8, off (off mb w.off) i ≠ off (off st 40) j)) →
    ∃ s', run H (ws.flatMap (emitMemWriteT Evm.CL.X86JIT.x86Flush idx) ++ rest) s = run H rest s' ∧
      s'.mem = ws.foldl (applyW mb es) s.mem ∧ s'.sp = s.sp ∧ (∀ r, keep r = true → s'.regs r = s.regs r)
  | [], s, _, _, _, _, _, _, _ => ⟨s, by simp, rfl, rfl, fun _ _ => rfl⟩
  | w :: ws, s, hsp, h20, hmb, hoff, hn, hslots, hdisj => by
    simp only [List.flatMap_cons, List.append_assoc, List.foldl_cons]
    obtain ⟨s1, h1, hmem1, hsp1, hregs1⟩ := memWrite_runX H st idx w es _ s h20 (hoff w (by simp))
      (by rw [hsp]; exact hslots w (by simp)) (hn w (by simp))
    rw [h1]
    rw [hmb] at hmem1
    have hout : ∀ x, (∀ i < wWidth w, x ≠ off (off mb w.off) i) → s1.mem x = s.mem x := by
      intro x hx; rw [hmem1]; exact applyW_out _ _ _ _ _ hx
    have hslots1 : ∀ w' ∈ ws, ld256 s1.mem (slotAddr fp (idx w'.val)) = eval w'.val es := by
      intro w' hw'
      rw [← hslots w' (by simp [hw'])]
      apply ld256_eq_of_eq_on
      intro j hj
      apply hout
      intro i hi h
      exact ((hdisj w (by simp) i hi).1 w' (by simp [hw']) j hj) h.symm
    have hmb1 : mbAt s1.mem st = mb := by
      rw [← hmb]
      show ld64 s1.mem (off st 40) = ld64 s.mem (off st 40)
      apply ld64_eq_of_eq_on
      intro j hj
      apply hout
      intro i hi h
      exact ((hdisj w (by simp) i hi).2 j hj) h.symm
    obtain ⟨s', h', hmem', hsp', hregs'⟩ := writes_runX H fp mb st idx es rest ws s1 (by rw [hsp1, hsp])
      (by rw [hregs1 _ (by decide), h20]) hmb1 (fun w' hw' => hoff w' (by simp [hw']))
      (fun w' hw' => hn w' (by simp [hw'])) hslots1
      (fun w' hw' i hi => ⟨fun w'' hw'' => (hdisj w' (by simp [hw']) i hi).1 w'' (by simp [hw'']),
                           (hdisj w' (by simp [hw']) i hi).2⟩)
    refine ⟨s', h', ?_, by rw [hsp', hsp1], fun r hr => by rw [hregs' r hr, hregs1 r hr]⟩
    rw [hmem', hmem1]

/-! ## The whole commit -/

theorem memCommitT_eqX (idx : Expr → Nat) (ws : List MemWrite) (hne : ws ≠ []) :
    memCommitT Evm.CL.X86JIT.x86Flush idx ws =
      memExpandFlushT Evm.CL.X86JIT.x86Flush (maxEndOf ws) ++ mpUpdateFlushT Evm.CL.X86JIT.x86Flush (maxEndOf ws) ++
        ws.flatMap (emitMemWriteT Evm.CL.X86JIT.x86Flush idx) := by
  unfold memCommitT
  rw [ite_eq_right (by simpa using hne)]
  rfl

/-- `memCommitT` on a non-empty write list. -/
theorem memCommit_runX (H : Helpers) (F : Fr) (idx : Expr → Nat) (st mb : BitVec 64) (ws : List MemWrite)
    (hne : ws ≠ []) (es : List Evm.U256) (rest : List AInstr) (s : RS)
    (hL : Evm.CL.X86.FlushSemX.LayX F) (hM : MLay F st mb (capAt s.mem st).toNat)
    (hsp : s.sp = F.fp) (h20 : s.regs .x20 = st) (hmb : mbAt s.mem st = mb)
    (hok : (msAt s.mem st).toNat ≤ (capAt s.mem st).toNat)
    (hoff : ∀ w ∈ ws, w.off + wWidth w < 2 ^ 64)
    (hidx : ∀ w ∈ ws, idx w.val < F.n)
    (hslots : ∀ w ∈ ws, ld256 s.mem (slotAddr F.fp (idx w.val)) = eval w.val es) :
    ((capAt s.mem st).toNat < maxEndOf ws →
      ∃ sf, run H (memCommitT Evm.CL.X86JIT.x86Flush idx ws ++ rest) s = .fault "_eita_oog" sf) ∧
    (maxEndOf ws ≤ (capAt s.mem st).toNat →
      (s.regs .x22).toNat < ecost ((msAt s.mem st).toNat / 32) (wordsOf (maxEndOf ws)) →
      ∃ sf, run H (memCommitT Evm.CL.X86JIT.x86Flush idx ws ++ rest) s = .fault "_eita_oog" sf) ∧
    (maxEndOf ws ≤ (capAt s.mem st).toNat →
      ecost ((msAt s.mem st).toNat / 32) (wordsOf (maxEndOf ws)) ≤ (s.regs .x22).toNat →
      ∃ s', run H (memCommitT Evm.CL.X86JIT.x86Flush idx ws ++ rest) s = run H rest s' ∧
        s'.sp = s.sp ∧
        (s'.regs .x22).toNat = (s.regs .x22).toNat - ecost ((msAt s.mem st).toNat / 32) (wordsOf (maxEndOf ws)) ∧
        (∀ r, keep r = true → r ≠ .x22 → s'.regs r = s.regs r) ∧
        (msAt s'.mem st).toNat = (if wordsOf (maxEndOf ws) ≤ (msAt s.mem st).toNat / 32
                                  then (msAt s.mem st).toNat else 32 * wordsOf (maxEndOf ws)) ∧
        (mpAt s'.mem st).toNat = max (mpAt s.mem st).toNat (maxEndOf ws) ∧
        capAt s'.mem st = capAt s.mem st ∧ mbAt s'.mem st = mb ∧
        (∀ i < (capAt s.mem st).toNat, s'.mem (off mb i) = (ws.foldl (applyW mb es) s.mem) (off mb i)) ∧
        (∀ x, (∀ i, 24 ≤ i → i < 64 → x ≠ off st i) → (∀ i < (capAt s.mem st).toNat, x ≠ off mb i) →
          s'.mem x = s.mem x)) := by
  have hmaxlt := maxEnd_lt ws hoff
  rw [memCommitT_eqX idx ws hne, List.append_assoc, List.append_assoc]
  obtain ⟨hE1, hE2, hE3⟩ := memExpand_runX H st (maxEndOf ws) _ s h20 hmaxlt hM.capLt hok
  refine ⟨hE1, hE2, ?_⟩
  intro hle hgas
  obtain ⟨s1, h1, hsp1, hgas1, hregs1, hms1, hmem1⟩ := hE3 hle hgas
  rw [h1]
  -- struct words other than +48 are intact after the expansion
  have hcap1 : capAt s1.mem st = capAt s.mem st := by
    apply ld64_eq_of_eq_on; intro i hi; apply hmem1
    intro j hj; exact st_word_ne st 56 48 i j (by omega) (by omega) (by omega) hi hj
  have hmp1 : mpAt s1.mem st = mpAt s.mem st := by
    apply ld64_eq_of_eq_on; intro i hi; apply hmem1
    intro j hj; exact st_word_ne st 24 48 i j (by omega) (by omega) (by omega) hi hj
  have hmb1 : mbAt s1.mem st = mb := by
    rw [← hmb]; apply ld64_eq_of_eq_on; intro i hi; apply hmem1
    intro j hj; exact st_word_ne st 40 48 i j (by omega) (by omega) (by omega) hi hj
  have h20_1 : s1.regs .x20 = st := by rw [hregs1 _ (by decide) (by decide) (by decide) (by decide) (by decide), h20]
  obtain ⟨s2, h2, hsp2, hregs2, hmp2, hmem2⟩ := mpUpdate_runX H st (maxEndOf ws) hmaxlt _ s1 h20_1
  rw [h2]
  have hcap2 : capAt s2.mem st = capAt s.mem st := by
    rw [← hcap1]; apply ld64_eq_of_eq_on; intro i hi; apply hmem2
    intro j hj; exact st_word_ne st 56 24 i j (by omega) (by omega) (by omega) hi hj
  have hms2 : msAt s2.mem st = msAt s1.mem st := by
    apply ld64_eq_of_eq_on; intro i hi; apply hmem2
    intro j hj; exact st_word_ne st 48 24 i j (by omega) (by omega) (by omega) hi hj
  have hmb2 : mbAt s2.mem st = mb := by
    rw [← hmb1]; apply ld64_eq_of_eq_on; intro i hi; apply hmem2
    intro j hj; exact st_word_ne st 40 24 i j (by omega) (by omega) (by omega) hi hj
  have h20_2 : s2.regs .x20 = st := by rw [hregs2 _ (by decide) (by decide), h20_1]
  -- memory outside the two struct words is intact so far
  have hmem12 : ∀ x, (∀ i, 24 ≤ i → i < 64 → x ≠ off st i) → s2.mem x = s.mem x := by
    intro x hx
    rw [hmem2 x (fun i hi => by rw [off_off]; exact hx (24 + i) (by omega) (by omega)),
        hmem1 x (fun i hi => by rw [off_off]; exact hx (48 + i) (by omega) (by omega))]
  -- the slots are in the frame, hence intact
  have hslots2 : ∀ w ∈ ws, ld256 s2.mem (slotAddr F.fp (idx w.val)) = eval w.val es := by
    intro w hw
    rw [← hslots w hw]
    apply ld256_eq_of_eq_on
    intro j hj
    apply hmem12
    intro i hi1 hi2 h
    have := hidx w hw
    exact hM.stFrame i hi1 hi2 (32 * idx w.val + j) (by omega) (by rw [← h, slotAddr, off_off])
  -- every write lands inside the buffer
  have hin : ∀ w ∈ ws, ∀ i < wWidth w, w.off + i < (capAt s.mem st).toNat := by
    intro w hw i hi; have := le_maxEnd ws w hw; omega
  obtain ⟨s3, h3, hmem3, hsp3, hregs3⟩ := writes_runX H F.fp mb st idx es rest ws s2 (by rw [hsp2, hsp1, hsp])
    h20_2 hmb2 (fun w hw => by have := hoff w hw; unfold wWidth at this; split at this <;> omega)
    (fun w hw => by have := hidx w hw; have := hL.fpOk; omega) hslots2
    (by
      intro w hw i hi
      refine ⟨fun w' hw' j hj => ?_, fun j hj => ?_⟩
      · rw [off_off, slotAddr, off_off]
        have := hidx w' hw'
        exact hM.bufFrame _ (hin w hw i hi) _ (by omega)
      · rw [off_off, off_off]
        exact hM.bufSt _ (hin w hw i hi) _ (by omega) (by omega))
  refine ⟨s3, h3, by rw [hsp3, hsp2, hsp1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hregs3 _ (by decide), hregs2 _ (by decide) (by decide), hgas1]
  · intro r hr h22
    obtain ⟨h0, _, _, _, _, _, _, _, _, _, _, _, h14, h15, h16, _⟩ := keep_ne r hr
    rw [hregs3 r hr, hregs2 r h15 h16, hregs1 r h0 h14 h15 h16 h22]
  · -- memory_size: the +48 word is outside the buffer, so the writes leave it alone
    rw [← hms1, ← hms2]
    congr 1
    show ld64 s3.mem (off st 48) = ld64 s2.mem (off st 48)
    apply ld64_eq_of_eq_on; intro i hi
    rw [hmem3]
    apply applyWs_out
    intro w hw k hk h
    rw [off_off, off_off] at h
    exact hM.bufSt _ (hin w hw k hk) _ (by omega) (by omega) h.symm
  · rw [← hmp1, ← hmp2]
    congr 1
    show ld64 s3.mem (off st 24) = ld64 s2.mem (off st 24)
    apply ld64_eq_of_eq_on; intro i hi
    rw [hmem3]
    apply applyWs_out
    intro w hw k hk h
    rw [off_off, off_off] at h
    exact hM.bufSt _ (hin w hw k hk) _ (by omega) (by omega) h.symm
  · rw [← hcap2]
    show ld64 s3.mem (off st 56) = ld64 s2.mem (off st 56)
    apply ld64_eq_of_eq_on; intro i hi
    rw [hmem3]
    apply applyWs_out
    intro w hw k hk h
    rw [off_off, off_off] at h
    exact hM.bufSt _ (hin w hw k hk) _ (by omega) (by omega) h.symm
  · rw [← hmb2]
    show ld64 s3.mem (off st 40) = ld64 s2.mem (off st 40)
    apply ld64_eq_of_eq_on; intro i hi
    rw [hmem3]
    apply applyWs_out
    intro w hw k hk h
    rw [off_off, off_off] at h
    exact hM.bufSt _ (hin w hw k hk) _ (by omega) (by omega) h.symm
  · intro i hi
    rw [hmem3]
    apply applyWs_congr_at
    apply hmem12
    intro j hj1 hj2 h
    exact hM.bufSt i hi j hj1 hj2 h
  · intro x hst hbuf
    rw [hmem3, applyWs_out, hmem12 x hst]
    intro w hw k hk h
    rw [off_off] at h
    exact hbuf _ (hin w hw k hk) h

end Evm.CL.X86.MemCommitSemX
