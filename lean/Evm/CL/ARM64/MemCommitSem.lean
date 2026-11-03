/-
  Evm.CL.ARM64.MemCommitSem — the memory commit of a region flush
  (`memCommitT`: the expansion gadget, the high-water update, the buffered
  constant-offset MSTORE/MSTORE8s) run under `AsmRun`.

  The EvmState fields are read from the struct at x20 (`c/evm_state.h`):
  `mp` at +24, the byte buffer pointer at +40, `memory_size` at +48 and the
  capacity at +56. The expansion gadget is EELS's `calculate_memory_gas_cost`
  delta (`Gas.memoryExpansionCost`), faulting to `_eita_oog` when the new end
  is past the capacity or the delta is past the gas left.
-/

import Evm.CL.ARM64.FlushSem
import Evm.Frontier.Vm.Gas

namespace Evm.CL.ARM64.MemCommitSem

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun Evm.CL.ARM64.JIT Evm.CL.ARM64.FlushSem Evm.CL.ARM64.CoreSem
open Evm.CL.ARM64.ChunkGasSem (movImmInstrs_run)
open Evm.IR.SymExpr (Expr eval)

/-! ## The struct fields -/

def mpAt  (m : Mem) (st : BitVec 64) : BitVec 64 := ld64 m (off st 24)
def mbAt  (m : Mem) (st : BitVec 64) : BitVec 64 := ld64 m (off st 40)
def msAt  (m : Mem) (st : BitVec 64) : BitVec 64 := ld64 m (off st 48)
def capAt (m : Mem) (st : BitVec 64) : BitVec 64 := ld64 m (off st 56)

/-- `⌈n / 32⌉`. -/
def wordsOf (n : Nat) : Nat := (n + 31) / 32

/-- `C_mem` and the expansion delta, as plain `Nat` (the spec's `Gas` is an
    abbreviation `omega` does not see through; these are definitionally it). -/
def mcost (w : Nat) : Nat := 3 * w + w * w / 512
def ecost (oldW newW : Nat) : Nat := if newW ≤ oldW then 0 else mcost newW - mcost oldW

theorem mcost_eq_spec (w : Nat) : mcost w = Evm.Frontier.Vm.Gas.memoryCost w := rfl
theorem ecost_eq_spec (o n : Nat) : ecost o n = Evm.Frontier.Vm.Gas.memoryExpansionCost o n := rfl

theorem mcost_mono {a b : Nat} (h : a ≤ b) : mcost a ≤ mcost b := by
  unfold mcost
  have h1 : a * a ≤ b * b := Nat.mul_le_mul h h
  have h2 : a * a / 512 ≤ b * b / 512 := Nat.div_le_div_right h1
  omega

/-! ## Flags and control -/

theorem run_cons_blsLbl (H : Helpers) (l : String) (rest : List AInstr) (s : RS) :
    run H (.blsLbl l :: rest) s =
      if bcHolds .ls s.flags then run H (AsmRun.skipTo l rest) s else run H rest s := by simp [run, ctrl]

theorem hi_subFlags (a b : BitVec 64) : bcHolds .hi (subFlags a b) = decide (b.toNat < a.toNat) := by
  have : bcHolds .hi (subFlags a b) = BitVec.ult b a := by simp only [bcHolds, subFlags]; bv_decide
  exact this

theorem ls_subFlags (a b : BitVec 64) : bcHolds .ls (subFlags a b) = decide (a.toNat ≤ b.toNat) := by
  have : bcHolds .ls (subFlags a b) = BitVec.ule a b := by simp only [bcHolds, subFlags]; bv_decide
  exact this

theorem hs_subFlags' (a b : BitVec 64) : bcHolds .hs (subFlags a b) = decide (b.toNat ≤ a.toNat) := by
  have : bcHolds .hs (subFlags a b) = BitVec.ule b a := by simp only [bcHolds, subFlags]; bv_decide
  exact this

/-! ## Nat views of the gadget's arithmetic -/

theorem toNat_ofNat64 (k : Nat) (h : k < 2 ^ 64) : (BitVec.ofNat 64 k).toNat = k := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `(x0 + 31) >> 5` is the word count. -/
theorem words_bv (n : Nat) (h : n + 31 < 2 ^ 64) :
    ((BitVec.ofNat 64 n + BitVec.ofNat 64 31) >>> 5).toNat = wordsOf n := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, toNat_ofNat64 n (by omega), toNat_ofNat64 31 (by omega),
      Nat.mod_eq_of_lt h, Nat.shiftRight_eq_div_pow]
  rfl

/-- `ms >> 5` is the old word count. -/
theorem oldWords_bv (ms : BitVec 64) : (ms >>> 5).toNat = ms.toNat / 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- `((n + 31) >> 5) << 5`. -/
theorem aligned_bv (n : Nat) (h : n + 31 < 2 ^ 64) (hw : 32 * wordsOf n < 2 ^ 64) :
    (((BitVec.ofNat 64 n + BitVec.ofNat 64 31) >>> 5) <<< 5).toNat = 32 * wordsOf n := by
  rw [BitVec.toNat_shiftLeft, words_bv n h, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The three-instruction `C_mem`: `w + (w*w >> 9) + (w << 1)`. -/
theorem mcost_bv (w : BitVec 64) (hw : w.toNat < 2 ^ 28) :
    (w + ((w * w) >>> 9) + (w <<< 1)).toNat = mcost w.toNat := by
  have hww : w.toNat * w.toNat < 2 ^ 56 := by
    have := Nat.mul_lt_mul_of_lt_of_lt hw hw
    have e : (2 : Nat) ^ 28 * 2 ^ 28 = 2 ^ 56 := by decide
    omega
  have h1 : (w * w).toNat = w.toNat * w.toNat := by
    rw [BitVec.toNat_mul, Nat.mod_eq_of_lt (by omega)]
  have h2 : ((w * w) >>> 9).toNat = w.toNat * w.toNat / 512 := by
    rw [BitVec.toNat_ushiftRight, h1, Nat.shiftRight_eq_div_pow]
  have h3 : (w <<< 1).toNat = 2 * w.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; omega
  have hd : w.toNat * w.toNat / 512 ≤ w.toNat * w.toNat := Nat.div_le_self _ _
  rw [BitVec.toNat_add, BitVec.toNat_add, h2, h3, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  unfold mcost; omega

/-! ## Label skipping inside the gadget -/

theorem skipTo_5 (r : List AInstr) :
    AsmRun.skipTo "5f" (.bFar "_eita_oog" :: .label "5" :: r) = .label "5" :: r := by simp [AsmRun.skipTo]
theorem skipTo_6 (r : List AInstr) :
    AsmRun.skipTo "6f" (.bFar "_eita_oog" :: .label "6" :: r) = .label "6" :: r := by simp [AsmRun.skipTo]

/-- The cost block, skipped when no expansion is needed. -/
def costBlock : List AInstr :=
  [ .mulReg .x16 .x14 .x14, .addLsr .x16 .x14 .x16 9, .addLsl .x16 .x16 .x14 1,
    .mulReg .x14 .x15 .x15, .addLsr .x14 .x15 .x14 9, .addLsl .x14 .x14 .x15 1,
    .subReg .x16 .x16 .x14,
    .subsReg .x22 .x22 .x16, .bcLbl .hs "6f", .bFar "_eita_oog", .label "6",
    .addImm .x14 .x0 31, .lsrImm .x14 .x14 5, .lslImm .x14 .x14 5, .strOff .x14 .x20 48 ]

theorem skipTo_7 (r : List AInstr) :
    AsmRun.skipTo "7f" (costBlock ++ .label "7" :: r) = .label "7" :: r := by
  simp only [costBlock, List.cons_append, List.nil_append]
  rw [AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo,
      AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, if_neg (by decide),
      AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, AsmRun.skipTo, if_pos (by decide)]
  all_goals (intro t h; cases h)

theorem memExpandFlushT_eq (maxEnd : Nat) :
    memExpandFlushT armFlush maxEnd =
      movImmInstrs .x0 maxEnd ++
      [ .ldrOff .x14 .x20 56, .cmpReg .x0 .x14, .blsLbl "5f", .bFar "_eita_oog", .label "5",
        .addImm .x14 .x0 31, .lsrImm .x14 .x14 5,
        .ldrOff .x15 .x20 48, .lsrImm .x15 .x15 5,
        .cmpReg .x14 .x15, .blsLbl "7f" ] ++ costBlock ++ [.label "7"] := by
  simp [memExpandFlushT, armFlush, costBlock, movImmA]

/-! ## The expansion gadget -/

/-- The simp set that evaluates projections of an explicit state chain. -/
macro "rs_simp" : tactic => `(tactic| simp only [AsmRun.set_regs, AsmRun.set_mem, AsmRun.set_sp, AsmRun.set_flags,
  AsmRun.withFlags_regs, AsmRun.withFlags_mem, AsmRun.withFlags_sp, AsmRun.withFlags_flags,
  AsmRun.store64_regs, AsmRun.store64_mem, AsmRun.store64_sp, AsmRun.store64_flags,
  AsmRun.store8_regs, AsmRun.store8_mem, AsmRun.store8_sp, AsmRun.store8_flags,
  reduceCtorEq, ite_true, ite_false])

theorem wordsOf_le (n cap : Nat) (h : n ≤ cap) (hc : cap < 2 ^ 32) : wordsOf n < 2 ^ 28 := by
  unfold wordsOf; omega

/-- `memExpandFlushT`: EELS's expansion charge, or `_eita_oog`. -/
theorem memExpand_run (H : Helpers) (st : BitVec 64) (maxEnd : Nat) (rest : List AInstr) (s : RS)
    (h20 : s.regs .x20 = st) (hmax : maxEnd < 2 ^ 64)
    (hcap : (capAt s.mem st).toNat < 2 ^ 32) (hms : (msAt s.mem st).toNat ≤ (capAt s.mem st).toNat) :
    ((capAt s.mem st).toNat < maxEnd →
      ∃ sf, run H (memExpandFlushT armFlush maxEnd ++ rest) s = .fault "_eita_oog" sf) ∧
    (maxEnd ≤ (capAt s.mem st).toNat →
      (s.regs .x22).toNat < ecost ((msAt s.mem st).toNat / 32) (wordsOf maxEnd) →
      ∃ sf, run H (memExpandFlushT armFlush maxEnd ++ rest) s = .fault "_eita_oog" sf) ∧
    (maxEnd ≤ (capAt s.mem st).toNat →
      ecost ((msAt s.mem st).toNat / 32) (wordsOf maxEnd) ≤ (s.regs .x22).toNat →
      ∃ s', run H (memExpandFlushT armFlush maxEnd ++ rest) s = run H rest s' ∧
        s'.sp = s.sp ∧
        (s'.regs .x22).toNat = (s.regs .x22).toNat - ecost ((msAt s.mem st).toNat / 32) (wordsOf maxEnd) ∧
        (∀ r, r ≠ .x0 → r ≠ .x14 → r ≠ .x15 → r ≠ .x16 → r ≠ .x22 → s'.regs r = s.regs r) ∧
        (msAt s'.mem st).toNat =
          (if wordsOf maxEnd ≤ (msAt s.mem st).toNat / 32 then (msAt s.mem st).toNat else 32 * wordsOf maxEnd) ∧
        (∀ x, (∀ i < 8, x ≠ off (off st 48) i) → s'.mem x = s.mem x)) := by
  -- the common prefix up to the capacity check
  rw [memExpandFlushT_eq]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [movImmInstrs_run H _ _ hmax,
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
    rw [if_neg (by simp; omega), run_cons_bFar]
    exact ⟨_, rfl⟩
  · -- the charge is past the gas left
    intro hle hgas
    rw [if_pos (by simp; omega), skipTo_5, run_cons_label,
        run_cons_step H _ _ _ _ (ctrl_addImm ..) (step_addImm ..),
        run_cons_step H _ _ _ _ (ctrl_lsrImm ..) (step_lsrImm ..),
        run_cons_step H _ _ _ _ (ctrl_ldrOff ..) (step_ldrOff ..),
        run_cons_step H _ _ _ _ (ctrl_lsrImm ..) (step_lsrImm ..),
        run_cons_step H _ _ _ _ (ctrl_cmpReg ..) (step_cmpReg ..),
        run_cons_blsLbl]
    rs_simp
    rw [h20, ls_subFlags, words_bv maxEnd (by omega), oldWords_bv, ← hmsE]
    have hnot : ¬ wordsOf maxEnd ≤ (msAt s.mem st).toNat / 32 := by
      intro hw; unfold ecost at hgas; rw [if_pos hw] at hgas; omega
    rw [if_neg (by simpa using hnot)]
    simp only [costBlock, List.cons_append, List.nil_append]
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
      unfold ecost; rw [if_neg hnot]
    rw [hcostv, if_neg (by simp; omega), run_cons_bFar]
    exact ⟨_, rfl⟩
  · -- success
    intro hle hgas
    rw [if_pos (by simp; omega), skipTo_5, run_cons_label,
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
      rw [if_pos (by simpa using hw), skipTo_7, run_cons_label]
      refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rs_simp
      · rs_simp; unfold ecost; rw [if_pos hw]; simp
      · intro r h0 h14 h15 h16 h22; rs_simp; simp [h0, h14, h15]
      · rs_simp; rw [if_pos hw]
      · intro x _; rs_simp
    · rw [if_neg (by simpa using hw)]
      simp only [costBlock, List.cons_append, List.nil_append]
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
        unfold ecost; rw [if_neg hw]
      rw [hcostv, if_pos (by simp; omega), skipTo_6, run_cons_label,
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
        rw [h20, if_neg hw]
        show (ld64 (st64 _ (off st 48) _) (off st 48)).toNat = _
        rw [ld64_st64_same, aligned_bv maxEnd (by omega) (by unfold wordsOf; omega)]
      · intro x hx; rs_simp; rw [h20]; exact st64_out _ _ _ _ hx

/-! ## Big-endian u256 stores -/

/-- `rev` each limb, high limb first: the 32 big-endian bytes of `v` at `a`. -/
def stBE (m : Mem) (a : BitVec 64) (v : Evm.U256) : Mem :=
  st64 (st64 (st64 (st64 m a (rev64 (v.extractLsb' 192 64))) (off a 8) (rev64 (v.extractLsb' 128 64)))
    (off a 16) (rev64 (v.extractLsb' 64 64))) (off a 24) (rev64 (v.extractLsb' 0 64))

theorem stBE_out (m : Mem) (a : BitVec 64) (v : Evm.U256) (x : BitVec 64)
    (hx : ∀ i < 32, x ≠ off a i) : stBE m a v x = m x := by
  have sub : ∀ (k : Nat), k + 8 ≤ 32 → ∀ i < 8, x ≠ off (off a k) i := by
    intro k hk i hi; rw [off_off]; exact hx (k + i) (by omega)
  have s0 := sub 0 (by omega); have s8 := sub 8 (by omega); have s16 := sub 16 (by omega); have s24 := sub 24 (by omega)
  rw [off_zero] at s0
  simp only [stBE]
  rw [st64_out _ _ _ _ s24, st64_out _ _ _ _ s16, st64_out _ _ _ _ s8, st64_out _ _ _ _ s0]

/-- Byte `i` of an `st64`. -/
theorem st64_at (m : Mem) (a v : BitVec 64) (i : Nat) (hi : i < 8) :
    st64 m a v (off a i) = v.extractLsb' (8 * i) 8 := by
  have ne : ∀ i j : Nat, i < 8 → j < 8 → i ≠ j → off a i ≠ off a j :=
    fun i j hi hj h => off_ne_off a i j (by omega) (by omega) h
  have nb : ∀ i : Nat, 0 < i → i < 8 → off a i ≠ a := fun i h h' => off_ne_base a i h (by omega)
  have nb' : ∀ i : Nat, 0 < i → i < 8 → a ≠ off a i := fun i h h' => (nb i h h').symm
  match i, hi with
  | 0, _ => simp [st64, st8, nb']
  | 1, _ => simp [st64, st8, ne]
  | 2, _ => simp [st64, st8, ne]
  | 3, _ => simp [st64, st8, ne]
  | 4, _ => simp [st64, st8, ne]
  | 5, _ => simp [st64, st8, ne]
  | 6, _ => simp [st64, st8, ne]
  | 7, _ => simp [st64, st8]

theorem rev64_byte (l : BitVec 64) (i : Nat) (hi : i < 8) :
    (rev64 l).extractLsb' (8 * i) 8 = l.extractLsb' (8 * (7 - i)) 8 := by
  match i, hi with
  | 0, _ => show (rev64 l).extractLsb' 0 8 = l.extractLsb' 56 8; simp only [rev64]; bv_decide
  | 1, _ => show (rev64 l).extractLsb' 8 8 = l.extractLsb' 48 8; simp only [rev64]; bv_decide
  | 2, _ => show (rev64 l).extractLsb' 16 8 = l.extractLsb' 40 8; simp only [rev64]; bv_decide
  | 3, _ => show (rev64 l).extractLsb' 24 8 = l.extractLsb' 32 8; simp only [rev64]; bv_decide
  | 4, _ => show (rev64 l).extractLsb' 32 8 = l.extractLsb' 24 8; simp only [rev64]; bv_decide
  | 5, _ => show (rev64 l).extractLsb' 40 8 = l.extractLsb' 16 8; simp only [rev64]; bv_decide
  | 6, _ => show (rev64 l).extractLsb' 48 8 = l.extractLsb' 8 8; simp only [rev64]; bv_decide
  | 7, _ => show (rev64 l).extractLsb' 56 8 = l.extractLsb' 0 8; simp only [rev64]; bv_decide

theorem extract_extract (v : BitVec 256) (s1 s2 n : Nat) (h : s2 + n ≤ 64) :
    (v.extractLsb' s1 64).extractLsb' s2 n = v.extractLsb' (s1 + s2) n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [BitVec.getLsbD_extractLsb']
  by_cases hi : i < n
  · simp [hi, show s2 + i < 64 by omega, Nat.add_assoc]
  · simp [hi]

/-- The bytes `stBE` writes: byte `j` is `v`'s big-endian byte `j`. -/
theorem stBE_byte (m : Mem) (a : BitVec 64) (v : Evm.U256) (j : Nat) (hj : j < 32) :
    stBE m a v (off a j) = v.extractLsb' (8 * (31 - j)) 8 := by
  have miss : ∀ k, k + 8 ≤ 32 → (j < k ∨ k + 8 ≤ j) → ∀ i < 8, off a j ≠ off (off a k) i := by
    intro k hk hjk i hi; rw [off_off]; exact off_ne_off a j (k + i) (by omega) (by omega) (by omega)
  have at_ : ∀ k, k + 8 ≤ 32 → k ≤ j → j < k + 8 → off a j = off (off a k) (j - k) := by
    intro k hk h1 h2; rw [off_off]; congr 2; omega
  simp only [stBE]
  rcases (show j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) ∨ 24 ≤ j by omega) with h | h | h | h
  · rw [st64_out _ _ _ _ (miss 24 (by omega) (by omega)), st64_out _ _ _ _ (miss 16 (by omega) (by omega)),
        st64_out _ _ _ _ (miss 8 (by omega) (by omega)), st64_at _ _ _ j h, rev64_byte _ j h,
        extract_extract _ _ _ _ (by omega)]
    congr 1; omega
  · rw [st64_out _ _ _ _ (miss 24 (by omega) (by omega)), st64_out _ _ _ _ (miss 16 (by omega) (by omega)),
        at_ 8 (by omega) h.1 h.2, st64_at _ _ _ (j - 8) (by omega), rev64_byte _ (j - 8) (by omega),
        extract_extract _ _ _ _ (by omega)]
    congr 1; omega
  · rw [st64_out _ _ _ _ (miss 24 (by omega) (by omega)), at_ 16 (by omega) h.1 h.2,
        st64_at _ _ _ (j - 16) (by omega), rev64_byte _ (j - 16) (by omega), extract_extract _ _ _ _ (by omega)]
    congr 1; omega
  · rw [at_ 24 (by omega) h (by omega), st64_at _ _ _ (j - 24) (by omega), rev64_byte _ (j - 24) (by omega),
        extract_extract _ _ _ _ (by omega)]
    congr 1; omega

/-! ## One buffered write -/

def wWidth (w : MemWrite) : Nat := if w.isByte then 1 else 32

/-- What a write leaves in memory: MSTORE8 the low byte, MSTORE the 32 BE bytes. -/
def applyW (mb : BitVec 64) (es : List Evm.U256) (m : Mem) (w : MemWrite) : Mem :=
  if w.isByte then st8 m (off mb w.off) ((eval w.val es).extractLsb' 0 8)
  else stBE m (off mb w.off) (eval w.val es)

theorem applyW_out (mb : BitVec 64) (es : List Evm.U256) (m : Mem) (w : MemWrite) (x : BitVec 64)
    (hx : ∀ i < wWidth w, x ≠ off (off mb w.off) i) : applyW mb es m w x = m x := by
  unfold applyW wWidth at *
  split
  · rename_i hb; simp only [hb, ite_true] at hx
    exact st8_other _ _ _ _ (by have := hx 0 (by omega); rwa [off_zero] at this)
  · rename_i hb; simp only [hb] at hx; exact stBE_out _ _ _ _ hx

/-- `memBaseAtT`: x14 ← the buffer pointer plus the constant offset. -/
theorem memBaseAt_run (H : Helpers) (st : BitVec 64) (o : Nat) (ho : o < 2 ^ 64) (rest : List AInstr) (s : RS)
    (h20 : s.regs .x20 = st) :
    ∃ s', run H (memBaseAtT armFlush o ++ rest) s = run H rest s' ∧
      s'.regs .x14 = off (mbAt s.mem st) o ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x14 → r ≠ .x15 → s'.regs r = s.regs r) := by
  simp only [memBaseAtT, armFlush, List.cons_append]
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
    · rw [movImmA, List.append_assoc, movImmInstrs_run H _ _ ho, List.singleton_append,
          run_cons_step H _ _ _ _ (ctrl_addReg ..) (step_addReg ..)]
      refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
      · rs_simp; rw [h20]; rfl
      · intro r h14 h15; rs_simp; simp [h14, h15]

/-- `emitMemWriteT`: the slot's value lands in the buffer at the constant offset. -/
theorem memWrite_run (H : Helpers) (st : BitVec 64) (idx : Expr → Nat) (w : MemWrite) (es : List Evm.U256)
    (rest : List AInstr) (s : RS) (h20 : s.regs .x20 = st) (ho : w.off < 2 ^ 64)
    (hslot : ld256 s.mem (slotAddr s.sp (idx w.val)) = eval w.val es) (hn : 32 * idx w.val < 2 ^ 64) :
    ∃ s', run H (emitMemWriteT armFlush idx w ++ rest) s = run H rest s' ∧
      s'.mem = applyW (mbAt s.mem st) es s.mem w ∧ s'.sp = s.sp ∧
      (∀ r, keep r = true → s'.regs r = s.regs r) := by
  simp only [emitMemWriteT, List.append_assoc]
  obtain ⟨s1, h1, hv1, hsp1, hmem1, _, hregs1⟩ := loadSlot_x6_run H (idx w.val) hn _ s
  rw [show loadSlotT armFlush .x6 (idx w.val) = loadSlotA .x6 (idx w.val) from rfl, h1]
  have h20' : s1.regs .x20 = st := by
    rw [hregs1 _ (by decide) (by decide) (by decide) (by decide) (by decide), h20]
  obtain ⟨s2, h2, h14, hsp2, hmem2, _, hregs2⟩ := memBaseAt_run H st w.off ho _ s1 h20'
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
    simp only [armFlush, List.singleton_append]
    rw [run_cons_step H _ _ _ _ (ctrl_strbBase ..) (step_strbBase ..)]
    refine ⟨_, rfl, ?_, by rs_simp; exact hsp2', ?_⟩
    · rs_simp; rw [h14, hx6, hmem2', extract_extract _ _ _ _ (by omega), Nat.zero_add]
    · intro r hr; rs_simp; exact hkeep r hr
  · rename_i hb
    simp only [armFlush, List.cons_append, List.nil_append]
    rw [run_cons_step H _ _ _ _ (ctrl_rev ..) (step_rev ..),
        run_cons_step H _ _ _ _ (ctrl_rev ..) (step_rev ..),
        run_cons_step H _ _ _ _ (ctrl_rev ..) (step_rev ..),
        run_cons_step H _ _ _ _ (ctrl_rev ..) (step_rev ..)]
    rs_simp
    rw [hx6, hx7, hx8, hx9]
    rw [run_cons_step H _ _ _ _ (ctrl_strBase ..) (step_strBase ..),
        run_cons_step H _ _ _ _ (ctrl_strOff ..) (step_strOff ..),
        run_cons_step H _ _ _ _ (ctrl_strOff ..) (step_strOff ..),
        run_cons_step H _ _ _ _ (ctrl_strOff ..) (step_strOff ..)]
    refine ⟨_, rfl, ?_, by rs_simp; exact hsp2', ?_⟩
    · rs_simp; rw [h14, hmem2']; rfl
    · intro r hr
      obtain ⟨h0, h1', h2', h3, _, _, _, _, _, _, _, _, _, _, _, _⟩ := keep_ne r hr
      rs_simp; simp only [h0, h1', h2', h3, ite_false]; exact hkeep r hr

/-! ## The high-water update -/

theorem mpUpdate_run (H : Helpers) (st : BitVec 64) (maxEnd : Nat) (hmax : maxEnd < 2 ^ 64) (rest : List AInstr)
    (s : RS) (h20 : s.regs .x20 = st) :
    ∃ s', run H (mpUpdateFlushT armFlush maxEnd ++ rest) s = run H rest s' ∧
      s'.sp = s.sp ∧ (∀ r, r ≠ .x15 → r ≠ .x16 → s'.regs r = s.regs r) ∧
      (mpAt s'.mem st).toNat = max (mpAt s.mem st).toNat maxEnd ∧
      (∀ x, (∀ i < 8, x ≠ off (off st 24) i) → s'.mem x = s.mem x) := by
  simp only [mpUpdateFlushT, armFlush, movImmA, List.append_assoc, List.cons_append, List.nil_append]
  rw [movImmInstrs_run H _ _ hmax,
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
theorem writes_run (H : Helpers) (fp mb st : BitVec 64) (idx : Expr → Nat) (es : List Evm.U256)
    (rest : List AInstr) : ∀ (ws : List MemWrite) (s : RS),
    s.sp = fp → s.regs .x20 = st → mbAt s.mem st = mb →
    (∀ w ∈ ws, w.off < 2 ^ 64) → (∀ w ∈ ws, 32 * idx w.val < 2 ^ 64) →
    (∀ w ∈ ws, ld256 s.mem (slotAddr fp (idx w.val)) = eval w.val es) →
    (∀ w ∈ ws, ∀ i < wWidth w,
      (∀ w' ∈ ws, ∀ j < 32, off (off mb w.off) i ≠ off (slotAddr fp (idx w'.val)) j) ∧
      (∀ j < 8, off (off mb w.off) i ≠ off (off st 40) j)) →
    ∃ s', run H (ws.flatMap (emitMemWriteT armFlush idx) ++ rest) s = run H rest s' ∧
      s'.mem = ws.foldl (applyW mb es) s.mem ∧ s'.sp = s.sp ∧ (∀ r, keep r = true → s'.regs r = s.regs r)
  | [], s, _, _, _, _, _, _, _ => ⟨s, by simp, rfl, rfl, fun _ _ => rfl⟩
  | w :: ws, s, hsp, h20, hmb, hoff, hn, hslots, hdisj => by
    simp only [List.flatMap_cons, List.append_assoc, List.foldl_cons]
    obtain ⟨s1, h1, hmem1, hsp1, hregs1⟩ := memWrite_run H st idx w es _ s h20 (hoff w (by simp))
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
    obtain ⟨s', h', hmem', hsp', hregs'⟩ := writes_run H fp mb st idx es rest ws s1 (by rw [hsp1, hsp])
      (by rw [hregs1 _ (by decide), h20]) hmb1 (fun w' hw' => hoff w' (by simp [hw']))
      (fun w' hw' => hn w' (by simp [hw'])) hslots1
      (fun w' hw' i hi => ⟨fun w'' hw'' => (hdisj w' (by simp [hw']) i hi).1 w'' (by simp [hw'']),
                           (hdisj w' (by simp [hw']) i hi).2⟩)
    refine ⟨s', h', ?_, by rw [hsp', hsp1], fun r hr => by rw [hregs' r hr, hregs1 r hr]⟩
    rw [hmem', hmem1]

/-! ## The whole commit -/

/-- `memCommitT`'s `maxEnd`. -/
def maxEndOf (ws : List MemWrite) : Nat := ws.foldl (fun m w => max m (w.off + wWidth w)) 0

theorem memCommitT_eq (idx : Expr → Nat) (ws : List MemWrite) (hne : ws ≠ []) :
    memCommitT armFlush idx ws =
      memExpandFlushT armFlush (maxEndOf ws) ++ mpUpdateFlushT armFlush (maxEndOf ws) ++
        ws.flatMap (emitMemWriteT armFlush idx) := by
  unfold memCommitT
  rw [if_neg (by simpa using hne)]
  rfl

theorem foldl_max_acc (ws : List MemWrite) : ∀ acc, acc ≤ ws.foldl (fun m w => max m (w.off + wWidth w)) acc := by
  intro acc
  induction ws generalizing acc with
  | nil => exact Nat.le_refl _
  | cons w ws ih => simp only [List.foldl_cons]; exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem le_maxEnd (ws : List MemWrite) (w : MemWrite) (hw : w ∈ ws) : w.off + wWidth w ≤ maxEndOf ws := by
  unfold maxEndOf
  generalize 0 = acc
  induction ws generalizing acc with
  | nil => simp at hw
  | cons w' ws ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_acc ws _)
    · exact ih hw _

theorem maxEnd_lt (ws : List MemWrite) (h : ∀ w ∈ ws, w.off + wWidth w < 2 ^ 64) : maxEndOf ws < 2 ^ 64 := by
  unfold maxEndOf
  have : ∀ acc, acc < 2 ^ 64 → ws.foldl (fun m w => max m (w.off + wWidth w)) acc < 2 ^ 64 := by
    induction ws with
    | nil => intro acc h; simpa using h
    | cons w ws ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      exact ih (fun w' hw' => h w' (by simp [hw'])) _ (by have := h w (by simp); omega)
  exact this 0 (by decide)

/-- The write list applied to a memory, at one address, depends on that address only. -/
theorem applyW_congr_at (mb : BitVec 64) (es : List Evm.U256) (m m' : Mem) (w : MemWrite) (x : BitVec 64)
    (h : m x = m' x) : applyW mb es m w x = applyW mb es m' w x := by
  unfold applyW
  split
  · simp only [st8]; split <;> simp [h]
  · by_cases hx : ∀ i < 32, x ≠ off (off mb w.off) i
    · rw [stBE_out _ _ _ _ hx, stBE_out _ _ _ _ hx, h]
    · simp only [not_forall, not_not] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [stBE_byte _ _ _ _ hi, stBE_byte _ _ _ _ hi]

theorem applyWs_congr_at (mb : BitVec 64) (es : List Evm.U256) : ∀ (ws : List MemWrite) (m m' : Mem) (x : BitVec 64),
    m x = m' x → ws.foldl (applyW mb es) m x = ws.foldl (applyW mb es) m' x
  | [], _, _, _, h => h
  | w :: ws, m, m', x, h => by
    simp only [List.foldl_cons]
    exact applyWs_congr_at mb es ws _ _ x (applyW_congr_at mb es m m' w x h)

theorem applyWs_out (mb : BitVec 64) (es : List Evm.U256) : ∀ (ws : List MemWrite) (m : Mem) (x : BitVec 64),
    (∀ w ∈ ws, ∀ i < wWidth w, x ≠ off (off mb w.off) i) → ws.foldl (applyW mb es) m x = m x
  | [], _, _, _ => rfl
  | w :: ws, m, x, h => by
    simp only [List.foldl_cons]
    rw [applyWs_out mb es ws _ x (fun w' hw' => h w' (by simp [hw'])), applyW_out _ _ _ _ _ (h w (by simp))]

/-- The EvmState struct and its byte buffer, against the frame, the arena and
    the helper window. `cap` is the capacity read at entry (never written). -/
structure MLay (F : Fr) (st mb : BitVec 64) (cap : Nat) : Prop where
  stOk  : st.toNat + 64 < 2 ^ 64
  mbOk  : mb.toNat + cap < 2 ^ 64
  capLt : cap < 2 ^ 32
  stFrame  : ∀ i, 24 ≤ i → i < 64 → ∀ j < 32 * F.n + 16, off st i ≠ off F.fp j
  stStack  : ∀ i, 24 ≤ i → i < 64 → ∀ j < 32 * 1024, off st i ≠ off F.base j
  stOut    : ∀ i, 24 ≤ i → i < 64 → belowSp F.fp (off st i) = false
  bufFrame : ∀ i < cap, ∀ j < 32 * F.n + 16, off mb i ≠ off F.fp j
  bufStack : ∀ i < cap, ∀ j < 32 * 1024, off mb i ≠ off F.base j
  bufSt    : ∀ i < cap, ∀ j, 24 ≤ j → j < 64 → off mb i ≠ off st j
  bufOut   : ∀ i < cap, belowSp F.fp (off mb i) = false

/-- Struct words at distinct offsets are distinct bytes. -/
theorem st_word_ne (st : BitVec 64) (a b i j : Nat) (ha : a + 8 ≤ b ∨ b + 8 ≤ a) (ha' : a < 64) (hb' : b < 64)
    (hi : i < 8) (hj : j < 8) : off (off st a) i ≠ off (off st b) j := by
  rw [off_off, off_off]; exact off_ne_off st (a + i) (b + j) (by omega) (by omega) (by omega)

/-- `memCommitT` on a non-empty write list. -/
theorem memCommit_run (H : Helpers) (F : Fr) (idx : Expr → Nat) (st mb : BitVec 64) (ws : List MemWrite)
    (hne : ws ≠ []) (es : List Evm.U256) (rest : List AInstr) (s : RS)
    (hL : Lay F) (hM : MLay F st mb (capAt s.mem st).toNat)
    (hsp : s.sp = F.fp) (h20 : s.regs .x20 = st) (hmb : mbAt s.mem st = mb)
    (hok : (msAt s.mem st).toNat ≤ (capAt s.mem st).toNat)
    (hoff : ∀ w ∈ ws, w.off + wWidth w < 2 ^ 64)
    (hidx : ∀ w ∈ ws, idx w.val < F.n)
    (hslots : ∀ w ∈ ws, ld256 s.mem (slotAddr F.fp (idx w.val)) = eval w.val es) :
    ((capAt s.mem st).toNat < maxEndOf ws →
      ∃ sf, run H (memCommitT armFlush idx ws ++ rest) s = .fault "_eita_oog" sf) ∧
    (maxEndOf ws ≤ (capAt s.mem st).toNat →
      (s.regs .x22).toNat < ecost ((msAt s.mem st).toNat / 32) (wordsOf (maxEndOf ws)) →
      ∃ sf, run H (memCommitT armFlush idx ws ++ rest) s = .fault "_eita_oog" sf) ∧
    (maxEndOf ws ≤ (capAt s.mem st).toNat →
      ecost ((msAt s.mem st).toNat / 32) (wordsOf (maxEndOf ws)) ≤ (s.regs .x22).toNat →
      ∃ s', run H (memCommitT armFlush idx ws ++ rest) s = run H rest s' ∧
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
  rw [memCommitT_eq idx ws hne, List.append_assoc, List.append_assoc]
  obtain ⟨hE1, hE2, hE3⟩ := memExpand_run H st (maxEndOf ws) _ s h20 hmaxlt hM.capLt hok
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
  obtain ⟨s2, h2, hsp2, hregs2, hmp2, hmem2⟩ := mpUpdate_run H st (maxEndOf ws) hmaxlt _ s1 h20_1
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
  obtain ⟨s3, h3, hmem3, hsp3, hregs3⟩ := writes_run H F.fp mb st idx es rest ws s2 (by rw [hsp2, hsp1, hsp])
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

end Evm.CL.ARM64.MemCommitSem
