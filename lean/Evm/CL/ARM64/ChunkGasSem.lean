/-
  Evm.CL.ARM64.ChunkGasSem — the gas gadgets' PROGRAMS, run under `AsmRun`,
  are `GInstr.denote`.

  `ChunkGas` proved its theorems about the denotation (`compensation_refines`)
  and gated the instructions against the hand-written text; the joint between
  the `AInstr` program and `GInstr.denote` was by inspection. Here each gadget
  is executed symbolically from any state: the gas register ends at the
  denotation's gas when it does not halt, and the fragment faults to
  `_eita_oog` exactly when the denotation halts. The scratch registers the
  gadgets use (x14, x15) and the flags are the only other things touched.
-/

import Evm.CL.AsmRun
import Evm.CL.ARM64.ChunkGas

namespace Evm.CL.ARM64.ChunkGasSem

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun Evm.CL.ARM64.ChunkGas

/-! ## `mov r, #v` is `v` -/

theorem ofNat_mod_65536 (v : Nat) :
    BitVec.ofNat 64 (v % 65536) = BitVec.ofNat 64 v &&& 65535#64 := by
  have : v % 65536 = v &&& 2 ^ 16 - 1 := (Nat.and_two_pow_sub_one_eq_mod v 16).symm
  rw [this, BitVec.ofNat_and]

theorem ofNat_shiftRight (v k : Nat) (h : v < 2 ^ 64) :
    BitVec.ofNat 64 (v >>> k) = BitVec.ofNat 64 v >>> k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _) h

/-- The chunk `(v >>> 16k) % 65536`, as a bitvector. -/
theorem ofNat_chunk (v k : Nat) (h : v < 2 ^ 64) :
    BitVec.ofNat 64 ((v >>> k) % 65536) = (BitVec.ofNat 64 v >>> k) &&& 65535#64 := by
  rw [ofNat_mod_65536, ofNat_shiftRight v k h]

/-- A `movk` into a register whose bits above `16·hw` are clear. -/
theorem movk_sem (w : BitVec 64) (k : Nat) (hk : k < 3) :
    ((w &&& (BitVec.ofNat 64 (2 ^ (16 * (k + 1)) - 1))) &&& ~~~(65535#64 <<< (16 * (k + 1)))) |||
      (((w >>> (16 * (k + 1))) &&& 65535#64) <<< (16 * (k + 1))) =
    w &&& BitVec.ofNat 64 (2 ^ (16 * (k + 2)) - 1) := by
  match k with
  | 0 => simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.reduceSub]; bv_decide
  | 1 => simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.reduceSub]; bv_decide
  | 2 => simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.reduceSub]; bv_decide
  | k + 3 => omega

theorem movk_skip (w : BitVec 64) (k : Nat) (hk : k < 3)
    (hz : (w >>> (16 * (k + 1))) &&& 65535#64 = 0) :
    w &&& BitVec.ofNat 64 (2 ^ (16 * (k + 1)) - 1) = w &&& BitVec.ofNat 64 (2 ^ (16 * (k + 2)) - 1) := by
  match k with
  | 0 => simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at hz ⊢; bv_decide
  | 1 => simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at hz ⊢; bv_decide
  | 2 => simp only [Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, Nat.reduceSub] at hz ⊢; bv_decide
  | k + 3 => omega

/-- The register after the first `k` 16-bit stages. -/
def stage (w : BitVec 64) (k : Nat) : BitVec 64 := w &&& BitVec.ofNat 64 (2 ^ (16 * k) - 1)

theorem stage_four (w : BitVec 64) : stage w 4 = w := by
  simp only [stage, Nat.reduceMul, Nat.reducePow, Nat.reduceSub]; bv_decide

/-- One optional `movk` stage at `hw = k + 1`, from `stage w (k+1)` to `stage w (k+2)`. -/
theorem movk_stage_run (H : Helpers) (r : Reg) (v k : Nat) (hv : v < 2 ^ 64) (hk : k < 3)
    (rest : List AInstr) (s : RS) (hs : s.regs r = stage (BitVec.ofNat 64 v) (k + 1)) :
    run H ((if (v >>> (16 * (k + 1))) % 65536 > 0
            then [AInstr.movkImm r ((v >>> (16 * (k + 1))) % 65536) (k + 1)] else []) ++ rest) s =
    run H rest (s.set r (stage (BitVec.ofNat 64 v) (k + 2))) := by
  split
  · rw [List.singleton_append, run_cons_step H _ rest s _ (ctrl_movkImm ..) (step_movkImm ..)]
    congr 1
    simp only [RS.set, hs, ofNat_chunk v _ hv]
    congr 1
    funext r'
    split
    · exact movk_sem (BitVec.ofNat 64 v) k hk
    · rfl
  · rw [List.nil_append]
    have hz : (BitVec.ofNat 64 v >>> (16 * (k + 1))) &&& 65535#64 = 0 := by
      rw [← ofNat_chunk v _ hv]
      have : (v >>> (16 * (k + 1))) % 65536 = 0 := by omega
      simp [this]
    rw [set_eq_self s r _ (by rw [hs]; exact movk_skip (BitVec.ofNat 64 v) k hk hz)]

/-- The optional `movk` stage `i + 1`. -/
def opt (r : Reg) (v i : Nat) : List AInstr :=
  if (v >>> (16 * (i + 1))) % 65536 > 0
  then [AInstr.movkImm r ((v >>> (16 * (i + 1))) % 65536) (i + 1)] else []

theorem movImmInstrs_eq (r : Reg) (v : Nat) :
    movImmInstrs r v = [AInstr.movzImm r (v % 65536)] ++ opt r v 0 ++ opt r v 1 ++ opt r v 2 := by
  have hr : List.range 3 = [0, 1, 2] := rfl
  simp only [movImmInstrs, hr, List.filterMap_cons, List.filterMap_nil, opt]
  by_cases h0 : (v >>> (16 * (0 + 1))) % 65536 > 0 <;>
  by_cases h1 : (v >>> (16 * (1 + 1))) % 65536 > 0 <;>
  by_cases h2 : (v >>> (16 * (2 + 1))) % 65536 > 0 <;>
  simp [h0, h1, h2]

/-- Running `movImmInstrs r v`: the register holds `v`, nothing else changes. -/
theorem movImmInstrs_run (H : Helpers) (r : Reg) (v : Nat) (hv : v < 2 ^ 64) (rest : List AInstr) (s : RS) :
    run H (movImmInstrs r v ++ rest) s = run H rest (s.set r (BitVec.ofNat 64 v)) := by
  rw [movImmInstrs_eq, List.append_assoc, List.append_assoc, List.append_assoc, List.singleton_append,
      run_cons_step H _ _ s _ (ctrl_movzImm ..) (step_movzImm ..)]
  have h1 : (s.set r (BitVec.ofNat 64 (v % 65536))).regs r = stage (BitVec.ofNat 64 v) (0 + 1) := by
    simp [RS.set, stage, ofNat_mod_65536]
  rw [show opt r v 0 = (if (v >>> (16 * (0 + 1))) % 65536 > 0
                        then [AInstr.movkImm r ((v >>> (16 * (0 + 1))) % 65536) (0 + 1)] else []) from rfl,
      movk_stage_run H r v 0 hv (by omega) _ _ h1, set_set_same]
  rw [show opt r v 1 = (if (v >>> (16 * (1 + 1))) % 65536 > 0
                        then [AInstr.movkImm r ((v >>> (16 * (1 + 1))) % 65536) (1 + 1)] else []) from rfl,
      movk_stage_run H r v 1 hv (by omega) _ _ (by simp [RS.set]), set_set_same]
  rw [show opt r v 2 = (if (v >>> (16 * (2 + 1))) % 65536 > 0
                        then [AInstr.movkImm r ((v >>> (16 * (2 + 1))) % 65536) (2 + 1)] else []) from rfl,
      movk_stage_run H r v 2 hv (by omega) _ _ (by simp [RS.set]), set_set_same]
  rw [show (2 + 2 : Nat) = 4 from rfl, stage_four]

/-! ## The gadgets -/

/-- Gas as the denotation reads it. -/
def gasOf (s : RS) : Nat := (s.regs .x22).toNat

theorem hs_subFlags (a : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) :
    bcHolds .hs (subFlags a (BitVec.ofNat 64 n)) = decide (n ≤ a.toNat) := by
  simp [bcHolds, subFlags, BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem toNat_sub_ofNat (a : BitVec 64) (n : Nat) (hn : n < 2 ^ 64) (h : n ≤ a.toNat) :
    (a - BitVec.ofNat 64 n).toNat = a.toNat - n := by
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; exact h),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

/-- The OOG tail of a checked gadget: `b.hs lbl ; b _eita_oog ; lbl:`. -/
theorem oog_tail_run (H : Helpers) (lbl : String) (rest : List AInstr) (s : RS) :
    run H ([AInstr.bcLbl .hs lbl, .bFar "_eita_oog", .label lbl] ++ rest) s =
      if bcHolds .hs s.flags then run H rest s else .fault "_eita_oog" s := by
  rw [List.cons_append, run_cons_bcLbl]
  split
  · simp [AsmRun.skipTo, run_cons_label]
  · simp [run_cons_bFar]

/-- `charge n`: gas down by `n`, or the OOG fault. x14 and the flags are scratch. -/
theorem charge_run (H : Helpers) (n : Nat) (hn : n < 2 ^ 64) (lbl : String) (rest : List AInstr) (s : RS) :
    (n ≤ gasOf s →
      ∃ s', run H ((GInstr.charge n lbl).instrs ++ rest) s = run H rest s' ∧
        gasOf s' = gasOf s - n ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
        (∀ r, r ≠ .x22 → r ≠ .x14 → s'.regs r = s.regs r)) ∧
    (¬ n ≤ gasOf s → ∃ s', run H ((GInstr.charge n lbl).instrs ++ rest) s = .fault "_eita_oog" s') := by
  simp only [GInstr.instrs]
  by_cases hsmall : n ≤ 4095
  · rw [if_pos hsmall, List.append_assoc, List.singleton_append,
        run_cons_step H _ _ s _ (ctrl_subsImm ..) (step_subsImm ..), oog_tail_run]
    simp only [AsmRun.withFlags_flags, hs_subFlags _ _ hn]
    constructor
    · intro hle
      have hle' : n ≤ (s.regs .x22).toNat := hle
      refine ⟨(s.set .x22 (s.regs .x22 - BitVec.ofNat 64 n)).withFlags
                (subFlags (s.regs .x22) (BitVec.ofNat 64 n)), ?_, ?_, rfl, rfl, ?_⟩
      · rw [decide_eq_true hle', if_pos rfl]
      · simp only [gasOf, AsmRun.withFlags_regs, AsmRun.set_regs, ite_true]
        exact toNat_sub_ofNat _ _ hn hle'
      · intro r h22 _; simp [RS.set, h22]
    · intro hnle
      have hnle' : ¬ n ≤ (s.regs .x22).toNat := hnle
      refine ⟨(s.set .x22 (s.regs .x22 - BitVec.ofNat 64 n)).withFlags
                (subFlags (s.regs .x22) (BitVec.ofNat 64 n)), ?_⟩
      rw [decide_eq_false hnle', if_neg (by simp)]
  · rw [if_neg hsmall, List.append_assoc, List.append_assoc, movImmInstrs_run H _ _ hn,
        List.singleton_append, run_cons_step H _ _ _ _ (ctrl_subsReg ..) (step_subsReg ..), oog_tail_run]
    simp only [AsmRun.withFlags_flags, AsmRun.set_regs, ite_true, if_neg (show Reg.x22 ≠ Reg.x14 by decide),
               hs_subFlags _ _ hn]
    constructor
    · intro hle
      have hle' : n ≤ (s.regs .x22).toNat := hle
      refine ⟨((s.set .x14 (BitVec.ofNat 64 n)).set .x22 (s.regs .x22 - BitVec.ofNat 64 n)).withFlags
                (subFlags (s.regs .x22) (BitVec.ofNat 64 n)), ?_, ?_, rfl, rfl, ?_⟩
      · rw [decide_eq_true hle', if_pos rfl]
      · simp only [gasOf, AsmRun.withFlags_regs, AsmRun.set_regs, ite_true,
                   if_neg (show Reg.x22 ≠ Reg.x14 by decide)]
        exact toNat_sub_ofNat _ _ hn hle'
      · intro r h22 h14; simp [RS.set, h22, h14]
    · intro hnle
      have hnle' : ¬ n ≤ (s.regs .x22).toNat := hnle
      refine ⟨((s.set .x14 (BitVec.ofNat 64 n)).set .x22 (s.regs .x22 - BitVec.ofNat 64 n)).withFlags
                (subFlags (s.regs .x22) (BitVec.ofNat 64 n)), ?_⟩
      rw [decide_eq_false hnle', if_neg (by simp)]

/-- `handBack rem`: gas up by `rem` (no wrap: gas is bounded by the block limit). x15 is scratch. -/
theorem handBack_run (H : Helpers) (rem : Nat) (rest : List AInstr) (s : RS)
    (hw : gasOf s + rem < 2 ^ 64) :
    ∃ s', run H ((GInstr.handBack rem).instrs ++ rest) s = run H rest s' ∧
      gasOf s' = gasOf s + rem ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.flags = s.flags ∧
      (∀ r, r ≠ .x22 → r ≠ .x15 → s'.regs r = s.regs r) := by
  simp only [GInstr.instrs]
  rw [List.append_assoc, movImmInstrs_run H _ _ (by omega), List.singleton_append,
      run_cons_step H _ _ _ _ (ctrl_addReg ..) (step_addReg ..)]
  have hw' : (s.regs .x22).toNat + rem < 2 ^ 64 := hw
  refine ⟨_, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [gasOf, AsmRun.set_regs, ite_true, if_neg (show Reg.x22 ≠ Reg.x15 by decide)]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : rem < 2 ^ 64),
        Nat.mod_eq_of_lt hw']
  · intro r h22 h15; simp [RS.set, h22, h15]

/-- `retake rem`: like `charge`, through x15. -/
theorem retake_run (H : Helpers) (rem : Nat) (hn : rem < 2 ^ 64) (lbl : String) (rest : List AInstr) (s : RS) :
    (rem ≤ gasOf s →
      ∃ s', run H ((GInstr.retake rem lbl).instrs ++ rest) s = run H rest s' ∧
        gasOf s' = gasOf s - rem ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
        (∀ r, r ≠ .x22 → r ≠ .x15 → s'.regs r = s.regs r)) ∧
    (¬ rem ≤ gasOf s → ∃ s', run H ((GInstr.retake rem lbl).instrs ++ rest) s = .fault "_eita_oog" s') := by
  simp only [GInstr.instrs]
  rw [List.append_assoc, movImmInstrs_run H _ _ hn, List.cons_append,
      run_cons_step H _ _ _ _ (ctrl_subsReg ..) (step_subsReg ..), oog_tail_run]
  simp only [AsmRun.withFlags_flags, AsmRun.set_regs, ite_true, if_neg (show Reg.x22 ≠ Reg.x15 by decide),
             hs_subFlags _ _ hn]
  constructor
  · intro hle
    have hle' : rem ≤ (s.regs .x22).toNat := hle
    refine ⟨((s.set .x15 (BitVec.ofNat 64 rem)).set .x22 (s.regs .x22 - BitVec.ofNat 64 rem)).withFlags
              (subFlags (s.regs .x22) (BitVec.ofNat 64 rem)), ?_, ?_, rfl, rfl, ?_⟩
    · rw [decide_eq_true hle', if_pos rfl]
    · simp only [gasOf, AsmRun.withFlags_regs, AsmRun.set_regs, ite_true,
                 if_neg (show Reg.x22 ≠ Reg.x15 by decide)]
      exact toNat_sub_ofNat _ _ hn hle'
    · intro r h22 h15; simp [RS.set, h22, h15]
  · intro hnle
    have hnle' : ¬ rem ≤ (s.regs .x22).toNat := hnle
    refine ⟨((s.set .x15 (BitVec.ofNat 64 rem)).set .x22 (s.regs .x22 - BitVec.ofNat 64 rem)).withFlags
              (subFlags (s.regs .x22) (BitVec.ofNat 64 rem)), ?_⟩
    rw [decide_eq_false hnle', if_neg (by simp)]

/-! ## The joint: every gadget's program is its denotation -/

/-- `GInstr.denote` read off the machine: the gadget either continues with
    the denotation's gas, or faults to `_eita_oog` exactly when the
    denotation halts. -/
theorem ginstr_run (H : Helpers) (g : GInstr) (rest : List AInstr) (s : RS)
    (hb : ∀ n lbl, g = .charge n lbl → n < 2 ^ 64)
    (hr : ∀ rem lbl, g = .retake rem lbl → rem < 2 ^ 64)
    (hh : ∀ rem, g = .handBack rem → gasOf s + rem < 2 ^ 64) :
    let d := g.denote { gas := gasOf s, halted := false }
    (d.halted = false → ∃ s', run H (g.instrs ++ rest) s = run H rest s' ∧ gasOf s' = d.gas ∧
                         s'.sp = s.sp ∧ s'.mem = s.mem) ∧
    (d.halted = true → ∃ s', run H (g.instrs ++ rest) s = .fault "_eita_oog" s') := by
  intro d
  cases g with
  | charge n lbl =>
    have := charge_run H n (hb n lbl rfl) lbl rest s
    by_cases hle : n ≤ gasOf s
    · obtain ⟨s', h1, h2, h3, h4, _⟩ := this.1 hle
      refine ⟨fun _ => ⟨s', h1, ?_, h3, h4⟩, fun hh => ?_⟩
      · simp [d, GInstr.denote, hle, h2]
      · simp [d, GInstr.denote, hle] at hh
    · obtain ⟨s', h1⟩ := this.2 hle
      refine ⟨fun hh => ?_, fun _ => ⟨s', h1⟩⟩
      simp [d, GInstr.denote, hle, oog] at hh
  | handBack rem =>
    obtain ⟨s', h1, h2, h3, h4, _, _⟩ := handBack_run H rem rest s (hh rem rfl)
    refine ⟨fun _ => ⟨s', h1, ?_, h3, h4⟩, fun hh => ?_⟩
    · simp [d, GInstr.denote, h2]
    · simp [d, GInstr.denote] at hh
  | retake rem lbl =>
    have := retake_run H rem (hr rem lbl rfl) lbl rest s
    by_cases hle : rem ≤ gasOf s
    · obtain ⟨s', h1, h2, h3, h4, _⟩ := this.1 hle
      refine ⟨fun _ => ⟨s', h1, ?_, h3, h4⟩, fun hh => ?_⟩
      · simp [d, GInstr.denote, hle, h2]
      · simp [d, GInstr.denote, hle] at hh
    · obtain ⟨s', h1⟩ := this.2 hle
      refine ⟨fun hh => ?_, fun _ => ⟨s', h1⟩⟩
      simp [d, GInstr.denote, hle, oog] at hh

end Evm.CL.ARM64.ChunkGasSem
