/-
  Evm.CL.ARM64.FlushMain — THE theorem: the ARM64 region flush, run under
  `AsmRun`, leaves the EVM stack holding the region's symbolic stack
  (`SymStack.denote`), the depth register at the new depth, the TOS/NOS
  caches reloaded, the frame restored — or faults to the stack-underflow /
  stack-overflow stubs exactly when the depth checks say so.

  All regions: the stack-pure ones and those absorbing constant-offset
  MSTORE/MSTORE8s (the memory commit: EELS's expansion charge, the high-water
  mark, the big-endian bytes in the buffer), or faults to `_eita_oog` exactly
  when the commit says so.
-/

import Evm.CL.ARM64.FlushSem
import Evm.CL.ARM64.DagSlots
import Evm.CL.ARM64.MemCommitSem

namespace Evm.CL.ARM64.FlushMain

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun Evm.CL.ARM64.JIT Evm.CL.ARM64.CoreSem
open Evm.CL.ARM64.FlushSem Evm.CL.ARM64.DagSlots Evm.CL.ARM64.MemCommitSem
open Evm.IR.SymExpr (Expr eval SymStack)

/-- The roots of the exit DAG: the exit prefix and the buffered write values. -/
def rootsOf (r : Region) : List Expr := r.ss.exprs ++ r.writes.map (·.val)

/-- The slot list and index the flush computes. -/
def slotsOf (r : Region) : List Expr := (rootsOf r).foldl collectSlots []
def idxOf (r : Region) : Expr → Nat := slotIdx (slotsOf r)

theorem dagSlots_of (r : Region) :
    dagSlots (r.ss.exprs ++ r.writes.map (·.val)) = ((slotsOf r).toArray, idxOf r) := rfl

/-- What the flush needs of a region (`RegionBuild` proves the builder maintains these). -/
structure RegionWF (r : Region) : Prop where
  cLe      : r.ss.consumed ≤ r.need
  /-- every entry read in the exit DAG is within `need` -/
  stackIdx : ∀ e ∈ slotsOf r, ∀ k, e = .stackAt k → k < r.need
  /-- the final net growth is within the recorded peak -/
  netLe    : (r.ss.exprs.length : Int) - r.ss.consumed ≤ r.maxNet
  /-- every buffered write's end fits 64-bit address arithmetic (`regionStore`) -/
  wOff     : ∀ w ∈ r.writes, w.off + wWidth w < 2 ^ 64

/-- The frame the flush opens, for a region of `n` slots at entry sp `sp0`. -/
def frameOf (sp0 : BitVec 64) (n : Nat) (base : BitVec 64) (d : Nat) (es : List Evm.U256) : Fr :=
  { fp := sp0 - BitVec.ofNat 64 16 - BitVec.ofNat 64 (32 * n), n := n, base := base, d := d, es := es }

/-- The new depth, as a `Nat`. -/
def newDepthOf (r : Region) (d : Nat) : Nat := newDepth d r.ss.exprs.length r.ss.consumed

/-! ## The memory side -/

/-- The gas the commit charges: EELS's expansion delta to the writes' end. -/
def memGas (r : Region) (m : Mem) (st : BitVec 64) : Nat :=
  ecost ((msAt m st).toNat / 32) (wordsOf (maxEndOf r.writes))

/-- `memory_size` after the commit. -/
def newMs (r : Region) (m : Mem) (st : BitVec 64) : Nat :=
  if wordsOf (maxEndOf r.writes) ≤ (msAt m st).toNat / 32 then (msAt m st).toNat
  else 32 * wordsOf (maxEndOf r.writes)

theorem maxEndOf_nil : maxEndOf [] = 0 := rfl
theorem wordsOf_zero : wordsOf 0 = 0 := rfl

theorem memGas_nil (r : Region) (m : Mem) (st : BitVec 64) (hw : r.writes = []) : memGas r m st = 0 := by
  simp [memGas, hw, maxEndOf_nil, wordsOf_zero, ecost]

/-- The struct words and the buffer agree between two memories. -/
def Agree (st mb : BitVec 64) (cap : Nat) (m m' : Mem) : Prop :=
  (∀ i, 24 ≤ i → i < 64 → m' (off st i) = m (off st i)) ∧ (∀ i < cap, m' (off mb i) = m (off mb i))

theorem Agree.refl (st mb : BitVec 64) (cap : Nat) (m : Mem) : Agree st mb cap m m :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem Agree.trans {st mb : BitVec 64} {cap : Nat} {m1 m2 m3 : Mem}
    (h1 : Agree st mb cap m1 m2) (h2 : Agree st mb cap m2 m3) : Agree st mb cap m1 m3 :=
  ⟨fun i h h' => (h2.1 i h h').trans (h1.1 i h h'), fun i h => (h2.2 i h).trans (h1.2 i h)⟩

theorem Agree.of_eq {st mb : BitVec 64} {cap : Nat} {m m' : Mem} (h : m' = m) : Agree st mb cap m m' := by
  subst h; exact Agree.refl _ _ _ _

/-- A change outside the arena, the frame and the helper window keeps both. -/
theorem Agree.of_out (F : Fr) (st mb : BitVec 64) (cap : Nat) (hM : MLay F st mb cap) (m m' : Mem)
    (h : ∀ x, (∀ j < 32 * 1024, x ≠ off F.base j) → (∀ i < 32 * F.n + 16, x ≠ off F.fp i) →
      belowSp F.fp x = false → m' x = m x) : Agree st mb cap m m' :=
  ⟨fun i h1 h2 => h _ (fun j hj => hM.stStack i h1 h2 j hj) (fun j hj => hM.stFrame i h1 h2 j hj) (hM.stOut i h1 h2),
   fun i hi => h _ (fun j hj => hM.bufStack i hi j hj) (fun j hj => hM.bufFrame i hi j hj) (hM.bufOut i hi)⟩

theorem Agree.of_stack (F : Fr) (st mb : BitVec 64) (cap : Nat) (hM : MLay F st mb cap) (m m' : Mem)
    (h : ∀ x, (∀ j < 32 * 1024, x ≠ off F.base j) → m' x = m x) : Agree st mb cap m m' :=
  ⟨fun i h1 h2 => h _ (fun j hj => hM.stStack i h1 h2 j hj), fun i hi => h _ (fun j hj => hM.bufStack i hi j hj)⟩

theorem Agree.of_frame (F : Fr) (st mb : BitVec 64) (cap : Nat) (hM : MLay F st mb cap) (m m' : Mem)
    (h : ∀ x, (∀ i < 32 * F.n + 16, x ≠ off F.fp i) → m' x = m x) : Agree st mb cap m m' :=
  ⟨fun i h1 h2 => h _ (fun j hj => hM.stFrame i h1 h2 j hj), fun i hi => h _ (fun j hj => hM.bufFrame i hi j hj)⟩

theorem Agree.word {st mb : BitVec 64} {cap : Nat} {m m' : Mem} (h : Agree st mb cap m m') (k : Nat)
    (hk : 24 ≤ k) (hk' : k + 8 ≤ 64) : ld64 m' (off st k) = ld64 m (off st k) :=
  ld64_eq_of_eq_on _ _ _ (fun i hi => by rw [off_off]; exact h.1 (k + i) (by omega) (by omega))

theorem Agree.ms {st mb : BitVec 64} {cap : Nat} {m m' : Mem} (h : Agree st mb cap m m') : msAt m' st = msAt m st :=
  h.word 48 (by omega) (by omega)
theorem Agree.mp {st mb : BitVec 64} {cap : Nat} {m m' : Mem} (h : Agree st mb cap m m') : mpAt m' st = mpAt m st :=
  h.word 24 (by omega) (by omega)
theorem Agree.cap {st mb : BitVec 64} {cap : Nat} {m m' : Mem} (h : Agree st mb cap m m') : capAt m' st = capAt m st :=
  h.word 56 (by omega) (by omega)
theorem Agree.mb {st mb : BitVec 64} {cap : Nat} {m m' : Mem} (h : Agree st mb cap m m') : mbAt m' st = mbAt m st :=
  h.word 40 (by omega) (by omega)
theorem Agree.buf {st mb : BitVec 64} {cap : Nat} {m m' : Mem} (h : Agree st mb cap m m') (ws : List MemWrite)
    (es : List Evm.U256) : ∀ i < cap, ws.foldl (applyW mb es) m' (off mb i) = ws.foldl (applyW mb es) m (off mb i) :=
  fun i hi => applyWs_congr_at mb es ws _ _ _ (h.2 i hi)

theorem memGas_agree {st mb : BitVec 64} {cap : Nat} {m m' : Mem} (r : Region) (h : Agree st mb cap m m') :
    memGas r m' st = memGas r m st := by unfold memGas; rw [h.ms]
theorem newMs_agree {st mb : BitVec 64} {cap : Nat} {m m' : Mem} (r : Region) (h : Agree st mb cap m m') :
    newMs r m' st = newMs r m st := by unfold newMs; rw [h.ms]

/-- What the commit leaves: `memory_size`, `mp`, the capacity and buffer
    pointer, the buffer bytes. -/
structure MemOut (r : Region) (st mb : BitVec 64) (es : List Evm.U256) (cap : Nat) (m m' : Mem) : Prop where
  ms   : (msAt m' st).toNat = newMs r m st
  mp   : (mpAt m' st).toNat = max (mpAt m st).toNat (maxEndOf r.writes)
  capE : capAt m' st = capAt m st
  mbE  : mbAt m' st = mb
  buf  : ∀ i < cap, m' (off mb i) = (r.writes.foldl (applyW mb es) m) (off mb i)

theorem MemOut.of_agree (r : Region) (st mb : BitVec 64) (es : List Evm.U256) (cap : Nat) (m m' : Mem)
    (hw : r.writes = []) (hmb : mbAt m st = mb) (h : Agree st mb cap m m') : MemOut r st mb es cap m m' := by
  refine ⟨?_, ?_, h.cap, by rw [h.mb, hmb], ?_⟩
  · rw [h.ms]; simp [newMs, hw, maxEndOf_nil, wordsOf_zero]
  · rw [h.mp, hw, maxEndOf_nil]; omega
  · intro i hi; rw [hw, List.foldl_nil]; exact h.2 i hi

theorem MemOut.agree_right {r : Region} {st mb : BitVec 64} {es : List Evm.U256} {cap : Nat} {m m' m'' : Mem}
    (h : MemOut r st mb es cap m m') (ha : Agree st mb cap m' m'') : MemOut r st mb es cap m m'' :=
  ⟨by rw [ha.ms, h.ms], by rw [ha.mp, h.mp], by rw [ha.cap, h.capE], by rw [ha.mb, h.mbE],
   fun i hi => by rw [ha.2 i hi, h.buf i hi]⟩

theorem MemOut.agree_left {r : Region} {st mb : BitVec 64} {es : List Evm.U256} {cap : Nat} {m m' m'' : Mem}
    (h : MemOut r st mb es cap m' m'') (ha : Agree st mb cap m m') : MemOut r st mb es cap m m'' :=
  ⟨by rw [h.ms, newMs_agree r ha], by rw [h.mp, ha.mp], by rw [h.capE, ha.cap], h.mbE,
   fun i hi => by rw [h.buf i hi, ha.buf r.writes es i hi]⟩

/-- The outcome of a successful flush. -/
structure FlushOut (r : Region) (base : BitVec 64) (d : Nat) (es : List Evm.U256) (fp : BitVec 64) (n : Nat)
    (st mb : BitVec 64) (s s' : RS) : Prop where
  sp   : s'.sp = s.sp
  x23  : s'.regs .x23 = BitVec.ofNat 64 (newDepthOf r d)
  regs : ∀ r', keep r' = true → r' ≠ .x23 → r' ≠ .x22 → s'.regs r' = s.regs r'
  gas  : (s'.regs .x22).toNat = (s.regs .x22).toNat - memGas r s.mem st
  fplr : s'.regs .x29 = s.regs .x29 ∧ s'.regs .x30 = s.regs .x30
  stack : ∀ j < newDepthOf r d, ld256 s'.mem (stackAddr base (newDepthOf r d) j) =
    (SymStack.denote r.ss es).getD j 0
  tos  : 1 ≤ newDepthOf r d → lhs s' = (SymStack.denote r.ss es).getD 0 0
  nos  : 2 ≤ newDepthOf r d → rhs armRq s' = (SymStack.denote r.ss es).getD 1 0
  memOut : MemOut r st mb es (capAt s.mem st).toNat s.mem s'.mem
  mem  : ∀ x, (∀ j < 32 * 1024, x ≠ off base j) → (∀ i < 32 * n + 16, x ≠ off fp i) →
    belowSp fp x = false → (∀ i, 24 ≤ i → i < 64 → x ≠ off st i) → (∀ i < (capAt s.mem st).toNat, x ≠ off mb i) →
    s'.mem x = s.mem x

/-- Step 4 from a state whose memory already holds the new stack: the depth
    register and the caches. -/
theorem tail_run (H : Helpers) (exprs : List Expr) (c : Nat) (base : BitVec 64) (d : Nat) (es : List Evm.U256)
    (rest : List AInstr) (s : RS) (hd : d ≤ 1024) (hc : c ≤ d) (hd' : newDepth d exprs.length c ≤ 1024)
    (hes : es.length = d) (h23 : s.regs .x23 = BitVec.ofNat 64 d) (h24 : s.regs .x24 = base)
    (hstored : ∀ i (h : i < exprs.length), ld256 s.mem (stackAddr base (newDepth d exprs.length c) i) = eval exprs[i] es)
    (hkept : ∀ k, c ≤ k → k < d → ld256 s.mem (stackAddr base d k) = es.getD k 0) :
    ∃ s', run H (depthUpdate ((exprs.length : Int) - c) ++ (armFlush.cacheReload ++ rest)) s = run H rest s' ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.regs .x23 = BitVec.ofNat 64 (newDepth d exprs.length c) ∧
      (∀ r', r' ≠ .x23 → r' ≠ .x6 → r' ≠ .x7 → r' ≠ .x8 → r' ≠ .x9 → r' ≠ .x10 → r' ≠ .x11 → r' ≠ .x12 →
        r' ≠ .x13 → r' ≠ .x14 → s'.regs r' = s.regs r') ∧
      (∀ j < newDepth d exprs.length c, ld256 s'.mem (stackAddr base (newDepth d exprs.length c) j) =
        (newStack exprs es c).getD j 0) ∧
      (1 ≤ newDepth d exprs.length c → lhs s' = (newStack exprs es c).getD 0 0) ∧
      (2 ≤ newDepth d exprs.length c → rhs armRq s' = (newStack exprs es c).getD 1 0) := by
  have hnet : (d : Int) + ((exprs.length : Int) - c) ≥ 0 := by omega
  have hdn : ((d : Int) + ((exprs.length : Int) - c)).toNat = newDepth d exprs.length c := by
    simp only [newDepth]; omega
  rw [show armFlush.cacheReload = armCacheReload from rfl]
  obtain ⟨s1, h1, h23', hsp1, hmem1, _, hregs1⟩ := depthUpdate_run H _ d hnet
    (by have : ((exprs.length : Int) - c).toNat ≤ exprs.length := by omega
        have : exprs.length ≤ 1024 + c := by simp only [newDepth] at hd'; omega
        omega) _ s h23
  rw [h1]
  rw [hdn] at h23'
  have h24' : s1.regs .x24 = base := by rw [hregs1 _ (by decide), h24]
  obtain ⟨s2, h2, hsp2, hmem2, htos, hnos, hregs2⟩ := cacheReload_run H base _ (by omega) rest s1 h23' h24'
  have hns := newStack_of_mem base s.mem exprs es d c hes hc hstored hkept
  refine ⟨s2, h2, by rw [hsp2, hsp1], by rw [hmem2, hmem1], ?_, ?_, ?_, ?_, ?_⟩
  · rw [hregs2 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), h23']
  · intro r' h23r h6 h7 h8 h9 h10 h11 h12 h13 h14
    rw [hregs2 r' h6 h7 h8 h9 h10 h11 h12 h13 h14, hregs1 r' h23r]
  · intro j hj; rw [hmem2, hmem1]; exact hns j hj
  · intro h1d; rw [htos h1d, hmem1]; exact hns 0 (by omega)
  · intro h2d; rw [hnos h2d, hmem1]; exact hns 1 (by omega)

/-! ## The body: frame, DAG, commit, exit stores, frame -/

/-- `WFSlots` for a region's slot list, from `DagSlots`. -/
theorem wfSlots_of (r : Region) (hW : RegionWF r) (F : Fr) (hn : F.n = (slotsOf r).length)
    (hneed : r.need ≤ F.d) : WFSlots F (idxOf r) (slotsOf r) := by
  obtain ⟨_, hclosed, _, _⟩ := fold_wf (rootsOf r) [] List.nodup_nil closed_nil
  refine ⟨hclosed, ?_, ?_, ?_⟩
  · intro e he; obtain ⟨h, _⟩ := slotIdx_spec _ e he; rw [hn]; exact h
  · intro e e' he he' h; exact slotIdx_inj _ e e' he he' h
  · intro e he k hk; have := hW.stackIdx e he k hk; omega

/-- Every expression of the exit prefix is a slot. -/
theorem exprs_sub_slots (r : Region) : ∀ e ∈ r.ss.exprs, e ∈ slotsOf r :=
  fun e he => (fold_wf (rootsOf r) [] List.nodup_nil closed_nil).2.2.2 e (by simp [rootsOf, he])

/-- Every buffered write value is a slot. -/
theorem writes_sub_slots (r : Region) : ∀ w ∈ r.writes, w.val ∈ slotsOf r :=
  fun w hw => (fold_wf (rootsOf r) [] List.nodup_nil closed_nil).2.2.2 w.val (by simp [rootsOf]; right; exact ⟨w, hw, rfl⟩)

/-- A kept register is not one the frame code writes. -/
theorem keep_ne_frame (r : Reg) (h : keep r = true) : r ≠ .x15 ∧ r ≠ .x29 ∧ r ≠ .x30 := by
  cases r <;> simp [keep] at h ⊢


/-- Frame open and the DAG: the slots evaluated, the saved fp/lr readable,
    the struct and the buffer untouched. -/
theorem pre_run (H : Helpers) (hS : H.Spec) (hC : H.conv = armConv) (r : Region) (hW : RegionWF r) (s : RS) (base : BitVec 64) (d : Nat)
    (es : List Evm.U256) (st mb : BitVec 64) (rest : List AInstr)
    (hL : Lay (frameOf s.sp (slotsOf r).length base d es))
    (hM : MLay (frameOf s.sp (slotsOf r).length base d es) st mb (capAt s.mem st).toNat)
    (h23 : s.regs .x23 = BitVec.ofNat 64 d) (h24 : s.regs .x24 = base)
    (hstack : ∀ k < d, ld256 s.mem (stackAddr base d k) = es.getD k 0)
    (hneed : r.need ≤ d) :
    let n := (slotsOf r).length
    let F := frameOf s.sp n base d es
    ∃ sC, run H (armFlush.frameOpen n ++ ((slotsOf r).flatMap (evalNodeT armFlush (idxOf r)) ++ rest)) s =
            run H rest sC ∧
      Inv F (idxOf r) (slotsOf r) sC ∧
      (∀ r', keep r' = true → sC.regs r' = s.regs r') ∧
      ld64 sC.mem (off F.fp (32 * n)) = s.regs .x29 ∧ ld64 sC.mem (off (off F.fp (32 * n)) 8) = s.regs .x30 ∧
      Agree st mb (capAt s.mem st).toNat s.mem sC.mem ∧
      (∀ x, (∀ j < 32 * 1024, x ≠ off base j) → (∀ i < 32 * n + 16, x ≠ off F.fp i) →
        belowSp F.fp x = false → sC.mem x = s.mem x) := by
  intro n F
  have hFn : F.n = n := rfl
  have hFd : F.d = d := rfl
  have hFb : F.base = base := rfl
  have hfpOk : F.fp.toNat + 32 * n + 16 < 2 ^ 64 := hL.fpOk
  have hdisj : ∀ i < 32 * n + 16, ∀ j < 32 * 1024, off F.fp i ≠ off base j := hL.disj
  have hdLe : d ≤ 1024 := hL.dLe
  have h32n : 32 * n < 2 ^ 64 := by omega
  have hsave : s.sp - BitVec.ofNat 64 16 = off F.fp (32 * n) := by
    simp only [F, frameOf, off]; rw [BitVec.sub_add_cancel]
  -- 1. frame open
  obtain ⟨sB, hB, hspB, hmemB, _, hregsB⟩ := frameOpen_run H n h32n _ s
  rw [hB]
  have hspB' : sB.sp = F.fp := by rw [hspB]; rfl
  have saved_ne_stack : ∀ j < 16, ∀ k < 32 * 1024, off (s.sp - BitVec.ofNat 64 16) j ≠ off base k := by
    intro j hj k hk; rw [hsave, off_off]; exact hdisj _ (by omega) _ hk
  have hIB : Inv F (idxOf r) [] sB := by
    refine ⟨hspB', by rw [hregsB _ (by decide), h23]; rfl, by rw [hregsB _ (by decide), h24]; rfl, ?_,
            fun _ h => by simp at h⟩
    intro k hk
    show ld256 sB.mem (stackAddr base d k) = es.getD k 0
    rw [hmemB, ld256_st64_disj _ _ _ _ ?_, ld256_st64_disj _ _ _ _ ?_, hstack k hk]
    all_goals (intro i hi j hj; simp only [stackAddr, off_off];
               exact (saved_ne_stack _ (by omega) _ (by omega)).symm)
  -- memory outside the frame survives the open
  have hmemB' : ∀ x, (∀ i < 32 * n + 16, x ≠ off F.fp i) → sB.mem x = s.mem x := by
    intro x hxf
    rw [hmemB, st64_out _ _ _ _ ?_, st64_out _ _ _ _ ?_]
    · intro i hi
      rw [hsave, off_off]; exact hxf _ (by omega)
    · intro i hi
      rw [hsave, off_off, off_off]; exact hxf _ (by omega)
  -- 2. the DAG
  have hWF : WFSlots F (idxOf r) (slotsOf r) := wfSlots_of r hW F rfl hneed
  obtain ⟨sC, hC, hIC, hDC⟩ := dag_loop H hS hC F (idxOf r) _ hL (slotsOf r) [] sB (by simpa using hWF) hIB
  rw [hC]
  -- the saved words survive the DAG
  have above : ∀ j < 16, sC.mem (off F.fp (32 * n + j)) = sB.mem (off F.fp (32 * n + j)) := by
    intro j hj
    rw [hDC.mem _ ?_ ?_]
    · intro i hi; exact off_ne_off F.fp _ _ (by omega) (by omega) (by omega)
    · exact belowSp_off_false F.fp _ (by omega)
  have hx29 : ld64 sC.mem (off F.fp (32 * n)) = s.regs .x29 := by
    rw [ld64_eq_of_eq_on sB.mem sC.mem _ (fun i hi => by rw [off_off]; exact above i (by omega)), hmemB, ← hsave,
        ld64_st64_disj _ _ _ _ ?_, ld64_st64_same]
    intro i hi j hj; rw [off_off]; exact off_ne_off _ _ _ (by omega) (by omega) (by omega)
  have hx30 : ld64 sC.mem (off (off F.fp (32 * n)) 8) = s.regs .x30 := by
    rw [ld64_eq_of_eq_on sB.mem sC.mem _ (fun i hi => by rw [off_off, off_off]; exact above (8 + i) (by omega)),
        hmemB, ← hsave, ld64_st64_same]
  have hout : ∀ x, (∀ j < 32 * 1024, x ≠ off base j) → (∀ i < 32 * n + 16, x ≠ off F.fp i) →
      belowSp F.fp x = false → sC.mem x = s.mem x := by
    intro x _ hxf hxw
    rw [hDC.mem x (fun i hi => hxf i (by omega)) hxw, hmemB' x hxf]
  refine ⟨sC, rfl, hIC, ?_, hx29, hx30, ?_, hout⟩
  · intro r' hr'
    obtain ⟨h15, _, _⟩ := keep_ne_frame r' hr'
    rw [hDC.regs _ hr', hregsB _ h15]
  · exact Agree.of_out F st mb _ hM _ _ hout

/-- The commit, from a state where the DAG is evaluated: the uniform
    statement for empty and non-empty write lists. -/
theorem commit_run (H : Helpers) (r : Region) (hW : RegionWF r) (F : Fr) (hL : Lay F) (st mb : BitVec 64)
    (es : List Evm.U256) (rest : List AInstr) (sC : RS) (hFes : F.es = es)
    (hM : MLay F st mb (capAt sC.mem st).toNat)
    (hIC : Inv F (idxOf r) (slotsOf r) sC) (hWF : WFSlots F (idxOf r) (slotsOf r))
    (h20 : sC.regs .x20 = st) (hmb : mbAt sC.mem st = mb)
    (hok : (msAt sC.mem st).toNat ≤ (capAt sC.mem st).toNat)
    (hcapOk : maxEndOf r.writes ≤ (capAt sC.mem st).toNat) (hgasOk : memGas r sC.mem st ≤ (sC.regs .x22).toNat) :
    ∃ sC', run H (memCommitT armFlush (idxOf r) r.writes ++ rest) sC = run H rest sC' ∧
      sC'.sp = sC.sp ∧ (sC'.regs .x22).toNat = (sC.regs .x22).toNat - memGas r sC.mem st ∧
      (∀ r', keep r' = true → r' ≠ .x22 → sC'.regs r' = sC.regs r') ∧
      MemOut r st mb es (capAt sC.mem st).toNat sC.mem sC'.mem ∧
      (∀ x, (∀ i, 24 ≤ i → i < 64 → x ≠ off st i) → (∀ i < (capAt sC.mem st).toNat, x ≠ off mb i) →
        sC'.mem x = sC.mem x) := by
  cases hw : r.writes with
  | nil =>
    rw [show memCommitT armFlush (idxOf r) [] = [] from rfl, List.nil_append]
    refine ⟨sC, rfl, rfl, by rw [memGas_nil r _ _ hw]; omega, fun _ _ _ => rfl, ?_, fun _ _ _ => rfl⟩
    exact MemOut.of_agree r st mb es _ _ _ hw hmb (Agree.refl _ _ _ _)
  | cons w ws =>
    have hne : w :: ws ≠ [] := by simp
    obtain ⟨_, _, h3⟩ := memCommit_run H F (idxOf r) st mb (w :: ws) hne es rest sC hL hM hIC.sp h20 hmb hok
      (by rw [← hw]; exact hW.wOff) (fun w' hw' => hWF.idxLt _ (writes_sub_slots r w' (by rw [hw]; exact hw')))
      (fun w' hw' => by rw [← hFes]; exact hIC.slots _ (writes_sub_slots r w' (by rw [hw]; exact hw')))
    rw [hw] at hcapOk
    have hgasOk' : ecost ((msAt sC.mem st).toNat / 32) (wordsOf (maxEndOf (w :: ws))) ≤ (sC.regs .x22).toNat := by
      unfold memGas at hgasOk; rw [hw] at hgasOk; exact hgasOk
    obtain ⟨sC', h', hsp', hgas', hregs', hms', hmp', hcap', hmb', hbuf', hout'⟩ := h3 hcapOk hgasOk'
    refine ⟨sC', h', hsp', by rw [hgas']; unfold memGas; rw [hw], hregs',
            ⟨by unfold newMs; rw [hw]; exact hms', by rw [hw]; exact hmp', hcap', hmb', by rw [hw]; exact hbuf'⟩, hout'⟩

theorem body_run (H : Helpers) (hS : H.Spec) (hC : H.conv = armConv) (r : Region) (hW : RegionWF r) (s : RS) (base : BitVec 64) (d : Nat)
    (es : List Evm.U256) (st mb : BitVec 64) (rest : List AInstr)
    (hL : Lay (frameOf s.sp (slotsOf r).length base d es))
    (hM : MLay (frameOf s.sp (slotsOf r).length base d es) st mb (capAt s.mem st).toNat)
    (h23 : s.regs .x23 = BitVec.ofNat 64 d) (h24 : s.regs .x24 = base)
    (hstack : ∀ k < d, ld256 s.mem (stackAddr base d k) = es.getD k 0)
    (h20 : s.regs .x20 = st) (hmb : mbAt s.mem st = mb)
    (hok : (msAt s.mem st).toNat ≤ (capAt s.mem st).toNat)
    (hcapOk : maxEndOf r.writes ≤ (capAt s.mem st).toNat) (hgasOk : memGas r s.mem st ≤ (s.regs .x22).toNat)
    (hneed : r.need ≤ d) (hd' : newDepthOf r d ≤ 1024) :
    let n := (slotsOf r).length
    let F := frameOf s.sp n base d es
    ∃ s', run H (armFlush.frameOpen n ++ ((slotsOf r).flatMap (evalNodeT armFlush (idxOf r)) ++
                  (memCommitT armFlush (idxOf r) r.writes ++
                  (exitStoresT armFlush (idxOf r) ((r.ss.exprs.length : Int) - r.ss.consumed) r.ss.exprs ++
                  (armFlush.frameClose n ++ rest))))) s = run H rest s' ∧
      s'.sp = s.sp ∧ s'.regs .x23 = BitVec.ofNat 64 d ∧ s'.regs .x24 = base ∧
      (∀ r', keep r' = true → r' ≠ .x22 → s'.regs r' = s.regs r') ∧
      (s'.regs .x22).toNat = (s.regs .x22).toNat - memGas r s.mem st ∧
      s'.regs .x29 = s.regs .x29 ∧ s'.regs .x30 = s.regs .x30 ∧
      (∀ i (h : i < r.ss.exprs.length),
        ld256 s'.mem (stackAddr base (newDepthOf r d) i) = eval r.ss.exprs[i] es) ∧
      (∀ k, r.ss.consumed ≤ k → k < d → ld256 s'.mem (stackAddr base d k) = es.getD k 0) ∧
      MemOut r st mb es (capAt s.mem st).toNat s.mem s'.mem ∧
      (∀ x, (∀ j < 32 * 1024, x ≠ off base j) → (∀ i < 32 * n + 16, x ≠ off F.fp i) →
        belowSp F.fp x = false → (∀ i, 24 ≤ i → i < 64 → x ≠ off st i) →
        (∀ i < (capAt s.mem st).toNat, x ≠ off mb i) → s'.mem x = s.mem x) := by
  intro n F
  have hFn : F.n = n := rfl
  have hFd : F.d = d := rfl
  have hFb : F.base = base := rfl
  have hFes : F.es = es := rfl
  have hfpOk : F.fp.toNat + 32 * n + 16 < 2 ^ 64 := hL.fpOk
  have hdisj : ∀ i < 32 * n + 16, ∀ j < 32 * 1024, off F.fp i ≠ off base j := hL.disj
  have hdLe : d ≤ 1024 := hL.dLe
  have hc : r.ss.consumed ≤ d := Nat.le_trans hW.cLe hneed
  have h32n : 32 * n < 2 ^ 64 := by omega
  have hsave : s.sp - BitVec.ofNat 64 16 = off F.fp (32 * n) := by
    simp only [F, frameOf, off]; rw [BitVec.sub_add_cancel]
  -- 1-2. frame open and the DAG
  obtain ⟨sC, hC, hIC, hregsC, hx29C, hx30C, hAgC, houtC⟩ :=
    pre_run H hS hC r hW s base d es st mb _ hL hM h23 h24 hstack hneed
  rw [hC]
  have hWF : WFSlots F (idxOf r) (slotsOf r) := wfSlots_of r hW F rfl hneed
  have hcapC : capAt sC.mem st = capAt s.mem st := hAgC.cap
  -- 2.5 the commit
  obtain ⟨sD, hD, hspD, hgasD, hregsD, hMO, houtD⟩ := commit_run H r hW F hL st mb es _ sC hFes
    (by rw [hcapC]; exact hM) hIC hWF (by rw [hregsC _ (by decide), h20]) (by rw [hAgC.mb, hmb])
    (by rw [hAgC.ms, hcapC]; exact hok) (by rw [hcapC]; exact hcapOk)
    (by rw [memGas_agree r hAgC, hregsC _ (by decide)]; exact hgasOk)
  rw [hD]
  rw [hcapC] at hMO houtD
  -- the frame and the arena are neither struct nor buffer
  have frame_ok : ∀ i < 32 * n + 16, (∀ k, 24 ≤ k → k < 64 → off F.fp i ≠ off st k) ∧
      (∀ k < (capAt s.mem st).toNat, off F.fp i ≠ off mb k) :=
    fun i hi => ⟨fun k hk hk' h => hM.stFrame k hk hk' i hi h.symm, fun k hk h => hM.bufFrame k hk i hi h.symm⟩
  have stack_ok : ∀ j < 32 * 1024, (∀ k, 24 ≤ k → k < 64 → off base j ≠ off st k) ∧
      (∀ k < (capAt s.mem st).toNat, off base j ≠ off mb k) :=
    fun j hj => ⟨fun k hk hk' h => hM.stStack k hk hk' j hj h.symm, fun k hk h => hM.bufStack k hk j hj h.symm⟩
  have hframeD : ∀ i < 32 * n + 16, sD.mem (off F.fp i) = sC.mem (off F.fp i) :=
    fun i hi => houtD _ (frame_ok i hi).1 (frame_ok i hi).2
  have hstackD : ∀ j < 32 * 1024, sD.mem (off base j) = sC.mem (off base j) :=
    fun j hj => houtD _ (stack_ok j hj).1 (stack_ok j hj).2
  have hXD : ExitInv F (idxOf r) (slotsOf r) r.ss.consumed sD := by
    refine ⟨by rw [hspD, hIC.sp], by rw [hregsD _ (by decide) (by decide), hIC.x23],
            by rw [hregsD _ (by decide) (by decide), hIC.x24], ?_, ?_⟩
    · intro e he
      rw [← hIC.slots e he]
      apply ld256_eq_of_eq_on
      intro j hj
      have := hWF.idxLt e he
      simp only [slotAddr, off_off]
      exact hframeD _ (by omega)
    · intro k _ hk
      rw [← hIC.stack k hk]
      apply ld256_eq_of_eq_on
      intro j hj
      simp only [stackAddr, off_off, hFb]
      exact hstackD _ (by omega)
  -- 3. the exit stores
  have hidx : ∀ e ∈ slotsOf r, idxOf r e < F.n := fun e he => hWF.idxLt e he
  have hidx' : ∀ e ∈ slotsOf r, idxOf r e < n := fun e he => by rw [← hFn]; exact hidx e he
  obtain ⟨sE, hE, hXE, hstored, hspE, hregsE, hmemE⟩ := exit_loop H F hL (idxOf r) (slotsOf r) r.ss.consumed
    r.ss.exprs.length _ hc hd' hidx r.ss.exprs 0 sD (by simp) (exprs_sub_slots r)
    (fun e he => by have := hidx' e (exprs_sub_slots r e he); omega) hXD
  rw [show exitStoresT armFlush (idxOf r) ((r.ss.exprs.length : Int) - r.ss.consumed) r.ss.exprs =
        (r.ss.exprs.zipIdx 0).flatMap (fun (e, m) => exitOneT armFlush (idxOf r) ((r.ss.exprs.length : Int) - r.ss.consumed) e m)
        from rfl, hE]
  -- the exit stores only touch the arena
  have hmemE' : ∀ x, (∀ j < 32 * 1024, x ≠ off base j) → sE.mem x = sD.mem x := by
    intro x hxb
    apply hmemE
    intro m _ hm b hb
    simp only [stackAddr, off_off, hFb]
    exact hxb _ (by have : d + r.ss.exprs.length - r.ss.consumed ≤ 1024 := hd'; simp only [hFd, newDepth]; omega)
  -- 4. frame close
  obtain ⟨sF, hF, hspF, hmemF, _, h29, h30, hregsF⟩ := frameClose_run H n h32n rest sE
  rw [hF]
  have hspE' : sE.sp = F.fp := by rw [hspE, hspD, hIC.sp]
  -- the saved words survive the commit and the exit stores
  have above : ∀ j < 16, sE.mem (off F.fp (32 * n + j)) = sC.mem (off F.fp (32 * n + j)) := by
    intro j hj
    rw [hmemE' _ (fun k hk => hdisj _ (by omega) _ hk), hframeD _ (by omega)]
  have hx29 : ld64 sE.mem (off F.fp (32 * n)) = s.regs .x29 := by
    rw [ld64_eq_of_eq_on sC.mem sE.mem _ (fun i hi => by rw [off_off]; exact above i (by omega)), hx29C]
  have hx30 : ld64 sE.mem (off (off F.fp (32 * n)) 8) = s.regs .x30 := by
    rw [ld64_eq_of_eq_on sC.mem sE.mem _ (fun i hi => by rw [off_off, off_off]; exact above (8 + i) (by omega)), hx30C]
  have hAgE : Agree st mb (capAt s.mem st).toNat sD.mem sE.mem := Agree.of_stack F st mb _ hM _ _ hmemE'
  refine ⟨sF, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hspF, hspE']
    show off (off F.fp (32 * n)) 16 = s.sp
    rw [← hsave]; simp only [off]; exact BitVec.sub_add_cancel _ _
  · rw [hregsF _ (by decide) (by decide) (by decide), hregsE _ rfl, hregsD _ rfl (by decide), hIC.x23]; rfl
  · rw [hregsF _ (by decide) (by decide) (by decide), hregsE _ rfl, hregsD _ rfl (by decide), hIC.x24]; rfl
  · intro r' hr' h22
    obtain ⟨h15, h29, h30⟩ := keep_ne_frame r' hr'
    rw [hregsF _ h15 h29 h30, hregsE _ hr', hregsD _ hr' h22, hregsC _ hr']
  · rw [hregsF _ (by decide) (by decide) (by decide), hregsE _ rfl, hgasD, hregsC _ rfl, memGas_agree r hAgC]
  · rw [h29, hspE']; exact hx29
  · rw [h30, hspE']; exact hx30
  · intro i hi
    rw [hmemF]
    have := hstored i hi
    simpa [newDepthOf, F, frameOf] using this
  · intro k hck hkd
    rw [hmemF]
    exact hXE.keepStack k hck hkd
  · rw [hmemF]
    exact (hMO.agree_left hAgC).agree_right hAgE
  · intro x hxb hxf hxw hxs hxm
    rw [hmemF, hmemE' x hxb, houtD x hxs hxm, houtC x hxb hxf hxw]

/-! ## The depth checks, under the success conditions -/

theorem armFlush_far (sym : String) : armFlush.far sym = [AInstr.bFar sym] := rfl

/-- The check prefix passes: only the flags change. -/
theorem checks_run (H : Helpers) (r : Region) (d : Nat) (hd : d ≤ 1024) (rest : List AInstr) (s : RS)
    (h23 : s.regs .x23 = BitVec.ofNat 64 d) (hneed : r.need ≤ d)
    (hover : r.maxNet > 0 → (d : Int) < 1025 - r.maxNet) :
    ∃ s', run H ((if r.need > 0
                    then [AInstr.cmpImm .x23 r.need, .bcLbl .hs "8f", .bFar "_eita_stack_underflow", .label "8"]
                    else []) ++
                 ((if r.maxNet > 0
                    then [AInstr.cmpImm .x23 (1025 - r.maxNet).toNat, .bcLbl .lo "9f", .bFar "_eita_stack_overflow", .label "9"]
                    else []) ++ rest)) s = run H rest s' ∧
      s'.regs = s.regs ∧ s'.sp = s.sp ∧ s'.mem = s.mem := by
  have step1 : ∃ s1, run H ((if r.need > 0
      then [AInstr.cmpImm .x23 r.need, .bcLbl .hs "8f", .bFar "_eita_stack_underflow", .label "8"]
      else []) ++ ((if r.maxNet > 0
      then [AInstr.cmpImm .x23 (1025 - r.maxNet).toNat, .bcLbl .lo "9f", .bFar "_eita_stack_overflow", .label "9"]
      else []) ++ rest)) s = run H ((if r.maxNet > 0
      then [AInstr.cmpImm .x23 (1025 - r.maxNet).toNat, .bcLbl .lo "9f", .bFar "_eita_stack_overflow", .label "9"]
      else []) ++ rest) s1 ∧ s1.regs = s.regs ∧ s1.sp = s.sp ∧ s1.mem = s.mem := by
    split
    · simp only [List.cons_append, List.nil_append]
      rw [underflowCheck_run H r.need d (by omega) (by omega) _ s h23, ite_eq_left hneed]
      exact ⟨_, rfl, rfl, rfl, rfl⟩
    · rw [List.nil_append]; exact ⟨s, rfl, rfl, rfl, rfl⟩
  obtain ⟨s1, h1, hr1, hs1, hm1⟩ := step1
  rw [h1]
  have h23' : s1.regs .x23 = BitVec.ofNat 64 d := by rw [hr1, h23]
  split
  · rename_i hm
    have hlim : d < (1025 - r.maxNet).toNat := by have := hover hm; omega
    simp only [List.cons_append, List.nil_append]
    rw [overflowCheck_run H _ d (by omega) (by omega) _ s1 h23', ite_eq_left hlim]
    exact ⟨_, rfl, by rw [AsmRun.withFlags_regs, hr1], by rw [AsmRun.withFlags_sp, hs1], by rw [AsmRun.withFlags_mem, hm1]⟩
  · rw [List.nil_append]; exact ⟨s1, rfl, hr1, hs1, hm1⟩

/-- If the slot list is empty, so is the exit prefix. -/
theorem exprs_nil_of_slots_nil (r : Region) (h : (slotsOf r).length = 0) : r.ss.exprs = [] := by
  cases hx : r.ss.exprs with
  | nil => rfl
  | cons e tl =>
    exfalso
    have := exprs_sub_slots r e (by rw [hx]; simp)
    rw [List.length_eq_zero_iff] at h
    rw [h] at this; simp at this

/-! ## THE theorem -/

theorem flush_run (H : Helpers) (hS : H.Spec) (hC : H.conv = armConv) (r : Region) (hW : RegionWF r) (s : RS) (base : BitVec 64) (d : Nat)
    (es : List Evm.U256) (st mb : BitVec 64) (rest : List AInstr)
    (hL : Lay (frameOf s.sp (slotsOf r).length base d es))
    (hM : MLay (frameOf s.sp (slotsOf r).length base d es) st mb (capAt s.mem st).toNat)
    (h23 : s.regs .x23 = BitVec.ofNat 64 d) (h24 : s.regs .x24 = base) (hes : es.length = d)
    (hstack : ∀ k < d, ld256 s.mem (stackAddr base d k) = es.getD k 0)
    (htos : 1 ≤ d → lhs s = es.getD 0 0) (hnos : 2 ≤ d → rhs armRq s = es.getD 1 0)
    (h20 : s.regs .x20 = st) (hmb : mbAt s.mem st = mb)
    (hok : (msAt s.mem st).toNat ≤ (capAt s.mem st).toNat)
    (hcapOk : maxEndOf r.writes ≤ (capAt s.mem st).toNat) (hgasOk : memGas r s.mem st ≤ (s.regs .x22).toNat)
    (hneed : r.need ≤ d) (hover : r.maxNet > 0 → (d : Int) < 1025 - r.maxNet) :
    ∃ s', run H (emitRegionFlushT armFlush r ++ rest) s = run H rest s' ∧
      FlushOut r base d es (frameOf s.sp (slotsOf r).length base d es).fp (slotsOf r).length st mb s s' := by
  have hdLe : d ≤ 1024 := hL.dLe
  have hc : r.ss.consumed ≤ d := Nat.le_trans hW.cLe hneed
  have hd' : newDepthOf r d ≤ 1024 := by
    have := hW.netLe
    simp only [newDepthOf, newDepth]
    by_cases hm : r.maxNet > 0
    · have := hover hm; omega
    · omega
  have hdenote : SymStack.denote r.ss es = newStack r.ss.exprs es r.ss.consumed := rfl
  simp only [emitRegionFlushT, dagSlots_of, List.size_toArray, List.toList_toArray, armFlush_far,
             List.cons_append, List.nil_append]
  -- a successful flush with no DAG and no writes leaves depth `d`: the
  -- outcome from any state equal to `s` up to flags
  have trivialOut : ∀ s1 : RS, s1.regs = s.regs → s1.sp = s.sp → s1.mem = s.mem →
      r.ss.exprs.length = 0 → r.ss.consumed = 0 → r.writes = [] →
      FlushOut r base d es (frameOf s.sp (slotsOf r).length base d es).fp (slotsOf r).length st mb s s1 := by
    intro s1 hr1 hs1 hm1 hp hc0 hw
    have hd0 : newDepthOf r d = d := by simp [newDepthOf, newDepth, hp, hc0]
    have hex : r.ss.exprs = [] := List.length_eq_zero_iff.mp hp
    have hns : SymStack.denote r.ss es = es := by rw [hdenote]; simp [newStack, hex, hc0]
    refine ⟨hs1, by rw [hd0, hr1, h23], fun r' _ _ _ => by rw [hr1], by rw [hr1, memGas_nil r _ _ hw]; omega,
            ⟨by rw [hr1], by rw [hr1]⟩, ?_, ?_, ?_,
            MemOut.of_agree r st mb es _ _ _ hw hmb (Agree.of_eq hm1), fun x _ _ _ _ _ => by rw [hm1]⟩
    · intro j hj; rw [hd0] at hj ⊢; rw [hns, hm1]; exact hstack j hj
    · intro h1; rw [hd0] at h1; rw [hns]; simp only [lhs, hr1]; exact htos h1
    · intro h2; rw [hd0] at h2; rw [hns]; simp only [rhs, hr1]; exact hnos h2
  split
  · rename_i hall
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.isEmpty_iff] at hall
    exact ⟨s, by simp, trivialOut s rfl rfl rfl hall.1.1.1.1 hall.1.1.1.2 hall.1.1.2⟩
  · rename_i hnall
    split
    · rename_i hbig; exfalso; omega
    · rename_i hnbig
      split
      · rename_i hof; exfalso
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hof
        have := hover hof.1; omega
      · rename_i hnof
        split
        · rename_i hidle
          simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hidle
          obtain ⟨s1, h1, hr1, hs1, hm1⟩ := checks_run H r d hdLe rest s h23 hneed hover
          simp only [List.append_assoc]
          exact ⟨s1, h1, trivialOut s1 hr1 hs1 hm1 hidle.1.1 hidle.1.2 hidle.2⟩
        · rename_i hnidle
          simp only [List.append_assoc]
          obtain ⟨s1, h1, hr1, hs1, hm1⟩ := checks_run H r d hdLe _ s h23 hneed hover
          rw [h1]
          have h23' : s1.regs .x23 = BitVec.ofNat 64 d := by rw [hr1, h23]
          have h24' : s1.regs .x24 = base := by rw [hr1, h24]
          have h20' : s1.regs .x20 = st := by rw [hr1, h20]
          have hstack1 : ∀ k < d, ld256 s1.mem (stackAddr base d k) = es.getD k 0 := by rw [hm1]; exact hstack
          have hL1 : Lay (frameOf s1.sp (slotsOf r).length base d es) := by rw [hs1]; exact hL
          have hM1 : MLay (frameOf s1.sp (slotsOf r).length base d es) st mb (capAt s1.mem st).toNat := by
            rw [hs1, hm1]; exact hM
          split
          · rename_i hn
            simp only [List.append_assoc]
            obtain ⟨sE, hE, hspE, h23E, h24E, hregsE, hgasE, h29E, h30E, hstoredE, hkeptE, hMO, hmemE⟩ :=
              body_run H hS hC r hW s1 base d es st mb _ hL1 hM1 h23' h24' hstack1 h20' (by rw [hm1]; exact hmb)
                (by rw [hm1]; exact hok) (by rw [hm1]; exact hcapOk) (by rw [hm1, hr1]; exact hgasOk) hneed hd'
            rw [hE]
            obtain ⟨sF, hF, hspF, hmemF, h23F, hregsF, hstackF, htosF, hnosF⟩ :=
              tail_run H r.ss.exprs r.ss.consumed base d es rest sE hdLe hc hd' hes h23E h24E hstoredE hkeptE
            refine ⟨sF, hF, ⟨by rw [hspF, hspE, hs1], h23F, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
            · intro r' hr' hne h22
              obtain ⟨_, _, _, _, h6, h7, h8, h9, h10, h11, h12, h13, h14, _, _, _⟩ := keep_ne r' hr'
              rw [hregsF r' hne h6 h7 h8 h9 h10 h11 h12 h13 h14, hregsE r' hr' h22, hr1]
            · rw [hregsF _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                    (by decide) (by decide) (by decide), hgasE, hr1, hm1]
            · rw [hregsF _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                    (by decide) (by decide) (by decide), h29E, hr1]
            · rw [hregsF _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                    (by decide) (by decide) (by decide), h30E, hr1]
            · intro j hj; rw [hdenote]; exact hstackF j hj
            · intro h1d; rw [hdenote]; exact htosF h1d
            · intro h2d; rw [hdenote]; exact hnosF h2d
            · rw [hmemF]; rw [hm1] at hMO; exact hMO
            · intro x hxb hxf hxw hxs hxm
              rw [hmemF, hmemE x hxb (by rw [hs1]; exact hxf) (by rw [hs1]; exact hxw) hxs (by rw [hm1]; exact hxm), hm1]
          · rename_i hn0
            have hn0' : (slotsOf r).length = 0 := by omega
            have hex := exprs_nil_of_slots_nil r hn0'
            have hwnil : r.writes = [] := by
              cases hx : r.writes with
              | nil => rfl
              | cons w ws =>
                exfalso
                have := writes_sub_slots r w (by rw [hx]; simp)
                rw [List.length_eq_zero_iff] at hn0'
                rw [hn0'] at this; simp at this
            rw [List.nil_append]
            obtain ⟨sF, hF, hspF, hmemF, h23F, hregsF, hstackF, htosF, hnosF⟩ :=
              tail_run H r.ss.exprs r.ss.consumed base d es rest s1 hdLe hc hd' hes h23' h24'
                (fun i hi => by rw [hex] at hi; simp at hi) (fun k _ hk => hstack1 k hk)
            refine ⟨sF, hF, ⟨by rw [hspF, hs1], h23F, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
            · intro r' hr' hne _
              obtain ⟨_, _, _, _, h6, h7, h8, h9, h10, h11, h12, h13, h14, _, _, _⟩ := keep_ne r' hr'
              rw [hregsF r' hne h6 h7 h8 h9 h10 h11 h12 h13 h14, hr1]
            · rw [hregsF _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                    (by decide) (by decide) (by decide), hr1, memGas_nil r _ _ hwnil]; omega
            · rw [hregsF _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                    (by decide) (by decide) (by decide), hr1]
            · rw [hregsF _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                    (by decide) (by decide) (by decide), hr1]
            · intro j hj; rw [hdenote]; exact hstackF j hj
            · intro h1d; rw [hdenote]; exact htosF h1d
            · intro h2d; rw [hdenote]; exact hnosF h2d
            · rw [hmemF, hm1]; exact MemOut.of_agree r st mb es _ _ _ hwnil hmb (Agree.refl _ _ _ _)
            · intro x _ _ _ _ _; rw [hmemF, hm1]

/-- The out-of-gas path: when the commit's capacity or gas check fails, the
    flush faults to `_eita_oog` (after the depth checks pass). -/
theorem flush_run_oog (H : Helpers) (hS : H.Spec) (hC : H.conv = armConv) (r : Region) (hW : RegionWF r) (s : RS) (base : BitVec 64) (d : Nat)
    (es : List Evm.U256) (st mb : BitVec 64) (rest : List AInstr)
    (hL : Lay (frameOf s.sp (slotsOf r).length base d es))
    (hM : MLay (frameOf s.sp (slotsOf r).length base d es) st mb (capAt s.mem st).toNat)
    (h23 : s.regs .x23 = BitVec.ofNat 64 d) (h24 : s.regs .x24 = base)
    (hstack : ∀ k < d, ld256 s.mem (stackAddr base d k) = es.getD k 0)
    (h20 : s.regs .x20 = st) (hmb : mbAt s.mem st = mb)
    (hok : (msAt s.mem st).toNat ≤ (capAt s.mem st).toNat)
    (hbad : ¬ (maxEndOf r.writes ≤ (capAt s.mem st).toNat ∧ memGas r s.mem st ≤ (s.regs .x22).toNat))
    (hneed : r.need ≤ d) (hover : r.maxNet > 0 → (d : Int) < 1025 - r.maxNet) :
    ∃ sf, run H (emitRegionFlushT armFlush r ++ rest) s = .fault "_eita_oog" sf := by
  have hdLe : d ≤ 1024 := hL.dLe
  -- the write list is not empty (else both checks pass)
  have hwne : r.writes ≠ [] := by
    intro hw; apply hbad
    rw [hw, maxEndOf_nil, memGas_nil r _ _ hw]; omega
  obtain ⟨w, hw⟩ : ∃ w, w ∈ r.writes := by
    cases hx : r.writes with
    | nil => exact absurd hx hwne
    | cons w ws => exact ⟨w, by simp⟩
  have hn : 0 < (slotsOf r).length := List.length_pos_of_mem (writes_sub_slots r w hw)
  simp only [emitRegionFlushT, dagSlots_of, List.size_toArray, List.toList_toArray, armFlush_far,
             List.cons_append, List.nil_append]
  split
  · rename_i hall; exfalso
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.isEmpty_iff] at hall
    exact hwne hall.1.1.2
  · rename_i hnall
    split
    · rename_i hbig; exfalso; omega
    · rename_i hnbig
      split
      · rename_i hof; exfalso
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hof
        have := hover hof.1; omega
      · rename_i hnof
        split
        · rename_i hidle; exfalso
          simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hidle
          exact hwne hidle.2
        · rename_i hnidle
          simp only [List.append_assoc]
          obtain ⟨s1, h1, hr1, hs1, hm1⟩ := checks_run H r d hdLe _ s h23 hneed hover
          rw [h1]
          have h23' : s1.regs .x23 = BitVec.ofNat 64 d := by rw [hr1, h23]
          have h24' : s1.regs .x24 = base := by rw [hr1, h24]
          have hstack1 : ∀ k < d, ld256 s1.mem (stackAddr base d k) = es.getD k 0 := by rw [hm1]; exact hstack
          have hL1 : Lay (frameOf s1.sp (slotsOf r).length base d es) := by rw [hs1]; exact hL
          have hM1 : MLay (frameOf s1.sp (slotsOf r).length base d es) st mb (capAt s1.mem st).toNat := by
            rw [hs1, hm1]; exact hM
          have hM1' : MLay (frameOf s1.sp (slotsOf r).length base d es) st mb (capAt s.mem st).toNat := by
            rw [hs1]; exact hM
          try simp only [List.append_assoc]
          obtain ⟨sC, hC, hIC, hregsC, _, _, hAgC, _⟩ :=
            pre_run H hS hC r hW s1 base d es st mb _ hL1 hM1 h23' h24' hstack1 hneed
          rw [hC]
          have hWF : WFSlots (frameOf s1.sp (slotsOf r).length base d es) (idxOf r) (slotsOf r) :=
            wfSlots_of r hW _ rfl hneed
          have hcapC : capAt sC.mem st = capAt s.mem st := by rw [hAgC.cap, hm1]
          have hmsC : msAt sC.mem st = msAt s.mem st := by rw [hAgC.ms, hm1]
          have hgasC : sC.regs .x22 = s.regs .x22 := by rw [hregsC _ (by decide), hr1]
          obtain ⟨hE1, hE2, _⟩ := memCommit_run H _ (idxOf r) st mb r.writes hwne es _ sC hL1
            (by rw [hcapC]; exact hM1') hIC.sp (by rw [hregsC _ (by decide), hr1, h20]) (by rw [hAgC.mb, hm1, hmb])
            (by rw [hmsC, hcapC]; exact hok) hW.wOff
            (fun w' hw' => hWF.idxLt _ (writes_sub_slots r w' hw'))
            (fun w' hw' => hIC.slots _ (writes_sub_slots r w' hw'))
          rw [hcapC] at hE1
          rw [hcapC, hmsC, hgasC] at hE2
          by_cases hcap : (capAt s.mem st).toNat < maxEndOf r.writes
          · exact hE1 hcap
          · exact hE2 (by omega) (by unfold memGas at hbad; omega)

end Evm.CL.ARM64.FlushMain
