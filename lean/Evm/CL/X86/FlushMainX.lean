/-
  Evm.CL.X86.FlushMainX — THE x86-64 theorem: the region flush at the x86-64
  target (`emitRegionFlushT x86Flush r` after `spScale`, i.e.
  `FlushScaleX.emitRegionFlushX r`), run under `AsmRun`, leaves the EVM stack
  holding `SymStack.denote`, the byte-scaled depth register at the new depth,
  the TOS cache reloaded, the frame restored, the memory commit done — or
  faults through the trampolines exactly when the checks say so. The x86-64
  twin of `ARM64.FlushMain.flush_run`.
-/

import Evm.CL.ARM64.FlushMain
import Evm.CL.X86.FlushScaleX

namespace Evm.CL.X86.FlushMainX

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun Evm.CL.ARM64.JIT Evm.CL.ARM64.CoreSem
open Evm.CL.ARM64.FlushSem (Fr slotAddr stackAddr keep keep_ne set_regs_ne NodeOut DagOut WFSlots newDepth
  newStack newStack_of_mem belowSp_off_false)
open Evm.CL.ARM64.DagSlots Evm.CL.ARM64.MemCommitSem
open Evm.CL.ARM64.FlushMain (slotsOf idxOf rootsOf dagSlots_of RegionWF newDepthOf memGas newMs memGas_nil
  Agree MemOut wfSlots_of exprs_sub_slots writes_sub_slots keep_ne_frame exprs_nil_of_slots_nil
  memGas_agree newMs_agree)
open Evm.CL.X86.FlushSemX Evm.CL.X86.MemCommitSemX Evm.CL.X86.FlushScaleX Evm.CL.X86.CoreSemX
open Evm.CL.X86Sem (x86Conv)
open Evm.IR.SymExpr (Expr eval SymStack)

/-- The x86-64 frame: `32n + 8` bytes below the entry sp. -/
def frameOfX (sp0 : BitVec 64) (n : Nat) (base : BitVec 64) (d : Nat) (es : List Evm.U256) : Fr :=
  { fp := sp0 - BitVec.ofNat 64 (32 * n + 8), n := n, base := base, d := d, es := es }

/-- The outcome of a successful x86-64 flush. -/
structure FlushOutX (r : Region) (base : BitVec 64) (d : Nat) (es : List Evm.U256) (fp : BitVec 64) (n : Nat)
    (st mb : BitVec 64) (s s' : RS) : Prop where
  sp   : s'.sp = s.sp
  x23  : s'.regs .x23 = BitVec.ofNat 64 (32 * newDepthOf r d)
  regs : ∀ r', keep r' = true → r' ≠ .x23 → r' ≠ .x22 → s'.regs r' = s.regs r'
  gas  : (s'.regs .x22).toNat = (s.regs .x22).toNat - memGas r s.mem st
  stack : ∀ j < newDepthOf r d, ld256 s'.mem (stackAddr base (newDepthOf r d) j) =
    (SymStack.denote r.ss es).getD j 0
  tos  : 1 ≤ newDepthOf r d → lhs s' = (SymStack.denote r.ss es).getD 0 0
  memOut : MemOut r st mb es (capAt s.mem st).toNat s.mem s'.mem
  mem  : ∀ x, (∀ j < 32 * 1024, x ≠ off base j) → (∀ i < 32 * n + 16, x ≠ off fp i) →
    belowSp fp x = false → (∀ i, 24 ≤ i → i < 64 → x ≠ off st i) → (∀ i < (capAt s.mem st).toNat, x ≠ off mb i) →
    s'.mem x = s.mem x

/-! ## The tail: depth update and TOS reload -/

theorem tail_runX (H : Helpers) (exprs : List Expr) (c : Nat) (base : BitVec 64) (d : Nat) (es : List Evm.U256)
    (rest : List AInstr) (s : RS) (hd : d ≤ 1024) (hc : c ≤ d) (hd' : newDepth d exprs.length c ≤ 1024)
    (hes : es.length = d) (h23 : s.regs .x23 = BitVec.ofNat 64 (32 * d)) (h24 : s.regs .x24 = base)
    (hstored : ∀ i (h : i < exprs.length), ld256 s.mem (stackAddr base (newDepth d exprs.length c) i) = eval exprs[i] es)
    (hkept : ∀ k, c ≤ k → k < d → ld256 s.mem (stackAddr base d k) = es.getD k 0) :
    ∃ s', run H (depthUpdateX ((exprs.length : Int) - c) ++ (cacheReloadX ++ rest)) s = run H rest s' ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.regs .x23 = BitVec.ofNat 64 (32 * newDepth d exprs.length c) ∧
      (∀ r', r' ≠ .x23 → r' ≠ .x6 → r' ≠ .x7 → r' ≠ .x8 → r' ≠ .x9 → r' ≠ .x14 → s'.regs r' = s.regs r') ∧
      (∀ j < newDepth d exprs.length c, ld256 s'.mem (stackAddr base (newDepth d exprs.length c) j) =
        (newStack exprs es c).getD j 0) ∧
      (1 ≤ newDepth d exprs.length c → lhs s' = (newStack exprs es c).getD 0 0) := by
  have hnet : (d : Int) + ((exprs.length : Int) - c) ≥ 0 := by omega
  have hdn : ((d : Int) + ((exprs.length : Int) - c)).toNat = newDepth d exprs.length c := by
    simp only [newDepth]; omega
  obtain ⟨s1, h1, h23', hsp1, hmem1, _, hregs1⟩ := depthUpdateX_run H _ d hnet
    (by have : ((exprs.length : Int) - c).toNat ≤ exprs.length := by omega
        have : exprs.length ≤ 1024 + c := by simp only [newDepth] at hd'; omega
        omega) _ s h23
  rw [h1]
  rw [hdn] at h23'
  have h24' : s1.regs .x24 = base := by rw [hregs1 _ (by decide), h24]
  obtain ⟨s2, h2, hsp2, hmem2, htos, hregs2⟩ := cacheReloadX_run H base _ hd' rest s1 h23' h24'
  have hns := newStack_of_mem base s.mem exprs es d c hes hc hstored hkept
  refine ⟨s2, h2, by rw [hsp2, hsp1], by rw [hmem2, hmem1], ?_, ?_, ?_, ?_⟩
  · rw [hregs2 _ (by decide) (by decide) (by decide) (by decide) (by decide), h23']
  · intro r' h23r h6 h7 h8 h9 h14
    rw [hregs2 r' h6 h7 h8 h9 h14, hregs1 r' h23r]
  · intro j hj; rw [hmem2, hmem1]; exact hns j hj
  · intro h1d; rw [htos h1d, hmem1]; exact hns 0 (by omega)

/-! ## Frame open and the DAG -/

theorem pre_runX (H : Helpers) (hS : H.Spec) (hC : H.conv = x86Conv) (r : Region) (hW : RegionWF r) (s : RS)
    (base : BitVec 64) (d : Nat) (es : List Evm.U256) (st mb : BitVec 64) (rest : List AInstr)
    (hL : LayX (frameOfX s.sp (slotsOf r).length base d es))
    (hM : MLay (frameOfX s.sp (slotsOf r).length base d es) st mb (capAt s.mem st).toNat)
    (h23 : s.regs .x23 = BitVec.ofNat 64 (32 * d)) (h24 : s.regs .x24 = base)
    (hstack : ∀ k < d, ld256 s.mem (stackAddr base d k) = es.getD k 0)
    (hneed : r.need ≤ d) :
    let n := (slotsOf r).length
    let F := frameOfX s.sp n base d es
    ∃ sC, run H (frameOpenX n ++ ((slotsOf r).flatMap (evalNodeX (idxOf r)) ++ rest)) s = run H rest sC ∧
      InvX F (idxOf r) (slotsOf r) sC ∧
      (∀ r', keep r' = true → sC.regs r' = s.regs r') ∧
      Agree st mb (capAt s.mem st).toNat s.mem sC.mem ∧
      (∀ x, (∀ j < 32 * 1024, x ≠ off base j) → (∀ i < 32 * n + 16, x ≠ off F.fp i) →
        belowSp F.fp x = false → sC.mem x = s.mem x) := by
  intro n F
  have hFn : F.n = n := rfl
  rw [frameOpenX_run]
  have hspB : (s.withSp (s.sp - BitVec.ofNat 64 (32 * n + 8))).sp = F.fp := rfl
  have hIB : InvX F (idxOf r) [] (s.withSp (s.sp - BitVec.ofNat 64 (32 * n + 8))) :=
    ⟨hspB, by simpa [F, frameOfX] using h23, by simpa [F, frameOfX] using h24, fun k hk => by simpa [F, frameOfX] using hstack k hk, fun _ h => by simp at h⟩
  have hWF : WFSlots F (idxOf r) (slotsOf r) := wfSlots_of r hW F rfl hneed
  obtain ⟨sC, hC', hIC, hDC⟩ := dag_loopX H hS hC F (idxOf r) _ hL (slotsOf r) [] _ (by simpa using hWF) hIB
  rw [hC']
  have hout : ∀ x, (∀ j < 32 * 1024, x ≠ off base j) → (∀ i < 32 * n + 16, x ≠ off F.fp i) →
      belowSp F.fp x = false → sC.mem x = s.mem x := by
    intro x _ hxf hxw
    rw [hDC.mem x (fun i hi => hxf i (by omega)) hxw]; rfl
  refine ⟨sC, rfl, hIC, fun r' hr' => by rw [hDC.regs _ hr']; rfl, ?_, hout⟩
  exact Agree.of_out F st mb _ hM _ _ (fun x hxb hxf hxw => hout x hxb (fun i hi => hxf i (by omega)) hxw)

/-- The commit, from a state where the DAG is evaluated. -/
theorem commit_runX (H : Helpers) (r : Region) (hW : RegionWF r) (F : Fr) (hL : LayX F) (st mb : BitVec 64)
    (es : List Evm.U256) (rest : List AInstr) (sC : RS) (hFes : F.es = es)
    (hM : MLay F st mb (capAt sC.mem st).toNat)
    (hIC : InvX F (idxOf r) (slotsOf r) sC) (hWF : WFSlots F (idxOf r) (slotsOf r))
    (h20 : sC.regs .x20 = st) (hmb : mbAt sC.mem st = mb)
    (hok : (msAt sC.mem st).toNat ≤ (capAt sC.mem st).toNat)
    (hcapOk : maxEndOf r.writes ≤ (capAt sC.mem st).toNat) (hgasOk : memGas r sC.mem st ≤ (sC.regs .x22).toNat) :
    ∃ sC', run H (memCommitT Evm.CL.X86JIT.x86Flush (idxOf r) r.writes ++ rest) sC = run H rest sC' ∧
      sC'.sp = sC.sp ∧ (sC'.regs .x22).toNat = (sC.regs .x22).toNat - memGas r sC.mem st ∧
      (∀ r', keep r' = true → r' ≠ .x22 → sC'.regs r' = sC.regs r') ∧
      MemOut r st mb es (capAt sC.mem st).toNat sC.mem sC'.mem ∧
      (∀ x, (∀ i, 24 ≤ i → i < 64 → x ≠ off st i) → (∀ i < (capAt sC.mem st).toNat, x ≠ off mb i) →
        sC'.mem x = sC.mem x) := by
  cases hw : r.writes with
  | nil =>
    rw [show memCommitT Evm.CL.X86JIT.x86Flush (idxOf r) [] = [] from rfl, List.nil_append]
    refine ⟨sC, rfl, rfl, by rw [memGas_nil r _ _ hw]; omega, fun _ _ _ => rfl, ?_, fun _ _ _ => rfl⟩
    exact MemOut.of_agree r st mb es _ _ _ hw hmb (Agree.refl _ _ _ _)
  | cons w ws =>
    have hne : w :: ws ≠ [] := by simp
    obtain ⟨_, _, h3⟩ := memCommit_runX H F (idxOf r) st mb (w :: ws) hne es rest sC hL hM hIC.sp h20 hmb hok
      (by rw [← hw]; exact hW.wOff) (fun w' hw' => hWF.idxLt _ (writes_sub_slots r w' (by rw [hw]; exact hw')))
      (fun w' hw' => by rw [← hFes]; exact hIC.slots _ (writes_sub_slots r w' (by rw [hw]; exact hw')))
    rw [hw] at hcapOk
    have hgasOk' : ecost ((msAt sC.mem st).toNat / 32) (wordsOf (maxEndOf (w :: ws))) ≤ (sC.regs .x22).toNat := by
      unfold memGas at hgasOk; rw [hw] at hgasOk; exact hgasOk
    obtain ⟨sC', h', hsp', hgas', hregs', hms', hmp', hcap', hmb', hbuf', hout'⟩ := h3 hcapOk hgasOk'
    refine ⟨sC', h', hsp', by rw [hgas']; unfold memGas; rw [hw], hregs',
            ⟨by unfold newMs; rw [hw]; exact hms', by rw [hw]; exact hmp', hcap', hmb', by rw [hw]; exact hbuf'⟩, hout'⟩

theorem body_runX (H : Helpers) (hS : H.Spec) (hC : H.conv = x86Conv) (r : Region) (hW : RegionWF r) (s : RS)
    (base : BitVec 64) (d : Nat) (es : List Evm.U256) (st mb : BitVec 64) (rest : List AInstr)
    (hL : LayX (frameOfX s.sp (slotsOf r).length base d es))
    (hM : MLay (frameOfX s.sp (slotsOf r).length base d es) st mb (capAt s.mem st).toNat)
    (h23 : s.regs .x23 = BitVec.ofNat 64 (32 * d)) (h24 : s.regs .x24 = base)
    (hstack : ∀ k < d, ld256 s.mem (stackAddr base d k) = es.getD k 0)
    (h20 : s.regs .x20 = st) (hmb : mbAt s.mem st = mb)
    (hok : (msAt s.mem st).toNat ≤ (capAt s.mem st).toNat)
    (hcapOk : maxEndOf r.writes ≤ (capAt s.mem st).toNat) (hgasOk : memGas r s.mem st ≤ (s.regs .x22).toNat)
    (hneed : r.need ≤ d) (hd' : newDepthOf r d ≤ 1024) :
    let n := (slotsOf r).length
    let F := frameOfX s.sp n base d es
    ∃ s', run H (frameOpenX n ++ ((slotsOf r).flatMap (evalNodeX (idxOf r)) ++
                  (memCommitT Evm.CL.X86JIT.x86Flush (idxOf r) r.writes ++
                  (exitStoresX (idxOf r) ((r.ss.exprs.length : Int) - r.ss.consumed) r.ss.exprs ++
                  (frameCloseX n ++ rest))))) s = run H rest s' ∧
      s'.sp = s.sp ∧ s'.regs .x23 = BitVec.ofNat 64 (32 * d) ∧ s'.regs .x24 = base ∧
      (∀ r', keep r' = true → r' ≠ .x22 → s'.regs r' = s.regs r') ∧
      (s'.regs .x22).toNat = (s.regs .x22).toNat - memGas r s.mem st ∧
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
  have hfpOk : F.fp.toNat + 32 * n + 8 < 2 ^ 64 := hL.fpOk
  have hdisj : ∀ i < 32 * n + 8, ∀ j < 32 * 1024, off F.fp i ≠ off base j := hL.disj
  have hdLe : d ≤ 1024 := hL.dLe
  have hc : r.ss.consumed ≤ d := Nat.le_trans hW.cLe hneed
  -- 1-2. frame open and the DAG
  obtain ⟨sC, hC', hIC, hregsC, hAgC, houtC⟩ :=
    pre_runX H hS hC r hW s base d es st mb _ hL hM h23 h24 hstack hneed
  rw [hC']
  have hWF : WFSlots F (idxOf r) (slotsOf r) := wfSlots_of r hW F rfl hneed
  have hcapC : capAt sC.mem st = capAt s.mem st := hAgC.cap
  -- 2.5 the commit
  obtain ⟨sD, hD, hspD, hgasD, hregsD, hMO, houtD⟩ := commit_runX H r hW F hL st mb es _ sC hFes
    (by rw [hcapC]; exact hM) hIC hWF (by rw [hregsC _ (by decide), h20]) (by rw [hAgC.mb, hmb])
    (by rw [hAgC.ms, hcapC]; exact hok) (by rw [hcapC]; exact hcapOk)
    (by rw [memGas_agree r hAgC, hregsC _ (by decide)]; exact hgasOk)
  rw [hD]
  rw [hcapC] at hMO houtD
  have frame_ok : ∀ i < 32 * n + 16, (∀ k, 24 ≤ k → k < 64 → off F.fp i ≠ off st k) ∧
      (∀ k < (capAt s.mem st).toNat, off F.fp i ≠ off mb k) :=
    fun i hi =>
      have hi' : i < 32 * (frameOfX s.sp (slotsOf r).length base d es).n + 16 := hi
      ⟨fun k hk hk' h => hM.stFrame k hk hk' i hi' h.symm, fun k hk h => hM.bufFrame k hk i hi' h.symm⟩
  have stack_ok : ∀ j < 32 * 1024, (∀ k, 24 ≤ k → k < 64 → off base j ≠ off st k) ∧
      (∀ k < (capAt s.mem st).toNat, off base j ≠ off mb k) :=
    fun j hj => ⟨fun k hk hk' h => hM.stStack k hk hk' j hj h.symm, fun k hk h => hM.bufStack k hk j hj h.symm⟩
  have hframeD : ∀ i < 32 * n + 16, sD.mem (off F.fp i) = sC.mem (off F.fp i) :=
    fun i hi => houtD _ (frame_ok i hi).1 (frame_ok i hi).2
  have hstackD : ∀ j < 32 * 1024, sD.mem (off base j) = sC.mem (off base j) :=
    fun j hj => houtD _ (stack_ok j hj).1 (stack_ok j hj).2
  have hXD : ExitInvX F (idxOf r) (slotsOf r) r.ss.consumed sD := by
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
  obtain ⟨sE, hE, hXE, hstored, hspE, hregsE, hmemE⟩ := exit_loopX H F hL (idxOf r) (slotsOf r) r.ss.consumed
    r.ss.exprs.length _ hc hd' hidx r.ss.exprs 0 sD (by simp) (exprs_sub_slots r) hXD
  rw [show exitStoresX (idxOf r) ((r.ss.exprs.length : Int) - r.ss.consumed) r.ss.exprs =
        (r.ss.exprs.zipIdx 0).flatMap (fun (e, m) => exitOneX (idxOf r) ((r.ss.exprs.length : Int) - r.ss.consumed) e m)
        from rfl, hE]
  have hmemE' : ∀ x, (∀ j < 32 * 1024, x ≠ off base j) → sE.mem x = sD.mem x := by
    intro x hxb
    apply hmemE
    intro m _ hm b hb
    simp only [stackAddr, off_off, hFb]
    exact hxb _ (by have : d + r.ss.exprs.length - r.ss.consumed ≤ 1024 := hd'; simp only [hFd, newDepth]; omega)
  -- 4. frame close
  rw [frameCloseX_run]
  have hspE' : sE.sp = F.fp := by rw [hspE, hspD, hIC.sp]
  have hAgE : Agree st mb (capAt s.mem st).toNat sD.mem sE.mem := Agree.of_stack F st mb _ hM _ _ hmemE'
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [AsmRun.withSp_sp, hspE']
    show s.sp - BitVec.ofNat 64 (32 * n + 8) + BitVec.ofNat 64 (32 * n + 8) = s.sp
    exact BitVec.sub_add_cancel _ _
  · simp only [AsmRun.withSp_regs]; rw [hregsE _ rfl, hregsD _ rfl (by decide), hIC.x23]; rfl
  · simp only [AsmRun.withSp_regs]; rw [hregsE _ rfl, hregsD _ rfl (by decide), hIC.x24]; rfl
  · intro r' hr' h22
    simp only [AsmRun.withSp_regs]
    rw [hregsE _ hr', hregsD _ hr' h22, hregsC _ hr']
  · simp only [AsmRun.withSp_regs]
    rw [hregsE _ rfl, hgasD, hregsC _ rfl, memGas_agree r hAgC]
  · intro i hi
    simp only [AsmRun.withSp_mem]
    have := hstored i hi
    simpa [newDepthOf, F, frameOfX] using this
  · intro k hck hkd
    simp only [AsmRun.withSp_mem]
    exact hXE.keepStack k hck hkd
  · simp only [AsmRun.withSp_mem]
    exact (hMO.agree_left hAgC).agree_right hAgE
  · intro x hxb hxf hxw hxs hxm
    simp only [AsmRun.withSp_mem]
    rw [hmemE' x hxb, houtD x hxs hxm, houtC x hxb hxf hxw]

/-! ## The depth checks -/

theorem checks_runX (H : Helpers) (r : Region) (d : Nat) (hd : d ≤ 1024) (rest : List AInstr) (s : RS)
    (h23 : s.regs .x23 = BitVec.ofNat 64 (32 * d)) (hneed : r.need ≤ d)
    (hover : r.maxNet > 0 → (d : Int) < 1025 - r.maxNet) :
    ∃ s', run H ((if r.need > 0
                    then [AInstr.cmpImm .x23 (32 * r.need), .bcLbl .hs "8f", .bTramp "_eita_stack_underflow", .label "8"]
                    else []) ++
                 ((if r.maxNet > 0
                    then [AInstr.cmpImm .x23 (32 * (1025 - r.maxNet).toNat), .bcLbl .lo "9f", .bTramp "_eita_stack_overflow",
                          .label "9"]
                    else []) ++ rest)) s = run H rest s' ∧
      s'.regs = s.regs ∧ s'.sp = s.sp ∧ s'.mem = s.mem := by
  have step1 : ∃ s1, run H ((if r.need > 0
      then [AInstr.cmpImm .x23 (32 * r.need), .bcLbl .hs "8f", .bTramp "_eita_stack_underflow", .label "8"]
      else []) ++ ((if r.maxNet > 0
      then [AInstr.cmpImm .x23 (32 * (1025 - r.maxNet).toNat), .bcLbl .lo "9f", .bTramp "_eita_stack_overflow", .label "9"]
      else []) ++ rest)) s = run H ((if r.maxNet > 0
      then [AInstr.cmpImm .x23 (32 * (1025 - r.maxNet).toNat), .bcLbl .lo "9f", .bTramp "_eita_stack_overflow", .label "9"]
      else []) ++ rest) s1 ∧ s1.regs = s.regs ∧ s1.sp = s.sp ∧ s1.mem = s.mem := by
    split
    · simp only [List.cons_append, List.nil_append]
      rw [underflowCheckX_run H r.need d (by omega) (by omega) _ s h23, ite_eq_left hneed]
      exact ⟨_, rfl, rfl, rfl, rfl⟩
    · rw [List.nil_append]; exact ⟨s, rfl, rfl, rfl, rfl⟩
  obtain ⟨s1, h1, hr1, hs1, hm1⟩ := step1
  rw [h1]
  have h23' : s1.regs .x23 = BitVec.ofNat 64 (32 * d) := by rw [hr1, h23]
  split
  · rename_i hm
    have hlim : d < (1025 - r.maxNet).toNat := by have := hover hm; omega
    simp only [List.cons_append, List.nil_append]
    rw [overflowCheckX_run H _ d (by omega) (by omega) _ s1 h23', ite_eq_left hlim]
    exact ⟨_, rfl, by rw [AsmRun.withFlags_regs, hr1], by rw [AsmRun.withFlags_sp, hs1], by rw [AsmRun.withFlags_mem, hm1]⟩
  · rw [List.nil_append]; exact ⟨s1, rfl, hr1, hs1, hm1⟩

/-! ## THE theorem -/

theorem flush_runX (H : Helpers) (hS : H.Spec) (hC : H.conv = x86Conv) (r : Region) (hW : RegionWF r) (s : RS)
    (base : BitVec 64) (d : Nat) (es : List Evm.U256) (st mb : BitVec 64) (rest : List AInstr)
    (hL : LayX (frameOfX s.sp (slotsOf r).length base d es))
    (hM : MLay (frameOfX s.sp (slotsOf r).length base d es) st mb (capAt s.mem st).toNat)
    (h23 : s.regs .x23 = BitVec.ofNat 64 (32 * d)) (h24 : s.regs .x24 = base) (hes : es.length = d)
    (hstack : ∀ k < d, ld256 s.mem (stackAddr base d k) = es.getD k 0)
    (htos : 1 ≤ d → lhs s = es.getD 0 0)
    (h20 : s.regs .x20 = st) (hmb : mbAt s.mem st = mb)
    (hok : (msAt s.mem st).toNat ≤ (capAt s.mem st).toNat)
    (hcapOk : maxEndOf r.writes ≤ (capAt s.mem st).toNat) (hgasOk : memGas r s.mem st ≤ (s.regs .x22).toNat)
    (hneed : r.need ≤ d) (hover : r.maxNet > 0 → (d : Int) < 1025 - r.maxNet) :
    ∃ s', run H (emitRegionFlushX r ++ rest) s = run H rest s' ∧
      FlushOutX r base d es (frameOfX s.sp (slotsOf r).length base d es).fp (slotsOf r).length st mb s s' := by
  have hdLe : d ≤ 1024 := hL.dLe
  have hc : r.ss.consumed ≤ d := Nat.le_trans hW.cLe hneed
  have hd' : newDepthOf r d ≤ 1024 := by
    have := hW.netLe
    simp only [newDepthOf, newDepth]
    by_cases hm : r.maxNet > 0
    · have := hover hm; omega
    · omega
  have hdenote : SymStack.denote r.ss es = newStack r.ss.exprs es r.ss.consumed := rfl
  simp only [emitRegionFlushX, dagSlots_of, List.size_toArray, List.toList_toArray]
  have trivialOut : ∀ s1 : RS, s1.regs = s.regs → s1.sp = s.sp → s1.mem = s.mem →
      r.ss.exprs.length = 0 → r.ss.consumed = 0 → r.writes = [] →
      FlushOutX r base d es (frameOfX s.sp (slotsOf r).length base d es).fp (slotsOf r).length st mb s s1 := by
    intro s1 hr1 hs1 hm1 hp hc0 hw
    have hd0 : newDepthOf r d = d := by simp [newDepthOf, newDepth, hp, hc0]
    have hex : r.ss.exprs = [] := List.length_eq_zero_iff.mp hp
    have hns : SymStack.denote r.ss es = es := by rw [hdenote]; simp [newStack, hex, hc0]
    refine ⟨hs1, by rw [hd0, hr1, h23], fun r' _ _ _ => by rw [hr1], by rw [hr1, memGas_nil r _ _ hw]; omega,
            ?_, ?_, MemOut.of_agree r st mb es _ _ _ hw hmb (Agree.of_eq hm1), fun x _ _ _ _ _ => by rw [hm1]⟩
    · intro j hj; rw [hd0] at hj ⊢; rw [hns, hm1]; exact hstack j hj
    · intro h1; rw [hd0] at h1; rw [hns]; simp only [lhs, hr1]; exact htos h1
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
          obtain ⟨s1, h1, hr1, hs1, hm1⟩ := checks_runX H r d hdLe rest s h23 hneed hover
          simp only [List.append_assoc]
          exact ⟨s1, h1, trivialOut s1 hr1 hs1 hm1 hidle.1.1 hidle.1.2 hidle.2⟩
        · rename_i hnidle
          simp only [List.append_assoc]
          obtain ⟨s1, h1, hr1, hs1, hm1⟩ := checks_runX H r d hdLe _ s h23 hneed hover
          rw [h1]
          have h23' : s1.regs .x23 = BitVec.ofNat 64 (32 * d) := by rw [hr1, h23]
          have h24' : s1.regs .x24 = base := by rw [hr1, h24]
          have h20' : s1.regs .x20 = st := by rw [hr1, h20]
          have hstack1 : ∀ k < d, ld256 s1.mem (stackAddr base d k) = es.getD k 0 := by rw [hm1]; exact hstack
          have hL1 : LayX (frameOfX s1.sp (slotsOf r).length base d es) := by rw [hs1]; exact hL
          have hM1 : MLay (frameOfX s1.sp (slotsOf r).length base d es) st mb (capAt s1.mem st).toNat := by
            rw [hs1, hm1]; exact hM
          split
          · rename_i hn
            simp only [List.append_assoc]
            obtain ⟨sE, hE, hspE, h23E, h24E, hregsE, hgasE, hstoredE, hkeptE, hMO, hmemE⟩ :=
              body_runX H hS hC r hW s1 base d es st mb _ hL1 hM1 h23' h24' hstack1 h20' (by rw [hm1]; exact hmb)
                (by rw [hm1]; exact hok) (by rw [hm1]; exact hcapOk) (by rw [hm1, hr1]; exact hgasOk) hneed hd'
            rw [hE]
            obtain ⟨sF, hF, hspF, hmemF, h23F, hregsF, hstackF, htosF⟩ :=
              tail_runX H r.ss.exprs r.ss.consumed base d es rest sE hdLe hc hd' hes h23E h24E hstoredE hkeptE
            refine ⟨sF, hF, ⟨by rw [hspF, hspE, hs1], h23F, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
            · intro r' hr' hne h22
              obtain ⟨_, _, _, _, h6, h7, h8, h9, _, _, _, _, h14, _, _, _⟩ := keep_ne r' hr'
              rw [hregsF r' hne h6 h7 h8 h9 h14, hregsE r' hr' h22, hr1]
            · rw [hregsF _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hgasE, hr1, hm1]
            · intro j hj; rw [hdenote]; exact hstackF j hj
            · intro h1d; rw [hdenote]; exact htosF h1d
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
            obtain ⟨sF, hF, hspF, hmemF, h23F, hregsF, hstackF, htosF⟩ :=
              tail_runX H r.ss.exprs r.ss.consumed base d es rest s1 hdLe hc hd' hes h23' h24'
                (fun i hi => by rw [hex] at hi; simp at hi) (fun k _ hk => hstack1 k hk)
            refine ⟨sF, hF, ⟨by rw [hspF, hs1], h23F, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
            · intro r' hr' hne _
              obtain ⟨_, _, _, _, h6, h7, h8, h9, _, _, _, _, h14, _, _, _⟩ := keep_ne r' hr'
              rw [hregsF r' hne h6 h7 h8 h9 h14, hr1]
            · rw [hregsF _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr1,
                  memGas_nil r _ _ hwnil]; omega
            · intro j hj; rw [hdenote]; exact hstackF j hj
            · intro h1d; rw [hdenote]; exact htosF h1d
            · rw [hmemF, hm1]; exact MemOut.of_agree r st mb es _ _ _ hwnil hmb (Agree.refl _ _ _ _)
            · intro x _ _ _ _ _; rw [hmemF, hm1]

/-- The same, stated on the production program: `emitRegionFlushT x86Flush` after `spScale`. -/
theorem flush_runX_scaled (H : Helpers) (hS : H.Spec) (hC : H.conv = x86Conv) (r : Region) (hW : RegionWF r) (s : RS)
    (base : BitVec 64) (d : Nat) (es : List Evm.U256) (st mb : BitVec 64) (rest : List AInstr)
    (hL : LayX (frameOfX s.sp (slotsOf r).length base d es))
    (hM : MLay (frameOfX s.sp (slotsOf r).length base d es) st mb (capAt s.mem st).toNat)
    (h23 : s.regs .x23 = BitVec.ofNat 64 (32 * d)) (h24 : s.regs .x24 = base) (hes : es.length = d)
    (hstack : ∀ k < d, ld256 s.mem (stackAddr base d k) = es.getD k 0)
    (htos : 1 ≤ d → lhs s = es.getD 0 0)
    (h20 : s.regs .x20 = st) (hmb : mbAt s.mem st = mb)
    (hok : (msAt s.mem st).toNat ≤ (capAt s.mem st).toNat)
    (hcapOk : maxEndOf r.writes ≤ (capAt s.mem st).toNat) (hgasOk : memGas r s.mem st ≤ (s.regs .x22).toNat)
    (hneed : r.need ≤ d) (hover : r.maxNet > 0 → (d : Int) < 1025 - r.maxNet) :
    ∃ s', run H (scaleP (emitRegionFlushT Evm.CL.X86JIT.x86Flush r) ++ rest) s = run H rest s' ∧
      FlushOutX r base d es (frameOfX s.sp (slotsOf r).length base d es).fp (slotsOf r).length st mb s s' := by
  rw [scale_emitRegionFlush]
  exact flush_runX H hS hC r hW s base d es st mb rest hL hM h23 h24 hes hstack htos h20 hmb hok hcapOk hgasOk hneed hover

end Evm.CL.X86.FlushMainX
