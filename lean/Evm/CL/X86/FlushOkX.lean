/-
  Evm.CL.X86.FlushOkX — the x86-64 region flush is a certified fragment:
  `Ok` (liveness and flag provenance through every piece, with the dead code
  after each trampoline exit) and `LabelsOk` (every local branch finds its
  label, no trampoline label is defined inside) for `emitRegionFlushX r`, for
  EVERY region. Hence, through `sim_run`, the lowered x86 bytes of the flush
  reach the state `FlushMainX.flush_runX` describes.
-/

import Evm.CL.X86Xfer
import Evm.CL.X86.FlushMainX

namespace Evm.CL.X86.FlushOkX

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun Evm.CL.ARM64.JIT Evm.CL.X86Items Evm.CL.X86Sem Evm.CL.X86SemCtrl
open Evm.CL.X86Xfer Evm.CL.X86.FlushSemX Evm.CL.X86.FlushScaleX Evm.CL.X86.FlushMainX
open Evm.IR.SymExpr (Expr)

/-! ## The live sets and the label table -/

/-- Live between regions: the TOS cache and the chunk's pinned registers. -/
def Lend : List Reg := [.x6, .x7, .x8, .x9, .x20, .x21, .x22, .x23, .x24, .x26]
/-- Live inside the DAG: the pinned registers only (a helper call clobbers the cache). -/
def Lnode : List Reg := [.x20, .x21, .x22, .x23, .x24, .x26]
/-- At `5` in the expansion gadget: the end bound (x0) and the cap (x14). -/
def L5 : List Reg := [.x0, .x14, .x20, .x21, .x22, .x23, .x24, .x26]
/-- At `6`: the end bound. -/
def L6 : List Reg := [.x0, .x20, .x21, .x22, .x23, .x24, .x26]

def tblF : List (String × (List Reg × Prov)) :=
  [("5", (L5, .unknown)), ("6", (L6, .unknown)), ("7", (Lnode, .unknown)), ("8", (Lend, .unknown)), ("9", (Lend, .unknown))]

abbrev FragF := Frag tblF Lend .unknown

theorem Lnode_sub_Lend : ∀ r ∈ Lnode, r ∈ Lend := by decide

/-! ## Pieces -/

theorem frag_node (idx : Expr → Nat) (e : Expr) : FragF (evalNodeX idx e) Lnode .unknown Lnode .unknown := by
  cases e <;> exact Frag.ofB_sup Lnode rfl (by decide)

theorem frag_dag (idx : Expr → Nat) (l : List Expr) : FragF (l.flatMap (evalNodeX idx)) Lnode .unknown Lnode .unknown :=
  Frag.flatMap _ _ _ l (fun e _ => frag_node idx e)

theorem frag_memExpand (m : Nat) : FragF (memExpandFlushT Evm.CL.X86JIT.x86Flush m) Lnode .unknown Lnode .unknown :=
  Frag.ofB_sup Lnode rfl (by decide)

theorem frag_mpUpdate (m : Nat) : FragF (mpUpdateFlushT Evm.CL.X86JIT.x86Flush m) Lnode .unknown Lnode .unknown :=
  Frag.ofB_sup Lnode rfl (by decide)

/-- A write ends with the cache in sync (its slot was loaded into x6..x9). -/
theorem frag_memWrite (idx : Expr → Nat) (w : MemWrite) :
    FragF (emitMemWriteT Evm.CL.X86JIT.x86Flush idx w) Lnode .unknown Lend .unknown := by
  unfold emitMemWriteT memBaseAtT
  split <;> split <;> (try split) <;> exact Frag.ofB_sup Lend rfl (by decide)

theorem frag_exitOne (idx : Expr → Nat) (net : Int) (e : Expr) (m : Nat) :
    FragF (exitOneX idx net e m) Lnode .unknown Lend .unknown := by
  unfold exitOneX
  dsimp only
  split <;> exact Frag.ofB_sup Lend rfl (by decide)

theorem frag_frameOpen (n : Nat) : FragF (frameOpenX n) Lend .unknown Lend .unknown := Frag.ofB_sup Lend rfl (by decide)
theorem frag_frameClose (n : Nat) : FragF (frameCloseX n) Lend .unknown Lend .unknown := Frag.ofB_sup Lend rfl (by decide)

theorem frag_depthUpdate (net : Int) : FragF (depthUpdateX net) Lend .unknown Lend .unknown := by
  unfold depthUpdateX
  split
  · exact Frag.ofB_sup Lend rfl (by decide)
  · split
    · exact Frag.ofB_sup Lend rfl (by decide)
    · exact Frag.nil _ _

theorem frag_cacheReload : FragF cacheReloadX Lend .unknown Lend .unknown := Frag.ofB_sup Lend rfl (by decide)

theorem frag_underflow (need : Nat) :
    FragF [AInstr.cmpImm .x23 (32 * need), .bcLbl .hs "8f", .bTramp "_eita_stack_underflow", .label "8"]
      Lend .unknown Lend .unknown := Frag.ofB_sup Lend rfl (by decide)

theorem frag_overflow (lim : Nat) :
    FragF [AInstr.cmpImm .x23 (32 * lim), .bcLbl .lo "9f", .bTramp "_eita_stack_overflow", .label "9"]
      Lend .unknown Lend .unknown := Frag.ofB_sup Lend rfl (by decide)

theorem frag_tramp (sym : String) (L : List Reg) (p : Prov) : FragF [AInstr.bTramp sym] L p deadL .unknown :=
  Frag.ofB rfl

/-! ## Lists whose first element brings the cache back -/

theorem flatMap_lo {α : Type} (f : α → List AInstr) (h : ∀ a, FragF (f a) Lnode .unknown Lend .unknown) :
    ∀ (l : List α), l ≠ [] → FragF (l.flatMap f) Lnode .unknown Lend .unknown
  | [], hne => absurd rfl hne
  | a :: l, _ => by
    rw [List.flatMap_cons]
    exact (h a).append (Frag.flatMap f Lend .unknown l
      (fun b _ => (h b).mono Lnode_sub_Lend (provLe_refl _) (fun _ h => h) (provLe_refl _)))

theorem flatMap_hi {α : Type} (f : α → List AInstr) (h : ∀ a, FragF (f a) Lnode .unknown Lend .unknown)
    (l : List α) : FragF (l.flatMap f) Lend .unknown Lend .unknown :=
  Frag.flatMap f Lend .unknown l (fun b _ => (h b).mono Lnode_sub_Lend (provLe_refl _) (fun _ h => h) (provLe_refl _))

theorem frag_commit_exit (idx : Expr → Nat) (ws : List MemWrite) (net : Int) (exprs : List Expr)
    (hne : ws ≠ [] ∨ exprs ≠ []) :
    FragF (memCommitT Evm.CL.X86JIT.x86Flush idx ws ++ exitStoresX idx net exprs) Lnode .unknown Lend .unknown := by
  unfold exitStoresX
  cases ws with
  | nil =>
    rw [show memCommitT Evm.CL.X86JIT.x86Flush idx [] = [] from rfl, List.nil_append]
    cases exprs with
    | nil => exact absurd rfl (hne.resolve_left (fun h => h rfl))
    | cons e es =>
      rw [List.zipIdx_cons, List.flatMap_cons]
      exact (frag_exitOne idx net e 0).append (flatMap_hi _ (fun (p : Expr × Nat) => frag_exitOne idx net p.1 p.2) _)
  | cons w ws =>
    unfold memCommitT
    rw [if_neg (by simp)]
    dsimp only
    rw [List.append_assoc, List.append_assoc]
    refine (frag_memExpand _).append ((frag_mpUpdate _).append ?_)
    exact (flatMap_lo _ (frag_memWrite idx) (w :: ws) (by simp)).append
      (flatMap_hi _ (fun (p : Expr × Nat) => frag_exitOne idx net p.1 p.2) _)

/-- The body's tail, grouped as the flush program has it. -/
theorem frag_body_tail (idx : Expr → Nat) (ws : List MemWrite) (net : Int) (exprs : List Expr) (n : Nat)
    (hne : ws ≠ [] ∨ exprs ≠ []) :
    FragF (memCommitT Evm.CL.X86JIT.x86Flush idx ws ++ (exitStoresX idx net exprs ++ frameCloseX n))
      Lnode .unknown Lend .unknown := by
  rw [← List.append_assoc]
  exact (frag_commit_exit idx ws net exprs hne).append (frag_frameClose n)

theorem slots_nil_of (r : Region) (hex : r.ss.exprs = []) (hw : r.writes = []) :
    (Evm.CL.ARM64.FlushMain.slotsOf r).length = 0 := by
  simp [Evm.CL.ARM64.FlushMain.slotsOf, Evm.CL.ARM64.FlushMain.rootsOf, hex, hw]

/-! ## The whole flush is `Ok` -/

theorem ok_flush (r : Region) : Ok (annOf tblF) Lend .unknown (emitRegionFlushX r) Lend .unknown := by
  have hendOk : Dead Lend ∨ ((∀ r ∈ Lend, r ∈ Lend) ∧ provLe Prov.unknown Prov.unknown) :=
    Or.inr ⟨fun _ h => h, provLe_refl _⟩
  have hdeadOk : Dead deadL ∨ ((∀ r ∈ Lend, r ∈ deadL) ∧ provLe Prov.unknown Prov.unknown) :=
    Or.inl (by simp [Dead, deadL])
  have s1 : FragF (if r.need > 0
      then [AInstr.cmpImm .x23 (32 * r.need), .bcLbl .hs "8f", .bTramp "_eita_stack_underflow", .label "8"] else [])
      Lend .unknown Lend .unknown := Frag.ite (fun _ => frag_underflow _) (fun _ => Frag.nil _ _)
  have s2 : FragF (if r.maxNet > 0
      then [AInstr.cmpImm .x23 (32 * (1025 - r.maxNet).toNat), .bcLbl .lo "9f", .bTramp "_eita_stack_overflow", .label "9"]
      else []) Lend .unknown Lend .unknown := Frag.ite (fun _ => frag_overflow _) (fun _ => Frag.nil _ _)
  simp only [emitRegionFlushX, Evm.CL.ARM64.FlushMain.dagSlots_of, List.size_toArray, List.toList_toArray,
             List.append_assoc]
  split
  · exact Ok_of_Frag (Frag.nil _ _) hendOk
  · split
    · exact Ok_of_Frag (frag_tramp _ _ _) hdeadOk
    · split
      · exact Ok_of_Frag (s1.append (frag_tramp _ _ _)) hdeadOk
      · split
        · exact Ok_of_Frag (s1.append s2) hendOk
        · refine Ok_of_Frag (s1.append (s2.append (Frag.append ?_ ((frag_depthUpdate _).append frag_cacheReload)))) hendOk
          apply Frag.ite
          · intro hn
            have hne : r.writes ≠ [] ∨ r.ss.exprs ≠ [] := by
              by_cases hw : r.writes = []
              · by_cases hex : r.ss.exprs = []
                · exfalso; have := slots_nil_of r hex hw; omega
                · exact Or.inr hex
              · exact Or.inl hw
            exact (frag_frameOpen _).append
              (((frag_dag _ _).mono Lnode_sub_Lend (provLe_refl _) (fun _ h => h) (provLe_refl _)).append
                (frag_body_tail _ _ _ _ _ hne))
          · intro _; exact Frag.nil _ _


/-! ## Labels: the flush defines only `5`–`9`, and every branch finds its label -/

def five : List String := ["5", "6", "7", "8", "9"]
abbrev Five (ls : List String) : Prop := ∀ t ∈ ls, t ∈ five

theorem Five.nil : Five [] := fun _ h => by simp at h

theorem found_cons (l t : String) (ls : List String) : found l (t :: ls) = ((l == t || l == t ++ "f") || found l ls) := by
  simp [found]
theorem Five.append {a b : List String} (ha : Five a) (hb : Five b) : Five (a ++ b) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact ha t h
  · exact hb t h

theorem found_tramp (l : String) (hl : l = "Lx_oog" ∨ l = "Lx_under" ∨ l = "Lx_over") :
    ∀ (ls : List String), Five ls → found l ls = false
  | [], _ => rfl
  | t :: ls, h => by
    simp only [found, List.any_cons, Bool.or_eq_false_iff]
    refine ⟨?_, found_tramp l hl ls (fun u hu => h u (by simp [hu]))⟩
    have ht := h t (by simp)
    simp only [five, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases hl with rfl | rfl | rfl <;> rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide

/-- A fragment whose branches all land inside it, whose labels are among the five. -/
def Lok (p : List AInstr) : Prop := (∀ ext, Five ext → lokB p ext = true) ∧ Five (labelsOf p)

theorem Lok.nil : Lok [] := ⟨fun _ _ => rfl, Five.nil⟩

theorem Lok.append {p q : List AInstr} (hp : Lok p) (hq : Lok q) : Lok (p ++ q) := by
  refine ⟨fun ext hext => ?_, by rw [labelsOf_append]; exact hp.2.append hq.2⟩
  rw [lokB_append, hp.1 _ (hq.2.append hext), hq.1 _ hext]; rfl

theorem Lok.flatMap {α : Type} (f : α → List AInstr) (h : ∀ a, Lok (f a)) : ∀ (l : List α), Lok (l.flatMap f)
  | [] => by simpa using Lok.nil
  | a :: l => by rw [List.flatMap_cons]; exact (h a).append (Lok.flatMap f h l)

theorem Lok.ite {c : Prop} [Decidable c] {p q : List AInstr} (hp : c → Lok p) (hq : ¬c → Lok q) :
    Lok (if c then p else q) := by
  split
  · exact hp (by assumption)
  · exact hq (by assumption)

/-- A branch-free, label-free piece. -/
theorem Lok.closed (p : List AInstr) (h1 : ∀ ext, lokB p ext = true) (h2 : labelsOf p = []) : Lok p :=
  ⟨fun ext _ => h1 ext, by rw [h2]; exact Five.nil⟩

theorem lok_node (idx : Expr → Nat) (e : Expr) : Lok (evalNodeX idx e) := by
  cases e <;> exact Lok.closed _ (fun _ => rfl) rfl

theorem lok_memWrite (idx : Expr → Nat) (w : MemWrite) : Lok (emitMemWriteT Evm.CL.X86JIT.x86Flush idx w) := by
  unfold emitMemWriteT memBaseAtT
  split <;> split <;> (try split) <;> exact Lok.closed _ (fun _ => rfl) rfl

theorem lok_exitOne (idx : Expr → Nat) (net : Int) (e : Expr) (m : Nat) : Lok (exitOneX idx net e m) := by
  unfold exitOneX
  dsimp only
  split <;> exact Lok.closed _ (fun _ => rfl) rfl

theorem lok_mpUpdate (m : Nat) : Lok (mpUpdateFlushT Evm.CL.X86JIT.x86Flush m) := Lok.closed _ (fun _ => rfl) rfl
theorem lok_frameOpen (n : Nat) : Lok (frameOpenX n) := Lok.closed _ (fun _ => rfl) rfl
theorem lok_frameClose (n : Nat) : Lok (frameCloseX n) := Lok.closed _ (fun _ => rfl) rfl

theorem lok_depthUpdate (net : Int) : Lok (depthUpdateX net) := by
  unfold depthUpdateX
  split
  · exact Lok.closed _ (fun _ => rfl) rfl
  · split
    · exact Lok.closed _ (fun _ => rfl) rfl
    · exact Lok.nil

theorem tramp_oog : trampLabel "_eita_oog" = "Lx_oog" := rfl
theorem tramp_under : trampLabel "_eita_stack_underflow" = "Lx_under" := rfl
theorem tramp_over : trampLabel "_eita_stack_overflow" = "Lx_over" := rfl

theorem lok_memExpand (m : Nat) : Lok (memExpandFlushT Evm.CL.X86JIT.x86Flush m) := by
  refine ⟨fun ext hext => ?_, by rw [show labelsOf (memExpandFlushT Evm.CL.X86JIT.x86Flush m) = ["5", "6", "7"] from rfl]; decide⟩
  have h1 := found_tramp "Lx_oog" (Or.inl rfl) ext hext
  simp [memExpandFlushT, Evm.CL.X86JIT.x86Flush, lokB, lokStep, labelsOf, found_cons, tramp_oog, h1]

theorem lok_cacheReload : Lok cacheReloadX := by
  refine ⟨fun ext hext => ?_, by rw [show labelsOf cacheReloadX = ["8"] from rfl]; decide⟩
  simp [cacheReloadX, lokB, lokStep, labelsOf, found_cons]

theorem lok_underflow (need : Nat) :
    Lok [AInstr.cmpImm .x23 (32 * need), .bcLbl .hs "8f", .bTramp "_eita_stack_underflow", .label "8"] := by
  refine ⟨fun ext hext => ?_, by rw [show labelsOf [AInstr.cmpImm .x23 (32 * need), .bcLbl .hs "8f", .bTramp "_eita_stack_underflow", .label "8"] = ["8"] from rfl]; decide⟩
  have h1 := found_tramp "Lx_under" (Or.inr (Or.inl rfl)) ext hext
  simp [lokB, lokStep, labelsOf, found_cons, tramp_under, h1]

theorem lok_overflow (lim : Nat) :
    Lok [AInstr.cmpImm .x23 (32 * lim), .bcLbl .lo "9f", .bTramp "_eita_stack_overflow", .label "9"] := by
  refine ⟨fun ext hext => ?_, by rw [show labelsOf [AInstr.cmpImm .x23 (32 * lim), .bcLbl .lo "9f", .bTramp "_eita_stack_overflow", .label "9"] = ["9"] from rfl]; decide⟩
  have h1 := found_tramp "Lx_over" (Or.inr (Or.inr rfl)) ext hext
  simp [lokB, lokStep, labelsOf, found_cons, tramp_over, h1]

theorem lok_tramp_under : Lok [AInstr.bTramp "_eita_stack_underflow"] := by
  refine ⟨fun ext hext => ?_, Five.nil⟩
  have h1 := found_tramp "Lx_under" (Or.inr (Or.inl rfl)) ext hext
  simp [lokB, lokStep, labelsOf, tramp_under, h1]

theorem lok_tramp_over : Lok [AInstr.bTramp "_eita_stack_overflow"] := by
  refine ⟨fun ext hext => ?_, Five.nil⟩
  have h1 := found_tramp "Lx_over" (Or.inr (Or.inr rfl)) ext hext
  simp [lokB, lokStep, labelsOf, tramp_over, h1]

theorem lok_memCommit (idx : Expr → Nat) (ws : List MemWrite) : Lok (memCommitT Evm.CL.X86JIT.x86Flush idx ws) := by
  unfold memCommitT
  split
  · exact Lok.nil
  · dsimp only
    exact ((lok_memExpand _).append (lok_mpUpdate _)).append (Lok.flatMap _ (lok_memWrite idx) ws)

theorem lok_exitStores (idx : Expr → Nat) (net : Int) (exprs : List Expr) : Lok (exitStoresX idx net exprs) :=
  Lok.flatMap _ (fun (p : Expr × Nat) => lok_exitOne idx net p.1 p.2) _

theorem lok_flush (r : Region) : Lok (emitRegionFlushX r) := by
  have s1 : Lok (if r.need > 0
      then [AInstr.cmpImm .x23 (32 * r.need), .bcLbl .hs "8f", .bTramp "_eita_stack_underflow", .label "8"] else []) :=
    Lok.ite (fun _ => lok_underflow _) (fun _ => Lok.nil)
  have s2 : Lok (if r.maxNet > 0
      then [AInstr.cmpImm .x23 (32 * (1025 - r.maxNet).toNat), .bcLbl .lo "9f", .bTramp "_eita_stack_overflow", .label "9"]
      else []) := Lok.ite (fun _ => lok_overflow _) (fun _ => Lok.nil)
  simp only [emitRegionFlushX, Evm.CL.ARM64.FlushMain.dagSlots_of, List.size_toArray, List.toList_toArray,
             List.append_assoc]
  split
  · exact Lok.nil
  · split
    · exact lok_tramp_under
    · split
      · exact s1.append lok_tramp_over
      · split
        · exact s1.append s2
        · refine s1.append (s2.append (Lok.append ?_ ((lok_depthUpdate _).append lok_cacheReload)))
          apply Lok.ite
          · intro _
            exact (lok_frameOpen _).append ((Lok.flatMap _ (lok_node _) _).append
              ((lok_memCommit _ _).append ((lok_exitStores _ _ _).append (lok_frameClose _))))
          · intro _; exact Lok.nil

theorem labelsOk_flush (r : Region) : LabelsOk (emitRegionFlushX r) :=
  LabelsOk_of_lokB _ ((lok_flush r).1 [] Five.nil)

/-! ## THE x86-64 bytes theorem -/

/-- The lowered x86-64 flush, run on the x86-64 machine from a state related
    to the ARM-level one, falls off its end in a state related to the one the
    flush theorem describes: stack, depth, cache, frame, memory, gas. -/
theorem flush_x86 (H : Helpers) (HX : XHelpers) (hS : H.Spec) (hfns : HX.fns = H) (hconv : H.conv = X86Sem.x86Conv)
    (hsym : ∀ h, HX.sym s!"Lsym_{h}" = h)
    (hjunk : ∀ h (s : RS) (x : XS) y, x.mem = s.mem → x.regs .rsp = s.sp → HX.junk h x y = H.junk h s y)
    (r : Region) (hW : Evm.CL.ARM64.FlushMain.RegionWF r) (s : RS) (x : XS) (hR : Rel Lend .unknown s x)
    (base : BitVec 64) (d : Nat) (es : List Evm.U256) (st mb : BitVec 64)
    (hL : LayX (frameOfX s.sp (Evm.CL.ARM64.FlushMain.slotsOf r).length base d es))
    (hM : Evm.CL.ARM64.MemCommitSem.MLay (frameOfX s.sp (Evm.CL.ARM64.FlushMain.slotsOf r).length base d es) st mb
      (Evm.CL.ARM64.MemCommitSem.capAt s.mem st).toNat)
    (h23 : s.regs .x23 = BitVec.ofNat 64 (32 * d)) (h24 : s.regs .x24 = base) (hes : es.length = d)
    (hstack : ∀ k < d, ld256 s.mem (Evm.CL.ARM64.FlushSem.stackAddr base d k) = es.getD k 0)
    (htos : 1 ≤ d → Evm.CL.ARM64.CoreSem.lhs s = es.getD 0 0)
    (h20 : s.regs .x20 = st) (hmb : Evm.CL.ARM64.MemCommitSem.mbAt s.mem st = mb)
    (hok : (Evm.CL.ARM64.MemCommitSem.msAt s.mem st).toNat ≤ (Evm.CL.ARM64.MemCommitSem.capAt s.mem st).toNat)
    (hcapOk : Evm.CL.ARM64.MemCommitSem.maxEndOf r.writes ≤ (Evm.CL.ARM64.MemCommitSem.capAt s.mem st).toNat)
    (hgasOk : Evm.CL.ARM64.FlushMain.memGas r s.mem st ≤ (s.regs .x22).toNat)
    (hneed : r.need ≤ d) (hover : r.maxNet > 0 → (d : Int) < 1025 - r.maxNet) :
    ∃ s' x', xrun HX (Evm.CL.X86JIT.lowerX (emitRegionFlushT Evm.CL.X86JIT.x86Flush r)) x = .done x' ∧
      Rel Lend .unknown s' x' ∧
      FlushOutX r base d es (frameOfX s.sp (Evm.CL.ARM64.FlushMain.slotsOf r).length base d es).fp
        (Evm.CL.ARM64.FlushMain.slotsOf r).length st mb s s' := by
  obtain ⟨s', hrun, hout⟩ := flush_runX_scaled H hS hconv r hW s base d es st mb [] hL hM h23 h24 hes hstack htos h20 hmb
    hok hcapOk hgasOk hneed hover
  rw [List.append_nil] at hrun
  have hrun' : AsmRun.run H (scaleP (emitRegionFlushT Evm.CL.X86JIT.x86Flush r)) s = .done s' := by
    rw [hrun]; simp
  have hsim := sim_run H HX (annOf tblF) Lend .unknown hfns hconv hsym hjunk _
    (scaleP (emitRegionFlushT Evm.CL.X86JIT.x86Flush r)) (Nat.le_refl _) Lend .unknown s x
    (by rw [scale_emitRegionFlush]; exact ok_flush r) (by rw [scale_emitRegionFlush]; exact labelsOk_flush r) hR
  rw [hrun'] at hsim
  obtain ⟨s'', x', h⟩ := hsim
  rcases h with ⟨⟨h1, h2⟩ | ⟨h1, _⟩, hRel⟩ | ⟨_, _, _, h1, _, _⟩
  · cases h1
    exact ⟨s', x', h2, hRel, hout⟩
  · cases h1
  · cases h1

end Evm.CL.X86.FlushOkX
