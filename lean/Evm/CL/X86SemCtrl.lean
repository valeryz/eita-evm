/-
  Evm.CL.X86SemCtrl — the control side of the lowering simulation: local
  labels correspond (`x86Items` produces an `.L` only from `.label`, and both
  machines resolve `Nf` to the next `N`), so skipping to a label on the ARM
  fragment and on its lowering land on corresponding suffixes.
-/

import Evm.CL.X86Sem

namespace Evm.CL.X86SemCtrl

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.AsmRun Evm.CL.X86Encode Evm.CL.X86Items Evm.CL.X86Sem

/-- Is an item a local label? -/
def isL : XItem → Bool
  | .L _ => true
  | _ => false

/-- `aluFrom`/`movFrom`/`cmpFrom` never produce a label. -/
theorem aluFrom_not_L (o : AluOp) (d : XReg) (src : Reg) : isL (aluFrom o d src) = false := by
  unfold aluFrom; split <;> rfl
theorem movFrom_not_L (d : XReg) (src : Reg) : isL (movFrom d src) = false := by
  unfold movFrom; split <;> rfl
theorem cmpFrom_not_L (a b : Reg) : isL (cmpFrom a b) = false := by
  unfold cmpFrom; split
  · exact aluFrom_not_L _ _ _
  · rfl
  · rfl

/-- The lowering of a non-label instruction has no label item. -/
theorem x86Items_no_L (i : AInstr) (hl : ∀ t, i ≠ .label t) : ∀ it ∈ x86Items i, isL it = false := by
  intro it hit
  cases i <;> simp only [x86Items] at hit <;> (try exact absurd rfl (hl _))
  all_goals
    repeat' (first
      | (split at hit)
      | (simp only [twoOp, shiftThenAdd, List.mem_cons, List.not_mem_nil, or_false,
                    List.cons_append, List.nil_append] at hit)
      | (rcases hit with rfl | hit)
      | (rcases hit with hit | hit))
  all_goals first
    | rfl
    | exact aluFrom_not_L _ _ _
    | exact movFrom_not_L _ _
    | exact cmpFrom_not_L _ _


/-- Is an item the `ret` instruction? -/
def isRetI : XItem → Bool
  | .I .ret => true
  | _ => false

theorem aluFrom_not_ret (o : AluOp) (d : XReg) (src : Reg) : isRetI (aluFrom o d src) = false := by
  unfold aluFrom; split <;> rfl
theorem movFrom_not_ret (d : XReg) (src : Reg) : isRetI (movFrom d src) = false := by
  unfold movFrom; split <;> rfl
theorem cmpFrom_not_ret (a b : Reg) : isRetI (cmpFrom a b) = false := by
  unfold cmpFrom; split
  · exact aluFrom_not_ret _ _ _
  · rfl
  · rfl

/-- Only `ret` and `brCont` lower to `ret`. -/
theorem x86Items_no_ret (i : AInstr) (h1 : i ≠ .ret) (h2 : i ≠ .brCont) : ∀ it ∈ x86Items i, isRetI it = false := by
  intro it hit
  cases i <;> simp only [x86Items] at hit <;> (try exact absurd rfl h1) <;> (try exact absurd rfl h2)
  all_goals
    repeat' (first
      | (split at hit)
      | (simp only [twoOp, shiftThenAdd, List.mem_cons, List.not_mem_nil, or_false,
                    List.cons_append, List.nil_append] at hit)
      | (rcases hit with rfl | hit)
      | (rcases hit with hit | hit))
  all_goals first
    | rfl
    | exact aluFrom_not_ret _ _ _
    | exact movFrom_not_ret _ _
    | exact cmpFrom_not_ret _ _

/-! ## Label correspondence -/

theorem xskipTo_append_noL (l : String) : ∀ (its r : List XItem), (∀ it ∈ its, isL it = false) →
    xskipTo l (its ++ r) = xskipTo l r
  | [], r, _ => rfl
  | it :: its, r, h => by
    have hit := h it (by simp)
    cases it <;> simp [isL] at hit <;> simp only [List.cons_append, xskipTo] <;>
      exact xskipTo_append_noL l its r (fun i hi => h i (by simp [hi]))

/-- `AsmRun.skipTo` and `xskipTo` agree on a fragment and its lowering. -/
theorem skipTo_progItems (l : String) : ∀ (rest : List AInstr),
    (AsmRun.skipTo l rest = [] → xskipTo l (progItems rest) = none) ∧
    (∀ t r', AsmRun.skipTo l rest = .label t :: r' → xskipTo l (progItems rest) = some (progItems (.label t :: r')))
  | [] => ⟨fun _ => rfl, fun t r' h => by simp [AsmRun.skipTo] at h⟩
  | i :: rest => by
    by_cases hlab : ∃ t, i = .label t
    · obtain ⟨t, rfl⟩ := hlab
      refine ⟨fun h => ?_, fun t' r' h => ?_⟩
      · simp only [AsmRun.skipTo] at h
        split at h
        · cases h
        · rename_i hc
          simp only [progItems, List.flatMap_cons, x86Items, List.singleton_append, xskipTo, hc]
          exact (skipTo_progItems l rest).1 h
      · simp only [AsmRun.skipTo] at h
        split at h
        · rename_i hc
          cases h
          simp only [progItems, List.flatMap_cons, x86Items, List.singleton_append, xskipTo, hc, ite_true]
        · rename_i hc
          simp only [progItems, List.flatMap_cons, x86Items, List.singleton_append, xskipTo, hc]
          exact (skipTo_progItems l rest).2 t' r' h
    · have hnl : ∀ t, i ≠ .label t := fun t e => hlab ⟨t, e⟩
      have hskip : AsmRun.skipTo l (i :: rest) = AsmRun.skipTo l rest := by
        cases i <;> first | rfl | exact absurd ⟨_, rfl⟩ hlab
      have hprog : progItems (i :: rest) = x86Items i ++ progItems rest := by simp [progItems]
      rw [hskip, hprog, xskipTo_append_noL l _ _ (x86Items_no_L i hnl)]
      exact skipTo_progItems l rest


/-! ## Fragments: an annotation, and the simulation of `run` by `xrun`

    An annotation gives every local label the live set and provenance code
    arriving there may assume. `Ok` threads the live set and provenance down
    the fall-through path, checking each branch against its target's
    annotation; `LabelsOk` says every local branch target is defined in the
    fragment (so neither machine falls off through a missing label). -/

/-- Provenance weakening: `unknown` is implied by anything. -/
def provLe (p q : Prov) : Prop := q = .unknown ∨ q = p

theorem FlagsRel.weaken {p q : Prov} {f : Flags} {xf : XFlags} (h : FlagsRel p f xf) (hq : provLe p q) :
    FlagsRel q f xf := by
  rcases hq with rfl | rfl
  · trivial
  · exact h

theorem relWeaken {L L' : List Reg} {p q : Prov} {s : RS} {x : XS} (hR : Rel L p s x)
    (hL : ∀ r ∈ L', r ∈ L) (hq : provLe p q) : Rel L' q s x :=
  ⟨fun r hr => hR.regs r (hL r hr), hR.sp, hR.mem, FlagsRel.weaken hR.flags hq⟩

/-- Which conditions the lowering gets right under a provenance (`X86Sem.cond_*`). -/
def condOkP (c : BCond) (p : Prov) : Prop :=
  p = .sub ∨ ((c = .eq ∨ c = .ne ∨ c = .lt) ∧ (p = .add ∨ p = .logic))

theorem cond_of_condOkP (c : BCond) (p : Prov) (f : Flags) (xf : XFlags) (h : FlagsRel p f xf) (hc : condOkP c p) :
    xcHolds (bcondXc c) xf = bcHolds c f := by
  rcases hc with rfl | ⟨hc, hp⟩
  · exact cond_sub c f xf h
  · rcases hp with rfl | rfl
    · rcases hc with rfl | rfl | rfl
      · exact (cond_add_eq f xf h).1
      · exact (cond_add_eq f xf h).2.1
      · exact (cond_add_eq f xf h).2.2
    · rcases hc with rfl | rfl | rfl
      · exact (cond_logic_eq f xf h).1
      · exact (cond_logic_eq f xf h).2.1
      · exact (cond_logic_eq f xf h).2.2

/-- A data instruction's simulation obligation: from any related pair with
    the entry annotation, both step, to a related pair with the exit one. -/
def DataSim (i : AInstr) (L : List Reg) (p : Prov) (L' : List Reg) (p' : Prov) : Prop :=
  ∀ s x, Rel L p s x → ∃ s' x', AsmRun.step s i = some s' ∧ xsteps x (x86Items i) = some x' ∧ Rel L' p' s' x'

/-- What arrives at label `t` is at least its annotation. -/
def At (ann : String → List Reg × Prov) (t : String) (L : List Reg) (p : Prov) : Prop :=
  (∀ r ∈ (ann t).1, r ∈ L) ∧ provLe p (ann t).2

/-- A branch to `l` lands on the first label `t` with `l = t` or `l = t ++ "f"`
    (the assembler's `Nf` rule); whichever it is, its annotation must hold. -/
def Target (ann : String → List Reg × Prov) (l : String) (L : List Reg) (p : Prov) : Prop :=
  ∀ t, (l == t || l == t ++ "f") = true → At ann t L p

/-- A register the compare-and-branch forms can read: homed or NOS. -/
def readable (r : Reg) : Prop := (xreg? r).isSome ∨ (nosLimb r).isSome

/-- Dead code: a live set naming the unhomed `x5` is unsatisfiable (`Rel` needs
    a value for every live register), so what follows an unconditional transfer
    is annotated with `deadL` and the label that revives it skips the `At` check. -/
def deadL : List Reg := [.x5]
def Dead (L : List Reg) : Prop := Reg.x5 ∈ L

theorem rel_not_dead {L : List Reg} {p : Prov} {s : RS} {x : XS} (hR : Rel L p s x) (hd : Dead L) : False := by
  have := hR.regs .x5 hd
  simp [valOf, xreg?, nosLimb] at this

/-- The annotated-fragment predicate. `Lend`/`pend`: what holds at `[]` and `ret`. -/
def Ok (ann : String → List Reg × Prov) (Lend : List Reg) (pend : Prov) :
    List AInstr → List Reg → Prov → Prop
  | [], L, p => Dead L ∨ ((∀ r ∈ Lend, r ∈ L) ∧ provLe p pend)
  | .ret :: rest, L, p => (Dead L ∨ ((∀ r ∈ Lend, r ∈ L) ∧ provLe p pend)) ∧ Ok ann Lend pend rest deadL .unknown
  | .label t :: rest, L, p => (Dead L ∨ At ann t L p) ∧ Ok ann Lend pend rest (ann t).1 (ann t).2
  | .bLbl l :: rest, L, p => Target ann l L p ∧ Ok ann Lend pend rest deadL .unknown
  | .bcLbl c l :: rest, L, p => condOkP c p ∧ Target ann l L p ∧ Ok ann Lend pend rest L p
  | .blsLbl l :: rest, L, p => p = .sub ∧ Target ann l L p ∧ Ok ann Lend pend rest L p
  | .cbzLbl r l :: rest, L, _ => r ∈ L ∧ readable r ∧ Target ann l L .unknown ∧ Ok ann Lend pend rest L .unknown
  | .cbnzLbl r l :: rest, L, _ => r ∈ L ∧ (xreg? r).isSome ∧ Target ann l L .unknown ∧ Ok ann Lend pend rest L .unknown
  | .cbzWLbl r l :: rest, L, _ => r ∈ L ∧ (xreg? r).isSome ∧ Target ann l L .unknown ∧ Ok ann Lend pend rest L .unknown
  | .cbnzWLbl r l :: rest, L, _ => r ∈ L ∧ (xreg? r).isSome ∧ Target ann l L .unknown ∧ Ok ann Lend pend rest L .unknown
  | .blSym sym :: rest, L, _ =>
      Reg.x3 ∈ L ∧ Reg.x2 ∈ L ∧ Reg.x1 ∈ L ∧ (ternary sym = true → Reg.x14 ∈ L) ∧
        Ok ann Lend pend rest (killCall L) .unknown
  | .bTramp _ :: rest, _, _ => Ok ann Lend pend rest deadL .unknown
  | .bcTramp c _ :: rest, L, p => condOkP c p ∧ Ok ann Lend pend rest L p
  | i :: rest, L, p =>
      AsmRun.ctrl i = none ∧ i ≠ .brCont ∧ ∃ L' p', DataSim i L p L' p' ∧ Ok ann Lend pend rest L' p'

theorem endRel {L : List Reg} {p : Prov} {s : RS} {x : XS} (Lend : List Reg) (pend : Prov) (hR : Rel L p s x)
    (h : Dead L ∨ ((∀ r ∈ Lend, r ∈ L) ∧ provLe p pend)) : Rel Lend pend s x := by
  rcases h with hd | ⟨h1, h2⟩
  · exact absurd hd (rel_not_dead hR)
  · exact relWeaken hR h1 h2

theorem atRel {L : List Reg} {p : Prov} {s : RS} {x : XS} (ann : String → List Reg × Prov) (t : String)
    (hR : Rel L p s x) (h : Dead L ∨ At ann t L p) : Rel (ann t).1 (ann t).2 s x := by
  rcases h with hd | ⟨h1, h2⟩
  · exact absurd hd (rel_not_dead hR)
  · exact relWeaken hR h1 h2

/-- Every local branch target is defined (within the fragment, after the branch). -/
def LabelsOk : List AInstr → Prop
  | [] => True
  | i :: rest =>
      (match i with
       | .bLbl l | .bcLbl _ l | .blsLbl l | .cbzLbl _ l | .cbnzLbl _ l | .cbzWLbl _ l | .cbnzWLbl _ l =>
           AsmRun.skipTo l rest ≠ []
       -- a trampoline label is never defined inside a fragment
       | .bTramp sym | .bcTramp _ sym => AsmRun.skipTo (trampLabel sym) rest = []
       | _ => True) ∧ LabelsOk rest

/-- `skipTo` is a suffix. -/
theorem skipTo_eq_drop (l : String) : ∀ (rest : List AInstr), ∃ k, AsmRun.skipTo l rest = rest.drop k
  | [] => ⟨0, rfl⟩
  | i :: rest => by
    cases i <;> simp only [AsmRun.skipTo]
    all_goals first
      | (split
         · exact ⟨0, rfl⟩
         · obtain ⟨k, hk⟩ := skipTo_eq_drop l rest; exact ⟨k + 1, by simp [hk]⟩)
      | (obtain ⟨k, hk⟩ := skipTo_eq_drop l rest; exact ⟨k + 1, by simp [hk]⟩)

theorem LabelsOk_drop : ∀ (prog : List AInstr) (k : Nat), LabelsOk prog → LabelsOk (prog.drop k)
  | _, 0, h => h
  | [], _ + 1, _ => trivial
  | _ :: rest, k + 1, h => LabelsOk_drop rest k h.2

theorem Ok_drop (ann : String → List Reg × Prov) (Lend : List Reg) (pend : Prov) :
    ∀ (prog : List AInstr) (k : Nat) (L : List Reg) (p : Prov), Ok ann Lend pend prog L p →
      ∃ L' p', Ok ann Lend pend (prog.drop k) L' p'
  | prog, 0, L, p, h => ⟨L, p, h⟩
  | [], _ + 1, L, p, h => ⟨L, p, h⟩
  | i :: rest, k + 1, L, p, h => by
    simp only [List.drop_succ_cons]
    cases i with
    | ret => exact Ok_drop ann Lend pend rest k _ _ h.2
    | label t => exact Ok_drop ann Lend pend rest k _ _ h.2
    | bLbl l => exact Ok_drop ann Lend pend rest k _ _ h.2
    | bcLbl c l => exact Ok_drop ann Lend pend rest k _ _ h.2.2
    | blsLbl l => exact Ok_drop ann Lend pend rest k _ _ h.2.2
    | cbzLbl r l => exact Ok_drop ann Lend pend rest k _ _ h.2.2.2
    | cbnzLbl r l => exact Ok_drop ann Lend pend rest k _ _ h.2.2.2
    | cbzWLbl r l => exact Ok_drop ann Lend pend rest k _ _ h.2.2.2
    | cbnzWLbl r l => exact Ok_drop ann Lend pend rest k _ _ h.2.2.2
    | blSym _ => exact Ok_drop ann Lend pend rest k _ _ h.2.2.2.2
    | bTramp _ => exact Ok_drop ann Lend pend rest k _ _ h
    | bcTramp _ _ => exact Ok_drop ann Lend pend rest k _ _ h.2
    | _ =>
      obtain ⟨_, _, L', p', _, hrest⟩ := h
      exact Ok_drop ann Lend pend rest k L' p' hrest


theorem nosLimb_none_of_home (r : Reg) (xr : XReg) (h : xreg? r = some xr) : nosLimb r = none := by
  cases r <;> simp_all [nosLimb, xreg?]

/-- A non-empty `skipTo` result starts with the label it found. -/
theorem skipTo_found (l : String) : ∀ (rest : List AInstr), AsmRun.skipTo l rest ≠ [] →
    ∃ t r', AsmRun.skipTo l rest = .label t :: r' ∧ (l == t || l == t ++ "f") = true
  | [], h => absurd rfl h
  | i :: rest, h => by
    cases i <;> simp only [AsmRun.skipTo] at h ⊢
    all_goals first
      | exact skipTo_found l rest h
      | (split at h
         · rename_i hc; exact ⟨_, _, by rw [if_pos hc], hc⟩
         · rename_i hc
           obtain ⟨t, r', h1, h2⟩ := skipTo_found l rest h
           exact ⟨t, r', by rw [if_neg hc]; exact h1, h2⟩)

/-! ### `run` on the control forms -/

theorem arun_ret (H : Helpers) (rest : List AInstr) (s : RS) : AsmRun.run H (.ret :: rest) s = .ret s := by
  simp [AsmRun.run, AsmRun.ctrl]
theorem arun_bLbl (H : Helpers) (l : String) (rest : List AInstr) (s : RS) :
    AsmRun.run H (.bLbl l :: rest) s = AsmRun.run H (AsmRun.skipTo l rest) s := by simp [AsmRun.run, AsmRun.ctrl]
theorem arun_blsLbl (H : Helpers) (l : String) (rest : List AInstr) (s : RS) :
    AsmRun.run H (.blsLbl l :: rest) s =
      if bcHolds .ls s.flags then AsmRun.run H (AsmRun.skipTo l rest) s else AsmRun.run H rest s := by
  simp [AsmRun.run, AsmRun.ctrl]
theorem arun_cbzLbl (H : Helpers) (r : Reg) (l : String) (rest : List AInstr) (s : RS) :
    AsmRun.run H (.cbzLbl r l :: rest) s =
      if s.regs r = 0 then AsmRun.run H (AsmRun.skipTo l rest) s else AsmRun.run H rest s := by
  simp [AsmRun.run, AsmRun.ctrl]
theorem arun_cbnzLbl (H : Helpers) (r : Reg) (l : String) (rest : List AInstr) (s : RS) :
    AsmRun.run H (.cbnzLbl r l :: rest) s =
      if s.regs r = 0 then AsmRun.run H rest s else AsmRun.run H (AsmRun.skipTo l rest) s := by
  simp [AsmRun.run, AsmRun.ctrl]
theorem arun_cbzWLbl (H : Helpers) (r : Reg) (l : String) (rest : List AInstr) (s : RS) :
    AsmRun.run H (.cbzWLbl r l :: rest) s =
      if s.regs r &&& 0xffffffff = 0 then AsmRun.run H (AsmRun.skipTo l rest) s else AsmRun.run H rest s := by
  simp [AsmRun.run, AsmRun.ctrl]
theorem arun_cbnzWLbl (H : Helpers) (r : Reg) (l : String) (rest : List AInstr) (s : RS) :
    AsmRun.run H (.cbnzWLbl r l :: rest) s =
      if s.regs r &&& 0xffffffff = 0 then AsmRun.run H rest s else AsmRun.run H (AsmRun.skipTo l rest) s := by
  simp [AsmRun.run, AsmRun.ctrl]

theorem arun_blSym (H : Helpers) (h : String) (rest : List AInstr) (s : RS) :
    AsmRun.run H (.blSym h :: rest) s = AsmRun.run H rest (callHelper H h s) := by simp [AsmRun.run, AsmRun.ctrl]
theorem arun_bTramp (H : Helpers) (sym : String) (rest : List AInstr) (s : RS) :
    AsmRun.run H (.bTramp sym :: rest) s = .fault sym s := by simp [AsmRun.run, AsmRun.ctrl]
theorem arun_bcTramp (H : Helpers) (c : BCond) (sym : String) (rest : List AInstr) (s : RS) :
    AsmRun.run H (.bcTramp c sym :: rest) s = if bcHolds c s.flags then .fault sym s else AsmRun.run H rest s := by
  simp [AsmRun.run, AsmRun.ctrl]

/-- The 32-bit zero test is the masked test. -/
theorem low32_zero (v : BitVec 64) : ((v.extractLsb' 0 32).zeroExtend 64 = 0) ↔ (v &&& 0xffffffff = 0) := by
  constructor <;> intro h <;> bv_decide
theorem low32_zero' (v : BitVec 64) : (BitVec.setWidth 64 (v.extractLsb' 0 32) = 0) ↔ (v &&& 0xffffffff = 0) := by
  constructor <;> intro h <;> bv_decide

theorem progItems_cons (i : AInstr) (rest : List AInstr) : progItems (i :: rest) = x86Items i ++ progItems rest := by
  simp [progItems]

/-- `cmp r32, 0`'s ZF is the masked zero test. -/
theorem cmpRI32_zero (v : BitVec 64) :
    (subXF ((v.extractLsb' 0 32).zeroExtend 64) (BitVec.ofInt 64 0)).zf = decide (v &&& 0xffffffff = 0) := by
  simp only [subXF, ofInt_zero]
  bv_decide

/-- `Ok` on a data instruction (one `ctrl` does not classify). -/
theorem Ok_cons_data (ann : String → List Reg × Prov) (Lend : List Reg) (pend : Prov) (i : AInstr)
    (rest : List AInstr) (L : List Reg) (p : Prov) (hc : AsmRun.ctrl i = none) :
    Ok ann Lend pend (i :: rest) L p ↔
      (i ≠ .brCont ∧ ∃ L' p', DataSim i L p L' p' ∧ Ok ann Lend pend rest L' p') := by
  cases i <;> first
    | exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hc, h.1, h.2⟩⟩
    | (simp [AsmRun.ctrl] at hc)

/-! ### THE control theorem -/

/-- The outcome correspondence: both fall off or both `ret`, related at the
    exit annotation; or both leave for the same far symbol (ARM `fault`, x86
    `exit` through the trampoline), related at that point. -/
def OutRel (Lend : List Reg) (pend : Prov) (o : Outcome) (xo : XOutcome) : Prop :=
  ∃ s' x', ((o = .done s' ∧ xo = .done x') ∨ (o = .ret s' ∧ xo = .ret x')) ∧ Rel Lend pend s' x' ∨
    ∃ sym L' p', o = .fault sym s' ∧ xo = .exit (trampLabel sym) x' ∧ Rel L' p' s' x'

theorem sim_run (H : Helpers) (HX : XHelpers) (ann : String → List Reg × Prov) (Lend : List Reg) (pend : Prov)
    (hfns : HX.fns = H) (hconv : H.conv = x86Conv) (hsym : ∀ h, HX.sym s!"Lsym_{h}" = h)
    (hjunk : ∀ h (s : RS) (x : XS) y, x.mem = s.mem → x.regs .rsp = s.sp → HX.junk h x y = H.junk h s y) :
    ∀ (n : Nat) (prog : List AInstr), prog.length ≤ n → ∀ (L : List Reg) (p : Prov) (s : RS) (x : XS),
      Ok ann Lend pend prog L p → LabelsOk prog → Rel L p s x →
      OutRel Lend pend (AsmRun.run H prog s) (xrun HX (progItems prog) x) := by
  intro n
  induction n with
  | zero =>
    intro prog hlen L p s x hOk _ hR
    have : prog = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact ⟨s, x, Or.inl ⟨Or.inl ⟨by simp, by simp [progItems]⟩, endRel Lend pend hR hOk⟩⟩
  | succ n ih =>
    intro prog hlen L p s x hOk hLab hR
    -- the jump case, shared by every branch form
    have jump : ∀ (l : String) (rest : List AInstr) (L0 : List Reg) (p0 : Prov) (L1 : List Reg) (p1 : Prov)
        (s0 : RS) (x0 : XS),
        rest.length ≤ n → AsmRun.skipTo l rest ≠ [] → Target ann l L0 p0 → Ok ann Lend pend rest L1 p1 →
        LabelsOk rest → Rel L0 p0 s0 x0 →
        ∃ r', AsmRun.skipTo l rest = r' ∧ xskipTo l (progItems rest) = some (progItems r') ∧
          OutRel Lend pend (AsmRun.run H r' s0) (xrun HX (progItems r') x0) := by
      intro l rest L0 p0 L1 p1 s0 x0 hlen hne hT hOkr hLr hR0
      obtain ⟨t, r', hfound, hmatch⟩ := skipTo_found l rest hne
      obtain ⟨k, hk⟩ := skipTo_eq_drop l rest
      obtain ⟨L', p', hOk'⟩ := Ok_drop ann Lend pend rest k L1 p1 hOkr
      rw [← hk, hfound] at hOk'
      have hLab' : LabelsOk (.label t :: r') := by rw [← hfound, hk]; exact LabelsOk_drop rest k hLr
      have hlen' : (AInstr.label t :: r').length ≤ n := by
        have := AsmRun.skipTo_length_le l rest; rw [hfound] at this; omega
      refine ⟨.label t :: r', hfound, (skipTo_progItems l rest).2 t r' hfound, ?_⟩
      exact ih _ hlen' L0 p0 s0 x0 ⟨Or.inr (hT t hmatch), hOk'.2⟩ hLab' hR0
    cases prog with
    | nil =>
      exact ⟨s, x, Or.inl ⟨Or.inl ⟨by simp, by simp [progItems]⟩, endRel Lend pend hR hOk⟩⟩
    | cons i rest =>
      have hlenr : rest.length ≤ n := by simp at hlen; omega
      by_cases hc : AsmRun.ctrl i = none
      · -- a data instruction
        obtain ⟨hbr, L', p', hD, hOkr⟩ := (Ok_cons_data ann Lend pend i rest L p hc).mp hOk
        obtain ⟨s', x', hs', hx', hR'⟩ := hD s x hR
        rw [AsmRun.run_cons_step H _ _ _ _ hc hs', progItems_cons,
            xrun_xsteps HX _ _ _ _ (fun it hit j hj => by
              have := x86Items_no_ret i (by intro e; subst e; cases hc) hbr it hit
              subst hj; intro e; subst e; simp [isRetI] at this) hx']
        exact ih rest hlenr L' p' s' x' hOkr hLab.2 hR'
      · cases i with
        | ret =>
          exact ⟨s, x, Or.inl ⟨Or.inr ⟨arun_ret H rest s, by simp [progItems, x86Items, xrun_cons_ret]⟩,
                              endRel Lend pend hR hOk.1⟩⟩
        | blSym h =>
          obtain ⟨h3, h2, h1, h14, hOkr⟩ := hOk
          rw [arun_blSym, progItems_cons, x86Items, List.singleton_append, xrun_cons_CallRip]
          have hR' := sim_blSym L p s x hR H HX h _ hfns hconv (hsym h) h3 h2 h1 h14
            (fun y => hjunk h s x y hR.mem hR.sp)
          exact ih rest hlenr _ _ _ _ hOkr hLab.2 hR'
        | bTramp sym =>
          rw [arun_bTramp, progItems_cons, x86Items, List.singleton_append,
              xrun_cons_Jmp_exit _ _ _ _ ((skipTo_progItems _ rest).1 hLab.1)]
          exact ⟨s, x, Or.inr ⟨sym, L, p, rfl, rfl, hR⟩⟩
        | bcTramp c sym =>
          obtain ⟨hc, hOkr⟩ := hOk
          have hcond := cond_of_condOkP c p s.flags x.flags hR.flags hc
          rw [arun_bcTramp, progItems_cons, x86Items, List.singleton_append]
          by_cases hb : bcHolds c s.flags = true
          · rw [if_pos hb, xrun_cons_Jcc_exit _ _ _ _ _ (by rw [hcond, hb]) ((skipTo_progItems _ rest).1 hLab.1)]
            exact ⟨s, x, Or.inr ⟨sym, L, p, rfl, rfl, hR⟩⟩
          · rw [if_neg hb, xrun_cons_Jcc_not _ _ _ _ _ (by rw [hcond]; simpa using hb)]
            exact ih rest hlenr L p s x hOkr hLab.2 hR
        | label t =>
          rw [AsmRun.run_cons_label, progItems_cons, x86Items, List.singleton_append, xrun_cons_L]
          exact ih rest hlenr _ _ s x hOk.2 hLab.2 (atRel ann t hR hOk.1)
        | bLbl l =>
          obtain ⟨r', hr', hskip, hout⟩ := jump l rest L p deadL .unknown s x hlenr hLab.1 hOk.1 hOk.2 hLab.2 hR
          rw [arun_bLbl, progItems_cons, x86Items, List.singleton_append, xrun_cons_Jmp_skip _ _ _ _ _ hskip, hr']
          exact hout
        | bcLbl c l =>
          obtain ⟨hc, hT, hOkr⟩ := hOk
          have hcond := cond_of_condOkP c p s.flags x.flags hR.flags hc
          rw [AsmRun.run_cons_bcLbl, progItems_cons, x86Items, List.singleton_append]
          by_cases hb : bcHolds c s.flags = true
          · obtain ⟨r', hr', hskip, hout⟩ := jump l rest L p L p s x hlenr hLab.1 hT hOkr hLab.2 hR
            rw [if_pos hb, xrun_cons_Jcc_skip _ _ _ _ _ _ (by rw [hcond, hb]) hskip, hr']
            exact hout
          · rw [if_neg hb, xrun_cons_Jcc_not _ _ _ _ _ (by rw [hcond]; simpa using hb)]
            exact ih rest hlenr L p s x hOkr hLab.2 hR
        | blsLbl l =>
          obtain ⟨hp, hT, hOkr⟩ := hOk
          subst hp
          have hcond : xcHolds .be x.flags = bcHolds .ls s.flags := cond_sub .ls s.flags x.flags hR.flags
          rw [arun_blsLbl, progItems_cons, x86Items, List.singleton_append]
          by_cases hb : bcHolds .ls s.flags = true
          · obtain ⟨r', hr', hskip, hout⟩ := jump l rest L .sub L .sub s x hlenr hLab.1 hT hOkr hLab.2 hR
            rw [if_pos hb, xrun_cons_Jcc_skip _ _ _ _ _ _ (by rw [hcond, hb]) hskip, hr']
            exact hout
          · rw [if_neg hb, xrun_cons_Jcc_not _ _ _ _ _ (by rw [hcond]; simpa using hb)]
            exact ih rest hlenr L .sub s x hOkr hLab.2 hR
        | cbzLbl r l =>
          obtain ⟨hrL, hread, hT, hOkr⟩ := hOk
          rw [arun_cbzLbl, progItems_cons]
          obtain ⟨x1, hx1, hR1, hcond⟩ : ∃ x1, xrun HX (x86Items (.cbzLbl r l) ++ progItems rest) x =
              xrun HX (.Jcc .e l :: progItems rest) x1 ∧ Rel L .unknown s x1 ∧
              (xcHolds .e x1.flags = decide (s.regs r = 0)) := by
            rcases hread with hh | hh
            · obtain ⟨xr, hxr⟩ := Option.isSome_iff_exists.mp hh
              have hv := hR.val r hrL xr hxr
              have hn : nosLimb r = none := nosLimb_none_of_home r xr hxr
              simp only [x86Items, hn, dst, hxr, Option.getD_some, List.cons_append, List.nil_append]
              have hstep : xstep x (.aluRI .cmp xr 0) = some (x.withFlags (subXF (x.regs xr) (BitVec.ofInt 64 0))) := by
                simp [xstep, aluR, alu]
              refine ⟨_, xrun_cons_I HX _ (by intro h; cases h) _ _ _ hstep, hR.forget _, ?_⟩
              simp [xcHolds, subXF, hv]
            · obtain ⟨lm, hlm⟩ := Option.isSome_iff_exists.mp hh
              have hv := hR.valNos r hrL lm hlm
              simp only [x86Items, hlm, List.cons_append, List.nil_append]
              have hstep : xstep x (.aluMI .cmp (nosMemX lm) 0) =
                  some (x.withFlags (subXF (ld64 x.mem (ea x (nosMemX lm))) (BitVec.ofInt 64 0))) := by
                simp [xstep, alu]
              refine ⟨_, xrun_cons_I HX _ (by intro h; cases h) _ _ _ hstep, hR.forget _, ?_⟩
              simp [xcHolds, subXF, hv]
          rw [hx1]
          by_cases hb : s.regs r = 0
          · obtain ⟨r', hr', hskip, hout⟩ := jump l rest L .unknown L .unknown s x1 hlenr hLab.1 hT hOkr hLab.2 hR1
            rw [if_pos hb, xrun_cons_Jcc_skip _ _ _ _ _ _ (by rw [hcond]; exact decide_eq_true hb) hskip, hr']
            exact hout
          · rw [if_neg hb, xrun_cons_Jcc_not _ _ _ _ _ (by rw [hcond]; exact decide_eq_false hb)]
            exact ih rest hlenr L .unknown s x1 hOkr hLab.2 hR1
        | cbnzLbl r l =>
          obtain ⟨hrL, hh, hT, hOkr⟩ := hOk
          obtain ⟨xr, hxr⟩ := Option.isSome_iff_exists.mp hh
          have hv := hR.val r hrL xr hxr
          rw [arun_cbnzLbl, progItems_cons]
          simp only [x86Items, dst, hxr, Option.getD_some, List.cons_append, List.nil_append]
          have hstep : xstep x (.aluRI .cmp xr 0) = some (x.withFlags (subXF (x.regs xr) (BitVec.ofInt 64 0))) := by
            simp [xstep, aluR, alu]
          rw [xrun_cons_I HX _ (by intro h; cases h) _ _ _ hstep]
          have hR1 := hR.forget (subXF (x.regs xr) (BitVec.ofInt 64 0))
          have hcond : xcHolds .ne (x.withFlags (subXF (x.regs xr) (BitVec.ofInt 64 0))).flags =
              decide (s.regs r ≠ 0) := by
            simp [xcHolds, subXF, hv]
          by_cases hb : s.regs r = 0
          · rw [if_pos hb, xrun_cons_Jcc_not _ _ _ _ _ (by rw [hcond]; exact decide_eq_false (fun h => h hb))]
            exact ih rest hlenr L .unknown s _ hOkr hLab.2 hR1
          · obtain ⟨r', hr', hskip, hout⟩ := jump l rest L .unknown L .unknown s _ hlenr hLab.1 hT hOkr hLab.2 hR1
            rw [if_neg hb, xrun_cons_Jcc_skip _ _ _ _ _ _ (by rw [hcond]; exact decide_eq_true hb) hskip, hr']
            exact hout
        | cbzWLbl r l =>
          obtain ⟨hrL, hh, hT, hOkr⟩ := hOk
          obtain ⟨xr, hxr⟩ := Option.isSome_iff_exists.mp hh
          have hv := hR.val r hrL xr hxr
          rw [arun_cbzWLbl, progItems_cons]
          simp only [x86Items, dst, hxr, Option.getD_some, List.cons_append, List.nil_append]
          have hstep : xstep x (.cmpRI32 xr 0) =
              some (x.withFlags (subXF ((x.regs xr).extractLsb' 0 32 |>.zeroExtend 64) (BitVec.ofInt 64 0))) := rfl
          rw [xrun_cons_I HX _ (by intro h; cases h) _ _ _ hstep]
          have hR1 := hR.forget (subXF ((x.regs xr).extractLsb' 0 32 |>.zeroExtend 64) (BitVec.ofInt 64 0))
          have hcond : xcHolds .e (x.withFlags (subXF ((x.regs xr).extractLsb' 0 32 |>.zeroExtend 64)
              (BitVec.ofInt 64 0))).flags = decide (s.regs r &&& 0xffffffff = 0) := by
            simp only [xcHolds, XS.withFlags_flags, hv, cmpRI32_zero]
          by_cases hb : s.regs r &&& 0xffffffff = 0
          · obtain ⟨r', hr', hskip, hout⟩ := jump l rest L .unknown L .unknown s _ hlenr hLab.1 hT hOkr hLab.2 hR1
            rw [if_pos hb, xrun_cons_Jcc_skip _ _ _ _ _ _ (by rw [hcond]; exact decide_eq_true hb) hskip, hr']
            exact hout
          · rw [if_neg hb, xrun_cons_Jcc_not _ _ _ _ _ (by rw [hcond]; exact decide_eq_false hb)]
            exact ih rest hlenr L .unknown s _ hOkr hLab.2 hR1
        | cbnzWLbl r l =>
          obtain ⟨hrL, hh, hT, hOkr⟩ := hOk
          obtain ⟨xr, hxr⟩ := Option.isSome_iff_exists.mp hh
          have hv := hR.val r hrL xr hxr
          rw [arun_cbnzWLbl, progItems_cons]
          simp only [x86Items, dst, hxr, Option.getD_some, List.cons_append, List.nil_append]
          have hstep : xstep x (.cmpRI32 xr 0) =
              some (x.withFlags (subXF ((x.regs xr).extractLsb' 0 32 |>.zeroExtend 64) (BitVec.ofInt 64 0))) := rfl
          rw [xrun_cons_I HX _ (by intro h; cases h) _ _ _ hstep]
          have hR1 := hR.forget (subXF ((x.regs xr).extractLsb' 0 32 |>.zeroExtend 64) (BitVec.ofInt 64 0))
          have hcond : xcHolds .ne (x.withFlags (subXF ((x.regs xr).extractLsb' 0 32 |>.zeroExtend 64)
              (BitVec.ofInt 64 0))).flags = decide (s.regs r &&& 0xffffffff ≠ 0) := by
            simp only [xcHolds, XS.withFlags_flags, hv, cmpRI32_zero, decide_not]
          by_cases hb : s.regs r &&& 0xffffffff = 0
          · rw [if_pos hb, xrun_cons_Jcc_not _ _ _ _ _ (by rw [hcond]; exact decide_eq_false (fun h => h hb))]
            exact ih rest hlenr L .unknown s _ hOkr hLab.2 hR1
          · obtain ⟨r', hr', hskip, hout⟩ := jump l rest L .unknown L .unknown s _ hlenr hLab.1 hT hOkr hLab.2 hR1
            rw [if_neg hb, xrun_cons_Jcc_skip _ _ _ _ _ _ (by rw [hcond]; exact decide_eq_true hb) hskip, hr']
            exact hout


        | _ => first | exact absurd rfl hc | exact absurd hOk.1 (by simp [AsmRun.ctrl])
end Evm.CL.X86SemCtrl
