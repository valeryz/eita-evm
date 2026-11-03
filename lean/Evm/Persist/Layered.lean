import Evm.Persist.Recovery

/-! # Evm/Persist/Layered — layered snapshots: a base and a stack of delta layers

`docs/layered-snapshots.md`. The replay's persisted state is a BASE snapshot (`snap-B/`,
the flat state, `docs/state-snapshot-format.md`) under an ordered stack of immutable DELTA
LAYERS (`layer-P-N/`: the accounts and slots the replay touched in blocks `P+1..N`). An
anchor freezes the hot set into a layer instead of merging it into a new full snapshot;
a background compaction folds old layers into a new base. This file states and proves
what the Lisp relies on:

* Part A — the delta algebra. Lookup through the stack (newest layer first, a slot
  stops at the first layer that sets it or wipes its account) is lookup in the merged
  state (`lookupAcct_eq`, `lookupSlot_eq`). Composition is apply-then-apply
  (`apply_compose`), so composing a run of layers into one (minor compaction) leaves the
  view unchanged (`applyAll_composeAll`).
* Part B — materialization. A base snapshot does not hold raw RAM state: the writer's
  inclusion rule S1 drops empty accounts without storage or existence mark and rewrites
  the existence flag (`mat`). Reading a layered view materializes the merged raw state;
  a compacted base is materialized at the compaction block. The two agree because every
  layer carries the account fields of every address whose storage it touches
  (`FieldsCover`, the writer enforces it): `mat_apply_mat`, hence compaction preserves
  the view (`compact_view`).
* Part C — the replay. If each layer turns the canonical state at its parent block into
  the canonical state at its own block (`LayerOK`: the writer's contract), a base at `b₀`
  plus layers to `bₖ` reads as the canonical state at `bₖ` (`stack_view`); dropping the
  newest layers (a reorg rollback) reads as the canonical state at the new top
  (`rollback_view`); a resume from any sealed layer starts from the canonical state there.
* Part D — recovery over layered files. A resume point is a COMPOSITION (a base and the
  layers above it, recorded in its anchor line); the point is usable when every component
  file is sealed. `Recovery.resumePoint` and `gcSet` are reused over the points; GC deletes
  a file only when no kept point names it, and — whatever part of that set it deletes (the
  replay pins its live stack) — leaves the resume point where it was
  (`gcSubset_preserves_resume`, `gcFiles_preserves_resume`).

What is assumed, not proved: that the Lisp writer implements `apply`/`compose`/`mat`
(`LayerOK`, `CompactOK` are hypotheses, checked on the implementation by
`tests/layers.lisp` and the replay gates), keccak collision resistance (a matching
root means a matching state), and that the replay is a function of the blocks (a reorg
re-executes the same code). No `sorry`. -/

namespace Evm.Persist.Layered

/-! ## Part A — the delta algebra -/

section Algebra

variable {A S F : Type}

/-- A state: account fields (`none`: no account) and storage (`0`: no slot). -/
structure State (A S F : Type) where
  acct : A → Option F
  slot : A → S → Nat

/-- A delta layer: per address, the account fields it sets (`some none`: deleted), whether
    it wiped the address's storage, and the slots it sets (`some 0`: a tombstone). The
    Lisp layer file holds one account record (fields, WIPED bit) per address it mentions
    and its slot records, zeros included. -/
structure Delta (A S F : Type) where
  acct  : A → Option (Option F)
  wiped : A → Bool
  slot  : A → S → Option Nat

theorem State.ext' {s t : State A S F} (ha : ∀ a, s.acct a = t.acct a)
    (hs : ∀ a k, s.slot a k = t.slot a k) : s = t := by
  cases s; cases t
  simp only [State.mk.injEq]
  exact ⟨funext ha, funext fun a => funext (hs a)⟩

/-- The state after a layer. -/
def apply (d : Delta A S F) (s : State A S F) : State A S F where
  acct a := (d.acct a).getD (s.acct a)
  slot a k := match d.slot a k with
    | some v => v
    | none => if d.wiped a then 0 else s.slot a k

/-- One layer for two (`d₁` older): what minor compaction writes. -/
def compose (d₁ d₂ : Delta A S F) : Delta A S F where
  acct a := match d₂.acct a with
    | some x => some x
    | none => d₁.acct a
  wiped a := d₁.wiped a || d₂.wiped a
  slot a k := match d₂.slot a k with
    | some v => some v
    | none => if d₂.wiped a then none else d₁.slot a k

theorem apply_compose (d₁ d₂ : Delta A S F) (s : State A S F) :
    apply (compose d₁ d₂) s = apply d₂ (apply d₁ s) := by
  apply State.ext'
  · intro a; simp only [apply, compose]; cases d₂.acct a <;> simp
  · intro a k
    simp only [apply, compose]
    cases h2 : d₂.slot a k with
    | some v => rfl
    | none =>
      by_cases hw2 : d₂.wiped a = true
      · simp [hw2]
      · cases d₁.slot a k <;> simp [hw2]

/-- The identity layer (nothing touched). -/
def Delta.empty : Delta A S F := ⟨fun _ => none, fun _ => false, fun _ _ => none⟩

theorem apply_empty (s : State A S F) : apply Delta.empty s = s := by
  apply State.ext' <;> intros <;> rfl

/-- A stack, NEWEST FIRST, applied to a base. -/
def applyAll : List (Delta A S F) → State A S F → State A S F
  | [], s => s
  | d :: ds, s => apply d (applyAll ds s)

/-- A run of layers (newest first) composed into one. -/
def composeAll : List (Delta A S F) → Delta A S F
  | [] => Delta.empty
  | d :: ds => compose (composeAll ds) d

theorem applyAll_composeAll (ds : List (Delta A S F)) (s : State A S F) :
    apply (composeAll ds) s = applyAll ds s := by
  induction ds with
  | nil => exact apply_empty s
  | cons d ds ih => simp only [composeAll, applyAll, apply_compose, ih]

theorem applyAll_append (hi lo : List (Delta A S F)) (s : State A S F) :
    applyAll (hi ++ lo) s = applyAll hi (applyAll lo s) := by
  induction hi with
  | nil => rfl
  | cons d ds ih => simp only [List.cons_append, applyAll, ih]

/-- Minor compaction: a contiguous run of layers replaced by its composition. -/
theorem compose_run_view (hi run lo : List (Delta A S F)) (s : State A S F) :
    applyAll (hi ++ composeAll run :: lo) s = applyAll (hi ++ run ++ lo) s := by
  rw [applyAll_append, applyAll, applyAll_composeAll, List.append_assoc, applyAll_append,
    applyAll_append]

/-- The reader's account lookup (`stack-account`): the newest layer that mentions the
    address decides, else the base. -/
def lookupAcct : List (Delta A S F) → State A S F → A → Option F
  | [], b, a => b.acct a
  | d :: ds, b, a => match d.acct a with
    | some x => x
    | none => lookupAcct ds b a

/-- The reader's slot lookup (`stack-slot`): the newest layer that sets the slot decides;
    a layer that wiped the account's storage answers 0; else the layer below. -/
def lookupSlot : List (Delta A S F) → State A S F → A → S → Nat
  | [], b, a, k => b.slot a k
  | d :: ds, b, a, k => match d.slot a k with
    | some v => v
    | none => if d.wiped a then 0 else lookupSlot ds b a k

theorem lookupAcct_eq (ds : List (Delta A S F)) (b : State A S F) (a : A) :
    lookupAcct ds b a = (applyAll ds b).acct a := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [lookupAcct, applyAll, apply]
    cases d.acct a <;> simp [ih]

theorem lookupSlot_eq (ds : List (Delta A S F)) (b : State A S F) (a : A) (k : S) :
    lookupSlot ds b a k = (applyAll ds b).slot a k := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [lookupSlot, applyAll, apply]
    cases d.slot a k <;> simp [ih]

end Algebra

/-! ## Part B — materialization (the snapshot writer's inclusion rule S1)

Account fields are nonce, balance, codehash and the existence mark (the RAM's
`world-accounts`, the empty-but-present set). A base record exists iff the account is
non-empty, has storage, or is marked; its flag is then "empty" (the reader turns a
flagged record back into a mark). `ec` is the empty code hash. -/

section Mat

variable {A S : Type} (ec : Nat)

structure Acct where
  nonce   : Nat
  balance : Nat
  code    : Nat
  flag    : Bool
  deriving DecidableEq

def Acct.isEmpty (f : Acct) : Bool := f.nonce == 0 && f.balance == 0 && f.code == ec

/-- Does the address hold storage? -/
def HasSto (s : State A S Acct) (a : A) : Prop := ∃ k, s.slot a k ≠ 0

open Classical in
/-- `merge-account`'s output for one address: what a base snapshot holds. -/
noncomputable def mat (s : State A S Acct) : State A S Acct where
  acct a := match s.acct a with
    | none => if HasSto s a then some ⟨0, 0, ec, true⟩ else none
    | some f =>
      if f.isEmpty ec = false ∨ HasSto s a ∨ f.flag = true
      then some { f with flag := f.isEmpty ec } else none
  slot := s.slot

/-- Every layer the writer produces names the account fields of every address whose
    storage it touches (an address faulted in RAM brings its fields; one that was not —
    storage written without its account being read — gets its fields from the view
    below, `layer-fields-from-below`). -/
def FieldsCover (d : Delta A S Acct) : Prop :=
  ∀ a, (d.wiped a = true ∨ ∃ k, d.slot a k ≠ none) → d.acct a ≠ none

theorem mat_slot (s : State A S Acct) : (mat ec s).slot = s.slot := rfl

theorem hasSto_mat (s : State A S Acct) (a : A) : HasSto (mat ec s) a ↔ HasSto s a :=
  Iff.rfl

theorem mat_idem (s : State A S Acct) : mat ec (mat ec s) = mat ec s := by
  apply State.ext'
  · intro a
    show (mat ec (mat ec s)).acct a = (mat ec s).acct a
    have hs : HasSto (mat ec s) a ↔ HasSto s a := Iff.rfl
    simp only [mat]
    cases h : s.acct a with
    | none =>
      by_cases hh : HasSto s a
      · simp [hh, Acct.isEmpty]
      · simp [hh]; exact hh
    | some f =>
      by_cases hi : f.isEmpty ec = false ∨ HasSto s a ∨ f.flag = true
      · simp only [hi, if_true]
        cases he : f.isEmpty ec <;> simp_all [Acct.isEmpty]
      · simp only [hi, if_false]
        simp only [not_or] at hi
        simp; exact hi.2.1
  · intro a k; rfl

theorem mat_acct_congr {t t' : State A S Acct} {a : A} (h1 : t.acct a = t'.acct a)
    (h2 : HasSto t a ↔ HasSto t' a) : (mat ec t).acct a = (mat ec t').acct a := by
  simp only [mat, h1]
  by_cases h : HasSto t' a
  · have h' : HasSto t a := h2.2 h
    cases t'.acct a <;> simp [h, h']
  · have h' : ¬HasSto t a := fun x => h (h2.1 x)
    cases t'.acct a <;> simp [h, h']

/-- A layer over a materialized state reads as the same layer over the raw state, when the
    layer covers its storage writes with fields. -/
theorem mat_apply_mat (d : Delta A S Acct) (hd : FieldsCover d) (s : State A S Acct) :
    mat ec (apply d (mat ec s)) = mat ec (apply d s) := by
  apply State.ext'
  · intro a
    have hslot : ∀ k, (apply d (mat ec s)).slot a k = (apply d s).slot a k := fun _ => rfl
    have hsto : HasSto (apply d (mat ec s)) a ↔ HasSto (apply d s) a := by
      simp only [HasSto, hslot]
    cases hda : d.acct a with
    | some x =>
      exact mat_acct_congr ec (by simp [apply, hda]) hsto
    | none =>
      -- the layer does not touch the address at all
      have hnw : d.wiped a = false := by
        cases hw : d.wiped a
        · rfl
        · exact absurd hda (hd a (Or.inl hw))
      have hns : ∀ k, d.slot a k = none := by
        intro k
        cases hk : d.slot a k
        · rfl
        · exact absurd hda (hd a (Or.inr ⟨k, by simp [hk]⟩))
      have hsl : ∀ (t : State A S Acct) k, (apply d t).slot a k = t.slot a k := by
        intro t k; simp [apply, hns k, hnw]
      have hac : ∀ (t : State A S Acct), (apply d t).acct a = t.acct a := by
        intro t; simp [apply, hda]
      have h1 : (mat ec (apply d (mat ec s))).acct a = (mat ec (mat ec s)).acct a :=
        mat_acct_congr ec (hac _) (by simp only [HasSto, hsl])
      have h2 : (mat ec (apply d s)).acct a = (mat ec s).acct a :=
        mat_acct_congr ec (hac _) (by simp only [HasSto, hsl])
      rw [h1, h2, mat_idem]
  · intro a k; rfl

/-- The view a layered stack presents (what `stack-account`/`stack-slot` return): the
    merged raw state, materialized. -/
noncomputable def view (base : State A S Acct) (ds : List (Delta A S Acct)) : State A S Acct :=
  mat ec (applyAll ds base)

theorem view_nil (base : State A S Acct) (hb : mat ec base = base) : view ec base [] = base := hb

theorem view_cons (base : State A S Acct) (d : Delta A S Acct) (ds : List (Delta A S Acct))
    (hd : FieldsCover d) : view ec base (d :: ds) = mat ec (apply d (view ec base ds)) := by
  simp only [view, applyAll, mat_apply_mat ec d hd]

/-- Materializing below a covered stack changes nothing above it. -/
theorem view_mat_base (base : State A S Acct) (ds : List (Delta A S Acct))
    (hds : ∀ d ∈ ds, FieldsCover d) : view ec (mat ec base) ds = view ec base ds := by
  induction ds with
  | nil => exact mat_idem ec base
  | cons d ds ih =>
    rw [view_cons ec _ d ds (hds d List.mem_cons_self),
      view_cons ec _ d ds (hds d List.mem_cons_self),
      ih (fun d' h => hds d' (List.mem_cons_of_mem _ h))]

/-- Major compaction: the layers `lo` (all at or below the compaction block) are merged
    into the base, `base' = mat (applyAll lo base)` — `CompactOK`, the merge writer's
    contract. The layers above read the same over the new base. -/
theorem compact_view (base : State A S Acct) (hi lo : List (Delta A S Acct))
    (hhi : ∀ d ∈ hi, FieldsCover d) :
    view ec (view ec base lo) hi = view ec base (hi ++ lo) := by
  unfold view
  show mat ec (applyAll hi (mat ec (applyAll lo base))) = _
  have := view_mat_base ec (applyAll lo base) hi hhi
  unfold view at this
  rw [this, applyAll_append]

/-- Composition keeps the cover. -/
theorem fieldsCover_compose {d₁ d₂ : Delta A S Acct} (h₁ : FieldsCover d₁)
    (h₂ : FieldsCover d₂) : FieldsCover (compose d₁ d₂) := by
  intro a ha
  simp only [compose] at ha ⊢
  cases h2a : d₂.acct a with
  | some x => simp
  | none =>
    simp only
    have hw2 : d₂.wiped a = false := by
      cases hw : d₂.wiped a
      · rfl
      · exact absurd h2a (h₂ a (Or.inl hw))
    have hs2 : ∀ k, d₂.slot a k = none := by
      intro k; cases hk : d₂.slot a k
      · rfl
      · exact absurd h2a (h₂ a (Or.inr ⟨k, by simp [hk]⟩))
    apply h₁ a
    rcases ha with hw | ⟨k, hk⟩
    · simp [hw2] at hw; exact Or.inl hw
    · simp [hs2 k, hw2] at hk; exact Or.inr ⟨k, by simpa using hk⟩

theorem fieldsCover_composeAll (ds : List (Delta A S Acct)) (h : ∀ d ∈ ds, FieldsCover d) :
    FieldsCover (composeAll ds) := by
  induction ds with
  | nil => intro a ha; simp [composeAll, Delta.empty] at ha
  | cons d ds ih =>
    exact fieldsCover_compose (ih fun d' hd' => h d' (List.mem_cons_of_mem _ hd'))
      (h d List.mem_cons_self)

end Mat

/-! ## Part C — the replay: the stack reads as the canonical state

`V b` is the canonical (materialized) state after block `b`: what an uninterrupted replay
holds then. A layer written at block `b'` over parent `b` is correct when it turns `V b`
into `V b'` (`LayerOK`; the writer records every account and slot the replay faulted in
RAM during `b+1..b'`, with their RAM values). -/

section Replay

variable {A S : Type} (ec : Nat) (V : Nat → State A S Acct)

/-- The writer's contract for one layer: parent block, block, delta. -/
def LayerOK (b b' : Nat) (d : Delta A S Acct) : Prop :=
  FieldsCover d ∧ mat ec (apply d (V b)) = V b'

/-- A stack, NEWEST FIRST, of (block, layer) over a base at `b₀`, every layer correct
    over the one below it. -/
def StackOK (b₀ : Nat) : List (Nat × Delta A S Acct) → Prop
  | [] => True
  | [(b, d)] => LayerOK ec V b₀ b d
  | (b, d) :: (b', d') :: rest => LayerOK ec V b' b d ∧ StackOK b₀ ((b', d') :: rest)

def topBlock (b₀ : Nat) : List (Nat × Delta A S Acct) → Nat
  | [] => b₀
  | (b, _) :: _ => b

theorem stackOK_tail {b₀ : Nat} {p : Nat × Delta A S Acct} {rest : List (Nat × Delta A S Acct)}
    (h : StackOK ec V b₀ (p :: rest)) : StackOK ec V b₀ rest := by
  match rest, h with
  | [], _ => trivial
  | _ :: _, h => exact h.2

theorem stackOK_cover {b₀ : Nat} : ∀ {st : List (Nat × Delta A S Acct)},
    StackOK ec V b₀ st → ∀ p ∈ st, FieldsCover p.2
  | [], _, p, hp => by simp at hp
  | [(b, d)], h, p, hp => by simp at hp; subst hp; exact h.1
  | (b, d) :: (b', d') :: rest, h, p, hp => by
    rcases List.mem_cons.1 hp with e | hp'
    · subst e; exact h.1.1
    · exact stackOK_cover h.2 p hp'

/-- A base at `b₀` holding `V b₀`, with correct layers to block `bₖ`, reads as `V bₖ`:
    the replay's world (hot set empty) right after freezing layer `bₖ`, and a resume from
    that layer. -/
theorem stack_view (b₀ : Nat) (base : State A S Acct) (hb : base = V b₀)
    (hmat : mat ec (V b₀) = V b₀) :
    ∀ (st : List (Nat × Delta A S Acct)), StackOK ec V b₀ st →
      view ec base (st.map (·.2)) = V (topBlock b₀ st)
  | [], _ => by subst hb; exact hmat
  | [(b, d)], h => by
    simp only [List.map, topBlock]
    rw [view_cons ec base d [] h.1]
    simp only [view, applyAll]
    subst hb
    rw [hmat]; exact h.2
  | (b, d) :: (b', d') :: rest, h => by
    have ih := stack_view b₀ base hb hmat ((b', d') :: rest) h.2
    simp only [List.map, topBlock] at ih ⊢
    rw [view_cons ec base d _ h.1.1, ih]
    exact h.1.2

/-- A reorg rollback: dropping the `k` newest layers of a correct stack leaves a correct
    stack whose view is the canonical state at its new top. The replay then re-executes
    from that block; with a deterministic replay the result is the new branch's state. -/
theorem rollback_view (b₀ : Nat) (base : State A S Acct) (hb : base = V b₀)
    (hmat : mat ec (V b₀) = V b₀) (st : List (Nat × Delta A S Acct))
    (h : StackOK ec V b₀ st) (k : Nat) :
    view ec base ((st.drop k).map (·.2)) = V (topBlock b₀ (st.drop k)) := by
  apply stack_view ec V b₀ base hb hmat
  induction k generalizing st with
  | zero => simpa using h
  | succ k ih =>
    cases st with
    | nil => simp [StackOK]
    | cons p rest => simpa using ih rest (stackOK_tail ec V h)

/-- Major compaction at the stack's block `bₘ` (the layers `lo` at or below it) produces
    `V bₘ`, and the layers above still read as their canonical states. -/
theorem compaction_correct (b₀ : Nat) (base : State A S Acct) (hb : base = V b₀)
    (hmat : mat ec (V b₀) = V b₀) (hi lo : List (Nat × Delta A S Acct))
    (h : StackOK ec V b₀ (hi ++ lo)) :
    view ec (view ec base (lo.map (·.2))) (hi.map (·.2)) = V (topBlock b₀ (hi ++ lo)) := by
  have hc := stackOK_cover ec V h
  rw [compact_view ec base _ _ (fun d hd => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hd
        exact hc p (List.mem_append_left _ hp)),
    ← List.map_append]
  exact stack_view ec V b₀ base hb hmat _ h

end Replay

/-! ## Part D — recovery over layered files

The files are bases and layers (`snap-B/`, `layer-P-N/`), each sealed, torn or corrupt. A
resume POINT at block `n` is a composition: the components a resume from `n` loads (its
anchor line records them, so the bytes the root check read are the bytes resumed from;
an unanchored layer resolves its chain down to a base). The Part 1 view is derived from
the points: a point is a sealed dump iff all its components are sealed. GC deletes the
non-corrupt files no kept point names. -/

section Files

open Evm.Persist.Recovery

/-- A component file: a base at a block, or a layer by (parent, block). -/
inductive Comp | base (b : Nat) | layer (p b : Nat)
  deriving DecidableEq, Repr

abbrev FileEntry := Comp × DumpStatus

/-- A resume point: a block and the components that make its state. -/
abbrev Point := Nat × List Comp

def compSealed (fs : List FileEntry) (c : Comp) : Bool := fs.contains (c, .sealed)

def pointStatus (fs : List FileEntry) (p : Point) : DumpStatus :=
  if !p.2.isEmpty && p.2.all (compSealed fs) then .sealed else .torn

/-- The Part 1 view: one dump per point. -/
def dumpsOf (fs : List FileEntry) (ps : List Point) : List Dump :=
  ps.map (fun p => (p.1, pointStatus fs p))

/-- The files kept: every component of every point at a kept block. -/
def keepFiles (as : List Anchor) (fs : List FileEntry) (ps : List Point) : List Comp :=
  (ps.filter (fun p => decide (p.1 ∈ keep as (dumpsOf fs ps)))).flatMap (·.2)

/-- `run-gc`: the non-corrupt files outside `keepFiles`. -/
def gcFiles (as : List Anchor) (fs : List FileEntry) (ps : List Point) : List Comp :=
  (fs.filter (fun e => e.2 != .corrupt && decide (e.1 ∉ keepFiles as fs ps))).map (·.1)

/-- Deleting the non-corrupt files named in `D`. -/
def deleteFiles (D : List Comp) (fs : List FileEntry) : List FileEntry :=
  fs.filter (fun e => e.2 == .corrupt || decide (e.1 ∉ D))

/-- `run-gc`'s effect. (The replay's own GC passes its live stack as pinned: it deletes a
    subset of `gcFiles`, covered by `gcSubset_preserves_resume`.) -/
def applyGcFiles (as : List Anchor) (fs : List FileEntry) (ps : List Point) : List FileEntry :=
  deleteFiles (gcFiles as fs ps) fs

theorem mem_dumpsOf_sealed {fs : List FileEntry} {ps : List Point} {b : Nat} :
    (b, DumpStatus.sealed) ∈ dumpsOf fs ps ↔ ∃ p ∈ ps, p.1 = b ∧ pointStatus fs p = .sealed := by
  simp only [dumpsOf, List.mem_map, Prod.mk.injEq]

theorem pointStatus_sealed {fs : List FileEntry} {p : Point} :
    pointStatus fs p = .sealed ↔ p.2 ≠ [] ∧ ∀ c ∈ p.2, (c, DumpStatus.sealed) ∈ fs := by
  unfold pointStatus compSealed
  by_cases h : (!p.2.isEmpty && p.2.all fun c => fs.contains (c, DumpStatus.sealed)) = true
  · simp only [h, if_true, true_iff]
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true, List.contains_iff_mem] at h
    exact h
  · simp only [h, if_false, reduceCtorEq, false_iff]
    intro ⟨hne, hall⟩
    apply h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true, List.contains_iff_mem]
    exact ⟨hne, hall⟩

theorem mem_deleteFiles {D : List Comp} {fs : List FileEntry} {e : FileEntry} :
    e ∈ deleteFiles D fs ↔ e ∈ fs ∧ (e.2 = .corrupt ∨ e.1 ∉ D) := by
  simp [deleteFiles]

/-- Deleting only removes files: a point sealed after it was sealed before. -/
theorem sealed_after_delete {D : List Comp} {fs : List FileEntry} {p : Point}
    (h : pointStatus (deleteFiles D fs) p = .sealed) : pointStatus fs p = .sealed := by
  rw [pointStatus_sealed] at h ⊢
  exact ⟨h.1, fun c hc => (mem_deleteFiles.1 (h.2 c hc)).1⟩

/-- No component of a kept point is collected. -/
theorem kept_not_gc {as : List Anchor} {fs : List FileEntry} {ps : List Point} {c : Comp}
    (hc : c ∈ keepFiles as fs ps) : c ∉ gcFiles as fs ps := by
  simp only [gcFiles, List.mem_map, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq, not_exists, not_and]
  intro e ⟨_, _, hk⟩ he
  subst he; exact hk hc

/-- A sealed point at a kept block stays sealed after deleting any part of the GC set. -/
theorem kept_point_sealed {as : List Anchor} {fs : List FileEntry} {ps : List Point}
    {D : List Comp} (hD : ∀ c ∈ D, c ∈ gcFiles as fs ps)
    {p : Point} (hp : p ∈ ps) (hk : p.1 ∈ keep as (dumpsOf fs ps))
    (hs : pointStatus fs p = .sealed) : pointStatus (deleteFiles D fs) p = .sealed := by
  rw [pointStatus_sealed] at hs ⊢
  refine ⟨hs.1, fun c hc => mem_deleteFiles.2 ⟨hs.2 c hc, Or.inr fun hcD => kept_not_gc ?_ (hD c hcD)⟩⟩
  simp only [keepFiles, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
  exact ⟨p, ⟨hp, hk⟩, hc⟩

/-- I2 over layered files: deleting any part of the GC set (the replay pins its live
    stack) leaves the resume point where it was. -/
theorem gcSubset_preserves_resume (as : List Anchor) (fs : List FileEntry) (ps : List Point)
    (D : List Comp) (hD : ∀ c ∈ D, c ∈ gcFiles as fs ps) :
    resumePoint as (dumpsOf (deleteFiles D fs) ps) = resumePoint as (dumpsOf fs ps) := by
  have hsub : ∀ b, b ∈ candidates as (dumpsOf (deleteFiles D fs) ps) →
      b ∈ candidates as (dumpsOf fs ps) := by
    intro b hb
    rw [mem_candidates, mem_dumpsOf_sealed] at hb
    obtain ⟨hv, p, hp, hpb, hs⟩ := hb
    exact mem_candidates.2 ⟨hv, mem_dumpsOf_sealed.2 ⟨p, hp, hpb, sealed_after_delete hs⟩⟩
  cases h : resumePoint as (dumpsOf fs ps) with
  | block r =>
    apply resume_stable hsub _ h
    have ⟨hv, hs⟩ := resume_sound h
    obtain ⟨p, hp, hpr, hps⟩ := mem_dumpsOf_sealed.1 hs
    have hk : p.1 ∈ keep as (dumpsOf fs ps) := by
      rw [hpr]; exact List.mem_append_left _ (resume_mem_keepVerified h)
    exact mem_candidates.2 ⟨hv, mem_dumpsOf_sealed.2 ⟨p, hp, hpr, kept_point_sealed hD hp hk hps⟩⟩
  | genesis => exact resume_genesis_iff.2 (resume_genesis_iff.1 h)
  | refuse =>
    cases h' : resumePoint as (dumpsOf (deleteFiles D fs) ps) with
    | block r' =>
      have := hsub r' (resumePoint_eq_block.1 h').1
      have ⟨r, hr⟩ := resume_of_candidate this
      rw [hr] at h; cases h
    | genesis =>
      rw [resume_genesis_iff, ← resume_genesis_iff (ds := dumpsOf fs ps)] at h'
      rw [h'] at h; cases h
    | refuse => rfl

/-- I2 over layered files: running GC leaves the resume point where it was. -/
theorem gcFiles_preserves_resume (as : List Anchor) (fs : List FileEntry) (ps : List Point) :
    resumePoint as (dumpsOf (applyGcFiles as fs ps) ps) = resumePoint as (dumpsOf fs ps) :=
  gcSubset_preserves_resume as fs ps _ (fun _ h => h)

/-- The resume point's components are all sealed files: what the replay loads. -/
theorem resume_components_sealed {as : List Anchor} {fs : List FileEntry} {ps : List Point}
    {r : Nat} (h : resumePoint as (dumpsOf fs ps) = .block r) :
    r ∈ verified as ∧ ∃ p ∈ ps, p.1 = r ∧ p.2 ≠ [] ∧ ∀ c ∈ p.2, (c, DumpStatus.sealed) ∈ fs := by
  obtain ⟨hv, hs⟩ := resume_sound h
  obtain ⟨p, hp, hpr, hps⟩ := mem_dumpsOf_sealed.1 hs
  exact ⟨hv, p, hp, hpr, pointStatus_sealed.1 hps⟩

end Files

end Evm.Persist.Layered
