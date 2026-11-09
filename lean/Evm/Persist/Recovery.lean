/-! # Evm/Persist/Recovery — the restart decisions, proved (P1, persistence plan rev. 2 §2.5)

`src/state/recovery.lisp` decides, after any crash, where the replay resumes and which
state dumps may be deleted. Those two decisions are where the 2026-10-17/18 faults were
(F2–F4: a resume behind the verified frontier, a GC that deleted the only usable dump, a
genesis restart after blocks had been verified). They are small, so they are proved here
rather than tested; the Lisp functions mirror the definitions below one to one.

The input is a VIEW of the durable state, exactly what `recovery.lisp` reads:
  * anchors — the parsed lines of anchors.sexp: (block, root check passed?, dump hash);
  * dumps   — one entry per state file: (block, sealed | torn | corrupt).

Part 1 (this section) is the pure decision layer: I1 (resume point), I2 (monotone
recovery, bounded GC). The parts after it model the files underneath the view.
-/

namespace Evm.Persist.Recovery

/-! ## Part 1 — decisions over the view -/

inductive DumpStatus | sealed | torn | corrupt
  deriving DecidableEq, Repr

structure Anchor where
  block : Nat
  ok    : Bool
  hash  : Option String
  deriving DecidableEq, Repr

abbrev Dump := Nat × DumpStatus

/-- `verified-blocks`: blocks with a passed root check. -/
def verified (as : List Anchor) : List Nat := (as.filter (·.ok)).map (·.block)

/-- `usable-p`: block `b` has a sealed dump. -/
def usable (ds : List Dump) (b : Nat) : Bool := ds.contains (b, .sealed)

/-- Verified blocks one can resume from. -/
def candidates (as : List Anchor) (ds : List Dump) : List Nat :=
  (verified as).filter (usable ds)

inductive Resume | block (n : Nat) | genesis | refuse
  deriving DecidableEq, Repr

/-- `resume-point` (I1): the highest verified block with a sealed dump; `genesis` only when
    nothing was ever verified; otherwise `refuse` (going behind needs the operator, I2). -/
def resumePoint (as : List Anchor) (ds : List Dump) : Resume :=
  match (candidates as ds).max? with
  | some b => .block b
  | none   => if (verified as).isEmpty then .genesis else .refuse

def descSort (l : List Nat) : List Nat := l.mergeSort (fun a b => decide (b ≤ a))

def sealedBlocks (ds : List Dump) : List Nat :=
  (ds.filter (fun d => d.2 == .sealed)).map (·.1)

/-- The two highest verified sealed dumps. -/
def keepVerified (as : List Anchor) (ds : List Dump) : List Nat :=
  (descSort ((sealedBlocks ds).filter (fun b => decide (b ∈ verified as)))).take 2

/-- Up to two not-yet-verified sealed dumps above them (so they can still be verified). -/
def keepAbove (as : List Anchor) (ds : List Dump) : List Nat :=
  let top := (keepVerified as ds).head?
  (descSort ((sealedBlocks ds).filter
      (fun b => decide (b ∉ verified as) && top.all (· < b)))).take 2

def keep (as : List Anchor) (ds : List Dump) : List Nat :=
  keepVerified as ds ++ keepAbove as ds

/-- `gc-set`: every non-corrupt dump outside `keep` (corrupt ones are kept for inspection). -/
def gcSet (as : List Anchor) (ds : List Dump) : List Nat :=
  ((ds.filter (fun d => d.2 != .corrupt && decide (d.1 ∉ keep as ds))).map (·.1)).mergeSort
    (fun a b => decide (a ≤ b))

/-- The effect of `run-gc` on the view: the plain state files of the GC set are gone. -/
def applyGc (as : List Anchor) (ds : List Dump) : List Dump :=
  ds.filter (fun d => d.2 == .corrupt || decide (d.1 ∉ gcSet as ds))

/-- A load refused the dump at `n` (trailer or hash): it is renamed `.corrupt`. -/
def quarantine (n : Nat) (ds : List Dump) : List Dump :=
  ds.map (fun d => if d = (n, .sealed) then (n, .corrupt) else d)

/-! ### Resume point -/

theorem mem_candidates {as : List Anchor} {ds : List Dump} {b : Nat} :
    b ∈ candidates as ds ↔ b ∈ verified as ∧ (b, DumpStatus.sealed) ∈ ds := by
  simp [candidates, usable]

theorem resumePoint_eq_block {as : List Anchor} {ds : List Dump} {r : Nat} :
    resumePoint as ds = .block r ↔
      r ∈ candidates as ds ∧ ∀ b ∈ candidates as ds, b ≤ r := by
  unfold resumePoint
  cases h : (candidates as ds).max? with
  | some m =>
    rw [List.max?_eq_some_iff] at h
    constructor
    · intro e; cases e; exact h
    · rintro ⟨hr, hmax⟩
      have := Nat.le_antisymm (hmax m h.1) (h.2 r hr)
      simp [this]
  | none =>
    have hc := List.max?_eq_none_iff.1 h
    constructor
    · intro e; dsimp only at e; split at e <;> simp at e
    · rintro ⟨hr, -⟩; simp [hc] at hr

/-- I1, soundness: the resume point is verified and has a sealed dump. -/
theorem resume_sound {as : List Anchor} {ds : List Dump} {r : Nat}
    (h : resumePoint as ds = .block r) :
    r ∈ verified as ∧ (r, DumpStatus.sealed) ∈ ds :=
  mem_candidates.1 (resumePoint_eq_block.1 h).1

/-- I1, maximality: no verified block with a sealed dump lies above it. -/
theorem resume_max {as : List Anchor} {ds : List Dump} {r b : Nat}
    (h : resumePoint as ds = .block r) (hv : b ∈ verified as)
    (hs : (b, DumpStatus.sealed) ∈ ds) : b ≤ r :=
  (resumePoint_eq_block.1 h).2 b (mem_candidates.2 ⟨hv, hs⟩)

/-- Genesis exactly when nothing was ever verified (F4 cannot happen). -/
theorem resume_genesis_iff {as : List Anchor} {ds : List Dump} :
    resumePoint as ds = .genesis ↔ verified as = [] := by
  unfold resumePoint
  cases h : (candidates as ds).max? with
  | some m =>
    simp only [reduceCtorEq, false_iff]
    intro hv
    have := List.max?_mem h
    simp [candidates, hv] at this
  | none => by_cases hv : verified as = [] <;> simp [hv]

/-- Monotone recovery (I2): if every verified block stays verified and every sealed dump
    stays sealed, the resume point does not move down. -/
theorem resume_mono {as as' : List Anchor} {ds ds' : List Dump} {r : Nat}
    (hv : ∀ b, b ∈ verified as → b ∈ verified as')
    (hd : ∀ b, (b, DumpStatus.sealed) ∈ ds → (b, DumpStatus.sealed) ∈ ds')
    (h : resumePoint as ds = .block r) :
    ∃ r', resumePoint as' ds' = .block r' ∧ r ≤ r' := by
  have ⟨hv0, hs0⟩ := resume_sound h
  have hc : r ∈ candidates as' ds' := mem_candidates.2 ⟨hv r hv0, hd r hs0⟩
  cases hm : (candidates as' ds').max? with
  | none => simp [List.max?_eq_none_iff.1 hm] at hc
  | some m =>
    refine ⟨m, ?_, ?_⟩
    · simp [resumePoint, hm]
    · exact ((List.max?_eq_some_iff).1 hm).2 r hc

/-- The resume point is unchanged by any change that keeps it a candidate and adds none. -/
theorem resume_stable {as as' : List Anchor} {ds ds' : List Dump} {r : Nat}
    (hsub : ∀ b, b ∈ candidates as' ds' → b ∈ candidates as ds)
    (hr : r ∈ candidates as' ds')
    (h : resumePoint as ds = .block r) : resumePoint as' ds' = .block r := by
  obtain ⟨-, hmax⟩ := resumePoint_eq_block.1 h
  exact resumePoint_eq_block.2 ⟨hr, fun b hb => hmax b (hsub b hb)⟩

/-- Appending an anchor never lowers the resume point (anchors.sexp is append-only). -/
theorem resume_append_anchor {as : List Anchor} {ds : List Dump} {r : Nat} (a : Anchor)
    (h : resumePoint as ds = .block r) :
    ∃ r', resumePoint (as ++ [a]) ds = .block r' ∧ r ≤ r' :=
  resume_mono (fun b hb => by simp [verified] at hb ⊢; exact Or.inl hb) (fun _ h => h) h

/-- Publishing a dump never lowers the resume point. -/
theorem resume_add_dump {as : List Anchor} {ds : List Dump} {r : Nat} (d : Dump)
    (h : resumePoint as ds = .block r) :
    ∃ r', resumePoint as (d :: ds) = .block r' ∧ r ≤ r' :=
  resume_mono (fun _ h => h) (fun _ h => List.mem_cons_of_mem _ h) h

/-- Once something is verified, no later view (anchors only grow) restarts from genesis. -/
theorem no_genesis_after_verified {as : List Anchor} {ds : List Dump} (extra : List Anchor)
    (hv : verified as ≠ []) : resumePoint (as ++ extra) ds ≠ .genesis := by
  rw [Ne, resume_genesis_iff]
  intro h; apply hv
  simp only [verified, List.filter_append, List.map_append, List.append_eq_nil_iff] at h
  exact h.1

/-- Quarantining any dump but the resume point leaves the resume point where it is. -/
theorem resume_quarantine_other {as : List Anchor} {ds : List Dump} {r n : Nat}
    (hn : n ≠ r) (h : resumePoint as ds = .block r) :
    resumePoint as (quarantine n ds) = .block r := by
  have mem_q : ∀ b, (b, DumpStatus.sealed) ∈ quarantine n ds ↔
      (b, DumpStatus.sealed) ∈ ds ∧ b ≠ n := by
    intro b
    simp only [quarantine, List.mem_map]
    constructor
    · rintro ⟨d, hd, e⟩
      by_cases hdn : d = (n, .sealed)
      · simp [hdn] at e
      · simp only [hdn, ite_false] at e; subst e
        exact ⟨hd, fun hb => hdn (by simp [hb])⟩
    · rintro ⟨hb, hbn⟩
      exact ⟨_, hb, by simp [hbn]⟩
  apply resume_stable (as := as) (ds := ds)
  · intro b hb
    rw [mem_candidates, mem_q] at hb
    exact mem_candidates.2 ⟨hb.1, hb.2.1⟩
  · have ⟨hv, hs⟩ := resume_sound h
    exact mem_candidates.2 ⟨hv, (mem_q r).2 ⟨hs, fun e => hn e.symm⟩⟩
  · exact h

/-! ### GC -/

theorem resume_of_candidate {as : List Anchor} {ds : List Dump} {b : Nat}
    (hb : b ∈ candidates as ds) : ∃ r, resumePoint as ds = .block r := by
  cases hm : (candidates as ds).max? with
  | none => simp [List.max?_eq_none_iff.1 hm] at hb
  | some m => exact ⟨m, by simp [resumePoint, hm]⟩

theorem descSort_pairwise (l : List Nat) : (descSort l).Pairwise (fun a b => b ≤ a) := by
  have := List.pairwise_mergeSort (le := fun a b => decide (b ≤ a))
    (by intro a b c h1 h2; simp at *; omega) (by intro a b; simp; omega) l
  simpa [descSort] using this

theorem mem_descSort {l : List Nat} {b : Nat} : b ∈ descSort l ↔ b ∈ l := List.mem_mergeSort

theorem mem_sealedBlocks {ds : List Dump} {b : Nat} :
    b ∈ sealedBlocks ds ↔ (b, DumpStatus.sealed) ∈ ds := by
  simp only [sealedBlocks, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨b', st⟩, ⟨hd, hst⟩, rfl⟩; simp at hst; subst hst; exact hd
  · intro h; exact ⟨_, ⟨h, rfl⟩, rfl⟩

/-- The resume point is the first of the two kept verified dumps. -/
theorem resume_mem_keepVerified {as : List Anchor} {ds : List Dump} {r : Nat}
    (h : resumePoint as ds = .block r) : r ∈ keepVerified as ds := by
  have ⟨hv, hs⟩ := resume_sound h
  unfold keepVerified
  generalize hS : (sealedBlocks ds).filter (fun b => decide (b ∈ verified as)) = S
  have hmemS : ∀ x, x ∈ S ↔ (x, DumpStatus.sealed) ∈ ds ∧ x ∈ verified as := by
    intro x; subst hS; simp [mem_sealedBlocks]
  have hpw := descSort_pairwise S
  have hr : r ∈ descSort S := mem_descSort.2 ((hmemS r).2 ⟨hs, hv⟩)
  have hmemL : ∀ x, x ∈ descSort S → x ∈ S := fun _ => mem_descSort.1
  generalize descSort S = L at hpw hr hmemL
  cases L with
  | nil => simp at hr
  | cons x rest =>
    have ⟨hxs, hxv⟩ := (hmemS x).1 (hmemL x List.mem_cons_self)
    have hxle : x ≤ r := resume_max h hxv hxs
    have hx : x = r := by
      rcases List.mem_cons.1 hr with e | hr'
      · exact e.symm
      · have := (List.pairwise_cons.1 hpw).1 r hr'; omega
    subst hx; simp

theorem mem_gcSet {as : List Anchor} {ds : List Dump} {b : Nat} :
    b ∈ gcSet as ds ↔ ∃ st, (b, st) ∈ ds ∧ st ≠ .corrupt ∧ b ∉ keep as ds := by
  simp only [gcSet, List.mem_mergeSort, List.mem_map, List.mem_filter, Bool.and_eq_true,
    bne_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨b', st⟩, ⟨hd, hc, hk⟩, rfl⟩; exact ⟨st, hd, hc, hk⟩
  · rintro ⟨st, hd, hc, hk⟩; exact ⟨(b, st), ⟨hd, hc, hk⟩, rfl⟩

/-- I2: GC never deletes the resume point. -/
theorem resume_not_gc {as : List Anchor} {ds : List Dump} {r : Nat}
    (h : resumePoint as ds = .block r) : r ∉ gcSet as ds := by
  rw [mem_gcSet]
  rintro ⟨-, -, -, hk⟩
  exact hk (List.mem_append_left _ (resume_mem_keepVerified h))

theorem mem_applyGc {as : List Anchor} {ds : List Dump} {d : Dump} :
    d ∈ applyGc as ds ↔ d ∈ ds ∧ (d.2 = .corrupt ∨ d.1 ∉ gcSet as ds) := by
  simp [applyGc]

/-- I2: running GC leaves the resume point exactly where it was. -/
theorem gc_preserves_resume (as : List Anchor) (ds : List Dump) :
    resumePoint as (applyGc as ds) = resumePoint as ds := by
  have hsub : ∀ b, b ∈ candidates as (applyGc as ds) → b ∈ candidates as ds := by
    intro b hb
    rw [mem_candidates, mem_applyGc] at hb
    exact mem_candidates.2 ⟨hb.1, hb.2.1⟩
  cases h : resumePoint as ds with
  | block r =>
    apply resume_stable hsub _ h
    have ⟨hv, hs⟩ := resume_sound h
    exact mem_candidates.2 ⟨hv, mem_applyGc.2 ⟨hs, Or.inr (resume_not_gc h)⟩⟩
  | genesis =>
    exact resume_genesis_iff.2 (resume_genesis_iff.1 h)
  | refuse =>
    cases h' : resumePoint as (applyGc as ds) with
    | block r' =>
      have := hsub r' (resumePoint_eq_block.1 h').1
      have ⟨r, hr⟩ := resume_of_candidate this
      rw [hr] at h; cases h
    | genesis =>
      rw [resume_genesis_iff, ← resume_genesis_iff (ds := ds)] at h'
      rw [h'] at h; cases h
    | refuse => rfl

/-- Bounded disk: after GC every surviving non-corrupt dump is in `keep`, and `keep` has at
    most four blocks (two verified, two pending verification). -/
theorem gc_bounded (as : List Anchor) (ds : List Dump) :
    (∀ d ∈ applyGc as ds, d.2 ≠ .corrupt → d.1 ∈ keep as ds) ∧ (keep as ds).length ≤ 4 := by
  constructor
  · intro d hd hc
    rw [mem_applyGc] at hd
    rcases hd with ⟨hd, hc' | hg⟩
    · exact absurd hc' hc
    · apply Classical.byContradiction; intro hk
      exact hg (mem_gcSet.2 ⟨d.2, hd, hc, hk⟩)
  · simp only [keep, keepVerified, keepAbove, List.length_append, List.length_take]
    omega

/-! ## Part 2 — files, fsync and crashes; atomic publication

The fs model is the trust surface the plan names: what survives a crash.
  * A file has bytes and a durable prefix length `synced` (set by fsync).
  * A name is bound to an inode in the LIVE namespace (what the process sees) and in the
    DURABLE one (what a crash keeps for sure); fsync of the directory copies live to durable.
  * A crash keeps, per name, either its durable or its live binding (renames and unlinks
    not yet made durable may or may not survive, independently — a sound overapproximation
    of journalled metadata), and tears every file: the synced prefix survives, the rest is
    cut at any point and may be followed by zeros (delayed allocation extends the size
    without the data). Garbage other than zeros is outside the model: that is bit rot,
    which the content hash (I3) catches.

The writer publishes a file under a name `pub p` by the protocol every artifact uses
(dump, footer, committed marker): write `tmp p`, fsync it, rename it over `pub p`, fsync
the directory. `published_good`: in every state reachable by protocol steps and crashes
in any interleaving, every binding of every published name, live or durable, is a fully
synced file whose content the writer meant to publish. `rename_before_fsync_unsafe`
shows the fsync is necessary (the bug fixed in `factlog-commit!` the day this was written).
-/

abbrev Bytes := List Nat

inductive Name | tmp (p : Nat) | pub (p : Nat)
  deriving DecidableEq

structure File where
  data   : Bytes
  synced : Nat

structure FS where
  live    : Name → Option Nat
  durable : Name → Option Nat
  inode   : Nat → File
  next    : Nat

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-- A crash tears file `f` into `f'`. -/
def Tear (f f' : File) : Prop :=
  ∃ k j, f.synced ≤ k ∧ k + j ≤ f.data.length ∧
    f'.data = f.data.take k ++ List.replicate j 0 ∧ f'.synced = f'.data.length

def Crash (fs fs' : FS) : Prop :=
  (∀ n, fs'.live n = fs.durable n ∨ fs'.live n = fs.live n) ∧ fs'.durable = fs'.live ∧
  (∀ i, Tear (fs.inode i) (fs'.inode i)) ∧ fs'.next = fs.next

theorem tear_synced {f f' : File} (h : Tear f f') (hs : f.synced = f.data.length) :
    f' = f := by
  obtain ⟨k, j, hk, hkj, hd, hs'⟩ := h
  have hk' : k = f.data.length := by omega
  have hj : j = 0 := by omega
  subst hk' hj
  cases f; cases f'
  simp_all

/-- Writer program counter: the publication of `c` under `pub p` via inode `i`. -/
inductive Pc | idle | wrote (p : Nat) (c : Bytes) (i : Nat) | synced (p : Nat) (i : Nat)
  | renamed

section Publish
variable (Good : Nat → Bytes → Prop)

/-- One step of the system: a protocol step of the writer, or a crash. -/
inductive Step : FS × Pc → FS × Pc → Prop
  /-- open `tmp p` (O_TRUNC: a fresh inode) and write `c` -/
  | write (fs : FS) (p : Nat) (c : Bytes) (hc : Good p c) :
      Step (fs, .idle)
        ({ fs with live := upd fs.live (.tmp p) (some fs.next),
                   inode := upd fs.inode fs.next ⟨c, 0⟩, next := fs.next + 1 },
         .wrote p c fs.next)
  | fsync (fs : FS) (p : Nat) (c : Bytes) (i : Nat) :
      Step (fs, .wrote p c i)
        ({ fs with inode := upd fs.inode i ⟨(fs.inode i).data, (fs.inode i).data.length⟩ },
         .synced p i)
  | rename (fs : FS) (p : Nat) (i : Nat) :
      Step (fs, .synced p i)
        ({ fs with live := upd (upd fs.live (.pub p) (fs.live (.tmp p))) (.tmp p) none },
         .renamed)
  | fsyncDir (fs : FS) (pc : Pc) :
      Step (fs, pc) ({ fs with durable := fs.live }, pc)
  /-- GC of a published file, or startup removal of a stale tmp -/
  | unlink (fs : FS) (n : Name) :
      Step (fs, .idle) ({ fs with live := upd fs.live n none }, .idle)
  | finish (fs : FS) : Step (fs, .renamed) (fs, .idle)
  | crash (fs fs' : FS) (pc : Pc) (h : Crash fs fs') : Step (fs, pc) (fs', .idle)

def Bound (fs : FS) (n : Name) (i : Nat) : Prop := fs.live n = some i ∨ fs.durable n = some i

/-- The invariant. -/
structure Inv (st : FS × Pc) : Prop where
  pub   : ∀ p i, Bound st.1 (.pub p) i →
            Good p (st.1.inode i).data ∧ (st.1.inode i).synced = (st.1.inode i).data.length
  fresh : ∀ n i, Bound st.1 n i → i < st.1.next
  pc    : match st.2 with
          | .idle | .renamed => True
          | .wrote p c i => st.1.live (.tmp p) = some i ∧ (st.1.inode i).data = c ∧ Good p c
          | .synced p i => st.1.live (.tmp p) = some i ∧ Good p (st.1.inode i).data ∧
              (st.1.inode i).synced = (st.1.inode i).data.length

theorem inv_init : Inv Good (⟨fun _ => none, fun _ => none, fun _ => ⟨[], 0⟩, 0⟩, .idle) :=
  ⟨by simp [Bound], by simp [Bound], trivial⟩

theorem inv_step {st st' : FS × Pc} (h : Step Good st st') (hi : Inv Good st) :
    Inv Good st' := by
  obtain ⟨hpub, hfresh, hpc⟩ := hi
  cases h with
  | write fs p c hc =>
    dsimp only at hpub hfresh hpc ⊢
    refine ⟨?_, ?_, ?_⟩
    · intro q i hb
      have hne : i ≠ fs.next := by
        rintro rfl
        simp only [Bound, upd] at hb
        rcases hb with hb | hb
        · simp at hb; exact Nat.lt_irrefl _ (hfresh _ _ (Or.inl hb))
        · exact Nat.lt_irrefl _ (hfresh _ _ (Or.inr hb))
      have hb' : Bound fs (.pub q) i := by simpa [Bound, upd] using hb
      simpa [upd, hne] using hpub q i hb'
    · intro n i hb
      simp only [Bound, upd] at hb
      by_cases hn : n = .tmp p
      · subst hn; simp at hb
        rcases hb with rfl | hb
        · simp
        · have := hfresh _ _ (Or.inr hb); simp; omega
      · simp [hn] at hb
        have := hfresh _ _ hb; simp; omega
    · simp [upd]; exact hc
  | fsync fs p c i =>
    dsimp only at hpub hfresh hpc ⊢
    obtain ⟨hl, hd, hc⟩ := hpc
    refine ⟨?_, ?_, ?_⟩
    · intro q j hb
      have := hpub q j hb
      by_cases hj : j = i
      · subst hj; simp [upd]; exact this.1
      · simpa [upd, hj] using this
    · exact hfresh
    · simp [upd]; exact ⟨hl, hd ▸ hc⟩
  | rename fs p i =>
    dsimp only at hpub hfresh hpc ⊢
    obtain ⟨hl, hg, hs⟩ := hpc
    refine ⟨?_, ?_, trivial⟩
    · intro q j hb
      simp only [Bound, upd] at hb
      by_cases hq : q = p
      · subst hq
        simp [hl] at hb
        rcases hb with rfl | hb
        · exact ⟨hg, hs⟩
        · exact hpub _ _ (Or.inr hb)
      · have : Name.pub q ≠ Name.pub p := by simp [hq]
        simp [this] at hb
        exact hpub _ _ hb
    · intro n j hb
      simp only [Bound, upd] at hb
      by_cases h1 : n = .tmp p
      · subst h1; simp at hb; exact hfresh _ _ (Or.inr hb)
      · by_cases h2 : n = .pub p
        · subst h2; simp [hl] at hb
          rcases hb with rfl | hb
          · exact hfresh _ _ (Or.inl hl)
          · exact hfresh _ _ (Or.inr hb)
        · simp [h1, h2] at hb; exact hfresh _ _ hb
  | fsyncDir fs pc =>
    dsimp only at hpub hfresh hpc ⊢
    refine ⟨?_, ?_, ?_⟩
    · intro q i hb
      exact hpub q i (by simp only [Bound] at hb ⊢; rcases hb with h | h <;> exact Or.inl h)
    · intro n i hb
      exact hfresh n i (by simp only [Bound] at hb ⊢; rcases hb with h | h <;> exact Or.inl h)
    · exact hpc
  | unlink fs n =>
    dsimp only at hpub hfresh hpc ⊢
    refine ⟨?_, ?_, trivial⟩
    · intro q i hb
      apply hpub q i
      simp only [Bound, upd] at hb ⊢
      by_cases h : Name.pub q = n
      · subst h; simp at hb; exact Or.inr hb
      · simp [h] at hb; exact hb
    · intro m i hb
      apply hfresh m i
      simp only [Bound, upd] at hb ⊢
      by_cases h : m = n
      · subst h; simp at hb; exact Or.inr hb
      · simp [h] at hb; exact hb
  | finish fs => exact ⟨hpub, hfresh, trivial⟩
  | crash fs fs' pc hc =>
    dsimp only at hpub hfresh hpc ⊢
    obtain ⟨hn, hd, ht, hnext⟩ := hc
    have bound' : ∀ n i, Bound fs' n i → Bound fs n i := by
      intro n i hb
      have hl : fs'.live n = some i := by
        rcases hb with h | h
        · exact h
        · rw [hd] at h; exact h
      rcases hn n with h | h
      · exact Or.inr (h ▸ hl)
      · exact Or.inl (h ▸ hl)
    refine ⟨?_, ?_, trivial⟩
    · intro q i hb
      have hp := hpub q i (bound' _ _ hb)
      rw [tear_synced (ht i) hp.2]; exact hp
    · intro n i hb
      rw [hnext]; exact hfresh n i (bound' _ _ hb)

/-- Reachability from the empty filesystem. -/
inductive Reach : FS × Pc → Prop
  | init : Reach (⟨fun _ => none, fun _ => none, fun _ => ⟨[], 0⟩, 0⟩, .idle)
  | step {st st'} : Reach st → Step Good st st' → Reach st'

/-- Atomic publication: after any interleaving of protocol steps and crashes, a published
    name — as the process sees it or as the disk holds it — is bound only to a complete,
    fully synced file the writer meant to publish. Never a torn one, never an empty one. -/
theorem published_good {st : FS × Pc} (h : Reach Good st) {p i : Nat}
    (hb : Bound st.1 (.pub p) i) :
    Good p (st.1.inode i).data ∧ (st.1.inode i).synced = (st.1.inode i).data.length := by
  have : Inv Good st := by
    clear hb
    induction h with
    | init => exact inv_init Good
    | step _ hs ih => exact inv_step Good hs ih
  exact this.pub p i hb

end Publish

/-- Without the fsync before the rename, a crash leaves the published name bound to a
    torn file: here, the empty one `factlog-commit!` could leave before 2026-10-18. -/
theorem rename_before_fsync_unsafe :
    let fs0 : FS := ⟨fun _ => none, fun _ => none, fun _ => ⟨[], 0⟩, 0⟩
    -- write tmp 0 with content [1] (not synced), rename it to pub 0, fsync the directory
    let fs1 : FS := { fs0 with live := upd fs0.live (.tmp 0) (some 0),
                               inode := upd fs0.inode 0 ⟨[1], 0⟩, next := 1 }
    let fs2 : FS := { fs1 with live := upd (upd fs1.live (.pub 0) (some 0)) (.tmp 0) none }
    let fs3 : FS := { fs2 with durable := fs2.live }
    ∃ fs4, Crash fs3 fs4 ∧ fs4.live (.pub 0) = some 0 ∧ (fs4.inode 0).data = [] := by
  intro fs0 fs1 fs2 fs3
  refine ⟨{ fs3 with inode := fun _ => ⟨[], 0⟩ }, ⟨?_, rfl, ?_, rfl⟩, ?_, rfl⟩
  · intro n; exact Or.inl rfl
  · intro i
    by_cases hi : i = 0
    · subst hi; exact ⟨0, 0, by simp [fs3, fs2, fs1, upd]⟩
    · exact ⟨0, 0, by simp [fs3, fs2, fs1, fs0, upd, hi]⟩
  · simp [fs3, fs2, upd]

/-! ## Part 3 — anchors.sexp: appended verdicts under torn tails

anchors.sexp is appended one line per verdict and fsynced after each line. A crash tears
the unsynced tail. The reader (`read-anchors`) splits on newline and skips every line it
cannot parse. `append-anchor!` starts a fresh line when the file does not end with one.

Assumptions on the line codec (the Lisp printer and reader), as hypotheses:
  * `enc a` contains no newline;
  * the reader accepts a complete record, also with zeros after it (READ-FROM-STRING stops
    at the closing parenthesis);
  * it rejects any proper prefix of a record, zeros after it or not (an s-expression cut
    anywhere lacks its closing parenthesis), and so a line of zeros or an empty line.

`anchors_safe`: in every reachable state the parsed verdicts contain every verdict whose
append completed (fsync returned), in order, and nothing that was never appended.
-/

def nl : Nat := 10

def consHead (b : Nat) : List Bytes → List Bytes
  | l :: ls => (b :: l) :: ls
  | []      => [[b]]

/-- Split on newline; the final (possibly empty) segment is a line too. -/
def lines : Bytes → List Bytes
  | []      => [[]]
  | b :: bs => if b = nl then [] :: lines bs else consHead b (lines bs)

theorem lines_ne_nil (x : Bytes) : lines x ≠ [] := by
  cases x with
  | nil => simp [lines]
  | cons b bs =>
    simp only [lines]; split
    · simp
    · cases lines bs <;> simp [consHead]

theorem consHead_append (b : Nat) {l : List Bytes} (m : List Bytes) (hl : l ≠ []) :
    consHead b (l ++ m) = consHead b l ++ m := by
  cases l with
  | nil => exact absurd rfl hl
  | cons x xs => simp [consHead]

theorem lines_append_nl (x y : Bytes) : lines (x ++ nl :: y) = lines x ++ lines y := by
  induction x with
  | nil => simp [lines]
  | cons b x ih =>
    simp only [List.cons_append, lines]
    split
    · simp [ih]
    · rw [ih, consHead_append _ _ (lines_ne_nil x)]

theorem lines_no_nl {y : Bytes} (h : nl ∉ y) : lines y = [y] := by
  induction y with
  | nil => simp [lines]
  | cons b y ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [lines, Ne.symm h.1, ite_false, ih h.2, consHead]

/-- A file of complete lines `Ls` followed by a partial last line `T`. -/
def render (Ls : List Bytes) (T : Bytes) : Bytes := (Ls.map (· ++ [nl])).flatten ++ T

theorem lines_render {Ls : List Bytes} {T : Bytes} (hL : ∀ l ∈ Ls, nl ∉ l) (hT : nl ∉ T) :
    lines (render Ls T) = Ls ++ [T] := by
  induction Ls with
  | nil => simp [render, lines_no_nl hT]
  | cons l Ls ih =>
    have h1 : nl ∉ l := hL l List.mem_cons_self
    have h2 : ∀ l' ∈ Ls, nl ∉ l' := fun l' h => hL l' (List.mem_cons_of_mem _ h)
    have : render (l :: Ls) T = l ++ nl :: render Ls T := by simp [render]
    rw [this, lines_append_nl, lines_no_nl h1, ih h2]; rfl

section Anchors
variable (enc : Anchor → Bytes) (dec : Bytes → Option Anchor)

structure Codec : Prop where
  no_nl : ∀ a, nl ∉ enc a
  full  : ∀ a j, dec (enc a ++ List.replicate j 0) = some a
  part  : ∀ a m j, m < (enc a).length → dec ((enc a).take m ++ List.replicate j 0) = none
  zeros : ∀ j, dec (List.replicate j 0) = none

/-- `read-anchors`: every line that parses. -/
def parse (d : Bytes) : List Anchor := (lines d).filterMap dec

/-- `append-anchor!`'s fresh line: a newline first iff the file is non-empty and does not
    end with one. -/
def sep (d : Bytes) : Bytes :=
  match d.getLast? with
  | none   => []
  | some x => if x = nl then [] else [nl]

/-- What a torn last line can look like: a prefix of a record, then zeros. -/
def TailOK (T : Bytes) : Prop :=
  ∃ b m j, m ≤ (enc b).length ∧ T = (enc b).take m ++ List.replicate j 0

variable {enc dec}

theorem tail_no_nl (hc : Codec enc dec) {T : Bytes} (h : TailOK enc T) : nl ∉ T := by
  obtain ⟨b, m, j, -, rfl⟩ := h
  simp only [List.mem_append, List.mem_replicate, not_or]
  exact ⟨fun hm => hc.no_nl b (List.mem_of_mem_take hm), by simp [nl]⟩

theorem dec_tail_zeros (hc : Codec enc dec) {T : Bytes} (h : TailOK enc T) (j : Nat) :
    dec (T ++ List.replicate j 0) = dec T ∧ TailOK enc (T ++ List.replicate j 0) := by
  obtain ⟨b, m, j0, hm, rfl⟩ := h
  refine ⟨?_, ⟨b, m, j0 + j, hm, by simp [← List.replicate_append_replicate]⟩⟩
  rw [List.append_assoc, List.replicate_append_replicate]
  rcases Nat.lt_or_ge m (enc b).length with hlt | hge
  · rw [hc.part _ _ _ hlt, hc.part _ _ _ hlt]
  · have : m = (enc b).length := by omega
    subst this; simp only [List.take_length]; rw [hc.full, hc.full]

theorem parse_render {Ls : List Bytes} {T : Bytes}
    (hL : ∀ l ∈ Ls, nl ∉ l) (hT : nl ∉ T) :
    parse dec (render Ls T) = Ls.filterMap dec ++ (dec T).toList := by
  simp only [parse, lines_render hL hT, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil]
  cases dec T <;> simp

theorem dec_nil (hc : Codec enc dec) : dec [] = none := hc.zeros 0

/-- Closing the partial line: `render Ls T ++ sep (render Ls T)` is all complete lines. -/
def close (Ls : List Bytes) (T : Bytes) : List Bytes := if T = [] then Ls else Ls ++ [T]

theorem render_sep {Ls : List Bytes} {T : Bytes} (hT : nl ∉ T) :
    render Ls T ++ sep (render Ls T) = render (close Ls T) [] := by
  by_cases h0 : T = []
  · subst h0
    simp only [close, ite_true]
    rcases List.eq_nil_or_concat Ls with rfl | ⟨L, l, rfl⟩
    · simp [render, sep]
    · simp [render, sep, nl]
  · obtain ⟨T0, t, rfl⟩ := (List.eq_nil_or_concat T).resolve_left h0
    have ht : t ≠ nl := fun e => hT (by simp [e])
    simp [render, sep, close, ht]

theorem parse_close (hc : Codec enc dec) {Ls : List Bytes} {T : Bytes}
    (hL : ∀ l ∈ Ls, nl ∉ l) (hT : nl ∉ T) :
    parse dec (render Ls T) = (close Ls T).filterMap dec ∧ ∀ l ∈ close Ls T, nl ∉ l := by
  rw [parse_render hL hT]
  by_cases h0 : T = []
  · subst h0; simp only [close, ite_true]; exact ⟨by simp [dec_nil hc], hL⟩
  · simp only [close, h0, ite_false, List.filterMap_append, List.filterMap_cons,
      List.filterMap_nil, List.mem_append, List.mem_singleton]
    refine ⟨by cases dec T <;> simp, ?_⟩
    rintro l (hl | rfl)
    · exact hL l hl
    · exact hT

theorem render_snoc (Ls : List Bytes) (l : Bytes) :
    render Ls [] ++ (l ++ [nl]) = render (Ls ++ [l]) [] := by
  simp [render]

theorem close_nl {Ls : List Bytes} {T : Bytes} (hL : ∀ l ∈ Ls, nl ∉ l) (hT : nl ∉ T) :
    ∀ l ∈ close Ls T, nl ∉ l := by
  intro l hl
  unfold close at hl; split at hl
  · exact hL l hl
  · rcases List.mem_append.1 hl with h | h
    · exact hL l h
    · simp at h; subst h; exact hT

/-- A completed append adds exactly the record, whatever the torn tail before it was. -/
theorem parse_append_rec (hc : Codec enc dec) {Ls : List Bytes} {T : Bytes} (a : Anchor)
    (hL : ∀ l ∈ Ls, nl ∉ l) (hT : TailOK enc T) :
    parse dec (render Ls T ++ sep (render Ls T) ++ (enc a ++ [nl])) =
      parse dec (render Ls T) ++ [a] := by
  have hT' := tail_no_nl hc hT
  have ⟨hp, hcl⟩ := parse_close hc hL hT'
  have hfa : dec (enc a) = some a := by simpa using hc.full a 0
  rw [render_sep hT', render_snoc, parse_render, hp]
  · simp [hfa, dec_nil hc]
  · intro l hl
    rcases List.mem_append.1 hl with h | h
    · exact hcl l h
    · simp at h; subst h; exact hc.no_nl a
  · simp

theorem render_tail (Ls : List Bytes) (T U : Bytes) : render Ls T ++ U = render Ls (T ++ U) := by
  simp [render]

theorem render_split (Ls : List Bytes) (T : Bytes) : render Ls T = render Ls [] ++ T := by
  simp [render]

theorem sub_finish {c P att : List Anchor} {a : Anchor} (X : List Anchor)
    (hcom : c.Sublist P) (hatt : (P ++ [a]).Sublist att) (hX : X = [] ∨ X = [a]) :
    c.Sublist (P ++ X) ∧ (P ++ X ++ (none : Option Anchor).toList).Sublist att := by
  refine ⟨hcom.trans (List.sublist_append_left _ _), ?_⟩
  rcases hX with rfl | rfl
  · simpa using (List.sublist_append_left P [a]).trans hatt
  · simpa using hatt

structure AState where
  data      : Bytes
  synced    : Nat
  inflight  : Option Anchor
  committed : List Anchor   -- ghost: appends whose fsync returned
  attempted : List Anchor   -- ghost: every append ever begun

variable (enc) in
/-- `append-anchor!` (write the line, fsync) and crashes, which tear the unsynced tail. -/
inductive AStep : AState → AState → Prop
  | begin (st : AState) (a : Anchor) (h : st.inflight = none) :
      AStep st { st with data := st.data ++ sep st.data ++ (enc a ++ [nl]),
                         inflight := some a, attempted := st.attempted ++ [a] }
  | fsync (st : AState) (a : Anchor) (h : st.inflight = some a) :
      AStep st { st with synced := st.data.length, inflight := none,
                         committed := st.committed ++ [a] }
  | crash (st : AState) (k j : Nat) (hk : st.synced ≤ k) (hkj : k + j ≤ st.data.length) :
      AStep st { st with data := st.data.take k ++ List.replicate j 0, synced := k + j,
                         inflight := none }

def inflightBytes (enc : Anchor → Bytes) (D : Bytes) : Option Anchor → Bytes
  | none   => []
  | some a => sep D ++ (enc a ++ [nl])

variable (enc dec) in
def AInv (st : AState) : Prop :=
  ∃ Ls T, (∀ l ∈ Ls, nl ∉ l) ∧ TailOK enc T ∧ st.synced = (render Ls T).length ∧
    st.data = render Ls T ++ inflightBytes enc (render Ls T) st.inflight ∧
    st.committed.Sublist (parse dec (render Ls T)) ∧
    (parse dec (render Ls T) ++ st.inflight.toList).Sublist st.attempted

theorem tailOK_nil (a : Anchor) : TailOK enc [] := ⟨a, 0, 0, by simp, by simp⟩

theorem ainv_step (hc : Codec enc dec) {st st' : AState} (h : AStep enc st st')
    (hi : AInv enc dec st) : AInv enc dec st' := by
  obtain ⟨Ls, T, hL, hT, hs, hd, hcom, hatt⟩ := hi
  have hT' := tail_no_nl hc hT
  cases h with
  | begin a hn =>
    refine ⟨Ls, T, hL, hT, hs, ?_, hcom, ?_⟩
    · simp only [hn, inflightBytes, List.append_nil] at hd ⊢; rw [hd]; simp
    · simp only [hn, Option.toList, List.append_nil] at hatt ⊢
      exact hatt.append (List.Sublist.refl _)
  | fsync a ha =>
    have ⟨hp, hcl⟩ := parse_close hc hL hT'
    refine ⟨close Ls T ++ [enc a], [], ?_, tailOK_nil a, ?_, ?_, ?_, ?_⟩
    · intro l hl
      rcases List.mem_append.1 hl with h | h
      · exact hcl l h
      · simp at h; subst h; exact hc.no_nl a
    · simp only [ha, inflightBytes] at hd
      rw [hd, ← render_snoc, ← render_sep hT', List.append_assoc]
    · simp only [ha, inflightBytes] at hd; simp [inflightBytes]
      rw [hd, ← render_snoc, ← render_sep hT', List.append_assoc]
    · dsimp only
      rw [← render_snoc, ← render_sep hT', parse_append_rec hc a hL hT]
      exact hcom.append (List.Sublist.refl _)
    · dsimp only
      rw [← render_snoc, ← render_sep hT', parse_append_rec hc a hL hT]
      simpa [ha] using hatt
  | crash k j hk hkj =>
    cases hfl : st.inflight with
    | none =>
      simp only [hfl, inflightBytes, List.append_nil] at hd
      rw [hd] at hkj ⊢
      have hk' : k = (render Ls T).length := by omega
      have hj : j = 0 := by omega
      subst hj hk'
      refine ⟨Ls, T, hL, hT, by simp, by simp [inflightBytes], hcom, by simpa [hfl] using hatt⟩
    | some a =>
      simp only [hfl, inflightBytes] at hd hatt
      have ⟨hp, hcl⟩ := parse_close hc hL hT'
      have hC := render_sep (Ls := Ls) hT'
      have hkD : (render Ls T).length ≤ k := hs ▸ hk
      by_cases hA : k < (render Ls T ++ sep (render Ls T)).length
      · -- torn before the fresh newline: the old partial line just gains zeros
        have hk' : k = (render Ls T).length := by simp at hA; unfold sep at hA; split at hA <;> (try split at hA) <;> simp at hA <;> omega
        have hdata : st.data.take k = render Ls T := by
          rw [hd, hk', ← List.append_assoc, List.take_append_of_le_length (by simp)]
          rw [List.take_append_of_le_length (Nat.le_refl _), List.take_of_length_le (Nat.le_refl _)]
        have ⟨hdz, hTz⟩ := dec_tail_zeros hc hT j
        refine ⟨Ls, T ++ List.replicate j 0, hL, hTz, ?_, ?_, ?_, ?_⟩
        · have : (render Ls (T ++ List.replicate j 0)).length = (render Ls T).length + j := by
            rw [← render_tail]; simp
          dsimp only; omega
        · dsimp only; rw [hdata]; simp [inflightBytes, render]
        · rw [parse_render hL (tail_no_nl hc hTz), hdz, ← parse_render hL hT']; exact hcom
        · rw [parse_render hL (tail_no_nl hc hTz), hdz, ← parse_render hL hT']
          simpa using (List.sublist_append_left _ [a]).trans hatt
      · -- the newline (if any) is on disk: the record line is cut at u bytes
        have hlen : (render (close Ls T) []).length ≤ k := by rw [← hC]; omega
        have hd' : st.data = render (close Ls T) [] ++ (enc a ++ [nl]) := by
          rw [hd, ← List.append_assoc, hC]
        have hkj' : k + j ≤ (render (close Ls T) []).length + (enc a).length + 1 := by
          rw [hd'] at hkj; simpa [Nat.add_assoc] using hkj
        have htake : st.data.take k = render (close Ls T) [] ++
            (enc a ++ [nl]).take (k - (render (close Ls T) []).length) := by
          rw [hd', List.take_append, List.take_of_length_le hlen]
        have hfa : dec (enc a) = some a := by simpa using hc.full a 0
        by_cases hu : k - (render (close Ls T) []).length ≤ (enc a).length
        · -- torn inside the record (or right before its newline)
          generalize hU : k - (render (close Ls T) []).length = u at hu htake
          rw [List.take_append_of_le_length hu] at htake
          have hT2 : TailOK enc ((enc a).take u ++ List.replicate j 0) := ⟨a, u, j, hu, rfl⟩
          refine ⟨close Ls T, (enc a).take u ++ List.replicate j 0, hcl, hT2, ?_, ?_, ?_⟩
          · have : (render (close Ls T) ((enc a).take u ++ List.replicate j 0)).length =
                (render (close Ls T) []).length + u + j := by
              rw [render_split]; simp; omega
            dsimp only; omega
          · dsimp only; rw [htake]; simp [inflightBytes, render]
          · have hP : parse dec (render (close Ls T) ((enc a).take u ++ List.replicate j 0)) =
                parse dec (render Ls T) ++ (dec ((enc a).take u ++ List.replicate j 0)).toList := by
              rw [parse_render hcl (tail_no_nl hc hT2), hp]
            rw [hP]
            apply sub_finish _ hcom hatt
            rcases Nat.lt_or_ge u (enc a).length with hlt | hge
            · left; rw [hc.part _ _ _ hlt]; rfl
            · right; have : u = (enc a).length := by omega
              subst this; rw [List.take_length, hc.full]; rfl
        · -- the whole line is on disk; only zeros may follow
          have hu1 : k - (render (close Ls T) []).length = (enc a).length + 1 := by omega
          rw [hu1, List.take_of_length_le (l := enc a ++ [nl]) (by simp)] at htake
          have hcl2 : ∀ l ∈ close Ls T ++ [enc a], nl ∉ l := by
            intro l hl; rcases List.mem_append.1 hl with h | h
            · exact hcl l h
            · simp at h; subst h; exact hc.no_nl a
          have hT2 : TailOK enc (List.replicate j 0) := ⟨a, 0, j, by simp, by simp⟩
          refine ⟨close Ls T ++ [enc a], List.replicate j 0, hcl2, hT2, ?_, ?_, ?_⟩
          · have : (render (close Ls T ++ [enc a]) (List.replicate j 0)).length =
                (render (close Ls T) []).length + (enc a).length + 1 + j := by
              rw [render_split, ← render_snoc]; simp; omega
            dsimp only; omega
          · dsimp only; rw [htake]; simp [inflightBytes, render]
          · have hP : parse dec (render (close Ls T ++ [enc a]) (List.replicate j 0)) =
                parse dec (render Ls T) ++ [a] := by
              rw [parse_render hcl2 (tail_no_nl hc hT2), hp]; simp [hfa, hc.zeros]
            rw [hP]; exact sub_finish [a] hcom hatt (Or.inr rfl)

variable (enc) in
inductive AReach : AState → Prop
  | init : AReach ⟨[], 0, none, [], []⟩
  | step {st st'} : AReach st → AStep enc st st' → AReach st'

/-- anchors.sexp under crashes: what `read-anchors` returns, in every reachable state, keeps
    every verdict whose fsync returned, in order, and invents none. With F2 this is the
    durable half of I1: a verified block, once its verdict is durable, stays verified. -/
theorem anchors_safe (hc : Codec enc dec) {st : AState} (h : AReach enc st) :
    st.committed.Sublist (parse dec st.data) ∧ (parse dec st.data).Sublist st.attempted := by
  have hi : AInv enc dec st := by
    induction h with
    | init => exact ⟨[], [], by simp, tailOK_nil ⟨0, false, none⟩, rfl, rfl, by simp [parse,
        lines, render, dec_nil hc], by simp [parse, lines, render, dec_nil hc]⟩
    | step _ hs ih => exact ainv_step hc hs ih
  obtain ⟨Ls, T, hL, hT, -, hd, hcom, hatt⟩ := hi
  cases hfl : st.inflight with
  | none =>
    simp only [hfl, inflightBytes, List.append_nil, Option.toList] at hd hatt
    rw [hd]; exact ⟨hcom, by simpa using hatt⟩
  | some a =>
    simp only [hfl, inflightBytes] at hd hatt
    rw [hd, ← List.append_assoc, parse_append_rec hc a hL hT]
    exact ⟨hcom.trans (List.sublist_append_left _ _), by simpa using hatt⟩

end Anchors

/-! ## Part 4 — putting the layers together -/

/-- Bounded loss: a block whose verdict is durable and whose dump is in the view is never
    behind the resume point. Combined with `anchors_safe` (the verdict survives) and
    `durable_binding_survives` (the dump survives), a crash loses at most the work since the
    last checkpoint whose verdict and directory entry were made durable. -/
theorem resume_ge {as : List Anchor} {ds : List Dump} {b : Nat}
    (hv : b ∈ verified as) (hs : (b, DumpStatus.sealed) ∈ ds) :
    ∃ r, resumePoint as ds = .block r ∧ b ≤ r := by
  have hb := mem_candidates.2 ⟨hv, hs⟩
  obtain ⟨r, hr⟩ := resume_of_candidate hb
  exact ⟨r, hr, resume_max hr hv hs⟩

/-- A name whose binding was made durable (directory fsynced, not changed since) keeps it
    across a crash. -/
theorem durable_binding_survives {fs fs' : FS} {n : Name} (hc : Crash fs fs')
    (h : fs.live n = fs.durable n) : fs'.live n = fs.live n := by
  rcases hc.1 n with e | e
  · rw [e, h]
  · exact e

/-- The resume point's dump is exactly the dump the checkpoint wrote. Instantiate
    `published_good` with `Good b c := c = goodDump b` (the writer only ever publishes the
    serialization of the replayed state at `b`); the view lists a sealed dump at `b` only
    for a bound `state-b.txt`. Then the state the replay resumes from is `goodDump r`,
    and `r` is the highest verified such block: I1 and I3 at once, under any interleaving
    of checkpoints, GC, quarantines and crashes. -/
theorem resume_dump_good (goodDump : Nat → Bytes) {st : FS × Pc}
    (hreach : Reach (fun b c => c = goodDump b) st)
    {as : List Anchor} {ds : List Dump}
    (hview : ∀ b, (b, DumpStatus.sealed) ∈ ds → ∃ i, st.1.live (.pub b) = some i)
    {r : Nat} (hr : resumePoint as ds = .block r) :
    r ∈ verified as ∧ ∃ i, st.1.live (.pub r) = some i ∧ (st.1.inode i).data = goodDump r := by
  obtain ⟨hv, hs⟩ := resume_sound hr
  obtain ⟨i, hi⟩ := hview r hs
  exact ⟨hv, i, hi, (published_good _ hreach (Or.inl hi)).1⟩

/-- The committed frontier (I5): instantiate `published_good` with
    `Good _ c := ∃ n, gated n ∧ c = enc n`. Whatever survives a crash, the marker names a
    block whose header gate passed — never a torn or empty file, never one ahead. -/
theorem committed_gated (gated : Nat → Prop) (encN : Nat → Bytes) {st : FS × Pc}
    (hreach : Reach (fun _ c => ∃ n, gated n ∧ c = encN n) st) {i : Nat}
    (hb : Bound st.1 (.pub 0) i) : ∃ n, gated n ∧ (st.1.inode i).data = encN n :=
  (published_good _ hreach hb).1

/-! ## Part 5 — which code wrote which rows (I4)

A fact-log shard records, per segment, the version of the code that wrote its rows:
`segs = [(b₀, v₀), (b₁, v₁), …]` means rows from block `bᵢ` on (until the next segment)
came from `vᵢ`. A later run skips a sealed shard only if every segment is the running
version (`allCurrent`; an unknown running version — `none` — never skips). A resume at
`R` inside a shard keeps the rows of blocks `≤ R` (no state before `R` exists to
re-derive them), so it keeps their segments (`clip`) and appends the running version from
`R+1` (`extend`). The Lisp mirrors these as `factlog-versions-current-p`,
`factlog-versions-upto` and `factlog-versions-extend` (src/evm/). The
theorems: a skipped shard was written wholly by the running code (`skip_current`); after
a resume, every row above `R` is attributed to the running code (`resume_rows_current`)
and every row at or below it keeps its attribution (`resume_rows_kept`). Together: every
row of a block `> R` that the run leaves on disk comes from the code that is running —
I4 for the shards the run touches. -/

section Versions

variable {V : Type} [DecidableEq V]

abbrev Segs (V : Type) := List (Nat × V)

/-- The version that wrote the row of block `b`: the last segment starting at or before it. -/
def verOf (segs : Segs V) (b : Nat) : Option V :=
  ((segs.filter (fun s => decide (s.1 ≤ b))).getLast?).map (·.2)

/-- `factlog-versions-current-p`. -/
def allCurrent (cur : Option V) (segs : Segs V) : Bool :=
  match cur with
  | none => false
  | some c => !segs.isEmpty && segs.all (fun s => decide (s.2 = c))

/-- `factlog-versions-upto`. -/
def clip (segs : Segs V) (n : Nat) : Segs V := segs.filter (fun s => decide (s.1 ≤ n))

/-- `factlog-versions-extend`. -/
def extend (c : V) (segs : Segs V) (b : Nat) : Segs V :=
  match segs.getLast? with
  | some (_, v) => if v = c then segs else segs ++ [(b, c)]
  | none => segs ++ [(b, c)]

theorem unknown_never_skips (segs : Segs V) : allCurrent none segs = false := rfl

theorem skip_current {c : V} {segs : Segs V} (h : allCurrent (some c) segs = true)
    {b : Nat} {v : V} (hv : verOf segs b = some v) : v = c := by
  simp only [allCurrent, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  simp only [verOf, Option.map_eq_some_iff] at hv
  obtain ⟨s, hs, rfl⟩ := hv
  have hmem : s ∈ segs := (List.mem_filter.1 (List.mem_of_getLast? hs)).1
  exact h.2 s hmem

theorem getLast?_append_singleton (l : List α) (a : α) : (l ++ [a]).getLast? = some a := by
  simp

/-- A run that resumed at `R` and wrote rows from `R+1` on: every row of a block above `R`
    is attributed to the running code, whatever the kept prefix's segments were. -/
theorem resume_rows_current (c : V) (p : Segs V) (R b : Nat) (hb : R < b) :
    verOf (extend c (clip p R) (R + 1)) b = some c := by
  have hall : ∀ s ∈ clip p R, s.1 ≤ b := fun s hs => by
    have := (List.mem_filter.1 hs).2; simp at this; omega
  have hkeep : (clip p R).filter (fun s => decide (s.1 ≤ b)) = clip p R :=
    List.filter_eq_self.2 (fun s hs => by simpa using hall s hs)
  unfold extend
  split
  · rename_i _ v hl
    split
    · rename_i hvc
      simp only [verOf, hkeep, hl, Option.map_some, hvc]
    · simp only [verOf, List.filter_append, hkeep]
      have : decide (R + 1 ≤ b) = true := by simp; omega
      simp [List.filter, this]
  · simp only [verOf, List.filter_append, hkeep]
    have : decide (R + 1 ≤ b) = true := by simp; omega
    simp [List.filter, this]

/-- ... and every row at or below `R` keeps the attribution it had before the resume. -/
theorem resume_rows_kept (c : V) (p : Segs V) (R b : Nat) (hb : b ≤ R) :
    verOf (extend c (clip p R) (R + 1)) b = verOf p b := by
  have hclip : (clip p R).filter (fun s => decide (s.1 ≤ b)) = p.filter (fun s => decide (s.1 ≤ b)) := by
    simp only [clip, List.filter_filter]
    apply List.filter_congr
    intro s _
    by_cases h : s.1 ≤ b
    · have : s.1 ≤ R := by omega
      simp [h, this]
    · simp [h]
  have hnot : decide (R + 1 ≤ b) = false := by simp; omega
  unfold extend
  split
  · split
    · simp only [verOf, hclip]
    · simp only [verOf, List.filter_append, hclip, List.filter, hnot, List.append_nil]
  · simp only [verOf, List.filter_append, hclip, List.filter, hnot, List.append_nil]

end Versions

end Evm.Persist.Recovery
