import Evm.CL.JournalSpec
import Evm.Parallel.Scheduler

/-! # Evm/Parallel/BlockSTM — Block-STM parallel execution, SPECIFIED to refine sequential EELS

A parallel EVM is only a client if its parallel result is **provably identical** to
canonical sequential execution — otherwise it is a consensus split, and the bug is a
specific interleaving no test will hit. So, in the project's spec-first idiom (the way
JIT chunks, gas, and host decisions are derived from Lean), Block-STM is SPECIFIED here
and proven to refine `seqExec`; the threaded executor is then DERIVED from this spec.

THE LAYERING (the load-bearing insight):
  • CORRECTNESS needs NO commutativity. Block-STM is optimistic: run txs in parallel
    against a multi-version memory, then VALIDATE each tx's reads; a tx that read a value
    a lower-index tx later wrote is RE-EXECUTED. The safety theorem `blockSTM_refines_seq`
    says: any schedule whose committed reads agree with the sequential prefix (= validation
    passed) + deterministic txs ⇒ the committed state equals `seqExec`. Validation, not
    commutativity, is what makes it sound.
  • COMMUTATIVITY is the PERFORMANCE layer. `commute_disjoint` (the WETH `deposit_comm`
    result, lifted off WETH) and the system-account commutative pass (coinbase / OP fee
    vaults — the empirically-measured `FULL = 1.00×` collapse) justify SKIPPING false-conflict
    aborts. They can be tuned freely without ever endangering correctness.
  • ROLLBACK on abort is `Evm.CL.JournalSpec.undo_runWrites` (shipped #236): reverting a
    re-executed tx's writes restores the pre-tx storage exactly.
  • LIVENESS (the optimistic loop terminates) is a SEPARATE obligation — per the
    safety≠liveness discipline, removing sequential ordering needs its own termination proof.

Storage is modelled as `Key → Val` over `Nat` (as in JournalSpec): the refinement argument
is structural and bit-width-independent. The real instance plugs in EELS `State` + the
#262 R/W footprint as the runtime witness of `Tx.reads` / `Tx.writeKeys`.

COMPANION MODULES (2026-10-25):
  • `Evm.Parallel.Reads`     — reads DISCOVERED and logged (not declared), validation over
    the read log, commutative DELTAS for the coinbase fee credit, fact/receipt determinism,
    version-validation soundness. The declared-footprint model here is kept as the
    simpler statement; `Reads` is the one the executor is derived from.
  • `Evm.Parallel.Scheduler` — the incarnation transition system; `schedule_terminates`
    below is its bound.
  • `Evm.CL.JournalSpec`     — `abort_restores_prestate` below is its `undo_runWrites`.
-/

namespace Evm.Parallel.BlockSTM

abbrev Key : Type := Nat
abbrev Val : Type := Nat
abbrev Storage : Type := Key → Val

def store (s : Storage) (k : Key) (v : Val) : Storage := fun x => if x = k then v else s x

@[simp] theorem store_get_eq (s : Storage) (k : Key) (v : Val) : store s k v k = v := by
  simp [store]

/-- A transaction: its declared READ footprint and its EFFECT (the writes it produces as a
    function of the storage it reads). The runtime witness of both is the #262 R/W set. -/
structure Tx where
  reads  : List Key
  effect : Storage → List (Key × Val)

/-- Apply a write list left-to-right (later writes to the same key win). -/
def applyWrites : Storage → List (Key × Val) → Storage
  | s, []           => s
  | s, (k, v) :: ws => applyWrites (store s k v) ws

/-- A tx's sequential effect: read the live state, compute writes, apply them. -/
def Tx.run (t : Tx) (s : Storage) : Storage := applyWrites s (t.effect s)

/-- Canonical sequential block execution — THE reference (the EELS fold). -/
def seqExec (txs : List Tx) (σ : Storage) : Storage :=
  txs.foldl (fun s t => t.run s) σ

/-- Determinism on footprint: a tx's writes depend ONLY on its declared read keys. This is
    what optimistic re-execution relies on (re-running with the same reads ⇒ same writes). -/
def Tx.WellFormed (t : Tx) : Prop :=
  ∀ s s', (∀ k, k ∈ t.reads → s k = s' k) → t.effect s = t.effect s'

/-- The keys a tx writes given the state it read. -/
def Tx.writeKeys (t : Tx) (s : Storage) : List Key := (t.effect s).map Prod.fst

/-- Two txs CONFLICT (at the state each reads): one writes a key the other reads or writes.
    The conflict-graph edge; `scripts/conflict-graph.py` measures its critical path. -/
def Conflict (a b : Tx) (sa sb : Storage) : Prop :=
  (∃ k, k ∈ a.writeKeys sa ∧ (k ∈ b.reads ∨ k ∈ b.writeKeys sb)) ∨
  (∃ k, k ∈ b.writeKeys sb ∧ (k ∈ a.reads ∨ k ∈ a.writeKeys sa))

/-! ## The multi-version view and the validation predicate -/

/-- The view tx `i` is OBLIGED to see: the storage produced by the sequential prefix. A
    schedule whose committed reads match this is exactly one Block-STM's read-validation
    accepts (anything else is re-executed). Threaded through `s` so it coincides with the
    running sequential state once `WellFormed` is in play. -/
def ScheduleValidFrom (view : Nat → Storage) : Storage → Nat → List Tx → Prop
  | _, _, []      => True
  | s, i, t :: ts =>
      (∀ k, k ∈ t.reads → view i k = s k) ∧
      ScheduleValidFrom view (applyWrites s (t.effect (view i))) (i+1) ts

/-- Assemble the committed final storage: apply each tx in index order, but each tx's WRITES
    are the ones it computed against its own committed `view i` (what the parallel run did). -/
def commitFrom (view : Nat → Storage) : Storage → Nat → List Tx → Storage
  | s, _, []      => s
  | s, i, t :: ts => commitFrom view (applyWrites s (t.effect (view i))) (i+1) ts

def commitFold (txs : List Tx) (σ : Storage) (view : Nat → Storage) : Storage :=
  commitFrom view σ 0 txs

/-! ## Safety: a validated schedule equals sequential execution -/

/-- **Helper.** With WellFormed txs and a validated schedule, the committed fold coincides
    with the sequential fold from any starting point — because each tx's writes computed
    against its (validated) view equal its writes against the live state. -/
theorem commitFrom_eq_seq
    (view : Nat → Storage) :
    ∀ (txs : List Tx) (s : Storage) (i : Nat),
      (∀ t ∈ txs, t.WellFormed) →
      ScheduleValidFrom view s i txs →
      commitFrom view s i txs = txs.foldl (fun a t => t.run a) s := by
  intro txs
  induction txs with
  | nil => intro s i _ _; rfl
  | cons t ts ih =>
      intro s i wf valid
      have wft : t.WellFormed := wf t (by simp)
      have wfts : ∀ x ∈ ts, x.WellFormed := fun x hx => wf x (by simp [hx])
      obtain ⟨hread, hrest⟩ := valid
      -- tx t's writes against its view = its writes against s (WellFormed + read-agreement)
      have heff : t.effect (view i) = t.effect s := by
        apply wft; intro k hk; exact (hread k hk)
      -- both sides take one step to the SAME state, then recurse
      simp only [commitFrom, List.foldl_cons, Tx.run, heff]
      -- the recursive validated schedule from the stepped state matches
      have hrest' : ScheduleValidFrom view (applyWrites s (t.effect s)) (i+1) ts := by
        simpa [heff] using hrest
      simpa using ih (applyWrites s (t.effect s)) (i+1) wfts hrest'

/-- **Block-STM refines sequential execution (SAFETY).** Any validated schedule — i.e. every
    committed tx read, on its footprint, exactly the sequential-prefix values, which is what
    read-validation enforces — over deterministic txs produces the SAME final storage as the
    canonical sequential fold. Commutativity is NOT used; validation alone is sound. -/
theorem blockSTM_refines_seq
    (txs : List Tx) (σ : Storage) (view : Nat → Storage)
    (wf : ∀ t ∈ txs, t.WellFormed)
    (valid : ScheduleValidFrom view σ 0 txs) :
    commitFold txs σ view = seqExec txs σ :=
  commitFrom_eq_seq view txs σ 0 wf valid

/-- **Validation is NECESSARY (the bug is real).** Drop validation — let a tx commit against a
    STALE view that missed an earlier write — and the parallel result DIVERGES from sequential.
    Mirrors `JournalSpec.dropped_entry_is_wrong`: the safety theorem's hypothesis is load-bearing,
    not decoration. Witness: tx0 writes slot0:=5; tx1 reads slot0 and copies it to slot1. -/
theorem unvalidated_schedule_diverges :
    ∃ (txs : List Tx) (σ : Storage) (badview : Nat → Storage),
      commitFold txs σ badview ≠ seqExec txs σ := by
  refine ⟨[⟨[], fun _ => [(0, 5)]⟩, ⟨[0], fun s => [(1, s 0)]⟩], (fun _ => 0),
          (fun _ => (fun _ => 0)), ?_⟩
  intro h
  have := congrFun h 1
  simp [commitFold, commitFrom, seqExec, applyWrites, store, Tx.run] at this

/-! ## The operational obligations (the spec the executor is derived from)

Until 2026-10-25 the two theorems `schedule_terminates` and `abort_restores_prestate` below
were `True := trivial` — invisible to `#print axioms`, worse than a `sorry`. They are now
real statements with proofs (Scheduler.lean, JournalSpec.lean). -/

/-! ### The operational layer: multi-version memory and its fixpoint

`blockSTM_refines_seq` ASSUMED each tx read the sequential prefix (`ScheduleValidFrom`). The
optimistic protocol ACHIEVES that with a multi-version memory: tx `i` reads the accumulated
writes of all txs below it, records its own writes, and read-VALIDATION re-checks that no
lower-index tx has since changed a key it read (RE-EXECUTING if so). A SETTLED memory — the
loop's fixpoint, where every tx's recorded writes already match its current view, so no
re-execution is pending — is what the executor commits. We prove a settled memory commits
exactly `seqExec`. So `ScheduleValidFrom` is a CONSEQUENCE of the fixpoint, not an assumption:
validation, not commutativity, delivers consensus-correctness. (Reaching the fixpoint is
`schedule_terminates` — liveness, separate.) -/

/-- `mv i` = the writes tx `i` recorded into the multi-version memory. `mvCommit` is the
    committed final storage: recorded writes applied in index order (a later tx's write to a
    key shadows an earlier one — the MV "latest version" rule, expressed as a fold). -/
def mvCommit (mv : Nat → List (Key × Val)) : Storage → Nat → List Tx → Storage
  | s, _, []      => s
  | s, i, _ :: ts => mvCommit mv (applyWrites s (mv i)) (i+1) ts

/-- SETTLED — the optimistic loop's fixpoint: every tx's RECORDED writes already equal the
    writes it WOULD compute reading the memory accumulated below it, so read-validation passes
    for all and nothing is pending re-execution. `s` threads that accumulated MV view. -/
def SettledFrom (mv : Nat → List (Key × Val)) : Storage → Nat → List Tx → Prop
  | _, _, []      => True
  | s, i, t :: ts => mv i = t.effect s ∧ SettledFrom mv (applyWrites s (mv i)) (i+1) ts

/-- **OPERATIONAL refinement (validation ⇒ sequential).** A SETTLED multi-version memory
    commits exactly the sequential result. This DISCHARGES the `ScheduleValidFrom` assumption
    of `blockSTM_refines_seq`: at the fixpoint each tx's view IS the sequential prefix (the
    threaded `s`), so the committed fold equals `seqExec`. The optimistic exec/validate/
    re-execute loop is sound the instant it stops — independent of commutativity. -/
theorem settled_refines_seq :
    ∀ (mv : Nat → List (Key × Val)) (txs : List Tx) (s : Storage) (i : Nat),
      SettledFrom mv s i txs →
      mvCommit mv s i txs = txs.foldl (fun a t => t.run a) s := by
  intro mv txs
  induction txs with
  | nil => intro s i _; rfl
  | cons t ts ih =>
      intro s i settled
      obtain ⟨hmv, hrest⟩ := settled
      simp only [mvCommit, List.foldl_cons, Tx.run, hmv]
      exact ih (applyWrites s (t.effect s)) (i+1) (by simpa [hmv] using hrest)

/-- **LIVENESS** (safety ≠ liveness). The optimistic loop over `txs` reaches a fixpoint:
    every run of the abstract scheduler (`Evm.Parallel.Scheduler`: a tx is re-executed only
    on its first run or after a lower-index tx recorded a newer incarnation — the only way
    its read-validation can fail, `Reads.vread_congr_below`) has at most `2^n - 1` steps,
    and no infinite run exists. The executor inherits this by re-executing ONLY on a failed
    validation. The bound is finiteness, not performance; the real count is the conflict
    rate (#257). -/
theorem schedule_terminates (txs : List Tx) :
    (∀ (st : Scheduler.Sched) (k : Nat), Scheduler.Reach txs.length st k → k + 1 ≤ 2 ^ txs.length) ∧
    ¬ ∃ run : Nat → Scheduler.Sched,
        run 0 = Scheduler.init ∧ ∀ k, Scheduler.Step txs.length (run k) (run (k + 1)) :=
  ⟨fun st k h => Scheduler.run_bounded _ st k h, Scheduler.no_infinite_run _⟩

/-! ### Store algebra for the commutativity lemma -/

/-- A key not written by a list is unchanged by applying it. -/
theorem applyWrites_notMem (ws : List (Key × Val)) (s : Storage) (k : Key)
    (h : k ∉ ws.map Prod.fst) : applyWrites s ws k = s k := by
  induction ws generalizing s with
  | nil => rfl
  | cons p ws ih =>
      obtain ⟨k', v'⟩ := p
      simp only [List.map_cons, List.mem_cons, not_or] at h
      obtain ⟨hne, hnin⟩ := h
      simp only [applyWrites]
      rw [ih (store s k' v') hnin]
      simp only [store]
      rw [if_neg hne]

/-- The value at a WRITTEN key depends only on the write-list, not the base storage. -/
theorem applyWrites_memIndep (ws : List (Key × Val)) (s s' : Storage) (k : Key)
    (h : k ∈ ws.map Prod.fst) : applyWrites s ws k = applyWrites s' ws k := by
  induction ws generalizing s s' with
  | nil => simp at h
  | cons p ws ih =>
      obtain ⟨k', v'⟩ := p
      simp only [List.map_cons, List.mem_cons] at h
      simp only [applyWrites]
      by_cases hin : k ∈ ws.map Prod.fst
      · exact ih (store s k' v') (store s' k' v') hin
      · have hk : k = k' := h.resolve_right hin
        rw [applyWrites_notMem ws (store s k' v') k hin,
            applyWrites_notMem ws (store s' k' v') k hin]
        subst hk; simp [store]

/-- **Disjoint write-lists commute.** -/
theorem applyWrites_comm (wa wb : List (Key × Val)) (s : Storage)
    (hd : ∀ k, k ∈ wa.map Prod.fst → k ∉ wb.map Prod.fst) :
    applyWrites (applyWrites s wa) wb = applyWrites (applyWrites s wb) wa := by
  funext k
  by_cases hka : k ∈ wa.map Prod.fst
  · have hkb : k ∉ wb.map Prod.fst := hd k hka
    rw [applyWrites_notMem wb (applyWrites s wa) k hkb,
        applyWrites_memIndep wa (applyWrites s wb) s k hka]
  · by_cases hkb : k ∈ wb.map Prod.fst
    · rw [applyWrites_memIndep wb (applyWrites s wa) s k hkb,
          applyWrites_notMem wa (applyWrites s wb) k hka]
    · rw [applyWrites_notMem wb (applyWrites s wa) k hkb,
          applyWrites_notMem wa s k hka,
          applyWrites_notMem wa (applyWrites s wb) k hka,
          applyWrites_notMem wb s k hkb]

/-- **PERFORMANCE (commutativity).** Non-conflicting adjacent txs reorder without changing the
    fold — the WETH `deposit_comm` result lifted to the general footprint. Justifies running
    them concurrently and SKIPPING false-conflict aborts. Not needed for safety. -/
theorem commute_disjoint
    (a b : Tx) (s : Storage) (wfa : a.WellFormed) (wfb : b.WellFormed)
    (noconf : ¬ Conflict a b s s) :
    b.run (a.run s) = a.run (b.run s) := by
  simp only [Conflict, Tx.writeKeys] at noconf
  -- ¬(∃ conflict) ⇒ the two write-sets miss each other's reads and writes
  have n1 : ∀ k, k ∈ (a.effect s).map Prod.fst → k ∉ b.reads ∧ k ∉ (b.effect s).map Prod.fst :=
    fun k hk => ⟨fun hb => noconf (Or.inl ⟨k, hk, Or.inl hb⟩),
                 fun hb => noconf (Or.inl ⟨k, hk, Or.inr hb⟩)⟩
  have n2 : ∀ k, k ∈ (b.effect s).map Prod.fst → k ∉ a.reads ∧ k ∉ (a.effect s).map Prod.fst :=
    fun k hk => ⟨fun ha => noconf (Or.inr ⟨k, hk, Or.inl ha⟩),
                 fun ha => noconf (Or.inr ⟨k, hk, Or.inr ha⟩)⟩
  -- b's reads see the same values in `a.run s` as in `s` (a's writes miss b.reads)
  have hbr : ∀ k, k ∈ b.reads → applyWrites s (a.effect s) k = s k := by
    intro k hk; apply applyWrites_notMem; intro hmem; exact (n1 k hmem).1 hk
  have har : ∀ k, k ∈ a.reads → applyWrites s (b.effect s) k = s k := by
    intro k hk; apply applyWrites_notMem; intro hmem; exact (n2 k hmem).1 hk
  have heff_b : b.effect (applyWrites s (a.effect s)) = b.effect s := wfb _ _ hbr
  have heff_a : a.effect (applyWrites s (b.effect s)) = a.effect s := wfa _ _ har
  simp only [Tx.run]
  rw [heff_b, heff_a]
  exact applyWrites_comm (a.effect s) (b.effect s) s (fun k hk => (n1 k hk).2)

/-! ### Rollback: the journal model and this one agree -/

/-- `JournalSpec`'s storage and point-write ARE this module's (both `Nat → Nat`, same term). -/
theorem journal_store_eq : Evm.CL.JournalSpec.store = store := rfl

/-- Running a write list through the journaling executor (`cb-sstore` discipline: record
    the old value, then write) produces exactly `applyWrites`. -/
theorem runWrites_fst (ws : List (Key × Val)) : ∀ (s : Storage),
    (Evm.CL.JournalSpec.runWrites s ws).1 = applyWrites s ws := by
  induction ws with
  | nil => intro s; rfl
  | cons kv ws ih =>
      intro s
      obtain ⟨k, v⟩ := kv
      have := ih (store s k v)
      simp only [Evm.CL.JournalSpec.runWrites, applyWrites] at this ⊢
      exact this

/-- **ROLLBACK.** Reverting an incarnation's journal restores the storage it started from
    exactly — `Evm.CL.JournalSpec.undo_runWrites` (#236), instantiated at this module's
    `applyWrites`. This is the obligation of the in-place abort path (execute against the
    world, undo on abort — `revert-journal-to` from the tx's base cursor). An executor that
    buffers a tx's writes in its multi-version slot instead needs no undo for the ABORT:
    the slot is replaced (`mvCommit` reads only the latest recording); the journal then
    serves the intra-tx frame reverts (`Evm.CL.Journal.segmentRevert`) inside that buffer. -/
theorem abort_restores_prestate (s : Storage) (ws : List (Key × Val)) :
    Evm.CL.JournalSpec.undo (applyWrites s ws) (Evm.CL.JournalSpec.runWrites s ws).2 = s := by
  rw [← runWrites_fst ws s]
  exact Evm.CL.JournalSpec.undo_runWrites s ws

end Evm.Parallel.BlockSTM
