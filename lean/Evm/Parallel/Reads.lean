import Evm.Parallel.BlockSTM
import Evm.Parallel.MVMemory

/-! # Evm/Parallel/Reads — reads as a first-class notion; commutative deltas (#255)

`BlockSTM.lean` models a tx as `reads : List Key` + `effect : Storage → writes`: the read
footprint is DECLARED and validation compares the view to the prefix on those keys. Real
Block-STM has no declared footprint: a tx's reads are DISCOVERED while it runs (the read
set is Turing-complete data), each read is LOGGED with the value (or version) observed,
and validation re-checks the LOG. This module restates the spec that way:

  `Tx.run : Storage → Result`, where `Result` carries the logged `reads` (key, value
  observed), the `writes`, the commutative `deltas`, and the tx's `out` (gas, status,
  logs — everything a receipt or fact row is built from).

Two well-formedness conditions replace `BlockSTM.Tx.WellFormed`:
  * `Faithful`     — the logged value is what the view held (an honest read log);
  * `Deterministic` — the result depends only on the values at the keys it read
    (re-running against a view that agrees on the log gives the same result).
Both are properties of ANY deterministic executor that logs its reads; the runtime
witness is `rw-read!` extended with the value read (today it records the key only).

DELTAS (owner, 2026-10-25). Fee credits to the coinbase are the classic hot key: every tx
WRITES it, so a write/write or read-after-write rule serialises the whole block
(#257: FULL = 1.00x on every chain). The credit is a commutative "add δ" that reads
nothing, so it is modelled as a DELTA effect: validation ignores it (nothing was read),
the commit folds it in index order, and `applyDeltas_comm` / `applyDeltas_ext` prove the
fold order among deltas is irrelevant (an aggregator may accumulate them in any order).
But a READ of a delta-key — `BALANCE(coinbase)`, a tx sent from the coinbase,
`SELFDESTRUCT` to the coinbase, the EIP-161 "is the coinbase empty" check on a value
transfer — is logged like any read and validated against the committed prefix, which
includes every lower tx's delta. Those readers serialise behind their predecessors; no
other tx does. `deferred_delta_read_diverges` shows the read-validation of delta keys is
load-bearing (dropping it diverges from serial); `deltas_deferred` shows a key that is
only ever delta'd in a block may be settled once, at the end, with the sum.

The order inside one tx is writes-then-deltas (EELS: the message runs, then the fee
credit — `Homestead.processTransaction`'s `addBalance coinbase minerWei` after the
message). -/

namespace Evm.Parallel.Reads

open Evm.Parallel.BlockSTM (Key Val Storage store applyWrites applyWrites_notMem)

/-- What one execution of a tx produced. -/
structure Result where
  /-- The read log: (key, value observed), in read order. -/
  reads  : List (Key × Val)
  /-- Point writes, left-to-right (later wins). -/
  writes : List (Key × Val)
  /-- Commutative increments ("add δ to key"): fee credits and similar accumulators. -/
  deltas : List (Key × Nat)
  /-- Everything else the tx yields: gas used, status, logs, … — the receipt/fact payload. -/
  out    : List Nat

/-- A transaction: a deterministic function of the view it executes against. -/
structure Tx where
  run : Storage → Result

/-! ## Deltas -/

def addDelta (s : Storage) (k : Key) (d : Nat) : Storage := store s k (s k + d)

def applyDeltas : Storage → List (Key × Nat) → Storage
  | s, []           => s
  | s, (k, d) :: ds => applyDeltas (addDelta s k d) ds

/-- The total increment a delta list applies to `k`. -/
def sumDeltas : List (Key × Nat) → Key → Nat
  | [],            _ => 0
  | (k', d) :: ds, k => (if k' = k then d else 0) + sumDeltas ds k

theorem addDelta_get (s : Storage) (k' : Key) (d : Nat) (k : Key) :
    addDelta s k' d k = s k + (if k' = k then d else 0) := by
  simp only [addDelta, store]
  by_cases h : k = k'
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right (fun h' => h h'.symm)]; simp

/-- Applying deltas adds their per-key sum: the value is base + Σδ, whatever the order. -/
theorem applyDeltas_get (ds : List (Key × Nat)) (s : Storage) (k : Key) :
    applyDeltas s ds k = s k + sumDeltas ds k := by
  induction ds generalizing s with
  | nil => simp [applyDeltas, sumDeltas]
  | cons p ds ih =>
      obtain ⟨k', d⟩ := p
      simp only [applyDeltas, sumDeltas]
      rw [ih, addDelta_get]
      ac_rfl

/-- **Delta lists with the same per-key sums are interchangeable** — any order, any
    grouping (an aggregator summing concurrently is sound). -/
theorem applyDeltas_ext (da db : List (Key × Nat)) (h : ∀ k, sumDeltas da k = sumDeltas db k)
    (s : Storage) : applyDeltas s da = applyDeltas s db := by
  funext k; rw [applyDeltas_get, applyDeltas_get, h]

/-- **Deltas commute.** -/
theorem applyDeltas_comm (da db : List (Key × Nat)) (s : Storage) :
    applyDeltas (applyDeltas s da) db = applyDeltas (applyDeltas s db) da := by
  funext k; simp only [applyDeltas_get]; ac_rfl

theorem applyDeltas_append (da db : List (Key × Nat)) (s : Storage) :
    applyDeltas s (da ++ db) = applyDeltas (applyDeltas s da) db := by
  funext k; simp only [applyDeltas_get]
  have : ∀ (da : List (Key × Nat)), sumDeltas (da ++ db) k = sumDeltas da k + sumDeltas db k := by
    intro da
    induction da with
    | nil => simp [sumDeltas]
    | cons p da ih => obtain ⟨k', d⟩ := p; simp only [List.cons_append, sumDeltas]; rw [ih]; ac_rfl
  rw [this]; ac_rfl

/-! ## One tx step, sequential reference, validation, commit -/

/-- Apply a result to a state: writes, then deltas. -/
def Result.apply (s : Storage) (r : Result) : Storage := applyDeltas (applyWrites s r.writes) r.deltas

def Tx.step (t : Tx) (s : Storage) : Storage := (t.run s).apply s

/-- THE reference: the sequential fold (each tx reads the live state). -/
def seqExec (txs : List Tx) (σ : Storage) : Storage := txs.foldl (fun s t => t.step s) σ

def readKeys (r : Result) : List Key := r.reads.map Prod.fst

/-- An honest read log: every logged value is the view's value at that key. -/
def Tx.Faithful (t : Tx) : Prop := ∀ v, ∀ p ∈ (t.run v).reads, v p.1 = p.2

/-- Determinism on the read log: a view agreeing on every key `t` read (under `v`) yields
    the same result. Any sequential executor that reads keys one at a time satisfies it. -/
def Tx.Deterministic (t : Tx) : Prop :=
  ∀ v v', (∀ k, k ∈ readKeys (t.run v) → v k = v' k) → t.run v = t.run v'

def Tx.WellFormed (t : Tx) : Prop := t.Faithful ∧ t.Deterministic

/-- Read-validation of one result against the committed prefix state `s`: every logged
    read holds in `s`. Deltas and writes are not inspected — nothing was read for them. -/
def ReadsValid (r : Result) (s : Storage) : Prop := ∀ p ∈ r.reads, s p.1 = p.2

/-- Validated schedule: tx `i` ran against `view i`; its read log holds in the committed
    prefix; the prefix then advances by the result it computed. -/
def ScheduleValidFrom (view : Nat → Storage) : Storage → Nat → List Tx → Prop
  | _, _, []      => True
  | s, i, t :: ts =>
      ReadsValid (t.run (view i)) s ∧
      ScheduleValidFrom view ((t.run (view i)).apply s) (i + 1) ts

/-- The committed state: each tx's result (computed against ITS view) applied in index
    order — deltas included, folded in index order. -/
def commitFrom (view : Nat → Storage) : Storage → Nat → List Tx → Storage
  | s, _, []      => s
  | s, i, t :: ts => commitFrom view ((t.run (view i)).apply s) (i + 1) ts

def commitFold (txs : List Tx) (σ : Storage) (view : Nat → Storage) : Storage :=
  commitFrom view σ 0 txs

/-- The committed TRACE: (prefix state, result) per tx, in index order. Every fact row,
    receipt field and net diff the executor emits is a function of this pair. -/
def traceFrom (view : Nat → Storage) : Storage → Nat → List Tx → List (Storage × Result)
  | _, _, []      => []
  | s, i, t :: ts => (s, t.run (view i)) :: traceFrom view ((t.run (view i)).apply s) (i + 1) ts

/-- The sequential trace. -/
def seqTrace : Storage → List Tx → List (Storage × Result)
  | _, []      => []
  | s, t :: ts => (s, t.run s) :: seqTrace (t.step s) ts

/-- A validated read log against `s` makes the result equal to running against `s`. -/
theorem run_eq_of_valid (t : Tx) (wf : t.WellFormed) (v s : Storage)
    (hv : ReadsValid (t.run v) s) : t.run v = t.run s := by
  apply wf.2
  intro k hk
  simp only [readKeys, List.mem_map] at hk
  obtain ⟨p, hp, rfl⟩ := hk
  rw [wf.1 v p hp, hv p hp]

/-! ## Safety, re-proved over the read log -/

theorem traceFrom_eq_seq (view : Nat → Storage) :
    ∀ (txs : List Tx) (s : Storage) (i : Nat),
      (∀ t ∈ txs, t.WellFormed) →
      ScheduleValidFrom view s i txs →
      traceFrom view s i txs = seqTrace s txs := by
  intro txs
  induction txs with
  | nil => intro s i _ _; rfl
  | cons t ts ih =>
      intro s i wf valid
      obtain ⟨hv, hrest⟩ := valid
      have heq : t.run (view i) = t.run s := run_eq_of_valid t (wf t (by simp)) _ _ hv
      simp only [traceFrom, seqTrace, Tx.step, heq]
      rw [heq] at hrest
      exact congrArg _ (ih _ (i + 1) (fun x hx => wf x (by simp [hx])) hrest)

theorem commitFrom_eq_seq (view : Nat → Storage) :
    ∀ (txs : List Tx) (s : Storage) (i : Nat),
      (∀ t ∈ txs, t.WellFormed) →
      ScheduleValidFrom view s i txs →
      commitFrom view s i txs = txs.foldl (fun a t => t.step a) s := by
  intro txs
  induction txs with
  | nil => intro s i _ _; rfl
  | cons t ts ih =>
      intro s i wf valid
      obtain ⟨hv, hrest⟩ := valid
      have heq : t.run (view i) = t.run s := run_eq_of_valid t (wf t (by simp)) _ _ hv
      simp only [commitFrom, List.foldl_cons, Tx.step, heq]
      rw [heq] at hrest
      exact ih _ (i + 1) (fun x hx => wf x (by simp [hx])) hrest

/-- **Block-STM refines sequential execution (SAFETY), with discovered reads and deltas.**
    A schedule whose logged reads validate against the committed prefix commits exactly
    the sequential state. Deltas are folded without validation; a read of a delta-key is
    validated like any other read. -/
theorem blockSTM_refines_seq (txs : List Tx) (σ : Storage) (view : Nat → Storage)
    (wf : ∀ t ∈ txs, t.WellFormed) (valid : ScheduleValidFrom view σ 0 txs) :
    commitFold txs σ view = seqExec txs σ :=
  commitFrom_eq_seq view txs σ 0 wf valid

/-- **The emitted facts equal the serial run's.** Per tx, the pair (prefix state, result)
    the parallel executor commits is the sequential one — so gas, status, logs, receipts
    (`out`), and the net diffs computed from prefix state + writes + deltas, are
    byte-identical to a serial replay once they are emitted in index order. Facts about a
    delta-key (the coinbase's pre/post balance) must therefore be formed at COMMIT from the
    prefix state, not at execution from the tx's view. -/
theorem facts_eq_seq {α : Type} (F : Storage → Result → α)
    (txs : List Tx) (σ : Storage) (view : Nat → Storage)
    (wf : ∀ t ∈ txs, t.WellFormed) (valid : ScheduleValidFrom view σ 0 txs) :
    (traceFrom view σ 0 txs).map (fun p => F p.1 p.2) = (seqTrace σ txs).map (fun p => F p.1 p.2) := by
  rw [traceFrom_eq_seq view txs σ 0 wf valid]

/-! ## Deltas: exempt from validation, yet the read of a delta-key is not -/

/-- **Validation of a delta-key READ is load-bearing.** tx0 credits key 0 by 5 (a delta);
    tx1 reads key 0 and copies it to key 1. A view that hands tx1 the base state (the
    delta not yet materialised) fails validation — and committing it anyway diverges from
    serial. So a tx that reads the coinbase balance must see the prefix sum of the fee
    credits below it. -/
theorem deferred_delta_read_diverges :
    ∃ (txs : List Tx) (σ : Storage) (badview : Nat → Storage),
      ¬ ScheduleValidFrom badview σ 0 txs ∧ commitFold txs σ badview ≠ seqExec txs σ := by
  refine ⟨[⟨fun _ => ⟨[], [], [(0, 5)], []⟩⟩, ⟨fun v => ⟨[(0, v 0)], [(1, v 0)], [], []⟩⟩],
          (fun _ => 0), (fun _ _ => 0), ?_, ?_⟩
  · intro h
    obtain ⟨_, h1, _⟩ := h
    have := h1 (0, 0) (by simp)
    simp [Result.apply, applyWrites, applyDeltas, addDelta, store] at this
  · intro h
    have := congrFun h 1
    simp [commitFold, commitFrom, seqExec, Tx.step, Result.apply, applyWrites, applyDeltas,
          addDelta, store] at this

/-- Per-key sum of the deltas of a list of results. -/
def traceDeltaSum : List (Storage × Result) → Key → Nat
  | [],          _ => 0
  | (_, r) :: tr, k => sumDeltas r.deltas k + traceDeltaSum tr k

/-- **Deferred accumulation.** A key no committed tx WRITES (point-write) ends the block at
    base + the sum of every tx's deltas to it. So an executor may keep the coinbase's fee
    credits in one accumulator and settle it once — provided a READ of the key (which
    `ScheduleValidFrom` validates against the prefix) materialises the prefix sum first. -/
theorem deltas_deferred (view : Nat → Storage) (k : Key) :
    ∀ (txs : List Tx) (s : Storage) (i : Nat),
      (∀ p ∈ traceFrom view s i txs, k ∉ p.2.writes.map Prod.fst) →
      commitFrom view s i txs k = s k + traceDeltaSum (traceFrom view s i txs) k := by
  intro txs
  induction txs with
  | nil => intro s i _; simp [commitFrom, traceFrom, traceDeltaSum]
  | cons t ts ih =>
      intro s i hw
      have hk : k ∉ (t.run (view i)).writes.map Prod.fst := hw (s, t.run (view i)) (by simp [traceFrom])
      have hrest : ∀ p ∈ traceFrom view ((t.run (view i)).apply s) (i + 1) ts, k ∉ p.2.writes.map Prod.fst :=
        fun p hp => hw p (by simp [traceFrom, hp])
      simp only [commitFrom, traceFrom, traceDeltaSum]
      rw [ih _ (i + 1) hrest]
      simp only [Result.apply, applyDeltas_get]
      rw [applyWrites_notMem _ _ _ hk]
      ac_rfl

/-! ## Version validation: why a passed version check means the values are unchanged

The CL executor validates reads by VERSION (writer index, incarnation), not by value: tx
`i` logs, per key, which lower tx's write it read (`latestWriter`, or `none` for the
base), and validation passes if the multi-version memory still names the same writer
at the same incarnation. Here is why that is sound: the value `vread` returns is
determined by the writer index and that writer's (immutable per incarnation) write list.
And the liveness side: the read of `i` depends only on the write lists below `i`
(`latestWrite_congr_below`), so validation of `i` can fail only if some `j < i` recorded
a new incarnation — exactly `Scheduler.Justified`. -/

open Evm.Parallel.MVMemory (lastVal latestWrite vread)

/-- The index of the latest writer of `k` below `i`, if any. -/
def latestWriter (W : Nat → List (Key × Val)) : Nat → Key → Option Nat
  | 0,     _ => none
  | i + 1, k =>
      match lastVal (W i) k with
      | some _ => some i
      | none   => latestWriter W i k

theorem latestWrite_of_writer (W : Nat → List (Key × Val)) :
    ∀ (i : Nat) (k : Key),
      (latestWriter W i k = none → latestWrite W i k = none) ∧
      (∀ j, latestWriter W i k = some j → latestWrite W i k = lastVal (W j) k) := by
  intro i
  induction i with
  | zero => intro k; exact ⟨fun _ => rfl, fun j h => by simp [latestWriter] at h⟩
  | succ i ih =>
      intro k
      simp only [latestWriter, latestWrite]
      cases h : lastVal (W i) k with
      | some v => exact ⟨fun h' => by simp at h', fun j hj => by simp at hj; subst hj; rw [h]⟩
      | none => exact ⟨fun h' => (ih k).1 h', fun j hj => (ih k).2 j hj⟩

/-- **Version validation is sound.** If the writer tag tx `i` logged for `k` is unchanged
    (same writer index) and that writer's write list is the same (same incarnation — an
    incarnation's recorded writes are immutable; a re-execution gets a new incarnation),
    the multi-version read returns the same value as when it was logged. -/
theorem version_validation_sound (W₀ W : Nat → List (Key × Val)) (σ : Storage) (i : Nat) (k : Key)
    (htag : latestWriter W₀ i k = latestWriter W i k)
    (himm : ∀ j, latestWriter W₀ i k = some j → W₀ j = W j) :
    vread W₀ σ i k = vread W σ i k := by
  simp only [vread]
  cases h : latestWriter W₀ i k with
  | none =>
      rw [(latestWrite_of_writer W₀ i k).1 h, (latestWrite_of_writer W i k).1 (htag ▸ h)]
  | some j =>
      rw [(latestWrite_of_writer W₀ i k).2 j h, (latestWrite_of_writer W i k).2 j (htag ▸ h), himm j h]

/-- **A read below `i` sees only txs below `i`.** If no `j < i` changed its recorded writes,
    tx `i`'s view is unchanged — so its validation cannot fail. This is the hypothesis
    under which `Scheduler.Justified` abstracts "validation failed". -/
theorem latestWrite_congr_below (W W' : Nat → List (Key × Val)) :
    ∀ (i : Nat), (∀ j, j < i → W j = W' j) → ∀ k, latestWrite W i k = latestWrite W' i k := by
  intro i
  induction i with
  | zero => intro _ k; rfl
  | succ i ih =>
      intro h k
      simp only [latestWrite]
      rw [h i (Nat.lt_succ_self i), ih (fun j hj => h j (Nat.lt_succ_of_lt hj)) k]

theorem vread_congr_below (W W' : Nat → List (Key × Val)) (σ : Storage) (i : Nat)
    (h : ∀ j, j < i → W j = W' j) (k : Key) : vread W σ i k = vread W' σ i k := by
  simp only [vread]; rw [latestWrite_congr_below W W' i h k]

end Evm.Parallel.Reads
