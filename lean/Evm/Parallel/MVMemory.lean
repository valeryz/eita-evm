/-! # Evm/Parallel/MVMemory — the multi-version memory, refined to the sequential prefix

`BlockSTM.lean` proves the abstract spec: a *validated* schedule / *settled* memory commits
exactly `seqExec`. The executable Block-STM needs the CONCRETE data structure that makes a
schedule validated — the **multi-version memory**: per key, the writes tagged by tx index;
tx `i` reads the value of the highest-index writer below `i`. This module proves that concrete
read REFINES the abstract one: `vread … i k` (the latest version below `i`) equals
`prefixState … i k` (apply the writes of txs `0..i-1` in order, then read). So a CL MVMemory
implementing `vread` over a `key → (txIdx,val) list` hashtable is correct w.r.t. the proven
spec — `JournalSpec`-style refinement, the real prerequisite for intra-block Block-STM.

Self-contained (mirrors `BlockSTM`'s `Storage`/`applyWrites`, like `JournalSpec`); the
refinement target `prefixState` is exactly `BlockSTM.mvCommit`'s per-step accumulator. -/

namespace Evm.Parallel.MVMemory

abbrev Key : Type := Nat
abbrev Val : Type := Nat
abbrev Storage : Type := Key → Val

def store (s : Storage) (k : Key) (v : Val) : Storage := fun x => if x = k then v else s x

def applyWrites : Storage → List (Key × Val) → Storage
  | s, []           => s
  | s, (k, v) :: ws => applyWrites (store s k v) ws

/-- Last write to `k` in a write-list (later entries win — the `applyWrites` discipline). -/
def lastVal : List (Key × Val) → Key → Option Val
  | [],            _ => none
  | (k', v') :: ws, k =>
      match lastVal ws k with
      | some v => some v
      | none   => if k' = k then some v' else none

/-- `applyWrites` reads back the last write to `k`, or the base. -/
theorem applyWrites_lastVal (ws : List (Key × Val)) (s : Storage) (k : Key) :
    applyWrites s ws k = (lastVal ws k).getD (s k) := by
  induction ws generalizing s with
  | nil => rfl
  | cons p ws ih =>
      obtain ⟨k', v'⟩ := p
      simp only [applyWrites, lastVal]
      rw [ih (store s k' v')]
      cases h : lastVal ws k with
      | some v => rfl
      | none =>
          by_cases hk : k' = k
          · subst hk; simp [store]
          · simp only [ite_eq_right hk, Option.getD, store]
            rw [ite_eq_right (fun h' : k = k' => hk h'.symm)]

/-! ## The concrete multi-version memory and its read

`W i` = tx `i`'s write list (its recorded effect). The physical CL structure is the transpose
— a `key → (txIdx,val) list` hashtable — but the READ SEMANTICS is what must be correct, and
that's `vread`: the value of the highest-index writer below `i`. -/

/-- State after the sequential prefix `txs 0..i-1` — the value tx `i` MUST observe.
    (This is `BlockSTM.mvCommit`'s accumulator and `prefixView`.) -/
def prefixState (W : Nat → List (Key × Val)) (σ : Storage) : Nat → Storage
  | 0     => σ
  | i + 1 => applyWrites (prefixState W σ i) (W i)

/-- The multi-version read: value of the latest write to `k` by a tx `j < i` (highest `j`
    first), else the base. Exactly what a `key → versions` MVMemory lookup returns. -/
def latestWrite (W : Nat → List (Key × Val)) : Nat → Key → Option Val
  | 0,     _ => none
  | i + 1, k =>
      match lastVal (W i) k with
      | some v => some v
      | none   => latestWrite W i k

def vread (W : Nat → List (Key × Val)) (σ : Storage) (i : Nat) (k : Key) : Val :=
  (latestWrite W i k).getD (σ k)

/-- **MVMemory read refinement.** The concrete multi-version read (latest version below `i`)
    equals the abstract sequential-prefix read. So an MVMemory whose `read(k,i)` returns the
    highest-versioned write below `i` feeds each tx exactly its sequential-prefix view — which
    is the `ScheduleValidFrom` / `SettledFrom` precondition `BlockSTM.settled_refines_seq`
    discharges. The CL `key → (txIdx,val) list` is therefore correct by construction. -/
theorem vread_eq_prefix (W : Nat → List (Key × Val)) (σ : Storage) :
    ∀ (i : Nat) (k : Key), vread W σ i k = prefixState W σ i k := by
  intro i
  induction i with
  | zero => intro k; rfl
  | succ i ih =>
      intro k
      simp only [vread, latestWrite, prefixState, applyWrites_lastVal]
      cases h : lastVal (W i) k with
      | some v => rfl
      | none   =>
          -- latest version below i+1 misses tx i ⇒ same as below i ⇒ IH
          simp only [Option.getD]
          have := ih k
          simp only [vread] at this
          exact this

/-! ## Composition: an MVMemory-driven execution refines sequential

This joins the read-refinement above with the `BlockSTM` fixpoint argument into ONE concrete
statement. `eff i` is tx `i`'s effect (its writes as a function of what it reads). The
executor records, for each tx, the writes it computed reading the MVMemory — i.e. `W` is
**MV-consistent**: `W i = eff i (vread W σ i)`. (This is `BlockSTM.SettledFrom` expressed via
the concrete `vread`: every tx's recorded writes already match its effect on its MV-read view,
so validation passes — nothing pending re-execution.) We prove such a `W` commits exactly the
sequential result. So the whole Block-STM stack — concrete versioned reads, the settled
fixpoint — produces `seqExec`, end to end, at the spec level. -/

/-- Sequential execution of effects `eff 0 … eff (n-1)`: each reads the running state. -/
def seqExecN (eff : Nat → Storage → List (Key × Val)) (σ : Storage) : Nat → Storage
  | 0     => σ
  | i + 1 => applyWrites (seqExecN eff σ i) (eff i (seqExecN eff σ i))

/-- **MVMemory-driven Block-STM refines sequential.** If every tx's recorded writes equal its
    effect on its multi-version read view (the settled/validated fixpoint, stated concretely
    via `vread`), then the MVMemory's accumulated state after `n` txs equals sequential
    execution of those `n` txs. Correctness of the concrete data structure + the optimistic
    fixpoint, in one theorem. -/
theorem mvconsistent_refines_seq
    (eff : Nat → Storage → List (Key × Val)) (W : Nat → List (Key × Val)) (σ : Storage)
    (hc : ∀ i, W i = eff i (vread W σ i)) :
    ∀ n, prefixState W σ n = seqExecN eff σ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hview : vread W σ n = prefixState W σ n := by
        funext k; exact vread_eq_prefix W σ n k
      simp only [prefixState, seqExecN]
      rw [hc n, hview, ih]

/-! ## Well-posedness: the optimistic loop's fixpoint exists and is unique-as-sequential

`mvconsistent_refines_seq` says *if* the loop settles to an MV-consistent `W`, the result is
sequential. Liveness has two parts: (a) such a `W` EXISTS (the loop has a correct fixpoint to
reach), and (b) the loop REACHES it in finitely many steps (no infinite abort/re-execute
cycle). We discharge (a) here — well-posedness — by exhibiting the fixpoint explicitly: each
tx writing its effect on the *sequential* prefix is MV-consistent. Part (b), the termination
measure (the lowest-uncommitted index strictly rises; aborts are bounded), remains the
operational obligation `BlockSTM.schedule_terminates`. -/

/-- The explicit fixpoint witness: each tx's writes = its effect on the sequential prefix.
    NON-self-referential (depends on `seqExecN`, not on itself) — yet provably MV-consistent. -/
def witnessW (eff : Nat → Storage → List (Key × Val)) (σ : Storage) : Nat → List (Key × Val) :=
  fun i => eff i (seqExecN eff σ i)

theorem witnessW_prefixState (eff : Nat → Storage → List (Key × Val)) (σ : Storage) :
    ∀ n, prefixState (witnessW eff σ) σ n = seqExecN eff σ n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [prefixState, seqExecN, witnessW]; rw [ih]

/-- **Well-posedness (reachability half of liveness).** An MV-consistent `W` exists — the
    optimistic loop has a correct fixpoint to converge to, and by `mvconsistent_refines_seq`
    it is the sequential execution. (Termination — that the loop reaches it in bounded steps —
    is `schedule_terminates`, still open.) -/
theorem consistent_fixpoint_exists (eff : Nat → Storage → List (Key × Val)) (σ : Storage) :
    ∃ W, ∀ i, W i = eff i (vread W σ i) := by
  refine ⟨witnessW eff σ, fun i => ?_⟩
  have hv : vread (witnessW eff σ) σ i = prefixState (witnessW eff σ) σ i := by
    funext k; exact vread_eq_prefix _ σ i k
  show eff i (seqExecN eff σ i) = eff i (vread (witnessW eff σ) σ i)
  rw [hv, witnessW_prefixState]

end Evm.Parallel.MVMemory
