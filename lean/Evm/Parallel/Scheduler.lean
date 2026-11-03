/-! # Evm/Parallel/Scheduler — the optimistic re-execution loop TERMINATES (liveness, #255)

`BlockSTM.lean` proves SAFETY: a settled multi-version memory commits exactly `seqExec`.
Safety says nothing about reaching a settled memory — per the safety ≠ liveness
discipline, removing the sequential order needs its own termination argument. This
module gives it, over the one fact the Block-STM protocol guarantees about WHEN a tx is
re-executed:

  a tx `i` is (re-)executed only on its first run, or because its read-validation
  failed — and validation of `i` can only fail if some LOWER-index tx `j < i` has
  recorded a NEWER incarnation than the one `i` read from
  (`Reads.latestWrite_congr_below`: the multi-version read of `i` depends only on
  the write lists of txs below `i`).

So the scheduler is abstracted to incarnation counters: `inc i` = how many times tx `i`
has executed, `seen i j` = the incarnation of `j` that `i` observed when it last ran. A
step re-executes some `i < n` that is `Justified`. We prove:

  * the invariant `inc i ≤ 1 + Σ_{j<i} seen i j` (each re-execution beyond the first
    consumes a distinct incarnation bump of a lower tx), hence `inc i ≤ 2^i`;
  * every run from the initial state has at most `2^n - 1` steps (`run_bounded`),
    hence there is no infinite run (`no_infinite_run`).

The bound is the paper's finiteness argument, not a performance statement: the real
re-execution count is set by the conflict rate (#257). The executor discharges the
`Justified` hypothesis by re-executing ONLY on a failed validation (see
`Reads.version_validation_sound` for why a passed version check means the values the
tx read are unchanged). Import-free; core tactics only. -/

namespace Evm.Parallel.Scheduler

/-- The scheduler state, abstracted to incarnation counters. -/
structure Sched where
  /-- `inc i` = incarnations of tx `i` executed so far. -/
  inc  : Nat → Nat
  /-- `seen i j` = `inc j` as observed by tx `i` when `i` last executed (0 if never). -/
  seen : Nat → Nat → Nat

def init : Sched := ⟨fun _ => 0, fun _ _ => 0⟩

/-- Tx `i` may (re-)execute: first run, or a lower tx has a newer incarnation than `i`
    saw — the only way `i`'s read-validation can have failed. -/
def Justified (st : Sched) (i : Nat) : Prop :=
  st.inc i = 0 ∨ ∃ j, j < i ∧ st.seen i j < st.inc j

/-- Execute tx `i` once more: bump its incarnation, record what it saw below it. -/
def exec (st : Sched) (i : Nat) : Sched :=
  { inc  := fun x => if x = i then st.inc i + 1 else st.inc x,
    seen := fun x => if x = i then st.inc else st.seen x }

/-- One scheduler step over a block of `n` txs. -/
inductive Step (n : Nat) : Sched → Sched → Prop
  | exec (st : Sched) (i : Nat) (hi : i < n) (hj : Justified st i) : Step n st (exec st i)

/-- `Reach n st k`: `st` is reachable from `init` in exactly `k` steps. -/
inductive Reach (n : Nat) : Sched → Nat → Prop
  | zero : Reach n init 0
  | succ {st st' : Sched} {k : Nat} : Reach n st k → Step n st st' → Reach n st' (k + 1)

/-! ## Sums over the txs below an index -/

def sumBelow (f : Nat → Nat) : Nat → Nat
  | 0     => 0
  | i + 1 => sumBelow f i + f i

theorem sumBelow_congr (f g : Nat → Nat) : ∀ i, (∀ j, j < i → f j = g j) →
    sumBelow f i = sumBelow g i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
      intro h
      simp only [sumBelow]
      rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h i (Nat.lt_succ_self i)]

theorem sumBelow_mono (f g : Nat → Nat) : ∀ i, (∀ j, j < i → f j ≤ g j) →
    sumBelow f i ≤ sumBelow g i := by
  intro i
  induction i with
  | zero => intro _; exact Nat.le_refl _
  | succ i ih =>
      intro h
      simp only [sumBelow]
      have := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
      have := h i (Nat.lt_succ_self i)
      omega

/-- Pointwise `≤` with one strict position gives a strict sum. -/
theorem sumBelow_lt (f g : Nat → Nat) : ∀ i, (∀ j, j < i → f j ≤ g j) →
    (∃ j, j < i ∧ f j < g j) → sumBelow f i < sumBelow g i := by
  intro i
  induction i with
  | zero => intro _ ⟨j, hj, _⟩; exact absurd hj (Nat.not_lt_zero j)
  | succ i ih =>
      intro h ⟨j, hj, hlt⟩
      simp only [sumBelow]
      have hle := sumBelow_mono f g i (fun j hj => h j (Nat.lt_succ_of_lt hj))
      have hi := h i (Nat.lt_succ_self i)
      by_cases hji : j = i
      · subst hji; omega
      · have hj' : j < i := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hji
        have := ih (fun j hj => h j (Nat.lt_succ_of_lt hj)) ⟨j, hj', hlt⟩
        omega

theorem sumBelow_pow : ∀ i, sumBelow (fun j => 2 ^ j) i + 1 = 2 ^ i := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih => simp only [sumBelow, Nat.pow_succ]; omega

/-! ## The invariant -/

/-- (a) what `i` saw of `j` never exceeds `j`'s current incarnation (incarnations only
    grow); (b) every execution of `i` beyond the first was paid for by a distinct
    incarnation of a lower tx that `i` has since observed. -/
structure Inv (st : Sched) : Prop where
  seen_le : ∀ i j, st.seen i j ≤ st.inc j
  bound   : ∀ i, st.inc i ≤ 1 + sumBelow (st.seen i) i

theorem inv_init : Inv init := ⟨fun _ _ => Nat.le_refl 0, fun _ => by simp [init]⟩

theorem inv_exec (st : Sched) (i : Nat) (hinv : Inv st) (hj : Justified st i) :
    Inv (exec st i) := by
  refine ⟨?_, ?_⟩
  · intro x j
    simp only [exec]
    by_cases hx : x = i
    · subst hx
      by_cases hji : j = x
      · subst hji; simp
      · simp [hji]
    · simp only [if_neg hx]
      by_cases hji : j = i
      · subst hji; simp; have := hinv.seen_le x j; omega
      · simp [hji]; exact hinv.seen_le x j
  · intro x
    by_cases hx : x = i
    · subst hx
      have e1 : (exec st x).inc x = st.inc x + 1 := by simp [exec]
      have e2 : (exec st x).seen x = st.inc := by simp [exec]
      rw [e1, e2]
      -- the new `seen x` is the current `inc`; relate the old bound to it
      have hle : sumBelow (st.seen x) x ≤ sumBelow st.inc x :=
        sumBelow_mono _ _ x (fun j _ => hinv.seen_le x j)
      cases hj with
      | inl h0 => rw [h0]; omega
      | inr hj =>
          obtain ⟨j, hjx, hlt⟩ := hj
          have hstrict : sumBelow (st.seen x) x < sumBelow st.inc x :=
            sumBelow_lt _ _ x (fun j _ => hinv.seen_le x j) ⟨j, hjx, hlt⟩
          have := hinv.bound x
          omega
    · have e1 : (exec st i).inc x = st.inc x := by simp [exec, hx]
      have e2 : (exec st i).seen x = st.seen x := by simp [exec, hx]
      rw [e1, e2]
      exact hinv.bound x

theorem inv_reach (n : Nat) : ∀ (st : Sched) (k : Nat), Reach n st k → Inv st := by
  intro st k h
  induction h with
  | zero => exact inv_init
  | succ _ hstep ih =>
      cases hstep with
      | exec i _ hj => exact inv_exec _ i ih hj

/-! ## Bounds -/

/-- From the invariant: tx `i` executes at most `2^i` times. -/
theorem inc_le_pow (st : Sched) (hinv : Inv st) : ∀ i, ∀ j, j < i → st.inc j ≤ 2 ^ j := by
  intro i
  induction i with
  | zero => intro j hj; exact absurd hj (Nat.not_lt_zero j)
  | succ i ih =>
      intro j hj
      by_cases hji : j = i
      · subst hji
        have h1 := hinv.bound j
        have h2 : sumBelow (st.seen j) j ≤ sumBelow (fun x => 2 ^ x) j :=
          sumBelow_mono _ _ j (fun x hx => Nat.le_trans (hinv.seen_le j x) (ih x hx))
        have h3 := sumBelow_pow j
        omega
      · exact ih j (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hj) hji)

/-- A step on `i < n` adds exactly one to the total incarnation count below `n`. -/
theorem sumBelow_exec (st : Sched) (i : Nat) : ∀ n, i < n →
    sumBelow (exec st i).inc n = sumBelow st.inc n + 1 := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (Nat.not_lt_zero i)
  | succ n ih =>
      intro hi
      simp only [sumBelow]
      by_cases hin : i = n
      · subst hin
        have : sumBelow (exec st i).inc i = sumBelow st.inc i :=
          sumBelow_congr _ _ i (fun j hj => by
            simp only [exec]; rw [if_neg (Nat.ne_of_lt hj)])
        rw [this]; simp [exec]; omega
      · have hi' : i < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hin
        rw [ih hi']
        simp only [exec]
        rw [if_neg (fun h => hin h.symm)]
        omega

/-- The step count IS the total incarnation count. -/
theorem reach_count (n : Nat) : ∀ (st : Sched) (k : Nat), Reach n st k →
    k = sumBelow st.inc n := by
  intro st k h
  induction h with
  | zero =>
      have : ∀ m, sumBelow (fun _ => 0) m = 0 := by
        intro m; induction m with
        | zero => rfl
        | succ m ih => simp only [sumBelow, ih]
      exact (this n).symm
  | succ _ hstep ih =>
      cases hstep with
      | exec i hi _ => rw [sumBelow_exec _ i n hi]; omega

/-- **LIVENESS — every run is bounded.** From the initial state, a run of the optimistic
    scheduler over `n` txs takes at most `2^n - 1` steps: the loop cannot abort/re-execute
    forever. -/
theorem run_bounded (n : Nat) (st : Sched) (k : Nat) (h : Reach n st k) : k + 1 ≤ 2 ^ n := by
  have hinv := inv_reach n st k h
  have hk := reach_count n st k h
  have hle : sumBelow st.inc n ≤ sumBelow (fun j => 2 ^ j) n :=
    sumBelow_mono _ _ n (fun j hj => inc_le_pow st hinv n j hj)
  have hp := sumBelow_pow n
  omega

/-- No infinite run exists. -/
theorem no_infinite_run (n : Nat) :
    ¬ ∃ run : Nat → Sched, run 0 = init ∧ ∀ k, Step n (run k) (run (k + 1)) := by
  rintro ⟨run, h0, hstep⟩
  have hreach : ∀ k, Reach n (run k) k := by
    intro k
    induction k with
    | zero => rw [h0]; exact Reach.zero
    | succ k ih => exact Reach.succ ih (hstep k)
  have := run_bounded n (run (2 ^ n)) (2 ^ n) (hreach (2 ^ n))
  omega

end Evm.Parallel.Scheduler
