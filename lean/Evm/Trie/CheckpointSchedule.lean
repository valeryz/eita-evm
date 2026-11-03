/-
  Evm.Trie.CheckpointSchedule — when to verify the state root.

  A replay's results are trustworthy only if the state they derive from
  provably matches consensus, so at a
  *checkpoint* block B the replay computes its full state root and compares
  it with the header's `stateRoot(B)`. A match is a verified anchor.

  Bring-up policy (first genesis→tip replay): dense early, exponential
  backoff. The interval is a power of two that grows with the height:

      interval h = 2 ^ clamp (log2 h − 3) 10 20

  so every octave of height gets 8 checkpoints (1024, 2048, … while
  h < 2¹³; then every 2¹¹ up to 2¹⁴; …) and the interval reaches its cap
  2²⁰ at h = 2²³ (≈ 8.4M blocks). Block 0 (the genesis alloc) is always a
  checkpoint. A mismatch densifies (re-run the last interval with a
  checkpoint every block) to pin the source block — the automated form of
  how the historical divergences were hunted.

  The host mirrors `checkpointInterval` in Lisp (`arc-checkpoint-p`,
  src/chains/arc.lisp) — a policy, not consensus; the examples below pin
  the values the mirror must reproduce.
-/

namespace Evm.Trie.CheckpointSchedule

def minLog : Nat := 10   -- 2^10 = 1024 blocks
def maxLog : Nat := 20   -- 2^20 ≈ 1M blocks

/-- Power-of-two interval for height `h` (see module doc). -/
def checkpointInterval (h : Nat) : Nat :=
  let l := Nat.log2 h
  let k := if l < 3 then minLog else min maxLog (max minLog (l - 3))
  2 ^ k

/-- Block `h` is a checkpoint iff it is genesis or a multiple of its interval. -/
def isCheckpoint (h : Nat) : Bool :=
  h = 0 || (h ≥ 2 ^ minLog && h % checkpointInterval h = 0)

example : checkpointInterval 0 = 1024 := by decide
example : checkpointInterval 1024 = 1024 := by decide
example : checkpointInterval 8191 = 1024 := by decide
example : checkpointInterval 8192 = 1024 := by decide      -- log2 = 13 → 2^10
example : checkpointInterval 16384 = 2048 := by decide     -- log2 = 14 → 2^11
example : checkpointInterval 32768 = 4096 := by decide
example : checkpointInterval (2 ^ 23) = 2 ^ 20 := by decide
example : checkpointInterval (2 ^ 30) = 2 ^ 20 := by decide -- capped
example : isCheckpoint 0 = true := by decide
example : isCheckpoint 512 = false := by decide
example : isCheckpoint 1024 = true := by decide
example : isCheckpoint 3072 = true := by decide
example : isCheckpoint 17408 = false := by decide          -- 17·1024, interval 2048
example : isCheckpoint 18432 = true := by decide           -- 9·2048

/-- `Nat.log2` is monotone (core has only `log2_le_self`; derived from `Nat.le_log2`). -/
theorem log2_mono {a b : Nat} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  by_cases ha : a = 0
  · subst ha; simp
  · have hb : b ≠ 0 := by omega
    have h1 : 2 ^ Nat.log2 a ≤ a := (Nat.le_log2 ha).1 (Nat.le_refl _)
    exact (Nat.le_log2 hb).2 (Nat.le_trans h1 h)

/-- The interval never shrinks with height (backoff is monotone). -/
theorem interval_mono {a b : Nat} (h : a ≤ b) :
    checkpointInterval a ≤ checkpointInterval b := by
  have hl : Nat.log2 a ≤ Nat.log2 b := log2_mono h
  simp only [checkpointInterval, minLog, maxLog]
  apply Nat.pow_le_pow_right (by decide)
  generalize Nat.log2 a = la at hl
  generalize Nat.log2 b = lb at hl
  split <;> split <;> omega

end Evm.Trie.CheckpointSchedule
