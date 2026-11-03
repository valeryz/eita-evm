/-
  Evm.CL.ChunkMemExpand — the chunk's folded memory-expansion charge.

  Stage 1 of #238. `AsmCore.memExpand_charges_eels` proves the PER-OP gadget
  charges the EELS delta. The JIT does something stronger and so far unproved:
  `ARM64.JIT.memExpandFlush` charges ONE delta for the whole chunk, from the
  frame's runtime entry memory size to the chunk's maximum touched end, and its
  docstring justifies that with

      "expansion cost is a function of the word count alone and the size is
       monotone, so the deltas telescope"

  which is a claim about gas accounting, not about ARM64 — so it belongs here,
  ISA-neutral, and it transfers to the x86-64 backend unchanged.

  `telescope` below is that claim. `last_end_undercharges` is why the fold has
  to take the MAXIMUM rather than the final end: a chunk whose later op touches
  less memory than an earlier one would be undercharged, and an undercharge
  moves the sender refund and the coinbase fee, i.e. the state root — the same
  consequence as #266.
-/

import Evm.CL.AsmCore
import Evm.Frontier.Vm.Gas

namespace Evm.CL.ChunkMemExpand

open Evm.CL.AsmCore (memCost)

/-- `memCost w = 3·w + ⌊w²/512⌋` is monotone — the half of "a function of the
    word count alone and the size is monotone" that actually needs proving. -/
theorem memCost_mono {a b : Nat} (h : a ≤ b) : memCost a ≤ memCost b := by
  unfold memCost
  have h2 : a * a ≤ b * b := Nat.mul_le_mul h h
  have hd : a * a / 512 ≤ b * b / 512 := Nat.div_le_div_right h2
  omega

/-- One expansion charge, in words: EELS `memoryExpansionCost`. -/
def expand (old new : Nat) : Nat := if new ≤ old then 0 else memCost new - memCost old

theorem expand_eq_eels (old new : Nat) :
    expand old new = Evm.Frontier.Vm.Gas.memoryExpansionCost old new := rfl

/-- **Charges compose along a growing size.** This is the telescoping step. -/
theorem expand_trans {a b c : Nat} (hab : a ≤ b) (hbc : b ≤ c) :
    expand a b + expand b c = expand a c := by
  unfold expand
  have hma : memCost a ≤ memCost b := memCost_mono hab
  have hmb : memCost b ≤ memCost c := memCost_mono hbc
  by_cases h1 : b ≤ a
  · have hab' : a = b := Nat.le_antisymm hab h1
    subst hab'
    simp
  · by_cases h2 : c ≤ b
    · have hbc' : b = c := Nat.le_antisymm hbc h2
      subst hbc'
      simp [h1]
    · have h3 : ¬ (c ≤ a) := by omega
      simp only [h1, h2, h3, if_false]
      omega

/-- Charging up to `e` is charging up to the new high-water mark: below the
    current size the charge is zero, above it the max IS the end. -/
theorem expand_max (a b : Nat) : expand a b = expand a (max a b) := by
  by_cases h : b ≤ a
  · rw [Nat.max_eq_left h]
    simp [expand, h]
  · rw [Nat.max_eq_right (by omega : a ≤ b)]

/-- The memory size after a sequence of touched ends (in words): each op raises
    the high-water mark, never lowers it. -/
def sizeAfter (w0 : Nat) : List Nat → Nat
  | []      => w0
  | e :: es => sizeAfter (max w0 e) es

/-- What the interpreter charges: one delta per op, against the size as it
    stood at that op. -/
def sumDeltas (w0 : Nat) : List Nat → Nat
  | []      => 0
  | e :: es => expand w0 e + sumDeltas (max w0 e) es

theorem sizeAfter_ge (w0 : Nat) (es : List Nat) : w0 ≤ sizeAfter w0 es := by
  induction es generalizing w0 with
  | nil => exact Nat.le_refl _
  | cons e es ih => exact Nat.le_trans (Nat.le_max_left w0 e) (ih (max w0 e))

/-- **The chunk's single charge IS the sum of the per-op charges.** One `subs`
    at the chunk's flush point collects exactly what the interpreter collects op
    by op — which is what lets the JIT hoist memory-expansion gas out of the
    body, and what makes the two tiers agree on gas to the unit. -/
theorem telescope (w0 : Nat) (es : List Nat) :
    sumDeltas w0 es = expand w0 (sizeAfter w0 es) := by
  induction es generalizing w0 with
  | nil => simp [sumDeltas, sizeAfter, expand]
  | cons e es ih =>
    rw [sumDeltas, ih (max w0 e), sizeAfter, expand_max w0 e]
    exact expand_trans (Nat.le_max_left w0 e) (sizeAfter_ge (max w0 e) es)

/-- And `sizeAfter` is the maximum, so the flush's "max touched end" is the
    right thing to materialise. -/
theorem sizeAfter_eq_foldl_max (w0 : Nat) (es : List Nat) :
    sizeAfter w0 es = es.foldl max w0 := by
  induction es generalizing w0 with
  | nil => rfl
  | cons e es ih => simpa [sizeAfter] using ih (max w0 e)

/-! ## Why the MAXIMUM, and not the last end

A chunk that touches memory high and then low would be undercharged by a flush
that used the final end. Three words then one: the interpreter charges for the
growth to three and nothing back; a last-end flush charges for one. -/

theorem last_end_undercharges :
    ∃ (w0 : Nat) (es : List Nat) (last : Nat),
      es ≠ [] ∧ es.getLast? = some last ∧ expand w0 last < sumDeltas w0 es := by
  refine ⟨0, [3, 1], 1, by simp, by simp, ?_⟩
  simp [sumDeltas, expand, memCost]

/-- Spelled out: the right charge for that chunk is 9 gas, the last-end charge
    is 3. (`memCost 3 = 9`, `memCost 1 = 3`.) -/
example : sumDeltas 0 [3, 1] = 9 := by simp [sumDeltas, expand, memCost]
example : expand 0 1 = 3 := by simp [expand, memCost]

/-- A zero-length range charges nothing, whatever the offset — the `memRangeEnd`
    convention the CALL/CREATE gadgets rely on. -/
example (w0 : Nat) : expand w0 0 = 0 := by simp [expand]

/-- Monotone ends are the common case and telescope to a single delta, which is
    the shape `memExpandFlush` emits. -/
example : sumDeltas 0 [1, 2, 5] = expand 0 5 := by
  rw [telescope]; rfl

end Evm.CL.ChunkMemExpand
