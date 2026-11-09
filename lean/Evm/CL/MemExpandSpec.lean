import Evm.CL.AsmCore
import Evm.Frontier.Vm.Gas
import Mathlib.Tactic

/-! # CALL/CREATE memory-expansion refinement (#260, S1)

The structured `memRangeInstrs`/`memRangeEnd` combinator (AsmCore) replaced the
hand-written u64-truncating CALL memexp prologue. Here we PROVE it refines the
EELS memory-expansion semantics (`Evm.Frontier.Vm.Gas.memoryCost`):

* `memRangeEnd_some_eq` — when it yields an end, that end EXACTLY equals the true
  EELS end `off.toNat + size.toNat` (or 0 for a zero-length range), and fits u64.
* `memRangeEnd_none_huge` — when it OOGs, the true end is ≥ 2^64.
* `memexp_unaffordable` — and a ≥2^64-byte end costs more gas than ANY u64 budget,
  so EELS itself out-of-gases. Hence the combinator OOGs *iff* EELS does.

This is the guarantee replay can't give: it quantifies over ALL u256 operands —
including the adversarial `argsLen = 0x..._0000000000000000` (low limb 0, high
limbs huge) that block 4466928's relay used and that we previously mis-ran. -/

namespace Evm.CL.AsmCore
open Evm.Frontier.Vm

/-- Each limb-times-place summand is ≤ the whole `toNat` (linear once the
    nonlinear products are abstracted). -/
private theorem limb1_le_toNat (a : U256) : a.l1 * 2^64 ≤ a.toNat := by
  -- v4.29: `generalize` on the limb products loops on the projections
  -- (stack overflow); the coefficients are literal, so omega needs no
  -- abstraction — plain unfold suffices.
  unfold U256.toNat
  omega

private theorem limb2_le_toNat (a : U256) : a.l2 * 2^128 ≤ a.toNat := by
  -- v4.29: `generalize` on the limb products loops on the projections
  -- (stack overflow); the coefficients are literal, so omega needs no
  -- abstraction — plain unfold suffices.
  unfold U256.toNat
  omega

private theorem limb3_le_toNat (a : U256) : a.l3 * 2^192 ≤ a.toNat := by
  -- v4.29: `generalize` on the limb products loops on the projections
  -- (stack overflow); the coefficients are literal, so omega needs no
  -- abstraction — plain unfold suffices.
  unfold U256.toNat
  omega

private theorem l0_le_toNat (a : U256) : a.l0 ≤ a.toNat := by
  -- v4.29: `generalize` on the limb products loops on the projections
  -- (stack overflow); the coefficients are literal, so omega needs no
  -- abstraction — plain unfold suffices.
  unfold U256.toNat
  omega

/-- A u256 with a nonzero high limb is ≥ 2^64. -/
theorem toNat_ge_of_hi {a : U256} (h : a.l1 ≠ 0 ∨ a.l2 ≠ 0 ∨ a.l3 ≠ 0) :
    2^64 ≤ a.toNat := by
  rcases h with h | h | h
  · have hb : (2:Nat)^64 ≤ a.l1 * 2^64 := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h)
    exact Nat.le_trans hb (limb1_le_toNat a)
  · have hb : (2:Nat)^128 ≤ a.l2 * 2^128 := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h)
    have h64 : (2:Nat)^64 ≤ 2^128 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact Nat.le_trans (Nat.le_trans h64 hb) (limb2_le_toNat a)
  · have hb : (2:Nat)^192 ≤ a.l3 * 2^192 := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h)
    have h64 : (2:Nat)^64 ≤ 2^192 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    exact Nat.le_trans (Nat.le_trans h64 hb) (limb3_le_toNat a)

/-- High limbs all zero ⇒ `toNat = l0`. -/
private theorem toNat_eq_l0 {a : U256} (h1 : a.l1 = 0) (h2 : a.l2 = 0) (h3 : a.l3 = 0) :
    a.toNat = a.l0 := by
  unfold U256.toNat; simp [h1, h2, h3]

/-- When `memRangeEnd` returns an end, it equals the true EELS end and fits u64. -/
theorem memRangeEnd_some_eq (off len : U256) (e : Nat)
    (h : memRangeEnd off len = some e) :
    (len.toNat = 0 ∧ e = 0) ∨ (e = off.toNat + len.toNat ∧ e < 2^64) := by
  unfold memRangeEnd at h
  by_cases c1 : (len.l1 ≠ 0 ∨ len.l2 ≠ 0 ∨ len.l3 ≠ 0)
  · rw [ite_eq_left c1] at h; exact absurd h (by simp)
  · rw [ite_eq_right c1] at h
    by_cases c2 : len.l0 = 0
    · rw [ite_eq_left c2] at h
      left
      push Not at c1; obtain ⟨e1, e2, e3⟩ := c1
      exact ⟨by rw [toNat_eq_l0 e1 e2 e3]; exact c2, by simpa using h.symm⟩
    · rw [ite_eq_right c2] at h
      by_cases c3 : (off.l1 ≠ 0 ∨ off.l2 ≠ 0 ∨ off.l3 ≠ 0 ∨ 2^64 ≤ off.l0 + len.l0)
      · rw [ite_eq_left c3] at h; exact absurd h (by simp)
      · rw [ite_eq_right c3] at h
        right
        push Not at c1 c3
        obtain ⟨le1, le2, le3⟩ := c1
        obtain ⟨oe1, oe2, oe3, hcarry⟩ := c3
        have he : off.l0 + len.l0 = e := by simpa using h
        rw [toNat_eq_l0 oe1 oe2 oe3, toNat_eq_l0 le1 le2 le3]
        exact ⟨he.symm, by omega⟩

/-- When `memRangeEnd` OOGs, the true memory end is ≥ 2^64. -/
theorem memRangeEnd_none_huge (off len : U256)
    (h : memRangeEnd off len = none) :
    2^64 ≤ off.toNat + len.toNat := by
  unfold memRangeEnd at h
  by_cases c1 : (len.l1 ≠ 0 ∨ len.l2 ≠ 0 ∨ len.l3 ≠ 0)
  · have := toNat_ge_of_hi c1; have := l0_le_toNat off; omega
  · rw [ite_eq_right c1] at h
    by_cases c2 : len.l0 = 0
    · rw [ite_eq_left c2] at h; exact absurd h (by simp)
    · rw [ite_eq_right c2] at h
      by_cases c3 : (off.l1 ≠ 0 ∨ off.l2 ≠ 0 ∨ off.l3 ≠ 0 ∨ 2^64 ≤ off.l0 + len.l0)
      · rcases c3 with c | c | c | c
        · have := toNat_ge_of_hi (Or.inl c); have := l0_le_toNat len; omega
        · have := toNat_ge_of_hi (Or.inr (Or.inl c)); have := l0_le_toNat len; omega
        · have := toNat_ge_of_hi (Or.inr (Or.inr c)); have := l0_le_toNat len; omega
        · have := l0_le_toNat off; have := l0_le_toNat len; omega
      · rw [ite_eq_right c3] at h; exact absurd h (by simp)

/-- `memoryCost` of a ≥2^59-word memory exceeds 2^64. (`C_mem(a) ≥ a²/512 ≥
    2^118/512 = 2^109 ≥ 2^64`.) The quadratic term alone is unaffordable. -/
theorem memoryCost_ge {w : Nat} (hw : 2^59 ≤ w) : 2^64 ≤ Gas.memoryCost w := by
  have hsq : (2:Nat)^118 ≤ w * w := by
    have h := Nat.mul_le_mul hw hw
    have e : (2:Nat)^59 * 2^59 = 2^118 := by norm_num
    rwa [e] at h
  have hdiv : (2:Nat)^109 ≤ w * w / 512 := by
    have h := Nat.div_le_div_right (c := 512) hsq
    have e : (2:Nat)^118 / 512 = 2^109 := by norm_num
    rwa [e] at h
  have h64 : (2:Nat)^64 ≤ 2^109 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  unfold Gas.memoryCost
  exact Nat.le_trans (Nat.le_trans h64 hdiv) (Nat.le_add_left _ _)

/-- A ≥2^64-byte memory end is unaffordable under ANY u64 gas budget: EELS charges
    more than `g`. Combined with `memRangeEnd_none_huge`, the structured combinator
    out-of-gases exactly when EELS does. -/
theorem memexp_unaffordable (off len : U256) (g : Nat) (hg : g < 2^64)
    (h : memRangeEnd off len = none) :
    g < Gas.memoryCost ((off.toNat + len.toNat + 31) / 32) := by
  have hend : 2^64 ≤ off.toNat + len.toNat := memRangeEnd_none_huge off len h
  have hb : (2:Nat)^64 ≤ off.toNat + len.toNat + 31 :=
    Nat.le_trans hend (Nat.le_add_right _ 31)
  have hwords : (2:Nat)^59 ≤ (off.toNat + len.toNat + 31) / 32 := by
    have h := Nat.div_le_div_right (c := 32) hb
    have e : (2:Nat)^64 / 32 = 2^59 := by norm_num
    rwa [e] at h
  exact Nat.lt_of_lt_of_le hg (memoryCost_ge hwords)

/-! ## S3: the shared memexp gadget's denote charges exactly EELS gas

`memExpandInstrs` (the `.memExpand` op) accumulates `cost(nw) − cost(ow)` into
x17 (`acc`). We prove that delta IS `Gas.memoryExpansionCost ow nw` — so MLOAD/
MSTORE/KECCAK/CALL/COPY all charge the EELS memory-expansion gas by construction,
not by replay coincidence. -/

/-- When the new end is in-bounds, the `.memExpand` op's accumulator increases by
    exactly the EELS `memoryExpansionCost` (oldWords = memSize/32, newWords =
    ⌈scratch/32⌉). -/
theorem memExpand_acc_refines (m : Mach) (hcap : ¬ m.memCap < m.scratch) :
    (Op.denote .memExpand m).acc =
      m.acc + Gas.memoryExpansionCost (m.memSize / 32) ((m.scratch + 31) / 32) := by
  simp only [Op.denote, ite_eq_right hcap]
  by_cases hle : (m.scratch + 31) / 32 ≤ m.memSize / 32
  · simp [hle, Gas.memoryExpansionCost]
  · simp only [hle, ite_false]
    simp only [Gas.memoryExpansionCost, hle, ite_false, Gas.memoryCost]

end Evm.CL.AsmCore
