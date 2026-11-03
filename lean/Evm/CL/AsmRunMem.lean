/-
  Evm.CL.AsmRunMem — the byte-memory lemmas the chunk-flush proof reads and
  writes through: 64-bit and 256-bit round trips, frame rules for disjoint
  ranges, and the limb view of a u256 in memory (`ofLimbs`).

  Addresses are `base + ofNat i`; disjointness is stated on those sums, so a
  layout hypothesis is a plain `∀ i < n, ∀ j < k, a + ofNat i ≠ b + ofNat j`,
  which `toNat_add_ofNat` turns into interval arithmetic for `omega` when the
  ranges do not wrap.
-/

import Evm.CL.AsmRun

namespace Evm.CL.AsmRun

/-! ## Address arithmetic without wrap -/

theorem toNat_add_ofNat (a : BitVec 64) (i : Nat) (h : a.toNat + i < 2 ^ 64) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt h]

theorem add_ofNat_eq_iff (a b : BitVec 64) (i j : Nat) (ha : a.toNat + i < 2 ^ 64) (hb : b.toNat + j < 2 ^ 64) :
    a + BitVec.ofNat 64 i = b + BitVec.ofNat 64 j ↔ a.toNat + i = b.toNat + j := by
  rw [← toNat_add_ofNat a i ha, ← toNat_add_ofNat b j hb]
  exact ⟨fun h => by rw [h], fun h => BitVec.eq_of_toNat_eq h⟩

/-- The same base: offsets decide. -/
theorem add_ofNat_eq_add_ofNat (a : BitVec 64) (i j : Nat) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 j ↔ i = j := by
  rw [BitVec.add_right_inj]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
    exact this
  · intro h; rw [h]

/-! ## Bytes -/

@[simp] theorem st8_same (m : Mem) (a : BitVec 64) (v : BitVec 8) : st8 m a v a = v := by simp [st8]
theorem st8_other (m : Mem) (a : BitVec 64) (v : BitVec 8) (x : BitVec 64) (h : x ≠ a) : st8 m a v x = m x := by
  simp [st8, h]

/-! ## 64-bit words -/

/-- A byte `st64` did not write. -/
@[simp] theorem off_zero (a : BitVec 64) : off a 0 = a := by simp [off]

theorem st64_out (m : Mem) (a v : BitVec 64) (x : BitVec 64) (hx : ∀ i < 8, x ≠ off a i) :
    st64 m a v x = m x := by
  have h0 := hx 0 (by omega); have h1 := hx 1 (by omega); have h2 := hx 2 (by omega)
  have h3 := hx 3 (by omega); have h4 := hx 4 (by omega); have h5 := hx 5 (by omega)
  have h6 := hx 6 (by omega); have h7 := hx 7 (by omega)
  rw [off_zero] at h0
  simp only [st64, st8_other _ _ _ _ h7, st8_other _ _ _ _ h6, st8_other _ _ _ _ h5, st8_other _ _ _ _ h4,
             st8_other _ _ _ _ h3, st8_other _ _ _ _ h2, st8_other _ _ _ _ h1, st8_other _ _ _ _ h0]

/-- Only the eight bytes at `a` matter to `ld64`. -/
theorem ld64_eq_of_eq_on (m m' : Mem) (a : BitVec 64)
    (h : ∀ i < 8, m' (off a i) = m (off a i)) : ld64 m' a = ld64 m a := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
  have h3 := h 3 (by omega); have h4 := h 4 (by omega); have h5 := h 5 (by omega)
  have h6 := h 6 (by omega); have h7 := h 7 (by omega)
  rw [off_zero] at h0
  simp only [ld64, h0, h1, h2, h3, h4, h5, h6, h7]

theorem off_ne_off (a : BitVec 64) (i j : Nat) (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) (h : i ≠ j) :
    off a i ≠ off a j := fun e => h ((add_ofNat_eq_add_ofNat a i j hi hj).mp e)

theorem off_ne_base (a : BitVec 64) (i : Nat) (hi : 0 < i) (hi' : i < 2 ^ 64) : off a i ≠ a := by
  intro e; have := (add_ofNat_eq_add_ofNat a i 0 hi' (by omega)).mp (by simpa using e); omega

theorem ld64_st64_same (m : Mem) (a v : BitVec 64) : ld64 (st64 m a v) a = v := by
  have ne : ∀ i j : Nat, i < 8 → j < 8 → i ≠ j → off a i ≠ off a j :=
    fun i j hi hj h => off_ne_off a i j (by omega) (by omega) h
  have nb : ∀ i : Nat, 0 < i → i < 8 → off a i ≠ a := fun i h h' => off_ne_base a i h (by omega)
  have nb' : ∀ i : Nat, 0 < i → i < 8 → a ≠ off a i := fun i h h' => (nb i h h').symm
  simp only [ld64, st64, st8, if_true]
  simp
  bv_decide

theorem ld64_st64_disj (m : Mem) (a b v : BitVec 64)
    (h : ∀ i < 8, ∀ j < 8, off a i ≠ off b j) :
    ld64 (st64 m b v) a = ld64 m a :=
  ld64_eq_of_eq_on m _ a (fun i hi => st64_out m b v _ (fun j hj => h i hi j hj))

theorem ld64_st8_disj (m : Mem) (a b : BitVec 64) (v : BitVec 8)
    (h : ∀ i < 8, off a i ≠ b) :
    ld64 (st8 m b v) a = ld64 m a :=
  ld64_eq_of_eq_on m _ a (fun i hi => st8_other m b v _ (h i hi))

/-! ## u256 -/

/-- Four little-endian limbs as a u256, at the literal width (what `bv_decide`
    accepts; an `++` chain lives at `BitVec (64+64+64+64)`). -/
def ofLimbs (l0 l1 l2 l3 : BitVec 64) : Evm.U256 :=
  (l3.zeroExtend 256 <<< 192) ||| (l2.zeroExtend 256 <<< 128) ||| (l1.zeroExtend 256 <<< 64) ||| l0.zeroExtend 256

theorem ofLimbs_extract (v : Evm.U256) :
    ofLimbs (v.extractLsb' 0 64) (v.extractLsb' 64 64) (v.extractLsb' 128 64) (v.extractLsb' 192 64) = v := by
  simp only [ofLimbs]; dsimp only [Evm.U256]; bv_decide

@[simp] theorem extract0_ofLimbs (l0 l1 l2 l3 : BitVec 64) : (ofLimbs l0 l1 l2 l3).extractLsb' 0 64 = l0 := by
  simp only [ofLimbs]; bv_decide
@[simp] theorem extract1_ofLimbs (l0 l1 l2 l3 : BitVec 64) : (ofLimbs l0 l1 l2 l3).extractLsb' 64 64 = l1 := by
  simp only [ofLimbs]; bv_decide
@[simp] theorem extract2_ofLimbs (l0 l1 l2 l3 : BitVec 64) : (ofLimbs l0 l1 l2 l3).extractLsb' 128 64 = l2 := by
  simp only [ofLimbs]; bv_decide
@[simp] theorem extract3_ofLimbs (l0 l1 l2 l3 : BitVec 64) : (ofLimbs l0 l1 l2 l3).extractLsb' 192 64 = l3 := by
  simp only [ofLimbs]; bv_decide

/-- `ld256` is the limbs. -/
theorem ld256_eq_ofLimbs (m : Mem) (a : BitVec 64) :
    ld256 m a = ofLimbs (ld64 m a) (ld64 m (off a 8)) (ld64 m (off a 16)) (ld64 m (off a 24)) := by
  simp only [ld256, ofLimbs]; dsimp only [Evm.U256]; bv_decide

/-- Two `stp`s (four `str`s) are an `st256` of the limbs. -/
theorem st64_four_eq_st256 (m : Mem) (a : BitVec 64) (l0 l1 l2 l3 : BitVec 64) :
    st64 (st64 (st64 (st64 m a l0) (off a 8) l1) (off a 16) l2) (off a 24) l3 =
      st256 m a (ofLimbs l0 l1 l2 l3) := by
  simp only [st256, extract0_ofLimbs, extract1_ofLimbs, extract2_ofLimbs, extract3_ofLimbs]

/-- `off (off a k) i = off a (k + i)`. -/
theorem off_off (a : BitVec 64) (k i : Nat) : off (off a k) i = off a (k + i) := by
  simp only [off, BitVec.add_assoc, BitVec.ofNat_add]

theorem st256_out (m : Mem) (a : BitVec 64) (v : Evm.U256) (x : BitVec 64)
    (hx : ∀ i < 32, x ≠ off a i) : st256 m a v x = m x := by
  have sub : ∀ (k : Nat), k + 8 ≤ 32 → ∀ i < 8, x ≠ off (off a k) i := by
    intro k hk i hi; rw [off_off]; exact hx (k + i) (by omega)
  have s0 := sub 0 (by omega); have s8 := sub 8 (by omega); have s16 := sub 16 (by omega); have s24 := sub 24 (by omega)
  rw [off_zero] at s0
  simp only [st256]
  rw [st64_out _ _ _ _ s24, st64_out _ _ _ _ s16, st64_out _ _ _ _ s8, st64_out _ _ _ _ s0]

theorem ld256_eq_of_eq_on (m m' : Mem) (a : BitVec 64)
    (h : ∀ i < 32, m' (off a i) = m (off a i)) : ld256 m' a = ld256 m a := by
  have sub : ∀ (k : Nat), k + 8 ≤ 32 → ld64 m' (off a k) = ld64 m (off a k) := by
    intro k hk
    apply ld64_eq_of_eq_on
    intro i hi; rw [off_off]; exact h (k + i) (by omega)
  have s0 := sub 0 (by omega); have s8 := sub 8 (by omega); have s16 := sub 16 (by omega); have s24 := sub 24 (by omega)
  rw [off_zero] at s0
  simp only [ld256, s0, s8, s16, s24]

/-- The 32-byte round trip, limb by limb: each `ld64` sees only its own `st64`. -/
theorem ld256_st256_same (m : Mem) (a : BitVec 64) (v : Evm.U256) : ld256 (st256 m a v) a = v := by
  have dj : ∀ k l : Nat, k + 8 ≤ 32 → l + 8 ≤ 32 → (k + 8 ≤ l ∨ l + 8 ≤ k) →
      ∀ i < 8, ∀ j < 8, off (off a k) i ≠ off (off a l) j := by
    intro k l hk hl hkl i hi j hj
    rw [off_off, off_off]
    exact off_ne_off a _ _ (by omega) (by omega) (by omega)
  rw [ld256_eq_ofLimbs]
  simp only [st256]
  have e0 : ld64 (st64 (st64 (st64 (st64 m a (v.extractLsb' 0 64)) (off a 8) (v.extractLsb' 64 64))
      (off a 16) (v.extractLsb' 128 64)) (off a 24) (v.extractLsb' 192 64)) a = v.extractLsb' 0 64 := by
    rw [ld64_st64_disj _ _ _ _ (by simpa using dj 0 24 (by omega) (by omega) (by omega)),
        ld64_st64_disj _ _ _ _ (by simpa using dj 0 16 (by omega) (by omega) (by omega)),
        ld64_st64_disj _ _ _ _ (by simpa using dj 0 8 (by omega) (by omega) (by omega)), ld64_st64_same]
  have e8 : ld64 (st64 (st64 (st64 (st64 m a (v.extractLsb' 0 64)) (off a 8) (v.extractLsb' 64 64))
      (off a 16) (v.extractLsb' 128 64)) (off a 24) (v.extractLsb' 192 64)) (off a 8) = v.extractLsb' 64 64 := by
    rw [ld64_st64_disj _ _ _ _ (dj 8 24 (by omega) (by omega) (by omega)),
        ld64_st64_disj _ _ _ _ (dj 8 16 (by omega) (by omega) (by omega)), ld64_st64_same]
  have e16 : ld64 (st64 (st64 (st64 (st64 m a (v.extractLsb' 0 64)) (off a 8) (v.extractLsb' 64 64))
      (off a 16) (v.extractLsb' 128 64)) (off a 24) (v.extractLsb' 192 64)) (off a 16) = v.extractLsb' 128 64 := by
    rw [ld64_st64_disj _ _ _ _ (dj 16 24 (by omega) (by omega) (by omega)), ld64_st64_same]
  have e24 : ld64 (st64 (st64 (st64 (st64 m a (v.extractLsb' 0 64)) (off a 8) (v.extractLsb' 64 64))
      (off a 16) (v.extractLsb' 128 64)) (off a 24) (v.extractLsb' 192 64)) (off a 24) = v.extractLsb' 192 64 := by
    rw [ld64_st64_same]
  rw [e0, e8, e16, e24, ofLimbs_extract]

theorem ld256_st256_disj (m : Mem) (a b : BitVec 64) (v : Evm.U256)
    (h : ∀ i < 32, ∀ j < 32, off a i ≠ off b j) :
    ld256 (st256 m b v) a = ld256 m a :=
  ld256_eq_of_eq_on m _ a (fun i hi => st256_out m b v _ (fun j hj => h i hi j hj))

theorem ld256_st64_disj (m : Mem) (a b v : BitVec 64)
    (h : ∀ i < 32, ∀ j < 8, off a i ≠ off b j) :
    ld256 (st64 m b v) a = ld256 m a :=
  ld256_eq_of_eq_on m _ a (fun i hi => st64_out m b v _ (fun j hj => h i hi j hj))

theorem ld64_st256_disj (m : Mem) (a b : BitVec 64) (v : Evm.U256)
    (h : ∀ i < 8, ∀ j < 32, off a i ≠ off b j) :
    ld64 (st256 m b v) a = ld64 m a :=
  ld64_eq_of_eq_on m _ a (fun i hi => st256_out m b v _ (fun j hj => h i hi j hj))

end Evm.CL.AsmRun
