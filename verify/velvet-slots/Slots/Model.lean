/-
One account's slot table of Eita's native storage (core c/world_slots.{h,c}, perf-native-storage
e7fcd13; the hash, probe, tombstones and growth of the Lisp `slots-*` it replaced): `cap`
entries, `words` = cap × (4 key limbs + 4 value limbs), `state` = cap bytes (0 empty, 1 full,
2 tombstone), linear probing from `hash(k0,k1) & mask`, `mask = cap - 1`.

This file: the abstract model (a finite map Key → Option Val), the representation predicates
(shape, probing invariant, uniqueness, counts, occupancy), and the arithmetic lemmas the Velvet
proofs use.
-/


abbrev Limb := UInt64
/-- A 256-bit word as four little-endian 64-bit limbs (the order of `u256-word 0..3`). -/
abbrev W4 := Limb × Limb × Limb × Limb
abbrev Key := W4
abbrev Val := W4

/-- The abstract model: a finite map. -/
abbrev SlotMap := Key → Option Val

def SlotMap.put (m : SlotMap) (k : Key) (v : Val) : SlotMap := fun k' => if k' = k then some v else m k'
def SlotMap.erase (m : SlotMap) (k : Key) : SlotMap := fun k' => if k' = k then none else m k'

/-! ## The hash (Lisp `slots-hash`) -/

def golden : UInt64 := 0x9E3779B97F4A7C15

def hashIdx (k0 k1 : UInt64) (mask : Nat) : Nat := ((k0 * golden + k1) >>> 17).toNat &&& mask

/-! ## Representation -/

def keyAt (w : Array UInt64) (i : Nat) : Key := (w[8*i]!, w[8*i+1]!, w[8*i+2]!, w[8*i+3]!)
def valAt (w : Array UInt64) (i : Nat) : Val := (w[8*i+4]!, w[8*i+5]!, w[8*i+6]!, w[8*i+7]!)

/-- Home slot of the entry stored at slot `i`. -/
def homeAt (mask : Nat) (w : Array UInt64) (i : Nat) : Nat := hashIdx w[8*i]! w[8*i+1]! mask

/-- Probe distance from `h` to `j` on the cycle of length `cap`. -/
def dist (cap h j : Nat) : Nat := (j + cap - h) % cap

structure Shape (cap mask : Nat) (w : Array UInt64) (s : Array UInt8) : Prop where
  cap_pos : 0 < cap
  mask_eq : mask + 1 = cap
  mask_mod : ∀ x : Nat, x &&& mask = x % cap
  w_size : w.size = 8 * cap
  s_size : s.size = cap
  pow : ∃ lg, cap = 2 ^ lg

/-- Only the three states occur. -/
def StatesOk (cap : Nat) (s : Array UInt8) : Prop := ∀ i < cap, s[i]! = 0 ∨ s[i]! = 1 ∨ s[i]! = 2

/-- The probing invariant: every slot on the probe path from a full entry's home to the entry
itself is non-empty (full or tombstone). -/
def Probing (cap mask : Nat) (w : Array UInt64) (s : Array UInt8) : Prop :=
  ∀ j < cap, s[j]! = 1 → ∀ d < dist cap (homeAt mask w j) j, s[(homeAt mask w j + d) % cap]! ≠ 0

/-- At most one full slot per key. -/
def Unique (cap : Nat) (w : Array UInt64) (s : Array UInt8) : Prop :=
  ∀ i < cap, ∀ j < cap, s[i]! = 1 → s[j]! = 1 → keyAt w i = keyAt w j → i = j

/-- The table represents the map `m`. -/
def Models (cap : Nat) (w : Array UInt64) (s : Array UInt8) (m : SlotMap) : Prop :=
  ∀ k v, m k = some v ↔ ∃ i < cap, s[i]! = 1 ∧ keyAt w i = k ∧ valAt w i = v

def nFull (cap : Nat) (s : Array UInt8) : Nat := ((List.range cap).filter (fun i => s[i]! == 1)).length
def nUsed (cap : Nat) (s : Array UInt8) : Nat := ((List.range cap).filter (fun i => s[i]! != 0)).length

/-- Everything a valid table satisfies. `count`/`used` are the struct's counters. -/
structure TableInv (cap mask : Nat) (w : Array UInt64) (s : Array UInt8) (count used : Nat) : Prop where
  shape : Shape cap mask w s
  states : StatesOk cap s
  probing : Probing cap mask w s
  unique : Unique cap w s
  count_eq : count = nFull cap s
  used_eq : used = nUsed cap s
  /-- The occupancy bound: used ≤ 3/4 cap. -/
  occ : 4 * used ≤ 3 * cap

/-! ## Arithmetic of the probe cycle -/

theorem dist_lt {cap h j : Nat} (hc : 0 < cap) : dist cap h j < cap := Nat.mod_lt _ hc

theorem add_dist {cap h j : Nat} (hh : h < cap) (hj : j < cap) : (h + dist cap h j) % cap = j := by
  unfold dist
  rw [Nat.add_mod_mod]
  have : h + (j + cap - h) = j + cap := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hj]

theorem dist_add {cap h d : Nat} (hh : h < cap) (hd : d < cap) : dist cap h ((h + d) % cap) = d := by
  unfold dist
  by_cases hc : h + d < cap
  · rw [Nat.mod_eq_of_lt hc]
    have : h + d + cap - h = d + cap := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hd]
  · have e : (h + d) % cap = h + d - cap := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [e]
    have : h + d - cap + cap - h = d := by omega
    rw [this, Nat.mod_eq_of_lt hd]

theorem hash_lt {cap mask : Nat} {w : Array UInt64} {s : Array UInt8} (sh : Shape cap mask w s)
    (k0 k1 : UInt64) : hashIdx k0 k1 mask < cap := by
  unfold hashIdx; rw [sh.mask_mod]; exact Nat.mod_lt _ sh.cap_pos

theorem step_mod {cap mask : Nat} {w : Array UInt64} {s : Array UInt8} (sh : Shape cap mask w s)
    (h n : Nat) : ((h + n) % cap + 1) &&& mask = (h + (n + 1)) % cap := by
  rw [sh.mask_mod, Nat.mod_add_mod]; rfl

/-! ## The probe prefix -/

/-- The first `n` slots of the probe path from `h` are non-empty and do not hold `k`. -/
def Visited (cap h : Nat) (w : Array UInt64) (s : Array UInt8) (k : Key) (n : Nat) : Prop :=
  ∀ d < n, s[(h + d) % cap]! ≠ 0 ∧ (s[(h + d) % cap]! = 1 → keyAt w ((h + d) % cap) ≠ k)

theorem visited_zero {cap h w s k} : Visited cap h w s k 0 := fun _ hd => absurd hd (Nat.not_lt_zero _)

theorem visited_succ {cap h w s k n} (hv : Visited cap h w s k n) (h0 : s[(h + n) % cap]! ≠ 0)
    (h1 : s[(h + n) % cap]! = 1 → keyAt w ((h + n) % cap) ≠ k) : Visited cap h w s k (n + 1) := by
  intro d hd
  rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd | rfl
  · exact hv d hd
  · exact ⟨h0, h1⟩

theorem homeAt_of_key {mask : Nat} {w : Array UInt64} {j : Nat} {k0 k1 k2 k3 : UInt64}
    (hk : keyAt w j = (k0, k1, k2, k3)) : homeAt mask w j = hashIdx k0 k1 mask := by
  simp only [keyAt, Prod.mk.injEq] at hk
  simp [homeAt, hk.1, hk.2.1]

theorem absent_of_empty {cap mask n : Nat} {w : Array UInt64} {s : Array UInt8} {k0 k1 k2 k3 : UInt64}
    (sh : Shape cap mask w s) (pr : Probing cap mask w s)
    (hv : Visited cap (hashIdx k0 k1 mask) w s (k0, k1, k2, k3) n)
    (he : s[(hashIdx k0 k1 mask + n) % cap]! = 0) :
    ∀ j < cap, s[j]! = 1 → keyAt w j ≠ (k0, k1, k2, k3) := by
  intro j hj hf hk
  have hh := hash_lt sh k0 k1
  have home := homeAt_of_key (mask := mask) hk
  have ad := add_dist hh hj
  rcases Nat.lt_trichotomy (dist cap (hashIdx k0 k1 mask) j) n with hlt | heq | hgt
  · have := (hv _ hlt).2; rw [ad] at this; exact this hf hk
  · rw [heq] at ad; rw [ad] at he; rw [he] at hf; exact absurd hf (by decide)
  · have := pr j hj hf n (by rw [home]; exact hgt); rw [home] at this; exact this he

theorem absent_of_exhausted {cap mask : Nat} {w : Array UInt64} {s : Array UInt8} {k0 k1 k2 k3 : UInt64}
    (sh : Shape cap mask w s) (hv : Visited cap (hashIdx k0 k1 mask) w s (k0, k1, k2, k3) cap) :
    ∀ j < cap, s[j]! = 1 → keyAt w j ≠ (k0, k1, k2, k3) := by
  intro j hj hf hk
  have hh := hash_lt sh k0 k1
  have := (hv _ (dist_lt (h := hashIdx k0 k1 mask) (j := j) sh.cap_pos)).2
  rw [add_dist hh hj] at this; exact this hf hk

theorem path_of_visited {cap h n d0 : Nat} {w : Array UInt64} {s : Array UInt8} {k : Key}
    (hh : h < cap) (hd0 : d0 < cap) (hle : d0 ≤ n) (hv : Visited cap h w s k n) :
    ∀ d < dist cap h ((h + d0) % cap), s[(h + d) % cap]! ≠ 0 := by
  rw [dist_add hh hd0]; intro d hd; exact (hv d (by omega)).1

theorem nFull_eq_cap {cap : Nat} {s : Array UInt8} (hall : ∀ j < cap, s[j]! = 1) : nFull cap s = cap := by
  unfold nFull
  rw [List.filter_eq_self.mpr, List.length_range]
  intro j hj
  simp [hall j (List.mem_range.mp hj)]

theorem full_of_exhausted {cap mask : Nat} {w : Array UInt64} {s : Array UInt8} {k : Key} {k0 k1 : UInt64}
    (sh : Shape cap mask w s) (st : StatesOk cap s) (hv : Visited cap (hashIdx k0 k1 mask) w s k cap)
    (nt : ∀ d < cap, s[(hashIdx k0 k1 mask + d) % cap]! ≠ 2) : nFull cap s = cap := by
  apply nFull_eq_cap
  intro j hj
  have hh := hash_lt sh k0 k1
  have h1 := (hv _ (dist_lt (h := hashIdx k0 k1 mask) (j := j) sh.cap_pos)).1
  have h2 := nt _ (dist_lt (h := hashIdx k0 k1 mask) (j := j) sh.cap_pos)
  rw [add_dist hh hj] at h1 h2
  rcases st j hj with h | h | h
  · exact absurd h h1
  · exact h
  · exact absurd h h2


theorem mask_mod_of_pow {cap : Nat} (h : ∃ lg, cap = 2 ^ lg) : ∀ x : Nat, x &&& (cap - 1) = x % cap := by
  obtain ⟨lg, rfl⟩ := h; intro x; exact Nat.and_two_pow_sub_one_eq_mod x lg
