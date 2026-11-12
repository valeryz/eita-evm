import Velvet
import Slots.Model
import Slots.Mem

set_option velvet_vcgen.showVCReport true

/-- `eita_ws_probe` (world_slots.c): `(true, i)` when the key is at entry `i`, else `(false, ins)`
with `ins` the first tombstone on the probe path, or the empty entry that ends it. The C encodes
the pair as `i` / `-1 - ins`. The mask is `cap - 1`, as in the C. -/
method find (cap : Nat) (w : Array UInt64) (s : Array UInt8) (k0 k1 k2 k3 : UInt64)
  returns (r : Bool × Nat)
  requires shape: Shape cap (cap - 1) w s
  requires states: StatesOk cap s
  requires probing: Probing cap (cap - 1) w s
  requires notFull: nFull cap s < cap
  ensures r_lt: r.2 < cap
  ensures found: r.1 = true → s[r.2]! = 1 ∧ keyAt w r.2 = (k0, k1, k2, k3)
  ensures absent: r.1 = false → (∀ j < cap, s[j]! = 1 → keyAt w j ≠ (k0, k1, k2, k3))
  ensures ins_free: r.1 = false → s[r.2]! ≠ 1
  ensures ins_path: r.1 = false → ∀ d < dist cap (hashIdx k0 k1 (cap - 1)) r.2,
                      s[(hashIdx k0 k1 (cap - 1) + d) % cap]! ≠ 0
  ensures ins_first: r.1 = false → ∀ d < dist cap (hashIdx k0 k1 (cap - 1)) r.2,
                      s[(hashIdx k0 k1 (cap - 1) + d) % cap]! = 1
do
  let h := hashIdx k0 k1 (cap - 1)
  let mut i := h
  let mut n : Nat := 0
  let mut tomb := cap
  while n < cap
    invariant n_le: n ≤ cap
    invariant i_eq: i = (h + n) % cap
    invariant visited: Visited cap h w s (k0, k1, k2, k3) n
    invariant tomb_ok: tomb = cap ∨ (∃ d < n, tomb = (h + d) % cap ∧ s[tomb]! = 2 ∧
                         ∀ d' < d, s[(h + d') % cap]! ≠ 2)
    invariant no_tomb: tomb = cap → ∀ d < n, s[(h + d) % cap]! ≠ 2
    decreasing cap - n
  do
    let st ← rd s i
    if st == 0 then
      if tomb < cap then return (false, tomb) else return (false, i)
    else if st == 2 then
      if tomb == cap then tomb := i
    else
      let e0 ← rd w (8*i)
      let e1 ← rd w (8*i+1)
      let e2 ← rd w (8*i+2)
      let e3 ← rd w (8*i+3)
      if e0 == k0 && e1 == k1 && e2 == k2 && e3 == k3 then
        return (true, i)
    i := (i + 1) &&& (cap - 1)
    n := n + 1
  return (false, tomb)

theorem full_of_ne {cap : Nat} {s : Array UInt8} (st : StatesOk cap s) {x : Nat} (hx : x < cap)
    (h0 : s[x]! ≠ 0) (h2 : s[x]! ≠ 2) : s[x]! = 1 := by
  rcases st x hx with h | h | h <;> simp_all

/-- The probe prefix up to `d` holds only full entries. -/
theorem first_of {cap h n d : Nat} {w : Array UInt64} {s : Array UInt8} {k : Key}
    (st : StatesOk cap s) (cp : 0 < cap) (hh : h < cap) (hd : d < cap) (hdn : d ≤ n)
    (hv : Visited cap h w s k n) (nt : ∀ d' < d, s[(h + d') % cap]! ≠ 2) :
    ∀ d' < dist cap h ((h + d) % cap), s[(h + d') % cap]! = 1 := by
  rw [dist_add hh hd]
  intro d' hd'
  exact full_of_ne st (Nat.mod_lt _ cp) (hv d' (by omega)).1 (nt d' hd')

set_option maxRecDepth 20000 in
prove_correct find by
  intro cap w s k0 k1 k2 k3
  velvet_vcgen [find] with try finish
  all_goals (
    have cp := shape.cap_pos
    have hh := hash_lt shape k0 k1
    have sm := step_mod shape (hashIdx k0 k1 (cap - 1))
    have ws := shape.w_size
    have ss := shape.s_size
    have ap := fun n => absent_of_empty (n := n) (k0 := k0) (k1 := k1) (k2 := k2) (k3 := k3) shape probing
    have ae := absent_of_exhausted (k0 := k0) (k1 := k1) (k2 := k2) (k3 := k3) shape
    have fe := full_of_exhausted (k := (k0, k1, k2, k3)) (k0 := k0) (k1 := k1) shape states
    try subst i_eq
    try simp only [beq_iff_eq, Bool.and_eq_true, ne_eq] at *
    first
    | (rw [Nat.add_zero, Nat.mod_eq_of_lt hh])
    | exact Nat.mod_lt _ cp
    | (rw [ss]; exact Nat.mod_lt _ cp)
    | (have := Nat.mod_lt (hashIdx k0 k1 (cap - 1) + n) cp; omega)
    | exact sm n
    | exact visited_zero
    | (apply visited_succ visited <;> (try intro) <;> (try intro) <;> simp_all [keyAt]); done
    | exact Or.inr ⟨n, Nat.lt_succ_self n, rfl, if_cond_1, no_tomb if_cond_2⟩
    | (intro h; exact absurd h (Nat.ne_of_lt (Nat.mod_lt _ cp)))
    | (rcases tomb_ok with h | ⟨d, hd, e, h2, h3⟩
       · exact Or.inl h
       · exact Or.inr ⟨d, by omega, e, h2, h3⟩)
    | (intro _; exact ap n visited if_cond)
    | (intro _; have : n = cap := by omega
       subst this; exact ae visited)
    | (intro _; exact path_of_visited hh h_loop (Nat.le_refl _) visited)
    | (intro _
       have tc : tomb = cap := by
         rcases tomb_ok with h | ⟨d, hd, e, _, _⟩
         · exact h
         · exfalso; apply if_cond_1; rw [e]; exact Nat.mod_lt _ cp
       exact first_of states cp hh h_loop (Nat.le_refl _) visited (fun d' hd' => no_tomb tc d' (by omega)))
    | (intro _; rcases tomb_ok with h | ⟨d, hd, e, _, h3⟩
       · omega
       · rw [e]; exact path_of_visited hh (by omega) (by omega) visited)
    | (intro _; rcases tomb_ok with h | ⟨d, hd, e, _, h3⟩
       · omega
       · rw [e]; exact first_of states cp hh (by omega) (by omega) visited h3)
    | (have : n = cap := by omega
       subst this
       rcases tomb_ok with h | ⟨d, hd, e, h2, h3⟩
       · exact absurd (fe visited (no_tomb h)) (Nat.ne_of_lt notFull)
       · first
         | (rw [e]; exact Nat.mod_lt _ cp)
         | (intro _; rw [h2]; exact (by decide : (2:UInt8) ≠ 1))
         | (intro _; rw [e]; exact path_of_visited hh hd (Nat.le_of_lt hd) visited)
         | (intro _; rw [e]; exact first_of states cp hh hd (Nat.le_of_lt hd) visited h3))
    | (intro _; refine ⟨?_, ?_⟩
       · rcases states _ (Nat.mod_lt _ cp) with h | h | h
         · exact absurd h if_cond
         · exact h
         · exact absurd h if_cond_1
       · obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := if_cond_2
         simp only [keyAt, a, b, c, d]))
#print axioms find.spec
