import Velvet
import Slots.Place

set_option velvet_vcgen.showVCReport true

/-- `eita_ws_remove` on a table (`slots-remove`): tombstone the key's slot. Returns `(state, count)`; `used` is unchanged. -/
method remove (cap : Nat) (w : Array UInt64) (s : Array UInt8) (count : Nat)
    (k0 k1 k2 k3 : UInt64)
  returns (r : Array UInt8 × Nat)
  requires shape: Shape cap (cap - 1) w s
  requires states: StatesOk cap s
  requires probing: Probing cap (cap - 1) w s
  requires unique: Unique cap w s
  requires count_eq: count = nFull cap s
  requires notFull: nFull cap s < cap
  ensures shape': Shape cap (cap - 1) w r.1
  ensures states': StatesOk cap r.1
  ensures probing': Probing cap (cap - 1) w r.1
  ensures unique': Unique cap w r.1
  ensures rel: EraseRel cap w s w r.1 (k0, k1, k2, k3)
  ensures count': r.2 = nFull cap r.1
  ensures used': nUsed cap r.1 = nUsed cap s
do
  let f ← find cap w s k0 k1 k2 k3
  if f.1 then
    let s' ← wr s f.2 2
    return (s', count - 1)
  else
    return (s, count)

prove_correct remove by
  intro cap w s count k0 k1 k2 k3
  velvet_vcgen [remove] with try finish
  all_goals first
    | (have := shape.s_size; have := r_lt; omega)
    | (have hfi := found if_cond
       rename_i fa fb
       first
       | exact rm_shape shape
       | exact rm_states shape r_lt states
       | exact rm_probing shape r_lt probing
       | exact rm_unique shape r_lt unique
       | exact rm_eraserel shape r_lt unique hfi.1 hfi.2
       | (have h1 := nFull_set cap fb s 2 shape.s_size r_lt
          have h2 : (2 : UInt8) ≠ 1 := by decide
          simp only [hfi.1, h2, if_true, if_false] at h1
          omega)
       | (have h1 := nUsed_set cap fb s 2 shape.s_size r_lt
          have h2 : (2 : UInt8) ≠ 0 := by decide
          have h3 : s[fb]! ≠ 0 := by rw [hfi.1]; decide
          simp only [h2, h3, ne_eq, not_false_eq_true, if_true] at h1
          omega))
    | (rename_i fa fb
       have hf : fa = false := by simpa using if_cond
       first
       | (intro k' v'
          constructor
          · intro h; refine ⟨fun e => ?_, h⟩
            subst e; obtain ⟨i, hi, fi, ki, _⟩ := h; exact absent hf i hi fi ki
          · intro h; exact h.2)
       | exact count_eq)

/-- The walk (`eita_ws_map`, `slots-map`): the first full slot at or after `i`, or `cap`. Iterating
`next (j + 1)` from `next 0` visits the full slots in index order, as the C/Lisp walk does. -/
method next (cap : Nat) (s : Array UInt8) (i : Nat)
  returns (j : Nat)
  requires s_size: s.size = cap
  requires i_le: i ≤ cap
  ensures j_ge: i ≤ j
  ensures j_le: j ≤ cap
  ensures full: j < cap → s[j]! = 1
  ensures skipped: ∀ l, i ≤ l → l < j → s[l]! ≠ 1
do
  let mut j := i
  while j < cap
    invariant ge: i ≤ j
    invariant le: j ≤ cap
    invariant skip: ∀ l, i ≤ l → l < j → s[l]! ≠ 1
    decreasing cap - j
  do
    let st ← rd s j
    if st == 1 then return j
    j := j + 1
  return j

prove_correct next by
  velvet_vcgen [next] with try finish
  all_goals first
  | omega
  | (intro l h1 h2
     rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
     · exact skip l h1 h
     · subst h; simpa using if_cond)

/-- A fresh, empty table of capacity `cap` (`ws_slots_new`: the 4-entry table `eita_ws_touch` makes, and the arrays of a grow). -/
method create (cap : Nat) returns (r : Array UInt64 × Array UInt8)
  requires pow: ∃ lg, cap = 2 ^ lg
  ensures shape: Shape cap (cap - 1) r.1 r.2
  ensures states: StatesOk cap r.2
  ensures probing: Probing cap (cap - 1) r.1 r.2
  ensures unique: Unique cap r.1 r.2
  ensures empty: ∀ k v, ¬ Rep cap r.1 r.2 k v
  ensures count: nFull cap r.2 = 0
  ensures used: nUsed cap r.2 = 0
do
  return (Array.replicate (8 * cap) 0, Array.replicate cap 0)

theorem rep_zero {cap : Nat} {w : Array UInt64} {s : Array UInt8} (h : ∀ i < cap, s[i]! = 0) k v :
    ¬ Rep cap w s k v := fun ⟨i, hi, fi, _⟩ => by rw [h i hi] at fi; exact absurd fi (by decide)

theorem replicate_get {α} [Inhabited α] {n i : Nat} {x : α} (hi : i < n) : (Array.replicate n x)[i]! = x := by
  simp [hi]

theorem cnt_false (n : Nat) (f : Nat → Bool) (h : ∀ i < n, f i = false) : cnt n f = 0 := by
  unfold cnt; simp only [List.length_eq_zero_iff, List.filter_eq_nil_iff, List.mem_range]
  intro a ha; simp [h a ha]

prove_correct create by
  velvet_vcgen [create] with try finish
  all_goals (
    rename_i cap
    have cp : 0 < cap := by obtain ⟨lg, rfl⟩ := pow; exact Nat.two_pow_pos lg
    have z : ∀ i < cap, (Array.replicate cap (0 : UInt8))[i]! = 0 := fun i hi => replicate_get hi
    first
    | exact ⟨cp, by omega, mask_mod_of_pow pow, by simp, by simp, pow⟩
    | (intro i hi; exact Or.inl (z i hi))
    | (intro j hj hf; rw [z j hj] at hf; exact absurd hf (by decide))
    | (intro i hi j hj fi; rw [z i hi] at fi; exact absurd fi (by decide))
    | exact rep_zero z
    | exact cnt_false cap _ (fun i hi => by simp [z i hi]))
