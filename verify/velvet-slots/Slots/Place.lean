import Velvet
import Slots.Find
import Slots.Frame

set_option velvet_vcgen.showVCReport true

/-- `ws_place` (world_slots.c; the Lisp `slots-put` after the grow check): overwrite the value, or write key and value at the slot
`find` chose. Returns `(words, state, count, used)`. -/
method place (cap : Nat) (w : Array UInt64) (s : Array UInt8) (count used : Nat)
    (k0 k1 k2 k3 v0 v1 v2 v3 : UInt64)
  returns (r : Array UInt64 × Array UInt8 × Nat × Nat)
  requires shape: Shape cap (cap - 1) w s
  requires states: StatesOk cap s
  requires probing: Probing cap (cap - 1) w s
  requires unique: Unique cap w s
  requires count_eq: count = nFull cap s
  requires used_eq: used = nUsed cap s
  requires notFull: nFull cap s < cap
  ensures shape': Shape cap (cap - 1) r.1 r.2.1
  ensures states': StatesOk cap r.2.1
  ensures probing': Probing cap (cap - 1) r.1 r.2.1
  ensures unique': Unique cap r.1 r.2.1
  ensures rel: PutRel cap w s r.1 r.2.1 (k0, k1, k2, k3) (v0, v1, v2, v3)
  ensures count': r.2.2.1 = nFull cap r.2.1
  ensures used': r.2.2.2 = nUsed cap r.2.1
  ensures used_le: r.2.2.2 ≤ used + 1
  ensures fresh: (∀ v, ¬ Rep cap w s (k0, k1, k2, k3) v) → r.2.2.1 = count + 1
  ensures no_tomb: (∀ i < cap, s[i]! ≠ 2) → ∀ i < cap, r.2.1[i]! ≠ 2
do
  let f ← find cap w s k0 k1 k2 k3
  if f.1 then
    let w' ← wrV w f.2 (v0, v1, v2, v3)
    return (w', s, count, used)
  else
    let st ← rd s f.2
    let used' := if st == 0 then used + 1 else used
    let w' ← wrKV w f.2 (k0, k1, k2, k3) (v0, v1, v2, v3)
    let s' ← wr s f.2 1
    return (w', s', count + 1, used')

prove_correct place by
  intro cap w s count used k0 k1 k2 k3 v0 v1 v2 v3
  velvet_vcgen [place] with try finish
  all_goals first
    | (have := shape.w_size; have := shape.s_size; have := r_lt; omega)
    | (have hfi := found if_cond
       first
       | exact upd_shape shape
       | exact states
       | exact upd_probing shape r_lt probing
       | exact upd_unique shape r_lt unique
       | exact upd_putrel shape r_lt unique hfi.1 hfi.2
       | exact count_eq
       | exact used_eq
       | omega
       | (intro h; exact absurd ⟨_, r_lt, hfi.1, hfi.2, rfl⟩ (h _))
       | (intro h; exact h))
    | (rename_i fa fb
       have hf : fa = false := by simpa using if_cond
       have ns := (⟨r_lt, ins_free hf, absent hf, ins_path hf⟩ : NewSlot cap (cap - 1) w s (k0, k1, k2, k3) fb)
       have hs : fb < s.size := by rw [shape.s_size]; exact r_lt
       first
       | exact new_shape shape ns
       | exact new_states shape states ns
       | exact new_probing shape probing ns
       | exact new_unique shape unique ns
       | exact new_putrel shape ns
       | (have := nFull_set cap fb s 1 shape.s_size r_lt
          simp only [ins_free hf, if_false, if_true] at this; omega)
       | (have := nUsed_set cap fb s 1 shape.s_size r_lt
          split <;> simp_all <;> omega)
       | (split <;> omega)
       | rfl
       | (intro h i hi; rw [get_set _ _ _ _ hs]; split
          · decide
          · exact h i hi))
