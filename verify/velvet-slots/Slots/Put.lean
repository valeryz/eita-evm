import Velvet
import Slots.Grow

set_option velvet_vcgen.showVCReport true

/-- `ws_insert` (world_slots.c, Lisp `slots-put`): grow when one more used entry would reach
3/4 (`4 (used + 1) >= 3 cap`), then place. Returns `(cap, words, state, count, used)`.
Ghost-free (a callee's `given` ghost is not instantiable at a call site): the contract is the
`Rep`-level put relation; `put_models` below lifts it to the finite map. -/
method put (cap : Nat) (w : Array UInt64) (s : Array UInt8) (count used : Nat)
    (k0 k1 k2 k3 v0 v1 v2 v3 : UInt64) (maxCap : Nat)
  returns (r : Nat × Array UInt64 × Array UInt8 × Nat × Nat)
  requires inv: TableInv cap (cap - 1) w s count used
  requires cap4: 4 ≤ cap
  signals tooLarge: 3 * cap ≤ 4 * (used + 1) ∧ maxCap < newCap cap count
  ensures inv': TableInv r.1 (r.1 - 1) r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
  ensures rel: ∀ k' v', Rep r.1 r.2.1 r.2.2.1 k' v' ↔
                 (k' = (k0, k1, k2, k3) ∧ v' = (v0, v1, v2, v3)) ∨
                 (k' ≠ (k0, k1, k2, k3) ∧ Rep cap w s k' v')
  ensures cap4': 4 ≤ r.1
  ensures cap_le: r.1 = cap ∨ r.1 ≤ maxCap
do
  if 4 * (used + 1) ≥ 3 * cap then
    let g ← grow cap w s count used maxCap
    let p ← place g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2 k0 k1 k2 k3 v0 v1 v2 v3
    return (g.1, p.1, p.2.1, p.2.2.1, p.2.2.2)
  else
    let p ← place cap w s count used k0 k1 k2 k3 v0 v1 v2 v3
    return (cap, p.1, p.2.1, p.2.2.1, p.2.2.2)

prove_correct put by
  intro cap w s count used k0 k1 k2 k3 v0 v1 v2 v3 maxCap
  velvet_vcgen [put] with try finish
  all_goals (
    have occ := inv.occ
    have cu : count ≤ used := by rw [inv.count_eq, inv.used_eq]; exact nFull_le_nUsed cap s
    first
    | exact inv'.shape | exact inv'.states | exact inv'.probing | exact inv'.unique
    | exact inv'.count_eq | exact inv'.used_eq
    | (rename_i c' w' s' n' u'
       have := nFull_le_nUsed c' s'; have := inv'.used_eq; omega)
    | exact inv.shape | exact inv.states | exact inv.probing | exact inv.unique
    | exact inv.count_eq | exact inv.used_eq
    | (have := nFull_le_nUsed cap s; have := inv.shape.cap_pos; have := inv.used_eq; omega)
    | (refine ⟨shape', states', probing', unique', count', used', ?_⟩; omega)
    | (intro k' v'; rw [rel, rep'])
    | (intro k' v'; rw [rel]))

/-- `put` at the finite-map level. -/
theorem put_models {cap w s cap' w' s'} {k : Key} {v : Val} {m : SlotMap} (hm : Models cap w s m)
    (rel : ∀ k' v', Rep cap' w' s' k' v' ↔ (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ Rep cap w s k' v')) :
    Models cap' w' s' (m.put k v) := by
  intro k' v'
  change _ ↔ Rep cap' w' s' k' v'
  rw [rel, ← models_rep hm]; simp only [SlotMap.put]
  by_cases h : k' = k <;> simp [h, eq_comm]

#print axioms put.spec
