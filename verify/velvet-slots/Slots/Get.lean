import Velvet
import Slots.Put

set_option velvet_vcgen.showVCReport true

/-- `eita_ws_get` on a table (`slots-get`): `(true, i)` with the value at entry `i`'s value
limbs (the C returns `words + 8 i + 4`), or `(false, _)`. Ghost-free; `lookup_models` below
states it against the finite map. -/
method lookup (cap : Nat) (w : Array UInt64) (s : Array UInt8) (count used : Nat)
    (k0 k1 k2 k3 : UInt64)
  returns (r : Bool × Nat)
  requires inv: TableInv cap (cap - 1) w s count used
  ensures hit: r.1 = true → r.2 < cap ∧ Rep cap w s (k0, k1, k2, k3) (valAt w r.2)
  ensures miss: r.1 = false → ∀ v, ¬ Rep cap w s (k0, k1, k2, k3) v
do
  let f ← find cap w s k0 k1 k2 k3
  return f

theorem nFull_lt_of_inv {cap mask w s count used} (inv : TableInv cap mask w s count used) :
    nFull cap s < cap := by
  have := nFull_le_nUsed cap s; have := inv.occ; have := inv.used_eq; have := inv.shape.cap_pos; omega

prove_correct lookup by
  intro cap w s count used k0 k1 k2 k3
  velvet_vcgen [lookup] with try finish
  all_goals try (first
    | exact inv.shape | exact inv.states | exact inv.probing
    | exact nFull_lt_of_inv inv)
  all_goals try (
    rename_i fa fb
    first
    | (intro h; have hf := found h
       exact ⟨r_lt, fb, r_lt, hf.1, hf.2, rfl⟩)
    | (intro h v ⟨j, hj, fj, kj, _⟩
       exact absent h j hj fj kj))

theorem lookup_models {cap w s} {m : SlotMap} {k : Key} (hm : Models cap w s m) :
    (∀ i, Rep cap w s k (valAt w i) → m k = some (valAt w i)) ∧
    ((∀ v, ¬ Rep cap w s k v) → m k = none) := by
  refine ⟨fun i h => (hm _ _).mpr h, fun h => ?_⟩
  cases e : m k with
  | none => rfl
  | some v => exact absurd ((hm _ _).mp e) (h v)

/-- Removal at the model level: `remove`'s `EraseRel` turned into `Models … (m.erase k)`. -/
theorem remove_models {cap w s s' k m} (hm : Models cap w s m) (hr : EraseRel cap w s w s' k) :
    Models cap w s' (m.erase k) := models_erase hm hr

#print axioms lookup.spec
#print axioms remove.spec
#print axioms place.spec
#print axioms next.spec
#print axioms create.spec
#print axioms grow.spec
