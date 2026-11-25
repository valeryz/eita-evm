import Velvet
import Slots.Dir
import Evm.CL.WorldSlotsModel

set_option velvet_vcgen.showVCReport true
set_option linter.unusedSimpArgs false

/-!
# The world: the per-account directory, against core's model

`c/world_slots.c` (the glue) mirrored as Velvet methods over a Lean picture of the C structs, and
proved to refine core's finite-map model `Evm.CL.WorldSlotsModel` (`lean/Evm/CL/WorldSlotsModel.lean`,
compiled into this package from core's file). These methods are not emitted: the
glue is their hand translation (one C statement per Lean step); every table decision they make is
a call to an emitted method.
-/

open Evm.CL.WorldSlotsModel (M Word)

/-- `ws_slots`: field for field (offsets 0, 8, 16, 24, 32). -/
structure Tbl where
  count : Nat
  used : Nat
  cap : Nat
  words : Array UInt64
  state : Array UInt8

/-- `ws_world`: `acct` is the directory (`n = acct.size`, `none` = NULL). `serial` is not modelled. -/
structure World where
  acct : Array (Option Tbl)

/-- `eita_ws_table`. -/
def tbl (W : World) (id : Nat) : Option Tbl := (W.acct[id]?).join

/-- A valid table: the table invariant (occupancy included) and capacity at least 4. -/
def TblOk (t : Tbl) : Prop := TableInv t.cap (t.cap - 1) t.words t.state t.count t.used ∧ 4 ≤ t.cap

def WOk (W : World) : Prop := ∀ i t, tbl W i = some t → TblOk t

/-! ## Words and limbs (least significant limb first, as `WorldSlotsVectors.ofLimbs`) -/

def toWord (x : W4) : Word :=
  BitVec.ofNat 256 (x.1.toNat + x.2.1.toNat * 2 ^ 64 + x.2.2.1.toNat * 2 ^ 128 + x.2.2.2.toNat * 2 ^ 192)

def ofWord (w : Word) : W4 :=
  (UInt64.ofNat (w.toNat % 2 ^ 64), UInt64.ofNat (w.toNat / 2 ^ 64 % 2 ^ 64),
   UInt64.ofNat (w.toNat / 2 ^ 128 % 2 ^ 64), UInt64.ofNat (w.toNat / 2 ^ 192 % 2 ^ 64))

theorem ofWord_toWord (x : W4) : ofWord (toWord x) = x := by
  obtain ⟨a, b, c, d⟩ := x
  have ha := a.toNat_lt; have hb := b.toNat_lt; have hc := c.toNat_lt; have hd := d.toNat_lt
  simp only [ofWord, toWord, BitVec.toNat_ofNat, Prod.mk.injEq]
  have hlt : a.toNat + b.toNat * 2 ^ 64 + c.toNat * 2 ^ 128 + d.toNat * 2 ^ 192 < 2 ^ 256 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply UInt64.toNat_inj.mp <;> simp only [UInt64.toNat_ofNat'] <;> omega

theorem toWord_ofWord (w : Word) : toWord (ofWord w) = w := by
  apply BitVec.eq_of_toNat_eq
  have hw := w.isLt
  simp only [ofWord, toWord, BitVec.toNat_ofNat, UInt64.toNat_ofNat']
  omega

theorem toWord_inj {x y : W4} (h : toWord x = toWord y) : x = y := by
  rw [← ofWord_toWord x, h, ofWord_toWord]

/-! ## The abstraction -/

/-- The finite map of a world: `(id, key) ↦ value` through ID's table, and table existence. -/
noncomputable def absW (W : World) : M where
  val id k := (tbl W id).bind fun t => (repMap t.cap t.words t.state (ofWord k)).map toWord
  has id := (tbl W id).isSome

theorem M_eq {a b : M} (hv : ∀ i j, a.val i j = b.val i j) (hh : ∀ i, a.has i = b.has i) : a = b := by
  cases a; cases b; congr 1 <;> funext <;> simp_all

/-! ## Directory lemmas -/

theorem tbl_grow (a : Array (Option Tbl)) (m i : Nat) :
    tbl ⟨a ++ Array.replicate m none⟩ i = tbl ⟨a⟩ i := by
  simp only [tbl, Array.getElem?_append]
  split
  · rfl
  · rename_i h
    simp only [Array.getElem?_replicate]
    rw [Array.getElem?_eq_none (by omega)]
    split <;> rfl

theorem tbl_set (a : Array (Option Tbl)) (id i : Nat) (x : Option Tbl) (h : id < a.size) :
    tbl ⟨a.set! id x⟩ i = if i = id then x else tbl ⟨a⟩ i := by
  simp only [tbl, Array.set!, Array.getElem?_setIfInBounds]
  by_cases e : i = id
  · subst e; simp [h]
  · simp [Ne.symm e, e]

theorem tbl_setIf (a : Array (Option Tbl)) (id i : Nat) (x : Option Tbl) (h : id < a.size) :
    tbl ⟨a.setIfInBounds id x⟩ i = if i = id then x else tbl ⟨a⟩ i := tbl_set a id i x h

/-- The grown directory (`eita_ws_touch`: a new pointer array of `n` entries, the old ones copied,
the rest NULL). -/
def growDir (a : Array (Option Tbl)) (n : Nat) : Array (Option Tbl) :=
  if n == a.size then a else a ++ Array.replicate (n - a.size) none

theorem tbl_growDir (a : Array (Option Tbl)) (n i : Nat) : tbl ⟨growDir a n⟩ i = tbl ⟨a⟩ i := by
  unfold growDir; split
  · rfl
  · exact tbl_grow a _ i

theorem size_growDir (a : Array (Option Tbl)) (n : Nat) (h : a.size ≤ n) : (growDir a n).size = n := by
  unfold growDir; split
  · simp_all
  · simp; omega

/-- `eita_ws_touch`: ID's table, created empty (4 entries) when it has none. -/
method touch (W : World) (id dmin : Nat) returns (r : World)
  requires ok: WOk W
  requires dpos: 0 < dmin
  signals idRange: W.acct.size ≤ id ∧ 1099511627776 ≤ id
  ensures ok': WOk r
  ensures lt: id < r.acct.size
  ensures other: ∀ i, i ≠ id → tbl r i = tbl W i
  ensures kept: ∀ t, tbl W id = some t → tbl r id = some t
  ensures new: tbl W id = none → ∃ t, tbl r id = some t ∧ t.count = 0 ∧ t.used = 0 ∧ t.cap = 4 ∧
                 ∀ k v, ¬ Rep t.cap t.words t.state k v
do
  let n ← dirGrow W.acct.size id dmin
  let acct := growDir W.acct n
  match tbl ⟨acct⟩ id with
  | some _ => return ⟨acct⟩
  | none =>
    let f ← fresh
    return ⟨acct.set! id (some ⟨0, 0, f.1, f.2.1, f.2.2⟩)⟩

prove_correct touch by
  intro W id dmin
  velvet_vcgen [touch] with try finish
  all_goals (
    have hsz : (growDir W.acct n).size = n := size_growDir _ _ mono
    have htg := tbl_growDir W.acct n
    have hid : id < (growDir W.acct n).size := by omega
    first
    | (intro i t h; rw [htg] at h; exact ok i t h)
    | omega
    | (intro i _; exact htg i)
    | (intro t h; rw [htg]; exact h)
    | (intro h; rw [htg] at h_some; simp_all [tbl])
    | (intro i t h
       rw [tbl_set _ _ _ _ hid] at h
       by_cases hi : i = id
       · rw [if_pos hi] at h; cases h; exact And.intro inv (by dsimp only; omega)
       · rw [if_neg hi, htg] at h; exact ok i t h)
    | (simp only [Array.size_set!]; omega)
    | (intro i hi; rw [tbl_set _ _ _ _ hid, if_neg hi, htg])
    | (intro t h; rw [htg] at h_none; simp_all [tbl]; done)
    | (intro _; exact ⟨_, by rw [tbl_set _ _ _ _ hid, if_pos rfl], rfl, rfl, cap4, noRep⟩)
    )
#print axioms touch.spec

/-! ## Maps of tables -/

/-- The map of a table. -/
noncomputable def tmap (t : Tbl) : SlotMap := repMap t.cap t.words t.state

theorem models_unique {c : Nat} {w : Array UInt64} {s : Array UInt8} {m1 m2 : SlotMap}
    (h1 : Models c w s m1) (h2 : Models c w s m2) : m1 = m2 := by
  funext x
  cases e1 : m1 x with
  | none =>
    cases e2 : m2 x with
    | none => rfl
    | some v => have := (h1 x v).mpr ((h2 x v).mp e2); rw [e1] at this; cases this
  | some v => exact ((h2 x v).mpr ((h1 x v).mp e1)).symm

theorem tmap_put {t t' : Tbl} (ut : Unique t.cap t.words t.state) (ut' : Unique t'.cap t'.words t'.state)
    {k : Key} {v : Val}
    (rel : ∀ k' v', Rep t'.cap t'.words t'.state k' v' ↔
      (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ Rep t.cap t.words t.state k' v')) :
    tmap t' = (tmap t).put k v :=
  models_unique (repMap_models ut') (put_models (repMap_models ut) rel)

theorem tmap_erase {t t' : Tbl} (ut : Unique t.cap t.words t.state) (ut' : Unique t'.cap t'.words t'.state)
    {k : Key} (hc : t'.cap = t.cap) (hw : t'.words = t.words)
    (rel : EraseRel t.cap t.words t.state t.words t'.state k) : tmap t' = (tmap t).erase k := by
  have := models_erase (repMap_models ut) rel
  unfold tmap; rw [hc, hw] at ut' ⊢
  exact models_unique (repMap_models ut') this

theorem tmap_erase' {t : Tbl} {c u : Nat} {s' : Array UInt8} (ut : Unique t.cap t.words t.state)
    (ut' : Unique t.cap t.words s') {k : Key} (rel : EraseRel t.cap t.words t.state t.words s' k) :
    tmap ⟨c, u, t.cap, t.words, s'⟩ = (tmap t).erase k :=
  tmap_erase (t' := ⟨c, u, t.cap, t.words, s'⟩) ut ut' rfl rfl rel

theorem tmap_empty {t : Tbl} (h : ∀ k v, ¬ Rep t.cap t.words t.state k v) : tmap t = fun _ => none := by
  funext x; unfold tmap repMap; rw [dif_neg]; rintro ⟨v, hv⟩; exact h x v hv

theorem absW_val (W : World) (i : Nat) (j : Word) :
    (absW W).val i j = (tbl W i).bind fun t => (tmap t (ofWord j)).map toWord := rfl

theorem absW_has (W : World) (i : Nat) : (absW W).has i = (tbl W i).isSome := rfl

theorem ofWord_eq_iff {j : Word} {k : W4} : ofWord j = k ↔ j = toWord k := by
  constructor
  · intro h; rw [← h, toWord_ofWord]
  · intro h; rw [h, ofWord_toWord]

/-- The table a touch leaves: the old one, or an empty one. -/
theorem touched_tmap {W W1 : World} {id : Nat} {t : Tbl}
    (kept : ∀ t, tbl W id = some t → tbl W1 id = some t)
    (new : tbl W id = none → ∃ t, tbl W1 id = some t ∧ t.count = 0 ∧ t.used = 0 ∧ t.cap = 4 ∧
             ∀ k v, ¬ Rep t.cap t.words t.state k v)
    (ht : tbl W1 id = some t) (j : Word) :
    (tmap t (ofWord j)).map toWord = (tbl W id).bind fun t => (tmap t (ofWord j)).map toWord := by
  cases e : tbl W id with
  | some t0 => rw [kept t0 e] at ht; cases ht; rfl
  | none =>
    obtain ⟨t1, h1, _, _, _, he⟩ := new e
    rw [h1] at ht; cases ht
    rw [tmap_empty he]; rfl

/-! ## `eita_ws_put` -/

method wput (W : World) (id dmin maxCap : Nat) (k0 k1 k2 k3 v0 v1 v2 v3 : UInt64) returns (r : World)
  requires ok: WOk W
  requires dpos: 0 < dmin
  signals aborts: (W.acct.size ≤ id ∧ 1099511627776 ≤ id) ∨
    (∃ t, tbl W id = some t ∧ 3 * t.cap ≤ 4 * (t.used + 1) ∧ maxCap < newCap t.cap t.count)
  ensures ok': WOk r
  ensures abs: absW r = Evm.CL.WorldSlotsModel.put (absW W) id (toWord (k0, k1, k2, k3)) (toWord (v0, v1, v2, v3))
do
  let W1 ← touch W id dmin
  match tbl W1 id with
  | none => oob
  | some t =>
    let p ← put t.cap t.words t.state t.count t.used k0 k1 k2 k3 v0 v1 v2 v3 maxCap
    return ⟨W1.acct.set! id (some ⟨p.2.2.2.1, p.2.2.2.2, p.1, p.2.1, p.2.2.1⟩)⟩

prove_correct wput by
  intro W id dmin maxCap k0 k1 k2 k3 v0 v1 v2 v3
  velvet_vcgen [wput, oob] with try finish
  all_goals try first
  | (exfalso
     cases e : tbl W id with
     | none => obtain ⟨t, h, _⟩ := new e; rw [h] at h_none; cases h_none
     | some t => rw [kept t e] at h_none; cases h_none)
  | exact (ok' id t h_some).1
  | exact (ok' id t h_some).2
  | (right
     cases e : tbl W id with
     | none =>
       obtain ⟨t1, h1, _, hu, hc, _⟩ := new e
       rw [h1] at h_some; cases h_some; omega
     | some t0 => rw [kept t0 e] at h_some; cases h_some; exact ⟨_, rfl, tooLarge⟩)
  | (intro i t' h
     rw [tbl_set _ _ _ _ lt] at h
     by_cases hi : i = id
     · rw [if_pos hi] at h; cases h; exact And.intro inv' (by dsimp only; omega)
     · rw [if_neg hi] at h; exact ok' i t' h)
  case abs =>
    (apply M_eq
     · intro i j
       simp only [Evm.CL.WorldSlotsModel.put]
       rw [absW_val, absW_val, tbl_set _ _ _ _ lt]
       by_cases hi : i = id
       · subst hi
         rw [if_pos rfl]
         have ut := (ok' _ t h_some).1.unique
         simp only [Option.bind_some]
         rw [tmap_put (t' := ⟨_, _, _, _, _⟩) ut inv'.unique rel]
         simp only [SlotMap.put]
         by_cases hj : ofWord j = (k0, k1, k2, k3)
         · rw [if_pos hj]; simp [ofWord_eq_iff.mp hj]
         · rw [if_neg hj]
           have hj' : ¬ j = toWord (k0, k1, k2, k3) := fun h => hj (ofWord_eq_iff.mpr h)
           simp only [hj', and_false, if_false]
           exact touched_tmap kept new h_some j
       · rw [if_neg hi, if_neg (fun h => hi h.1), other i hi]
     · intro i
       simp only [Evm.CL.WorldSlotsModel.put]
       rw [absW_has, absW_has, tbl_set _ _ _ _ lt]
       by_cases hi : i = id
       · simp [hi]
       · simp [hi, other i hi])
#print axioms wput.spec

/-! ## `eita_ws_remove` -/

method wremove (W : World) (id dmin : Nat) (k0 k1 k2 k3 : UInt64) returns (r : World)
  requires ok: WOk W
  requires dpos: 0 < dmin
  signals aborts: W.acct.size ≤ id ∧ 1099511627776 ≤ id
  ensures ok': WOk r
  ensures abs: absW r = Evm.CL.WorldSlotsModel.remove (absW W) id (toWord (k0, k1, k2, k3))
do
  let W1 ← touch W id dmin
  match tbl W1 id with
  | none => oob
  | some t =>
    let p ← remove t.cap t.words t.state t.count k0 k1 k2 k3
    return ⟨W1.acct.set! id (some ⟨p.2, t.used, t.cap, t.words, p.1⟩)⟩

prove_correct wremove by
  intro W id dmin k0 k1 k2 k3
  velvet_vcgen [wremove, oob] with try finish
  all_goals try first
  | (exfalso
     cases e : tbl W id with
     | none => obtain ⟨t, h, _⟩ := new e; rw [h] at h_none; cases h_none
     | some t => rw [kept t e] at h_none; cases h_none)
  | exact (ok' id t h_some).1.shape
  | exact (ok' id t h_some).1.states
  | exact (ok' id t h_some).1.probing
  | exact (ok' id t h_some).1.unique
  | exact (ok' id t h_some).1.count_eq
  | exact nFull_lt_of_inv (ok' id t h_some).1
  | (intro i t' h
     rw [tbl_set _ _ _ _ lt] at h
     by_cases hi : i = id
     · rw [if_pos hi] at h; cases h
       have iv := (ok' id t h_some).1
       exact And.intro ⟨shape', states', probing', unique', count', by rw [used']; exact iv.used_eq,
         by have := iv.occ; dsimp only; omega⟩ (by have := (ok' id t h_some).2; dsimp only; omega)
     · rw [if_neg hi] at h; exact ok' i t' h)
  case abs =>
    apply M_eq
    · intro i j
      simp only [Evm.CL.WorldSlotsModel.remove]
      rw [absW_val, absW_val, tbl_set _ _ _ _ lt]
      by_cases hi : i = id
      · subst hi
        rw [if_pos rfl]
        have ut := (ok' _ t h_some).1.unique
        simp only [Option.bind_some]
        rw [tmap_erase' ut unique' rel]
        simp only [SlotMap.erase]
        by_cases hj : ofWord j = (k0, k1, k2, k3)
        · rw [if_pos hj]; simp [ofWord_eq_iff.mp hj]
        · rw [if_neg hj]
          have hj' : ¬ j = toWord (k0, k1, k2, k3) := fun h => hj (ofWord_eq_iff.mpr h)
          simp only [hj', and_false, if_false]
          exact touched_tmap kept new h_some j
      · rw [if_neg hi, if_neg (fun h => hi h.1), other i hi]
    · intro i
      simp only [Evm.CL.WorldSlotsModel.remove]
      rw [absW_has, absW_has, tbl_set _ _ _ _ lt]
      by_cases hi : i = id
      · simp [hi]
      · simp [hi, other i hi]
#print axioms wremove.spec

/-! ## `eita_ws_drop`, `eita_ws_table`, `eita_ws_get` -/

method wdrop (W : World) (id : Nat) returns (r : World)
  requires ok: WOk W
  ensures ok': WOk r
  ensures size: r.acct.size = W.acct.size
  ensures gone: tbl r id = none
  ensures other: ∀ i, i ≠ id → tbl r i = tbl W i
  ensures abs: absW r = Evm.CL.WorldSlotsModel.drop (absW W) id
do
  if id < W.acct.size then return ⟨W.acct.set! id none⟩ else return W

theorem tbl_none_of_size {W : World} {id : Nat} (h : ¬ id < W.acct.size) : tbl W id = none := by
  simp only [tbl, Array.getElem?_eq_none (Nat.le_of_not_lt h), Option.join_none]

prove_correct wdrop by
  intro W id
  velvet_vcgen [wdrop] with try finish
  all_goals try first
  | (intro i t h; simp only [tbl_set _ _ _ _ if_cond, tbl_setIf _ _ _ _ if_cond] at h; split at h
     · cases h
     · exact ok i t h)
  | (simp [tbl_set _ _ _ _ if_cond, tbl_setIf _ _ _ _ if_cond]; done)
  | (intro i hi; simp [tbl_set _ _ _ _ if_cond, tbl_setIf _ _ _ _ if_cond, hi]; done)
  | exact tbl_none_of_size if_cond
  case abs =>
    apply M_eq
    · intro i j
      simp only [Evm.CL.WorldSlotsModel.drop]
      rw [absW_val, absW_val]
      simp only [tbl_set _ _ _ _ if_cond, tbl_setIf _ _ _ _ if_cond]
      by_cases hi : i = id <;> simp [hi]
    · intro i
      simp only [Evm.CL.WorldSlotsModel.drop]
      rw [absW_has, absW_has]
      simp only [tbl_set _ _ _ _ if_cond, tbl_setIf _ _ _ _ if_cond]
      by_cases hi : i = id <;> simp [hi]
  case abs =>
    apply M_eq
    · intro i j
      simp only [Evm.CL.WorldSlotsModel.drop]
      by_cases hi : i = id
      · subst hi; rw [absW_val, tbl_none_of_size if_cond]; simp
      · simp [hi]
    · intro i
      simp only [Evm.CL.WorldSlotsModel.drop]
      by_cases hi : i = id
      · subst hi; rw [absW_has, tbl_none_of_size if_cond]; simp
      · simp [hi]
#print axioms wdrop.spec

/-- `eita_ws_table(...) != NULL` is the model's `hasTable`. -/
theorem table_hasTable (W : World) (id : Nat) :
    (tbl W id).isSome = Evm.CL.WorldSlotsModel.hasTable (absW W) id := rfl

/-- `eita_ws_get`: the value limbs of (ID, KEY) (the C returns a pointer to them), or none. -/
method wget (W : World) (id : Nat) (k0 k1 k2 k3 : UInt64) returns (r : Option Val)
  requires ok: WOk W
  ensures abs: r.map toWord = Evm.CL.WorldSlotsModel.get (absW W) id (toWord (k0, k1, k2, k3))
do
  match tbl W id with
  | none => return none
  | some t =>
    let f ← lookup t.cap t.words t.state t.count t.used k0 k1 k2 k3
    if f.1 then return some (valAt t.words f.2) else return none

prove_correct wget by
  intro W id k0 k1 k2 k3
  velvet_vcgen [wget] with try finish
  all_goals try exact (ok id t h_some).1
  all_goals (simp only [Evm.CL.WorldSlotsModel.get]; rw [absW_val, ofWord_toWord])
  · rw [h_none]; rfl
  · rename_i fa fb
    have hm := (repMap_models (ok id t h_some).1.unique) (k0, k1, k2, k3) (valAt t.words fb)
    rw [h_some, Option.bind_some]
    unfold tmap
    rw [hm.mpr (hit if_cond).2]
  · rename_i fa fb
    rw [h_some, Option.bind_some]
    unfold tmap
    have hf : fa = false := by simpa using if_cond
    cases e : repMap t.cap t.words t.state (k0, k1, k2, k3) with
    | none => rfl
    | some v =>
      exact absurd ((repMap_models (ok id t h_some).1.unique _ _).mp e) (miss hf v)
#print axioms wget.spec

/-! ## `eita_ws_copy` -/

theorem absW_copy_of {D S R : World} {id : Nat}
    (h : ∀ i, tbl R i = if i = id then tbl S id else tbl D i) :
    absW R = Evm.CL.WorldSlotsModel.copy (absW D) (absW S) id := by
  apply M_eq
  · intro i j
    simp only [Evm.CL.WorldSlotsModel.copy]
    rw [absW_val, h i]
    by_cases hi : i = id
    · subst hi; simp [absW_val]
    · simp [hi, absW_val]
  · intro i
    simp only [Evm.CL.WorldSlotsModel.copy]
    rw [absW_has, h i]
    by_cases hi : i = id
    · subst hi; simp [absW_has]
    · simp [hi, absW_has]

/-- `eita_ws_copy` (DST, ID, SRC): ID's table in DST becomes a copy of SRC, ID's table in some
world S (or no table). -/
method wcopy (D : World) (id dmin : Nat) (src : Option Tbl) returns (r : World)
  given (S : World)
  requires okD: WOk D
  requires okS: WOk S
  requires hsrc: tbl S id = src
  requires dpos: 0 < dmin
  signals aborts: src.isSome ∧ D.acct.size ≤ id ∧ 1099511627776 ≤ id
  ensures ok': WOk r
  ensures abs: absW r = Evm.CL.WorldSlotsModel.copy (absW D) (absW S) id
do
  let D1 ← wdrop D id
  match src with
  | none => return D1
  | some s =>
    let D2 ← touch D1 id dmin
    let c ← copyArrs s.cap s.words s.state
    return ⟨D2.acct.set! id (some ⟨s.count, s.used, s.cap, c.1, c.2⟩)⟩

prove_correct wcopy by
  intro D id dmin src S
  velvet_vcgen [wcopy] with try finish
  all_goals try first
  | exact (okS id t (hsrc.trans h_some)).1.shape.w_size
  | exact (okS id t (hsrc.trans h_some)).1.shape.s_size
  | (refine ⟨by rw [h_some]; rfl, by omega, idRange.2⟩)
  | (apply absW_copy_of; intro i
     by_cases hi : i = id
     · subst hi; rw [gone, if_pos rfl, hsrc, h_none]
     · rw [if_neg hi, other i hi])
  | (intro i t' h
     simp only [tbl_set _ _ _ _ lt, tbl_setIf _ _ _ _ lt] at h
     by_cases hi : i = id
     · rw [if_pos hi] at h; cases h; rw [same_w, same_s]; exact okS id t (hsrc.trans h_some)
     · rw [if_neg hi] at h; exact ok'_1 i t' h)
  | (apply absW_copy_of; intro i
     simp only [tbl_set _ _ _ _ lt, tbl_setIf _ _ _ _ lt]
     by_cases hi : i = id
     · subst hi; rw [if_pos rfl, if_pos rfl, hsrc, h_some, same_w, same_s]
     · rw [if_neg hi, if_neg hi, other_1 i hi, other i hi])
#print axioms wcopy.spec

/-! ## `eita_ws_map`: the walk -/

/-- The full entries of a table, in index order. -/
def fullIdx (cap : Nat) (s : Array UInt8) : List Nat := (List.range cap).filter (fun i => s[i]! == 1)

theorem range_filter_skip {i j : Nat} {f : Nat → Bool} (hij : i ≤ j) (h : ∀ l, i ≤ l → l < j → f l = false) :
    (List.range j).filter f = (List.range i).filter f := by
  induction j with
  | zero => have : i = 0 := by omega
            subst this; rfl
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with h' | h'
    · rw [List.range_succ, List.filter_append, ih (by omega) (fun l h1 h2 => h l h1 (by omega))]
      simp [h j (by omega) (by omega)]
    · subst h'; rfl

/-- The index sequence `eita_ws_map` visits: `i := next 0; while i < cap: visit i; i := next (i+1)`. -/
method walk (cap : Nat) (s : Array UInt8) returns (l : List Nat)
  requires s_size: s.size = cap
  ensures order: l = fullIdx cap s
do
  let mut acc : List Nat := []
  let mut i ← next cap s 0
  while i < cap
    invariant i_le: i ≤ cap
    invariant acc_eq: acc = (List.range i).filter (fun l => s[l]! == 1)
    invariant at_full: i < cap → s[i]! = 1
    decreasing cap - i
  do
    acc := acc ++ [i]
    i ← next cap s (i + 1)
  return acc

prove_correct walk by
  intro cap s
  velvet_vcgen [walk] with try finish
  all_goals first
  | (rw [range_filter_skip (i := 0) (Nat.zero_le _) (fun l _ h2 => by simpa using skipped l (Nat.zero_le _) h2)]; rfl)
  | (rw [range_filter_skip (i := i + 1) j_ge_1 (fun l h1 h2 => by simpa using skipped_1 l h1 h2),
         List.range_succ, List.filter_append, acc_eq]
     simp [at_full h_loop])
  | (have : i = cap := by omega
     subst this; exact acc_eq)
#print axioms walk.spec

theorem nodup_map_of_inj_on {l : List Nat} {β} {f : Nat → β} (h : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y)
    (hl : l.Nodup) : (l.map f).Nodup := by
  unfold List.Nodup; rw [List.pairwise_map]
  exact List.Pairwise.imp_of_mem (fun ha hb hne e => hne (h _ ha _ hb e)) hl

/-- The walk visits exactly the present keys, each once: the entries at `fullIdx` are the table's
`Rep` pairs, and their keys are distinct (so `eita_ws_map` calls FN once per present key, in
index order, as core's loop `for i < cap: if state[i] == 1`). -/
theorem walk_rep {cap : Nat} {w : Array UInt64} {s : Array UInt8} (un : Unique cap w s) :
    (∀ k v, Rep cap w s k v ↔ ∃ i ∈ fullIdx cap s, keyAt w i = k ∧ valAt w i = v) ∧
    ((fullIdx cap s).map (keyAt w)).Nodup := by
  refine ⟨fun k v => ?_, ?_⟩
  · constructor
    · rintro ⟨i, hi, fi, ki, vi⟩
      exact ⟨i, by simp [fullIdx, hi, fi], ki, vi⟩
    · rintro ⟨i, hm, ki, vi⟩
      simp only [fullIdx, List.mem_filter, List.mem_range, beq_iff_eq] at hm
      exact ⟨i, hm.1, hm.2, ki, vi⟩
  · apply nodup_map_of_inj_on
    · intro a ha b hb e
      simp only [fullIdx, List.mem_filter, List.mem_range, beq_iff_eq] at ha hb
      exact un a ha.1 b hb.1 ha.2 hb.2 e
    · exact (List.nodup_range).filter _
#print axioms walk_rep
