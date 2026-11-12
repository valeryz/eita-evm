import Slots.Model

/-!
Frame and transfer lemmas: how the representation predicates change under the three writes the
table performs (write key+value at a free slot, overwrite a value, tombstone a slot), and the
counting lemmas for `count` / `used`.
-/

/-! ## Writes -/

/-- Write key and value limbs of slot `i` (the order `slots-put` writes them). -/
def setKV (w : Array UInt64) (i : Nat) (k : Key) (v : Val) : Array UInt64 :=
  ((((((((w.set! (8*i) k.1).set! (8*i+1) k.2.1).set! (8*i+2) k.2.2.1).set! (8*i+3) k.2.2.2).set! (8*i+4) v.1).set! (8*i+5) v.2.1).set! (8*i+6) v.2.2.1).set! (8*i+7) v.2.2.2)

/-- Overwrite the value limbs of slot `i`. -/
def setV (w : Array UInt64) (i : Nat) (v : Val) : Array UInt64 :=
  ((((w.set! (8*i+4) v.1).set! (8*i+5) v.2.1).set! (8*i+6) v.2.2.1).set! (8*i+7) v.2.2.2)

theorem get_set {α} [Inhabited α] (xs : Array α) (i j : Nat) (x : α) (hi : i < xs.size) :
    (xs.set! i x)[j]! = if i = j then x else xs[j]! := by
  split
  · subst_vars; exact Array.getElem!_set!_self xs _ x hi
  · exact Array.getElem!_set!_ne xs i j x (by assumption)

theorem gs_eq {α} [Inhabited α] (xs : Array α) (i : Nat) (x : α) (hi : i < xs.size) :
    (xs.set! i x)[i]! = x := Array.getElem!_set!_self xs i x hi

theorem gs_ne {α} [Inhabited α] (xs : Array α) (i j : Nat) (x : α) (h : i ≠ j) :
    (xs.set! i x)[j]! = xs[j]! := Array.getElem!_set!_ne xs i j x h

@[simp] theorem size_set!' {α} (xs : Array α) (i : Nat) (x : α) : (xs.set! i x).size = xs.size := by
  simp

@[simp] theorem size_setKV (w : Array UInt64) (i : Nat) (k : Key) (v : Val) :
    (setKV w i k v).size = w.size := by simp [setKV]

@[simp] theorem size_setV (w : Array UInt64) (i : Nat) (v : Val) : (setV w i v).size = w.size := by
  simp [setV]

theorem keyAt_setKV {w : Array UInt64} {i : Nat} {k : Key} {v : Val} (hi : 8*i+7 < w.size) (j : Nat) :
    keyAt (setKV w i k v) j = if j = i then k else keyAt w j := by
  by_cases h : j = i
  · subst h; rw [if_pos rfl]
    simp (disch := (first | (simp only [Array.size_set!]; omega) | omega)) only [setKV, setV, keyAt, valAt, gs_eq, gs_ne]
  · rw [if_neg h]
    simp (disch := omega) only [setKV, setV, keyAt, valAt, gs_ne]

theorem valAt_setKV {w : Array UInt64} {i : Nat} {k : Key} {v : Val} (hi : 8*i+7 < w.size) (j : Nat) :
    valAt (setKV w i k v) j = if j = i then v else valAt w j := by
  by_cases h : j = i
  · subst h; rw [if_pos rfl]
    simp (disch := (first | (simp only [Array.size_set!]; omega) | omega)) only [setKV, setV, keyAt, valAt, gs_eq, gs_ne]
  · rw [if_neg h]
    simp (disch := omega) only [setKV, setV, keyAt, valAt, gs_ne]

theorem keyAt_setV {w : Array UInt64} {i : Nat} {v : Val} (hi : 8*i+7 < w.size) (j : Nat) :
    keyAt (setV w i v) j = keyAt w j := by
  simp (disch := omega) only [setKV, setV, keyAt, valAt, gs_ne]

theorem valAt_setV {w : Array UInt64} {i : Nat} {v : Val} (hi : 8*i+7 < w.size) (j : Nat) :
    valAt (setV w i v) j = if j = i then v else valAt w j := by
  by_cases h : j = i
  · subst h; rw [if_pos rfl]
    simp (disch := (first | (simp only [Array.size_set!]; omega) | omega)) only [setKV, setV, keyAt, valAt, gs_eq, gs_ne]
  · rw [if_neg h]
    simp (disch := omega) only [setKV, setV, keyAt, valAt, gs_ne]

theorem homeAt_eq (mask : Nat) (w : Array UInt64) (j : Nat) :
    homeAt mask w j = hashIdx (keyAt w j).1 (keyAt w j).2.1 mask := rfl

/-! ## Counting -/

def cnt (n : Nat) (f : Nat → Bool) : Nat := ((List.range n).filter f).length

theorem cnt_update (n i : Nat) (f g : Nat → Bool) (h : ∀ j, j ≠ i → f j = g j) :
    cnt n g + (if i < n ∧ f i then 1 else 0) = cnt n f + (if i < n ∧ g i then 1 else 0) := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    simp only [cnt, List.range_succ, List.filter_append, List.length_append] at *
    by_cases hi : i = n
    · subst hi
      have e : ((List.range i).filter g).length = ((List.range i).filter f).length := by
        congr 1; apply List.filter_congr; intro x hx; have := List.mem_range.mp hx
        exact (h x (by omega)).symm
      rw [e]; simp only [List.filter_cons, List.filter_nil, Nat.lt_irrefl, false_and, if_false, Nat.lt_succ_self, true_and] at *
      cases f i <;> cases g i <;> simp
    · have e1 : List.filter g [n] = List.filter f [n] := by simp [List.filter_cons, List.filter_nil, h n (Ne.symm hi)]
      rw [e1]
      by_cases hl : i < n
      · have : i < n + 1 := by omega
        simp only [hl, this, true_and] at ih ⊢; omega
      · have : ¬ i < n + 1 := by omega
        simp only [hl, this, false_and, if_false] at ih ⊢; omega

theorem cnt_mono (n : Nat) (f g : Nat → Bool) (h : ∀ j, j < n → f j = true → g j = true) :
    cnt n f ≤ cnt n g := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    simp only [cnt, List.range_succ, List.filter_append, List.length_append] at *
    have := ih (fun j hj => h j (by omega))
    have hn := h n (by omega)
    cases hf : f n <;> cases hg : g n <;> simp [List.filter_cons, List.filter_nil, hf, hg]
    all_goals first | omega | simp_all

theorem nFull_le_nUsed (cap : Nat) (s : Array UInt8) : nFull cap s ≤ nUsed cap s :=
  cnt_mono cap _ _ (fun j _ hj => by simp at hj ⊢; rw [hj]; decide)

theorem nFull_set (cap i : Nat) (s : Array UInt8) (x : UInt8) (hs : s.size = cap) (hi : i < cap) :
    nFull cap (s.set! i x) + (if s[i]! = 1 then 1 else 0) = nFull cap s + (if x = 1 then 1 else 0) := by
  have := cnt_update cap i (fun j => s[j]! == 1) (fun j => (s.set! i x)[j]! == 1)
    (fun j hj => by simp only [get_set s i j x (by omega), if_neg (Ne.symm hj)])
  simp only [get_set s i i x (by omega), if_pos rfl, hi, true_and, beq_iff_eq] at this
  unfold nFull; simpa [cnt] using this

theorem nUsed_set (cap i : Nat) (s : Array UInt8) (x : UInt8) (hs : s.size = cap) (hi : i < cap) :
    nUsed cap (s.set! i x) + (if s[i]! ≠ 0 then 1 else 0) = nUsed cap s + (if x ≠ 0 then 1 else 0) := by
  have := cnt_update cap i (fun j => s[j]! != 0) (fun j => (s.set! i x)[j]! != 0)
    (fun j hj => by simp only [get_set s i j x (by omega), if_neg (Ne.symm hj)])
  simp only [get_set s i i x (by omega), if_pos rfl, hi, true_and, bne_iff_ne, ne_eq] at this
  unfold nUsed; simpa [cnt] using this

/-! ## Representation transfer -/

/-- `Rep`: the table holds `k ↦ v`. -/
def Rep (cap : Nat) (w : Array UInt64) (s : Array UInt8) (k : Key) (v : Val) : Prop :=
  ∃ i < cap, s[i]! = 1 ∧ keyAt w i = k ∧ valAt w i = v

theorem models_iff {cap w s m} : Models cap w s m ↔ ∀ k v, m k = some v ↔ Rep cap w s k v := Iff.rfl

section new
variable {cap mask ins : Nat} {w : Array UInt64} {s : Array UInt8} {k : Key} {v : Val}

/-- Writing a new key at a free slot `ins` reachable from the key's home. -/
structure NewSlot (cap mask : Nat) (w : Array UInt64) (s : Array UInt8) (k : Key) (ins : Nat) : Prop where
  ins_lt : ins < cap
  free : s[ins]! ≠ 1
  absent : ∀ j < cap, s[j]! = 1 → keyAt w j ≠ k
  path : ∀ d < dist cap (hashIdx k.1 k.2.1 mask) ins, s[(hashIdx k.1 k.2.1 mask + d) % cap]! ≠ 0

theorem new_shape (sh : Shape cap mask w s) (ns : NewSlot cap mask w s k ins) :
    Shape cap mask (setKV w ins k v) (s.set! ins 1) :=
  ⟨sh.cap_pos, sh.mask_eq, sh.mask_mod, by simp [sh.w_size], by simp [sh.s_size], sh.pow⟩

theorem new_states (sh : Shape cap mask w s) (st : StatesOk cap s) (ns : NewSlot cap mask w s k ins) :
    StatesOk cap (s.set! ins 1) := by
  intro j hj; rw [get_set _ _ _ _ (by rw [sh.s_size]; exact ns.ins_lt)]
  split
  · exact Or.inr (Or.inl rfl)
  · exact st j hj

theorem new_probing (sh : Shape cap mask w s) (pr : Probing cap mask w s) (ns : NewSlot cap mask w s k ins) :
    Probing cap mask (setKV w ins k v) (s.set! ins 1) := by
  have hw : 8*ins+7 < w.size := by rw [sh.w_size]; have := ns.ins_lt; omega
  have hs : ins < s.size := by rw [sh.s_size]; exact ns.ins_lt
  intro j hj hf d hd
  rw [homeAt_eq, keyAt_setKV hw] at hd ⊢
  rw [get_set _ _ _ _ hs] at hf ⊢
  by_cases hji : j = ins
  · subst hji; simp only [if_true] at hd ⊢
    split
    · simp
    · exact ns.path d hd
  · simp only [hji, if_false] at hd ⊢
    have hf' : s[j]! = 1 := by simpa [Ne.symm hji] using hf
    split
    · simp
    · exact pr j hj hf' d hd

theorem new_unique (sh : Shape cap mask w s) (un : Unique cap w s) (ns : NewSlot cap mask w s k ins) :
    Unique cap (setKV w ins k v) (s.set! ins 1) := by
  have hw : 8*ins+7 < w.size := by rw [sh.w_size]; have := ns.ins_lt; omega
  have hs : ins < s.size := by rw [sh.s_size]; exact ns.ins_lt
  intro i hi j hj fi fj e
  rw [get_set _ _ _ _ hs] at fi fj
  rw [keyAt_setKV hw, keyAt_setKV hw] at e
  by_cases h1 : i = ins <;> by_cases h2 : j = ins
  · omega
  · simp only [h1, h2, if_true, if_false, show ins ≠ j from Ne.symm h2] at e fj
    exact absurd e.symm (ns.absent j hj fj)
  · simp only [h1, h2, if_true, if_false, show ins ≠ i from Ne.symm h1] at e fi
    exact absurd e (ns.absent i hi fi)
  · simp only [h1, h2, if_false, show ins ≠ i from Ne.symm h1, show ins ≠ j from Ne.symm h2] at e fi fj
    exact un i hi j hj fi fj e

theorem new_rep (sh : Shape cap mask w s) (ns : NewSlot cap mask w s k ins) (k' : Key) (v' : Val) :
    Rep cap (setKV w ins k v) (s.set! ins 1) k' v' ↔
      (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ Rep cap w s k' v') := by
  have hw : 8*ins+7 < w.size := by rw [sh.w_size]; have := ns.ins_lt; omega
  have hs : ins < s.size := by rw [sh.s_size]; exact ns.ins_lt
  simp only [Rep, keyAt_setKV hw, valAt_setKV hw, get_set _ _ _ _ hs]
  constructor
  · rintro ⟨i, hi, fi, ki, vi⟩
    by_cases h : i = ins
    · subst h; simp at ki vi; exact Or.inl ⟨ki.symm, vi.symm⟩
    · simp only [h, if_false, show ins ≠ i from Ne.symm h] at ki vi fi
      exact Or.inr ⟨fun e => ns.absent i hi fi (e ▸ ki), i, hi, fi, ki, vi⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hne, i, hi, fi, ki, vi⟩)
    · exact ⟨ins, ns.ins_lt, by simp, by simp, by simp⟩
    · have h : i ≠ ins := fun e => by subst e; exact ns.free fi
      exact ⟨i, hi, by simp [Ne.symm h, fi], by simp [h, ki], by simp [h, vi]⟩

theorem new_models (sh : Shape cap mask w s) (ns : NewSlot cap mask w s k ins) {m : SlotMap}
    (hm : Models cap w s m) : Models cap (setKV w ins k v) (s.set! ins 1) (m.put k v) := by
  intro k' v'
  have hm' : m k' = some v' ↔ Rep cap w s k' v' := hm k' v'
  change _ ↔ Rep cap (setKV w ins k v) (s.set! ins 1) k' v'
  rw [new_rep sh ns, ← hm']
  simp only [SlotMap.put]
  by_cases h : k' = k <;> simp [h, eq_comm]

end new

section upd
variable {cap mask i : Nat} {w : Array UInt64} {s : Array UInt8} {k : Key} {v : Val}

theorem upd_shape (sh : Shape cap mask w s) : Shape cap mask (setV w i v) s :=
  ⟨sh.cap_pos, sh.mask_eq, sh.mask_mod, by simp [sh.w_size], sh.s_size, sh.pow⟩

theorem upd_probing (sh : Shape cap mask w s) (hi : i < cap) (pr : Probing cap mask w s) :
    Probing cap mask (setV w i v) s := by
  have hw : 8*i+7 < w.size := by rw [sh.w_size]; omega
  intro j hj hf d hd; rw [homeAt_eq, keyAt_setV hw] at hd ⊢; exact pr j hj hf d hd

theorem upd_unique (sh : Shape cap mask w s) (hi : i < cap) (un : Unique cap w s) :
    Unique cap (setV w i v) s := by
  have hw : 8*i+7 < w.size := by rw [sh.w_size]; omega
  intro a ha b hb fa fb e; rw [keyAt_setV hw, keyAt_setV hw] at e; exact un a ha b hb fa fb e

theorem upd_models (sh : Shape cap mask w s) (hi : i < cap) (un : Unique cap w s)
    (fi : s[i]! = 1) (ki : keyAt w i = k) {m : SlotMap} (hm : Models cap w s m) :
    Models cap (setV w i v) s (m.put k v) := by
  have hw : 8*i+7 < w.size := by rw [sh.w_size]; omega
  intro k' v'
  simp only [SlotMap.put]
  constructor
  · intro h
    by_cases hk : k' = k
    · simp only [hk, if_true, Option.some.injEq] at h; subst h; subst hk
      exact ⟨i, hi, fi, by rw [keyAt_setV hw]; exact ki, by simp [valAt_setV hw]⟩
    · simp only [hk, if_false] at h
      obtain ⟨j, hj, fj, kj, vj⟩ := (hm k' v').mp h
      have : j ≠ i := fun e => hk (by subst e; rw [← kj, ki])
      exact ⟨j, hj, fj, by rw [keyAt_setV hw]; exact kj, by simp [valAt_setV hw, this, vj]⟩
  · rintro ⟨j, hj, fj, kj, vj⟩
    rw [keyAt_setV hw] at kj
    by_cases hji : j = i
    · subst hji; simp [valAt_setV hw] at vj; simp [← kj, ki, vj]
    · have hk : k' ≠ k := fun e => hji (un j hj i hi fj fi (by rw [kj, ki, e]))
      simp only [hk, if_false]
      exact (hm k' v').mpr ⟨j, hj, fj, kj, by simpa [valAt_setV hw, hji] using vj⟩

end upd

section rm
variable {cap mask i : Nat} {w : Array UInt64} {s : Array UInt8} {k : Key}

theorem rm_shape (sh : Shape cap mask w s) : Shape cap mask w (s.set! i 2) :=
  ⟨sh.cap_pos, sh.mask_eq, sh.mask_mod, sh.w_size, by simp [sh.s_size], sh.pow⟩

theorem rm_states (sh : Shape cap mask w s) (hi : i < cap) (st : StatesOk cap s) :
    StatesOk cap (s.set! i 2) := by
  intro j hj; rw [get_set _ _ _ _ (by rw [sh.s_size]; exact hi)]
  split
  · exact Or.inr (Or.inr rfl)
  · exact st j hj

theorem rm_probing (sh : Shape cap mask w s) (hi : i < cap) (pr : Probing cap mask w s) :
    Probing cap mask w (s.set! i 2) := by
  have hs : i < s.size := by rw [sh.s_size]; exact hi
  intro j hj hf d hd
  rw [get_set _ _ _ _ hs] at hf ⊢
  have hf' : s[j]! = 1 := by split at hf <;> simp_all
  split
  · simp
  · exact pr j hj hf' d hd

theorem rm_unique (sh : Shape cap mask w s) (hi : i < cap) (un : Unique cap w s) :
    Unique cap w (s.set! i 2) := by
  have hs : i < s.size := by rw [sh.s_size]; exact hi
  intro a ha b hb fa fb e
  rw [get_set _ _ _ _ hs] at fa fb
  have fa' : s[a]! = 1 := by split at fa <;> simp_all
  have fb' : s[b]! = 1 := by split at fb <;> simp_all
  exact un a ha b hb fa' fb' e

theorem rm_models (sh : Shape cap mask w s) (hi : i < cap) (un : Unique cap w s)
    (fi : s[i]! = 1) (ki : keyAt w i = k) {m : SlotMap} (hm : Models cap w s m) :
    Models cap w (s.set! i 2) (m.erase k) := by
  have hs : i < s.size := by rw [sh.s_size]; exact hi
  intro k' v'
  simp only [SlotMap.erase]
  constructor
  · intro h
    by_cases hk : k' = k
    · simp [hk] at h
    · simp only [hk, if_false] at h
      obtain ⟨j, hj, fj, kj, vj⟩ := (hm k' v').mp h
      have : i ≠ j := fun e => hk (by subst e; rw [← kj, ki])
      exact ⟨j, hj, by rw [get_set _ _ _ _ hs, if_neg this]; exact fj, kj, vj⟩
  · rintro ⟨j, hj, fj, kj, vj⟩
    rw [get_set _ _ _ _ hs] at fj
    by_cases hij : i = j
    · simp [hij] at fj
    · simp only [hij, if_false] at fj
      have hk : k' ≠ k := fun e => hij (un i hi j hj fi fj (by rw [ki, kj, e]))
      simp only [hk, if_false]
      exact (hm k' v').mpr ⟨j, hj, fj, kj, vj⟩

end rm

/-! ## From `Models` to `Rep` -/

open Classical in
/-- The map a table with unique keys represents. -/
noncomputable def repMap (cap : Nat) (w : Array UInt64) (s : Array UInt8) : SlotMap :=
  fun k => if h : ∃ v, Rep cap w s k v then some (Classical.choose h) else none

theorem rep_val_unique {cap : Nat} {w : Array UInt64} {s : Array UInt8} (un : Unique cap w s)
    {k : Key} {v1 v2 : Val} (h1 : Rep cap w s k v1) (h2 : Rep cap w s k v2) : v1 = v2 := by
  obtain ⟨i, hi, fi, ki, vi⟩ := h1; obtain ⟨j, hj, fj, kj, vj⟩ := h2
  have := un i hi j hj fi fj (by rw [ki, kj]); subst this; rw [← vi, ← vj]

theorem repMap_models {cap : Nat} {w : Array UInt64} {s : Array UInt8} (un : Unique cap w s) :
    Models cap w s (repMap cap w s) := by
  intro k v
  change repMap cap w s k = some v ↔ Rep cap w s k v
  unfold repMap
  split
  · rename_i h
    constructor
    · intro e; cases e; exact Classical.choose_spec h
    · intro hv; rw [rep_val_unique un (Classical.choose_spec h) hv]
  · rename_i h
    constructor
    · intro e; cases e
    · intro hv; exact absurd ⟨v, hv⟩ h

theorem models_rep {cap w s m} (hm : Models cap w s m) (k : Key) (v : Val) :
    m k = some v ↔ Rep cap w s k v := hm k v

/-- Put, at the `Rep` level. -/
def PutRel (cap : Nat) (w : Array UInt64) (s : Array UInt8) (w' : Array UInt64) (s' : Array UInt8)
    (k : Key) (v : Val) : Prop :=
  ∀ k' v', Rep cap w' s' k' v' ↔ (k' = k ∧ v' = v) ∨ (k' ≠ k ∧ Rep cap w s k' v')

def EraseRel (cap : Nat) (w : Array UInt64) (s : Array UInt8) (w' : Array UInt64) (s' : Array UInt8)
    (k : Key) : Prop :=
  ∀ k' v', Rep cap w' s' k' v' ↔ (k' ≠ k ∧ Rep cap w s k' v')

theorem models_put {cap w s w' s' k v m} (hm : Models cap w s m) (hr : PutRel cap w s w' s' k v) :
    Models cap w' s' (m.put k v) := by
  intro k' v'
  change _ ↔ Rep cap w' s' k' v'
  rw [hr, ← models_rep hm]; simp only [SlotMap.put]
  by_cases h : k' = k <;> simp [h, eq_comm]

theorem models_erase {cap w s w' s' k m} (hm : Models cap w s m) (hr : EraseRel cap w s w' s' k) :
    Models cap w' s' (m.erase k) := by
  intro k' v'
  change _ ↔ Rep cap w' s' k' v'
  rw [hr, ← models_rep hm]; simp only [SlotMap.erase]
  by_cases h : k' = k <;> simp [h]

theorem new_putrel {cap mask ins w s k v} (sh : Shape cap mask w s) (ns : NewSlot cap mask w s k ins) :
    PutRel cap w s (setKV w ins k v) (s.set! ins 1) k v := new_rep sh ns

theorem upd_putrel {cap mask i w s k v} (sh : Shape cap mask w s) (hi : i < cap) (un : Unique cap w s)
    (fi : s[i]! = 1) (ki : keyAt w i = k) : PutRel cap w s (setV w i v) s k v := by
  intro k' v'
  have h1 := upd_models (v := v) sh hi un fi ki (repMap_models un) k' v'
  change _ ↔ Rep cap (setV w i v) s k' v' at h1
  rw [← h1]; simp only [SlotMap.put]
  by_cases h : k' = k
  · simp [h, eq_comm]
  · simp only [h, if_false, false_and, false_or, ne_eq, not_false_eq_true, true_and]
    exact models_rep (repMap_models un) k' v'

theorem rm_eraserel {cap mask i w s k} (sh : Shape cap mask w s) (hi : i < cap) (un : Unique cap w s)
    (fi : s[i]! = 1) (ki : keyAt w i = k) : EraseRel cap w s w (s.set! i 2) k := by
  intro k' v'
  have h1 := rm_models sh hi un fi ki (repMap_models un) k' v'
  change _ ↔ Rep cap w (s.set! i 2) k' v' at h1
  rw [← h1]; simp only [SlotMap.erase]
  by_cases h : k' = k
  · simp [h]
  · simp only [h, if_false, ne_eq, not_false_eq_true, true_and]
    exact models_rep (repMap_models un) k' v'

/-! ## Rehash support -/

theorem cnt_congr (n : Nat) (f g : Nat → Bool) (h : ∀ i < n, f i = g i) : cnt n f = cnt n g := by
  unfold cnt; congr 1; apply List.filter_congr; intro x hx; exact h x (List.mem_range.mp hx)

theorem cnt_succ (n : Nat) (f : Nat → Bool) : cnt (n + 1) f = cnt n f + (if f n then 1 else 0) := by
  unfold cnt; simp only [List.range_succ, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]; split <;> simp_all

theorem cnt_le (n m : Nat) (f : Nat → Bool) (h : n ≤ m) : cnt n f ≤ cnt m f := by
  induction m with
  | zero => have : n = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ m ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | h'
    · rw [cnt_succ]; have := ih (by omega); omega
    · subst h'; exact Nat.le_refl _

theorem nUsed_eq_nFull {cap : Nat} {s : Array UInt8} (st : StatesOk cap s) (nt : ∀ i < cap, s[i]! ≠ 2) :
    nUsed cap s = nFull cap s := by
  unfold nUsed nFull
  have := cnt_congr cap (fun i => s[i]! != 0) (fun i => s[i]! == 1) (fun i hi => by
    rcases st i hi with h | h | h
    · simp [h]
    · simp [h]
    · exact absurd h (nt i hi))
  simpa [cnt] using this

theorem rep_succ {cap j : Nat} {w : Array UInt64} {s : Array UInt8} (un : Unique cap w s) (hj : j < cap)
    (fj : s[j]! = 1) (k : Key) (v : Val) :
    Rep (j + 1) w s k v ↔ (k = keyAt w j ∧ v = valAt w j) ∨ (k ≠ keyAt w j ∧ Rep j w s k v) := by
  constructor
  · rintro ⟨i, hi, fi, ki, vi⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
    · by_cases e : k = keyAt w j
      · have := un i (by omega) j hj fi fj (by rw [ki, e]); omega
      · exact Or.inr ⟨e, i, h, fi, ki, vi⟩
    · exact Or.inl ⟨ki.symm, vi.symm⟩
  · rintro (⟨rfl, rfl⟩ | ⟨_, i, hi, fi, ki, vi⟩)
    · exact ⟨j, Nat.lt_succ_self j, fj, rfl, rfl⟩
    · exact ⟨i, by omega, fi, ki, vi⟩

theorem rep_succ_skip {j : Nat} {w : Array UInt64} {s : Array UInt8} (fj : s[j]! ≠ 1) (k : Key) (v : Val) :
    Rep (j + 1) w s k v ↔ Rep j w s k v := by
  constructor
  · rintro ⟨i, hi, fi, ki, vi⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
    · exact ⟨i, h, fi, ki, vi⟩
    · exact absurd fi fj
  · rintro ⟨i, hi, fi, ki, vi⟩; exact ⟨i, by omega, fi, ki, vi⟩

theorem not_rep_prefix {cap j : Nat} {w : Array UInt64} {s : Array UInt8} (un : Unique cap w s) (hj : j < cap)
    (fj : s[j]! = 1) (v : Val) : ¬ Rep j w s (keyAt w j) v := by
  rintro ⟨i, hi, fi, ki, _⟩
  have := un i (by omega) j hj fi fj ki; omega

theorem models_congr {cap cap' w s w' s' m} (hm : Models cap w s m)
    (h : ∀ k v, Rep cap' w' s' k v ↔ Rep cap w s k v) : Models cap' w' s' m := by
  intro k v; change _ ↔ Rep cap' w' s' k v; rw [h]; exact hm k v

theorem putrel_step {cap ncap j : Nat} {w nw nw' : Array UInt64} {s ns ns' : Array UInt8}
    (un : Unique cap w s) (hj : j < cap) (fj : s[j]! = 1)
    (inv : ∀ k v, Rep ncap nw ns k v ↔ Rep j w s k v)
    (pr : PutRel ncap nw ns nw' ns' (keyAt w j) (valAt w j)) :
    ∀ k v, Rep ncap nw' ns' k v ↔ Rep (j + 1) w s k v := by
  intro k v; rw [pr, rep_succ un hj fj, inv]
