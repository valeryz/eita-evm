import Velvet
import Slots.Ops

set_option velvet_vcgen.showVCReport true

/-- `ws_grow`'s body (`slots-grow`): re-insert every full slot, in index order, into a fresh table of
capacity `ncap`. Returns `(words, state, count)`; the new table has no tombstones. -/
method rehash (cap : Nat) (w : Array UInt64) (s : Array UInt8) (count ncap : Nat)
  returns (r : Array UInt64 × Array UInt8 × Nat)
  requires shape: Shape cap (cap - 1) w s
  requires unique: Unique cap w s
  requires count_eq: count = nFull cap s
  requires nshape: Shape ncap (ncap - 1) (Array.replicate (8 * ncap) 0) (Array.replicate ncap 0)
  requires room: count < ncap
  ensures shape': Shape ncap (ncap - 1) r.1 r.2.1
  ensures states': StatesOk ncap r.2.1
  ensures probing': Probing ncap (ncap - 1) r.1 r.2.1
  ensures unique': Unique ncap r.1 r.2.1
  ensures rep': ∀ k v, Rep ncap r.1 r.2.1 k v ↔ Rep cap w s k v
  ensures count': r.2.2 = nFull ncap r.2.1
  ensures used': nUsed ncap r.2.1 = r.2.2
  ensures count_same: r.2.2 = count
do
  let mut nw := Array.replicate (8 * ncap) 0
  let mut ns := Array.replicate ncap 0
  let mut ncount := 0
  let mut nused := 0
  let mut j := 0
  while j < cap
    invariant j_le: j ≤ cap
    invariant sh: Shape ncap (ncap - 1) nw ns
    invariant st: StatesOk ncap ns
    invariant pr: Probing ncap (ncap - 1) nw ns
    invariant un: Unique ncap nw ns
    invariant nt: ∀ i < ncap, ns[i]! ≠ 2
    invariant rep: ∀ k v, Rep ncap nw ns k v ↔ Rep j w s k v
    invariant c_eq: ncount = nFull ncap ns
    invariant c_pre: ncount = cnt j (fun i => s[i]! == 1)
    invariant u_eq: nused = ncount
    decreasing cap - j
  do
    let st ← rd s j
    if st == 1 then
      let a0 ← rd w (8*j)
      let a1 ← rd w (8*j+1)
      let a2 ← rd w (8*j+2)
      let a3 ← rd w (8*j+3)
      let a4 ← rd w (8*j+4)
      let a5 ← rd w (8*j+5)
      let a6 ← rd w (8*j+6)
      let a7 ← rd w (8*j+7)
      let r ← place ncap nw ns ncount nused a0 a1 a2 a3 a4 a5 a6 a7
      nw := r.1
      ns := r.2.1
      ncount := r.2.2.1
      nused := r.2.2.2
    j := j + 1
  return (nw, ns, ncount)

theorem replicate_zero_get {n i : Nat} (hi : i < n) : (Array.replicate n (0 : UInt8))[i]! = 0 := by
  simp [hi]

prove_correct rehash by
  intro cap w s count ncap
  velvet_vcgen [rehash] with try finish

  all_goals first
    | (have := shape.w_size; have := shape.s_size; omega)
    | (intro i hi; exact Or.inl (replicate_zero_get hi))
    | (intro j hj hf; rw [replicate_zero_get hj] at hf; exact absurd hf (by decide))
    | (intro i hi j hj fi; rw [replicate_zero_get hi] at fi; exact absurd fi (by decide))
    | (intro k v; constructor
       · rintro ⟨i, hi, fi, _⟩; rw [replicate_zero_get hi] at fi; exact absurd fi (by decide)
       · rintro ⟨i, hi, _⟩; omega)
    | exact (cnt_false ncap _ (fun i hi => by simp [replicate_zero_get hi])).symm
    | (simp [cnt]; done)
    | (rw [u_eq, c_eq, nUsed_eq_nFull st nt])
    | (have h1 := cnt_le j cap (fun i => s[i]! == 1) j_le
       have h2 : nFull cap s = cnt cap (fun i => s[i]! == 1) := rfl
       omega)
    | exact putrel_step unique h_loop (by simpa using if_cond) rep rel
    | (have fj : s[j]! = 1 := by simpa using if_cond
       have hfr := fresh (fun v h => not_rep_prefix unique h_loop fj v ((rep _ v).mp h))
       rw [cnt_succ]; simp only [fj, beq_self_eq_true, if_true]; omega)
    | (rw [used', count', nUsed_eq_nFull states' (no_tomb nt)])
    | (have fj : s[j]! ≠ 1 := by simpa using if_cond
       intro k v; rw [rep, rep_succ_skip fj])
    | (have fj : s[j]! ≠ 1 := by simpa using if_cond
       rw [cnt_succ]; simp only [beq_iff_eq, fj, if_false]; omega)
    | (have : j = cap := by omega
       subst this; exact rep)
    | (rw [nUsed_eq_nFull st nt, c_eq])
    | (have : j = cap := by omega
       subst this; rw [c_pre, count_eq]; rfl)
#print axioms rehash.spec

theorem shape_replicate {cap : Nat} (pow : ∃ lg, cap = 2 ^ lg) :
    Shape cap (cap - 1) (Array.replicate (8 * cap) 0) (Array.replicate cap 0) := by
  have cp : 0 < cap := by obtain ⟨lg, rfl⟩ := pow; exact Nat.two_pow_pos lg
  exact ⟨cp, by omega, mask_mod_of_pow pow, by simp, by simp, pow⟩

theorem pow_double {cap : Nat} (pow : ∃ lg, cap = 2 ^ lg) : ∃ lg, 2 * cap = 2 ^ lg := by
  obtain ⟨lg, rfl⟩ := pow; exact ⟨lg + 1, by rw [Nat.pow_succ]; omega⟩

/-- The growth rule (`ws_grow`, Lisp `slots-grow`): double when over half the entries are
present, else rehash at the same size (the table is mostly tombstones). -/
def newCap (cap count : Nat) : Nat := if 2 * count > cap then 2 * cap else cap

/-- `ws_grow`: rehash into a table of `newCap` entries; abort when that passes `maxCap`
(`WS_MAX_CAP`). Returns `(cap, words, state, count, used)`. -/
method grow (cap : Nat) (w : Array UInt64) (s : Array UInt8) (count used maxCap : Nat)
  returns (r : Nat × Array UInt64 × Array UInt8 × Nat × Nat)
  requires inv: TableInv cap (cap - 1) w s count used
  requires cap4: 4 ≤ cap
  signals tooLarge: maxCap < newCap cap count
  ensures inv': TableInv r.1 (r.1 - 1) r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
  ensures room: 4 * (r.2.2.2.2 + 1) ≤ 3 * r.1
  ensures rep': ∀ k v, Rep r.1 r.2.1 r.2.2.1 k v ↔ Rep cap w s k v
  ensures cap4': 4 ≤ r.1
  ensures cap_le: r.1 ≤ maxCap
do
  let ncap := newCap cap count
  if ncap > maxCap then wsAbort "eita_ws: table too large"
  let g ← rehash cap w s count ncap
  return (ncap, g.1, g.2.1, g.2.2, g.2.2)

prove_correct grow by
  intro cap w s count used maxCap
  velvet_vcgen [grow, wsAbort, newCap] with try finish
  all_goals (
    have occ := inv.occ
    have cu : count ≤ used := by rw [inv.count_eq, inv.used_eq]; exact nFull_le_nUsed cap s
    first
    | exact inv.shape
    | exact inv.unique
    | exact inv.count_eq
    | (unfold newCap; split
       · exact shape_replicate (pow_double inv.shape.pow)
       · exact shape_replicate inv.shape.pow)
    | (unfold newCap; split <;> omega)
    | (refine ⟨shape', states', probing', unique', count', used'.symm, ?_⟩
       unfold newCap; split <;> omega)
    | (unfold newCap; split <;> omega))
