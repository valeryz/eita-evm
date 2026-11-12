import Velvet
import Slots.Get

set_option velvet_vcgen.showVCReport true

/-!
The emitted pieces of the per-account directory and of `eita_ws_copy`: the directory size rule
(`eita_ws_touch`) and the array copy. The directory's pointer array itself (allocate, copy the
old pointers, free) is glue: `c/world_slots.c`, mirroring `Slots/World.lean`.
-/

/-- `eita_ws_touch`'s directory size: `n` when `id < n`; else the first of `n·2, n·4, …` (from
`dmin` = `WS_DIR_MIN` when the directory is empty) above `id`. Aborts when the directory must
grow for an id at or past `2^40`. -/
method dirGrow (n id dmin : Nat) returns (r : Nat)
  requires dpos: 0 < dmin
  signals idRange: n ≤ id ∧ 1099511627776 ≤ id
  ensures above: id < r
  ensures mono: n ≤ r
  ensures same: id < n → r = n
do
  if id < n then return n
  if id ≥ 1099511627776 then wsAbort "eita_ws: account id out of range"
  let mut m := if n == 0 then dmin else 2 * n
  while m ≤ id
    invariant pos: 0 < m
    invariant ge: n ≤ m
    decreasing id + 1 - m
  do
    m := 2 * m
  return m

prove_correct dirGrow by
  velvet_vcgen [dirGrow, wsAbort] with try finish
  all_goals (split <;> simp_all <;> omega)

/-- Equal entries give equal limbs. -/
theorem limbs_of_entries {cap : Nat} {a b : Array UInt64}
    (h : ∀ e < cap, keyAt a e = keyAt b e ∧ valAt a e = valAt b e) : ∀ l < 8 * cap, a[l]! = b[l]! := by
  intro l hl
  have he := h (l / 8) (by omega)
  simp only [keyAt, valAt, Prod.mk.injEq] at he
  obtain ⟨⟨h0, h1, h2, h3⟩, h4, h5, h6, h7⟩ := he
  have : l = 8 * (l / 8) + l % 8 := by omega
  have ht : l % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [this]
  generalize l % 8 = t at ht
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem arr_eq_of {α} [Inhabited α] {a b : Array α} (hs : a.size = b.size)
    (h : ∀ l < a.size, a[l]! = b[l]!) : a = b := by
  apply Array.ext hs
  intro l h1 h2
  have := h l h1
  rwa [getElem!_pos a l h1, getElem!_pos b l h2] at this

/-- `eita_ws_copy`'s arrays: fresh copies of `words` and `state`, entry by entry. -/
method copyArrs (cap : Nat) (w : Array UInt64) (s : Array UInt8)
  returns (r : Array UInt64 × Array UInt8)
  requires w_size: w.size = 8 * cap
  requires s_size: s.size = cap
  ensures same_w: r.1 = w
  ensures same_s: r.2 = s
do
  let mut nw := Array.replicate (8 * cap) (0 : UInt64)
  let mut ns := Array.replicate cap (0 : UInt8)
  let mut j := 0
  while j < cap
    invariant j_le: j ≤ cap
    invariant nw_size: nw.size = 8 * cap
    invariant ns_size: ns.size = cap
    invariant nw_eq: ∀ e < j, keyAt nw e = keyAt w e ∧ valAt nw e = valAt w e
    invariant ns_eq: ∀ l < j, ns[l]! = s[l]!
    decreasing cap - j
  do
    let a0 ← rd w (8*j)
    let a1 ← rd w (8*j+1)
    let a2 ← rd w (8*j+2)
    let a3 ← rd w (8*j+3)
    let a4 ← rd w (8*j+4)
    let a5 ← rd w (8*j+5)
    let a6 ← rd w (8*j+6)
    let a7 ← rd w (8*j+7)
    nw ← wrKV nw j (a0, a1, a2, a3) (a4, a5, a6, a7)
    let b ← rd s j
    ns ← wr ns j b
    j := j + 1
  return (nw, ns)

prove_correct copyArrs by
  intro cap w s
  velvet_vcgen [copyArrs] with try finish
  all_goals first
  | simp [nw_size]
  | (intro e he
     have hw : 8 * j + 7 < nw.size := by omega
     rw [keyAt_setKV hw, valAt_setKV hw]
     by_cases h : e = j
     · subst h; simp [keyAt, valAt]
     · simp only [h, if_false]; exact nw_eq e (by omega))
  | (apply arr_eq_of (by omega); rw [nw_size]; exact limbs_of_entries (fun e he => nw_eq e (by omega)))

/-- `ws_slots_new` as `eita_ws_touch` calls it: an empty 4-entry table. Returns `(cap, words, state)`
(count and used are 0). -/
method fresh returns (r : Nat × Array UInt64 × Array UInt8)
  ensures inv: TableInv r.1 (r.1 - 1) r.2.1 r.2.2 0 0
  ensures noRep: ∀ k v, ¬ Rep r.1 r.2.1 r.2.2 k v
  ensures cap4: r.1 = 4
do
  let c ← create 4
  return (4, c.1, c.2)

prove_correct fresh by
  velvet_vcgen [fresh] with try finish
  all_goals first
  | exact ⟨2, rfl⟩
  | exact ⟨shape, states, probing, unique, count.symm, used.symm, by omega⟩
  | exact empty

#print axioms fresh.spec
#print axioms dirGrow.spec
#print axioms copyArrs.spec
