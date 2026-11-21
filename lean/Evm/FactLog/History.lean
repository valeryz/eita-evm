import Evm.FactLog.Format
/-! # Evm/FactLog/History — the per-shard history index over the state diffs

`storage_diff` and `account_diff` rows are the chain's state history: every row is a change
`(block, tx, key, pre, post)` of one key (an `(address, slot)` or an address — the account
row carries nonce, balance and code hash, so code changes are indexed with it). The index
makes "the value of `K` at the end of block `N`" a lookup instead of a replay (erigon's
history tables are the model):

* **per shard**: the rows re-ordered by `(key, block, tx)` — a permutation `perm` of row
  positions (stable, so a key's changes stay in file order) — and a Bloom filter over the
  shard's distinct keys. The pre-value of each change is the row's `pre` column, so it is
  addressable by key through `perm`.
* **lookup** (`lookup`): the first change of `K` strictly after `N` gives its `pre`; if there
  is none, the last change (≤ `N`) gives its `post`; if `K` never changed in the shard, the
  value is whatever it was before the shard (`anchor`: the previous shard's answer, or the
  snapshot). `lookup_eq_fold` proves this equals folding the diffs in file order, under the
  invariants the writer guarantees: changes in block order (`Sorted`), consecutive changes
  of a key chained `post = next pre` (`Chained`), and the first change's `pre` being the
  anchor (`Anchored`).
* **across shards**: the footer records the index's offset and the Bloom parameters; a
  reader walks shards from `N` downward and opens only those whose filter admits `K`
  (`mem_bloom`: no false negatives). The top-level file of all shards' filters is a cache
  rebuilt from them by the reader library (one owner).
* **on disk**: the index is a section of the shard file after the last row group
  (`encodeIndex` / `decodeIndex`, magic `EFI1`); `decodeIndex_encodeIndex` is its round trip.
-/

namespace Evm.FactLog

/-! ## Changes and the two ways to answer "value at N" -/

structure Change (K V : Type) where
  block : Nat
  tx : Int
  key : K
  pre : V
  post : V
  deriving Repr

variable {K V : Type}

/-- The diffs of `K` in file order (what `perm` groups together). -/
def byKey [DecidableEq K] (k : K) (cs : List (Change K V)) : List (Change K V) := cs.filter (·.key = k)

/-- The reference: fold the diffs in file order, the last change at or before `N` wins. -/
def foldValue [DecidableEq K] (anchor : V) (k : K) (n : Nat) (cs : List (Change K V)) : V :=
  cs.foldl (fun v c => if c.key = k ∧ c.block ≤ n then c.post else v) anchor

/-- The fold restricted to one key's changes. -/
def foldK (anchor : V) (n : Nat) (l : List (Change K V)) : V :=
  l.foldl (fun v c => if c.block ≤ n then c.post else v) anchor

/-- The index answer over one key's changes: the first change after `N` gives its `pre`,
    else the last change gives its `post`, else the anchor. -/
def lookupK (anchor : V) (n : Nat) (l : List (Change K V)) : V :=
  match l.find? (fun c => decide (n < c.block)) with
  | some c => c.pre
  | none => match l.getLast? with
    | some c => c.post
    | none => anchor

/-- The index answer for key `K` in a shard whose changes are `cs`. -/
def lookup [DecidableEq K] (anchor : V) (k : K) (n : Nat) (cs : List (Change K V)) : V :=
  lookupK anchor n (byKey k cs)

/-- Changes are in block order (the writer emits blocks in order). -/
def Sorted (l : List (Change K V)) : Prop := l.Pairwise fun a b => a.block ≤ b.block

/-- Consecutive changes of one key are chained: each change starts from the previous one's
    result (the diff rows are net per tx of a single evolving value). -/
def Chained : List (Change K V) → Prop
  | a :: b :: l => a.post = b.pre ∧ Chained (b :: l)
  | _ => True

theorem Chained.tail {c : Change K V} {l : List (Change K V)} (h : Chained (c :: l)) : Chained l := by
  cases l with
  | nil => trivial
  | cons d l => exact h.2

/-- The first change of the key starts from the anchor value. -/
def Anchored (anchor : V) (l : List (Change K V)) : Prop := ∀ c, l.head? = some c → c.pre = anchor

theorem foldValue_eq_foldK [DecidableEq K] (anchor : V) (k : K) (n : Nat) (cs : List (Change K V)) :
    foldValue anchor k n cs = foldK anchor n (byKey k cs) := by
  induction cs generalizing anchor with
  | nil => rfl
  | cons c cs ih =>
    simp only [foldValue, List.foldl_cons, byKey, foldK] at *
    by_cases hk : c.key = k
    · rw [List.filter_cons_of_pos (by simpa using hk)]
      simp only [List.foldl_cons, hk, true_and]
      exact ih _
    · rw [List.filter_cons_of_neg (by simpa using hk)]
      simp only [hk, false_and, ↓reduceIte]
      exact ih _

theorem foldK_of_all_gt (anchor : V) (n : Nat) (l : List (Change K V)) (h : ∀ c ∈ l, n < c.block) :
    foldK anchor n l = anchor := by
  induction l generalizing anchor with
  | nil => rfl
  | cons c l ih =>
    have hc := h c (List.mem_cons_self ..)
    simp only [foldK, List.foldl_cons]
    rw [ite_eq_right (by omega)]
    exact ih anchor (fun x hx => h x (List.mem_cons_of_mem c hx))

/-- The index lookup over one key's changes equals the fold, given the invariants. -/
theorem lookupK_eq_foldK (anchor : V) (n : Nat) (l : List (Change K V))
    (hs : Sorted l) (hc : Chained l) (ha : Anchored anchor l) : lookupK anchor n l = foldK anchor n l := by
  induction l generalizing anchor with
  | nil => rfl
  | cons c l ih =>
    have hpre : c.pre = anchor := ha c rfl
    have hs' : Sorted l := (List.pairwise_cons.mp hs).2
    have hrel := (List.pairwise_cons.mp hs).1
    by_cases hn : n < c.block
    · -- the first change is already past N: nothing at or before N changed the key
      have hall : ∀ x ∈ c :: l, n < x.block := by
        intro x hx; simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hn
        · have := hrel x hx; omega
      rw [foldK_of_all_gt anchor n (c :: l) hall]
      simp only [lookupK, List.find?_cons, decide_eq_true hn]
      exact hpre
    · -- c is at or before N: the answer is the lookup over the tail from c.post
      have hc' : Chained l := hc.tail
      have ha' : Anchored c.post l := by
        intro d hd
        cases l with
        | nil => simp at hd
        | cons d' l' =>
          simp only [List.head?_cons, Option.some.injEq] at hd; subst hd
          exact hc.1.symm
      have ih' := ih c.post hs' hc' ha'
      simp only [foldK, List.foldl_cons, ite_eq_left (Nat.le_of_not_lt hn)]
      rw [show (l.foldl (fun v c => if c.block ≤ n then c.post else v) c.post) = foldK c.post n l from rfl, ← ih']
      simp only [lookupK, List.find?_cons, decide_eq_false hn]
      cases hfind : l.find? (fun c => decide (n < c.block)) with
      | some d => rfl
      | none =>
        cases l with
        | nil => rfl
        | cons d' l' =>
          cases hl : (d' :: l').getLast? with
          | some x => simp only [List.getLast?_cons_cons, hl]
          | none => simp at hl

/-- `lookup` answers the question the fold answers, for every key, under the invariants on
    that key's changes. -/
theorem lookup_eq_foldValue [DecidableEq K] (anchor : V) (k : K) (n : Nat) (cs : List (Change K V))
    (hs : Sorted (byKey k cs)) (hc : Chained (byKey k cs)) (ha : Anchored anchor (byKey k cs)) :
    lookup anchor k n cs = foldValue anchor k n cs := by
  rw [foldValue_eq_foldK, lookup, lookupK_eq_foldK anchor n _ hs hc ha]

/-- Sortedness of a key's changes follows from the shard's row order. -/
theorem sorted_byKey [DecidableEq K] (k : K) (cs : List (Change K V)) (h : Sorted cs) : Sorted (byKey k cs) :=
  List.Pairwise.sublist List.filter_sublist h

/-! ## The changes carried by the two diff tables -/

/-- A `storage_diff` row as a change of `(address, slot)`. -/
def storageChange (r : Row) : Option (Change (Nat × Nat) Nat) :=
  match r with
  | [.nat b, .int t, .nat a, .nat s, .nat pre, .nat post] => some ⟨b, t, (a, s), pre, post⟩
  | _ => none

/-- An `account_diff` row as a change of the account's `(nonce, balance, codeHash)`. -/
def accountChange (r : Row) : Option (Change Nat (Nat × Nat × Nat)) :=
  match r with
  | [.nat b, .int t, .nat a, .nat n0, .nat n1, .nat b0, .nat b1, .nat c0, .nat c1] =>
      some ⟨b, t, a, (n0, b0, c0), (n1, b1, c1)⟩
  | _ => none

/-- The canonical key bytes the index sorts (byte-lexicographically) and hashes: the address
    (20 bytes) then the slot (32), both big-endian, so byte order is numeric order — the
    `(address, slot)` memcmp convention of docs/state-snapshot-format.md. -/
def storageKeyBytes (a s : Nat) : Bytes := (encLE 20 a).reverse ++ (encLE 32 s).reverse
def accountKeyBytes (a : Nat) : Bytes := (encLE 20 a).reverse

/-! ## The Bloom filter over a shard's keys -/

/-- Bit positions of a key: double hashing from the FNV-1a 64 of its bytes, `k` probes. -/
def bloomPositions (m k : Nat) (key : Bytes) : List Nat :=
  let h := (fnv1a key).toNat
  let h1 := h % 2 ^ 32
  let h2 := (h / 2 ^ 32) ||| 1
  (List.range k).map fun i => (h1 + i * h2) % m

/-- The filter as the set of set bits. -/
def bloomOf (m k : Nat) (keys : List Bytes) : List Nat := (keys.map (bloomPositions m k)).flatten

def mayContain (m k : Nat) (bits : List Nat) (key : Bytes) : Bool :=
  (bloomPositions m k key).all (· ∈ bits)

/-- No false negatives: every inserted key tests positive. -/
theorem mem_bloom (m k : Nat) (keys : List Bytes) (key : Bytes) (h : key ∈ keys) :
    mayContain m k (bloomOf m k keys) key = true := by
  simp only [mayContain, List.all_eq_true, decide_eq_true_eq]
  intro p hp
  simp only [bloomOf, List.mem_flatten, List.mem_map]
  exact ⟨bloomPositions m k key, ⟨key, h, rfl⟩, hp⟩

/-! ## The index section on disk

      magic      4 bytes  "EFI1"
      sectionLen u32      bytes of the whole section
      rows       u32      entries of `perm` (= the shard's rows)
      bloomK     u8
      bloomBytes u32      m / 8
      perm       rows × u32   row positions in (key, block, tx) order
      bloom      bloomBytes   the filter's bits, little-endian within each byte -/

def indexMagic : Bytes := [0x45, 0x46, 0x49, 0x31]

def indexHeaderLen : Nat := 4 + 4 + 4 + 1 + 4

/-- The bit vector as bytes (bit `i` is bit `i % 8` of byte `i / 8`). -/
def bloomBytesOf (m : Nat) (bits : List Nat) : Bytes :=
  (List.range (m / 8)).map fun i =>
    (List.range 8).foldl (fun acc j => if (i * 8 + j) ∈ bits then acc ||| (UInt8.ofNat (1 <<< j)) else acc) 0

def encodeIndex (perm : List Nat) (bloomK : Nat) (bloom : Bytes) : Option Bytes :=
  match encodeColumn .u32 (perm.map .nat) with
  | some p =>
      if perm.length < 2 ^ 32 ∧ bloomK < 2 ^ 8 ∧ bloom.length < 2 ^ 32
         ∧ indexHeaderLen + p.length + bloom.length < 2 ^ 32 then
        some (indexMagic ++ encLE 4 (indexHeaderLen + p.length + bloom.length) ++ encLE 4 perm.length
              ++ encLE 1 bloomK ++ encLE 4 bloom.length ++ p ++ bloom)
      else none
  | none => none

def natsOf : List Value → Option (List Nat)
  | [] => some []
  | .nat n :: vs => (natsOf vs).map (n :: ·)
  | _ :: _ => none

def decodeIndex (bs : Bytes) : Option ((List Nat × Nat × Bytes) × Bytes) :=
  pipe (takeFixed 4 bs) fun m bs =>
    if m = indexMagic then
      pipe (takeFixed 4 bs) fun _tot bs =>
        pipe (takeFixed 4 bs) fun n bs =>
          pipe (takeFixed 1 bs) fun k bs =>
            pipe (takeFixed 4 bs) fun bl bs =>
              pipe (decodeColumn .u32 (decLE n) bs) fun vs bs =>
                pipe (takeFixed (decLE bl) bs) fun bloom rest =>
                  match natsOf vs with
                  | some perm => some ((perm, decLE k, bloom), rest)
                  | none => none
    else none

theorem natsOf_map (l : List Nat) : natsOf (l.map .nat) = some l := by
  induction l with
  | nil => rfl
  | cons n l ih => simp [natsOf, ih]

theorem decodeIndex_encodeIndex (perm : List Nat) (bloomK : Nat) (bloom e rest : Bytes)
    (h : encodeIndex perm bloomK bloom = some e) : decodeIndex (e ++ rest) = some ((perm, bloomK, bloom), rest) := by
  simp only [encodeIndex] at h
  split at h
  · rename_i p hp
    split at h
    · rename_i hfit
      cases h
      obtain ⟨hn, hk, hb, _⟩ := hfit
      have hn' : perm.length < 256 ^ 4 := by
        have : (256 : Nat) ^ 4 = 2 ^ 32 := by norm_num
        rw [this]; exact hn
      have hk' : bloomK < 256 ^ 1 := by simpa using hk
      have hb' : bloom.length < 256 ^ 4 := by
        have : (256 : Nat) ^ 4 = 2 ^ 32 := by norm_num
        rw [this]; exact hb
      simp only [decodeIndex, List.append_assoc]
      rw [takeFixed_append 4 _ _ rfl, pipe_some]
      simp only [↓reduceIte]
      rw [takeFixed_append 4 _ _ (length_encLE 4 _), pipe_some, takeFixed_append 4 _ _ (length_encLE 4 _), pipe_some,
        takeFixed_append 1 _ _ (length_encLE 1 _), pipe_some, takeFixed_append 4 _ _ (length_encLE 4 _), pipe_some,
        decLE_encLE 4 _ hn']
      have hcol := decodeColumn_encodeColumn .u32 (perm.map .nat) p (bloom ++ rest) hp
      rw [List.length_map] at hcol
      rw [hcol, pipe_some, decLE_encLE 4 _ hb', takeFixed_append _ _ _ rfl, pipe_some, natsOf_map,
        decLE_encLE 1 _ hk']
    · cases h
  · cases h

/-! ## Building the index from a shard's rows -/

/-- The row positions sorted by key, stable: a key's positions stay in file order. -/
def permOf (keys : List Bytes) : List Nat :=
  ((List.range keys.length).mergeSort fun i j =>
    decide (keys.getD i [] < keys.getD j [] ∨ (keys.getD i [] = keys.getD j [] ∧ i ≤ j)))

/-- Filter size: the smallest power of two holding ten bits per distinct key, at least 64. -/
def bloomBitsFor (distinct : Nat) : Nat :=
  let want := 10 * distinct
  let rec grow (m fuel : Nat) : Nat := match fuel with
    | 0 => m
    | fuel + 1 => if want ≤ m then m else grow (2 * m) fuel
  grow 64 40

def bloomK : Nat := 7

end Evm.FactLog
