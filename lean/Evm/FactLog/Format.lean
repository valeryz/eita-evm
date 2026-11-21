import Batteries
import Mathlib.Tactic.NormNum
/-! # Evm/FactLog/Format — the fact log's binary shard format, specified and proved

The fact log is append-only, block-range-sharded tables of facts the verified replay
emits. This file is the one definition of

* the **schema** — the seven tables and their typed columns (`tables`);
* the **field codecs** — fixed-width little-endian integers, 20-byte addresses, 32-byte
  words, an optional address, a list of words, a length-prefixed byte string
  (`encodeField` / `decodeField`);
* the **row** form — the fields of a row concatenated (`encodeRow`): the canonical bytes
  the shard's content hash is taken over, independent of how rows are grouped;
* the **columnar group** — a self-delimiting unit of a shard file: a header, then every
  column as one contiguous byte string, each through a per-column codec (raw, or a
  compressor the reader must invert) (`encodeGroup` / `decodeGroup`);
* the **shard** — a sequence of groups; a reader takes the complete groups and leaves a
  torn tail (`decodeShard`);
* the **schema evolution** rule — a table only gains optional columns at its end; a group
  carries its width, and a reader takes the table's first that many columns (`colsAt`,
  `decodeGroupAny`), so older shards and mixed shards stay readable, rows as narrow as the
  group they were written in;
* the **invariants** readers rely on: rows in `(block, tx)` order, every row inside the
  shard's block range (`WellFormed`), so that "the rows of blocks ≤ N" is a prefix
  (`takeWhile_block_le`), which is what the resume pull-back truncates to.

Everything is total (structural recursion, explicit counts), so the theorems are about
the functions the emitter prints: `src/generated/factlog-schema.lisp` and
`scripts/generated/factlog_schema.py` are emitted from `tables` and the layout constants
below by `lake exe emitFactLog`, and `src/factlog/format.lisp` / `scripts/factlog.py`
implement exactly these definitions (checked against the emitted vectors by
`scripts/verify-factlog-emit.sh`).

What is assumed, not proved: a compressing codec (zstd) inverts its own output. It
enters only through `Codec.roundtrip`, a field of the codec the group theorem is
parameterised by; `Codec.raw` discharges it by `rfl`.
-/

namespace Evm.FactLog

abbrev Bytes := List UInt8

/-! ## Little-endian integers -/

/-- `encLE k n`: `n` in `k` bytes, least significant first (`n` is taken mod `256^k`). -/
def encLE : Nat → Nat → Bytes
  | 0, _ => []
  | k + 1, n => UInt8.ofNat (n % 256) :: encLE k (n / 256)

def decLE : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * decLE bs

@[simp] theorem length_encLE (k n : Nat) : (encLE k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [encLE, ih]

theorem decLE_encLE (k n : Nat) (h : n < 256 ^ k) : decLE (encLE k n) = n := by
  induction k generalizing n with
  | zero => simp [encLE, decLE]; omega
  | succ k ih =>
    have hq : n / 256 < 256 ^ k := by
      rw [Nat.pow_succ] at h; exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h)
    simp only [encLE, decLE, ih _ hq]
    rw [UInt8.toNat_ofNat_of_lt' (Nat.mod_lt _ (by decide))]
    exact Nat.mod_add_div n 256

/-- `takeFixed k bs`: the first `k` bytes and the rest, if there are that many. -/
def takeFixed (k : Nat) (bs : Bytes) : Option (Bytes × Bytes) :=
  if k ≤ bs.length then some (bs.take k, bs.drop k) else none

theorem takeFixed_append (k : Nat) (w rest : Bytes) (h : w.length = k) :
    takeFixed k (w ++ rest) = some (w, rest) := by
  subst h
  simp [takeFixed]

/-- Sequencing of partial decoders: feed a decoded prefix and the rest on. -/
def pipe (x : Option (α × Bytes)) (f : α → Bytes → Option β) : Option β :=
  match x with
  | some (a, r) => f a r
  | none => none

@[simp] theorem pipe_some (a : α) (r : Bytes) (f : α → Bytes → Option β) : pipe (some (a, r)) f = f a r := rfl
@[simp] theorem pipe_none (f : α → Bytes → Option β) : pipe none f = none := rfl

/-! ## Column types and values -/

inductive ColType
  | u8 | u16 | u32 | u64        -- unsigned, fixed width
  | i64                         -- signed (tx index −1, call parent −1, selector −1, status −1)
  | addr                        -- 20 bytes
  | optAddr                     -- 1 flag byte + 20 bytes (a tx's `to`: NIL for a creation)
  | optU64                      -- 1 flag byte + 8 bytes (a header field a fork introduced)
  | u256                        -- 32 bytes
  | u256list                    -- 1 count byte + 32 bytes each (log topics, ≤ 4)
  | bytes                       -- 4-byte length + the bytes (log data)
  deriving DecidableEq, Repr

/-- Fixed widths; var-length columns have none. -/
def ColType.width : ColType → Option Nat
  | .u8 => some 1 | .u16 => some 2 | .u32 => some 4 | .u64 => some 8 | .i64 => some 8
  | .addr => some 20 | .optAddr => some 21 | .optU64 => some 9 | .u256 => some 32
  | .u256list => none | .bytes => none

def ColType.name : ColType → String
  | .u8 => "u8" | .u16 => "u16" | .u32 => "u32" | .u64 => "u64" | .i64 => "i64"
  | .addr => "addr" | .optAddr => "optaddr" | .optU64 => "optu64" | .u256 => "u256"
  | .u256list => "u256list" | .bytes => "bytes"

/-- A column whose value may be absent (`Value.none`): the only kind a table may gain (see
    `colsAt`), so the rows of an older, narrower group are the same facts with it absent. -/
def ColType.optional : ColType → Bool
  | .optAddr | .optU64 => true
  | _ => false

inductive Value
  | nat (n : Nat)
  | int (z : Int)
  | none
  | nats (l : List Nat)
  | bytes (b : Bytes)
  deriving DecidableEq, Repr

def two64 : Int := 18446744073709551616
def two63 : Int := 9223372036854775808

/-! ## Field codecs: one encoder/decoder pair per column shape -/

/-- An unsigned integer in `k` bytes, if below `bound` (the column's range). -/
def natField (k bound : Nat) : Value → Option Bytes
  | .nat n => if n < bound then some (encLE k n) else none
  | _ => none

def decNatField (k : Nat) (bs : Bytes) : Option (Value × Bytes) :=
  pipe (takeFixed k bs) fun w r => some (.nat (decLE w), r)

theorem decNatField_natField (k bound : Nat) (hb : bound ≤ 256 ^ k) (v : Value) (e rest : Bytes)
    (h : natField k bound v = some e) : decNatField k (e ++ rest) = some (v, rest) := by
  cases v with
  | nat n =>
    simp only [natField] at h
    split at h
    · rename_i hlt
      cases h
      simp only [decNatField, takeFixed_append k _ _ (length_encLE k n), pipe_some]
      rw [decLE_encLE k n (Nat.lt_of_lt_of_le hlt hb)]
    · cases h
  | _ => simp [natField] at h

/-- A signed 64-bit integer, two's complement. -/
def intField : Value → Option Bytes
  | .int z => if -two63 ≤ z ∧ z < two63 then some (encLE 8 (z % two64).toNat) else none
  | _ => none

def decIntField (bs : Bytes) : Option (Value × Bytes) :=
  pipe (takeFixed 8 bs) fun w r =>
    let n : Int := decLE w
    some (.int (if n < two63 then n else n - two64), r)

theorem decIntField_intField (v : Value) (e rest : Bytes) (h : intField v = some e) :
    decIntField (e ++ rest) = some (v, rest) := by
  cases v with
  | int z =>
    simp only [intField] at h
    split at h
    · rename_i hz
      cases h
      have hm : (z % two64).toNat < 256 ^ 8 := by
        have : (256 : Nat) ^ 8 = 18446744073709551616 := by norm_num
        rw [this]; simp only [two64, two63] at hz ⊢; omega
      have hnn : (0 : Int) ≤ z % two64 := Int.emod_nonneg _ (by simp [two64])
      have hcast : ((z % two64).toNat : Int) = z % two64 := Int.toNat_of_nonneg hnn
      simp only [decIntField, takeFixed_append 8 _ _ (length_encLE 8 _), pipe_some, decLE_encLE 8 _ hm, hcast]
      have key : (if z % two64 < two63 then z % two64 else z % two64 - two64) = z := by
        simp only [two64, two63] at hz ⊢; split_ifs <;> omega
      rw [key]
    · cases h
  | _ => simp [intField] at h

/-- An unsigned integer in `k` bytes that may be absent: a flag byte, then the `k` bytes (zero
    when absent). A tx's `to` (`optAddr`, NIL for a creation) and a header field that only
    exists from some fork on (`optU64`). -/
def optNatField (k bound : Nat) : Value → Option Bytes
  | .none => some (0 :: encLE k 0)
  | .nat n => if n < bound then some (1 :: encLE k n) else none
  | _ => none

def decOptNatField (k : Nat) : Bytes → Option (Value × Bytes)
  | flag :: rest => pipe (takeFixed k rest) fun w r => some (if flag = 0 then .none else .nat (decLE w), r)
  | [] => none

theorem decOptNatField_optNatField (k bound : Nat) (hb : bound ≤ 256 ^ k) (v : Value) (e rest : Bytes)
    (h : optNatField k bound v = some e) : decOptNatField k (e ++ rest) = some (v, rest) := by
  cases v with
  | none =>
    simp only [optNatField] at h; cases h
    simp [decOptNatField, takeFixed_append k _ _ (length_encLE k 0)]
  | nat n =>
    simp only [optNatField] at h
    split at h
    · rename_i hlt
      cases h
      simp [decOptNatField, takeFixed_append k _ _ (length_encLE k n),
        decLE_encLE k n (Nat.lt_of_lt_of_le hlt hb)]
    · cases h
  | _ => simp [optNatField] at h

/-- Up to 255 words of 32 bytes (log topics): a count byte, then the words. -/
def natsField : Value → Option Bytes
  | .nats l =>
      if l.length < 256 ∧ l.all (· < 2 ^ 256) then some (encLE 1 l.length ++ (l.map (encLE 32)).flatten)
      else none
  | _ => none

def decodeNats : Nat → Bytes → Option (List Nat × Bytes)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
      pipe (takeFixed 32 bs) fun w rest =>
        pipe (decodeNats n rest) fun l rest => some (decLE w :: l, rest)

def decNatsField : Bytes → Option (Value × Bytes)
  | cnt :: rest => pipe (decodeNats cnt.toNat rest) fun l r => some (.nats l, r)
  | [] => none

theorem encLE_one (n : Nat) : encLE 1 n = [UInt8.ofNat (n % 256)] := rfl

theorem decodeNats_encode (l : List Nat) (rest : Bytes) (h : ∀ x ∈ l, x < 2 ^ 256) :
    decodeNats l.length ((l.map (encLE 32)).flatten ++ rest) = some (l, rest) := by
  induction l with
  | nil => simp [decodeNats]
  | cons x l ih =>
    have hx : x < 256 ^ 32 := by
      have : (256 : Nat) ^ 32 = 2 ^ 256 := by norm_num
      rw [this]; exact h x (List.mem_cons_self ..)
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decodeNats]
    rw [takeFixed_append 32 _ _ (length_encLE 32 x), pipe_some, ih (fun y hy => h y (List.mem_cons_of_mem x hy)),
      pipe_some, decLE_encLE 32 x hx]

theorem decNatsField_natsField (v : Value) (e rest : Bytes) (h : natsField v = some e) :
    decNatsField (e ++ rest) = some (v, rest) := by
  cases v with
  | nats l =>
    simp only [natsField] at h
    split at h
    · rename_i hl
      cases h
      have hall : ∀ x ∈ l, x < 2 ^ 256 := by
        intro x hx; have := hl.2; simp only [List.all_eq_true, decide_eq_true_eq] at this; exact this x hx
      rw [encLE_one, Nat.mod_eq_of_lt hl.1]
      simp only [List.cons_append, List.nil_append, decNatsField]
      rw [UInt8.toNat_ofNat_of_lt' hl.1, decodeNats_encode l rest hall, pipe_some]
    · cases h
  | _ => simp [natsField] at h

/-- A byte string below 4 GiB: 4-byte length, then the bytes. -/
def bytesField : Value → Option Bytes
  | .bytes b => if b.length < 2 ^ 32 then some (encLE 4 b.length ++ b) else none
  | _ => none

def decBytesField (bs : Bytes) : Option (Value × Bytes) :=
  pipe (takeFixed 4 bs) fun w rest => pipe (takeFixed (decLE w) rest) fun b rest => some (.bytes b, rest)

theorem decBytesField_bytesField (v : Value) (e rest : Bytes) (h : bytesField v = some e) :
    decBytesField (e ++ rest) = some (v, rest) := by
  cases v with
  | bytes b =>
    simp only [bytesField] at h
    split at h
    · rename_i hlt
      cases h
      have hb : b.length < 256 ^ 4 := by
        have : (256 : Nat) ^ 4 = 2 ^ 32 := by norm_num
        rw [this]; exact hlt
      simp only [decBytesField, List.append_assoc, takeFixed_append 4 _ _ (length_encLE 4 _), pipe_some,
        decLE_encLE 4 _ hb, takeFixed_append b.length b rest rfl]
    · cases h
  | _ => simp [bytesField] at h

/-- The bytes of one field, or `none` when the value does not fit the column type. -/
def encodeField : ColType → Value → Option Bytes
  | .u8 => natField 1 (2 ^ 8)
  | .u16 => natField 2 (2 ^ 16)
  | .u32 => natField 4 (2 ^ 32)
  | .u64 => natField 8 (2 ^ 64)
  | .i64 => intField
  | .addr => natField 20 (2 ^ 160)
  | .optAddr => optNatField 20 (2 ^ 160)
  | .optU64 => optNatField 8 (2 ^ 64)
  | .u256 => natField 32 (2 ^ 256)
  | .u256list => natsField
  | .bytes => bytesField

/-- One field off the front of `bs`: the value and the remaining bytes. -/
def decodeField : ColType → Bytes → Option (Value × Bytes)
  | .u8 => decNatField 1
  | .u16 => decNatField 2
  | .u32 => decNatField 4
  | .u64 => decNatField 8
  | .i64 => decIntField
  | .addr => decNatField 20
  | .optAddr => decOptNatField 20
  | .optU64 => decOptNatField 8
  | .u256 => decNatField 32
  | .u256list => decNatsField
  | .bytes => decBytesField

/-- The round trip for one field: whatever `encodeField` accepts, `decodeField` returns,
    leaving the rest of the input untouched. -/
theorem decodeField_encodeField (t : ColType) (v : Value) (e rest : Bytes)
    (h : encodeField t v = some e) : decodeField t (e ++ rest) = some (v, rest) := by
  cases t
  case u8 => exact decNatField_natField 1 _ (by norm_num) v e rest h
  case u16 => exact decNatField_natField 2 _ (by norm_num) v e rest h
  case u32 => exact decNatField_natField 4 _ (by norm_num) v e rest h
  case u64 => exact decNatField_natField 8 _ (by norm_num) v e rest h
  case i64 => exact decIntField_intField v e rest h
  case addr => exact decNatField_natField 20 _ (by norm_num) v e rest h
  case optAddr => exact decOptNatField_optNatField 20 _ (by norm_num) v e rest h
  case optU64 => exact decOptNatField_optNatField 8 _ (by norm_num) v e rest h
  case u256 => exact decNatField_natField 32 _ (by norm_num) v e rest h
  case u256list => exact decNatsField_natsField v e rest h
  case bytes => exact decBytesField_bytesField v e rest h

/-! ## Rows: the canonical byte form (content hash input) -/

abbrev Row := List Value

/-- A row's fields, concatenated, or `none` when a field does not fit its column. -/
def encodeRow : List ColType → Row → Option Bytes
  | [], [] => some []
  | t :: ts, v :: vs =>
      match encodeField t v, encodeRow ts vs with
      | some e, some es => some (e ++ es)
      | _, _ => none
  | _, _ => none

def decodeRow : List ColType → Bytes → Option (Row × Bytes)
  | [], bs => some ([], bs)
  | t :: ts, bs =>
      pipe (decodeField t bs) fun v rest => pipe (decodeRow ts rest) fun vs rest => some (v :: vs, rest)

theorem decodeRow_encodeRow (ts : List ColType) (r : Row) (e rest : Bytes)
    (h : encodeRow ts r = some e) : decodeRow ts (e ++ rest) = some (r, rest) := by
  induction ts generalizing r e with
  | nil => cases r with
    | nil => simp only [encodeRow] at h; cases h; simp [decodeRow]
    | cons _ _ => simp [encodeRow] at h
  | cons t ts ih =>
    cases r with
    | nil => simp [encodeRow] at h
    | cons v vs =>
      simp only [encodeRow] at h
      split at h
      · rename_i e1 e2 h1 h2
        cases h
        simp only [decodeRow, List.append_assoc, decodeField_encodeField t v e1 _ h1, pipe_some, ih vs e2 h2]
      · cases h

/-- A row fits the columns iff it encodes. -/
def Typed (ts : List ColType) (r : Row) : Prop := (encodeRow ts r).isSome

/-! ## Columns of a group -/

/-- The columns of the rows: field `i` of every row, in row order (rows are rectangular). -/
def columns (k : Nat) (rows : List Row) : List (List Value) :=
  rows.foldr (fun r acc => List.zipWith (· :: ·) r acc) (List.replicate k [])

@[simp] theorem columns_nil (k : Nat) : columns k [] = List.replicate k [] := rfl
@[simp] theorem columns_cons (k : Nat) (r : Row) (rs : List Row) :
    columns k (r :: rs) = List.zipWith (· :: ·) r (columns k rs) := rfl

/-- Rows back from columns: `n` rows, the heads of the columns then their tails. -/
def rowsOf : Nat → List (List Value) → List Row
  | 0, _ => []
  | n + 1, cs => cs.map (·.headD .none) :: rowsOf n (cs.map List.tail)

def Rect (k : Nat) (rows : List Row) : Prop := ∀ r ∈ rows, r.length = k

theorem length_columns (k : Nat) (rows : List Row) (h : Rect k rows) : (columns k rows).length = k := by
  induction rows with
  | nil => simp [columns]
  | cons r rs ih =>
    have hr : r.length = k := h r (List.mem_cons_self ..)
    have := ih (fun x hx => h x (List.mem_cons_of_mem r hx))
    rw [columns_cons, List.length_zipWith, this, hr, Nat.min_self]

theorem map_headD_zipWith_cons (r : List Value) (cs : List (List Value)) (h : r.length = cs.length) :
    (List.zipWith (· :: ·) r cs).map (·.headD .none) = r := by
  induction r generalizing cs with
  | nil => simp
  | cons x xs ih =>
    cases cs with
    | nil => simp at h
    | cons c cs =>
      simp only [List.zipWith_cons_cons, List.map_cons, List.headD_cons]
      rw [ih cs (by simpa using h)]

theorem map_tail_zipWith_cons (r : List Value) (cs : List (List Value)) (h : r.length = cs.length) :
    (List.zipWith (· :: ·) r cs).map List.tail = cs := by
  induction r generalizing cs with
  | nil => cases cs <;> simp_all
  | cons x xs ih =>
    cases cs with
    | nil => simp at h
    | cons c cs =>
      simp only [List.zipWith_cons_cons, List.map_cons, List.tail_cons]
      rw [ih cs (by simpa using h)]

/-- Columnar transposition is invertible on rectangular rows. -/
theorem rowsOf_columns (k : Nat) (rows : List Row) (h : Rect k rows) :
    rowsOf rows.length (columns k rows) = rows := by
  induction rows with
  | nil => simp [rowsOf]
  | cons r rs ih =>
    have hr : r.length = k := h r (List.mem_cons_self ..)
    have hrs : Rect k rs := fun x hx => h x (List.mem_cons_of_mem r hx)
    have hlen : r.length = (columns k rs).length := by rw [length_columns k rs hrs, hr]
    rw [columns_cons, List.length_cons, rowsOf, map_headD_zipWith_cons r _ hlen, map_tail_zipWith_cons r _ hlen]
    exact congrArg (r :: ·) (ih hrs)

theorem length_zipWith_cons_entries (r : List Value) (cs : List (List Value)) (m : Nat)
    (h : r.length = cs.length) (hc : ∀ c ∈ cs, c.length = m) :
    ∀ c ∈ List.zipWith (· :: ·) r cs, c.length = m + 1 := by
  induction r generalizing cs with
  | nil => simp
  | cons x xs ih =>
    cases cs with
    | nil => simp at h
    | cons c cs =>
      intro y hy
      simp only [List.zipWith_cons_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · simp [hc c (List.mem_cons_self ..)]
      · exact ih cs (by simpa using h) (fun z hz => hc z (List.mem_cons_of_mem c hz)) y hy

/-- Every column of `columns k rows` has `rows.length` entries when the rows are rectangular. -/
theorem length_columns_entries (k : Nat) (rows : List Row) (h : Rect k rows) :
    ∀ c ∈ columns k rows, c.length = rows.length := by
  induction rows with
  | nil => intro c hc; simp only [columns_nil, List.mem_replicate] at hc; simp [hc.2]
  | cons r rs ih =>
    have hr : r.length = k := h r (List.mem_cons_self ..)
    have hrs : Rect k rs := fun x hx => h x (List.mem_cons_of_mem r hx)
    rw [columns_cons, List.length_cons]
    exact length_zipWith_cons_entries r _ rs.length (by rw [hr, length_columns k rs hrs]) (ih hrs)

/-! ## Column codecs -/

/-- A per-column byte codec. `raw` is the identity; a compressor (zstd in the
    implementation) must satisfy `roundtrip`, which is the one external assumption. -/
structure Codec where
  comp : Bytes → Bytes
  decomp : Bytes → Option Bytes
  roundtrip : ∀ b, decomp (comp b) = some b

def Codec.raw : Codec := ⟨id, some, fun _ => rfl⟩

/-- The column's fields concatenated. -/
def encodeColumn (t : ColType) : List Value → Option Bytes
  | [] => some []
  | v :: vs =>
      match encodeField t v, encodeColumn t vs with
      | some e, some es => some (e ++ es)
      | _, _ => none

def decodeColumn (t : ColType) : Nat → Bytes → Option (List Value × Bytes)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
      pipe (decodeField t bs) fun v rest => pipe (decodeColumn t n rest) fun vs rest => some (v :: vs, rest)

theorem decodeColumn_encodeColumn (t : ColType) (vs : List Value) (e rest : Bytes)
    (h : encodeColumn t vs = some e) : decodeColumn t vs.length (e ++ rest) = some (vs, rest) := by
  induction vs generalizing e with
  | nil => simp only [encodeColumn] at h; cases h; simp [decodeColumn]
  | cons v vs ih =>
    simp only [encodeColumn] at h
    split at h
    · rename_i e1 e2 h1 h2
      cases h
      simp only [List.length_cons, decodeColumn, List.append_assoc, decodeField_encodeField t v e1 _ h1,
        pipe_some, ih e2 h2]
    · cases h

/-! ## The group: header + columns

    Layout (all integers little-endian):

      magic      4 bytes  "EFG1"
      groupLen   u32      bytes of the whole group, this header included
      rows       u32
      firstBlock u64      block of the first row (0 when empty)
      lastBlock  u64      block of the last row
      ncols      u8
      per column: codec u8 · rawLen u32 · encLen u32
      payloads   the columns, each `encLen` bytes, in schema order -/

def magic : Bytes := [0x45, 0x46, 0x47, 0x31]

def headerLen (ncols : Nat) : Nat := 4 + 4 + 4 + 8 + 8 + 1 + 9 * ncols

/-- The block of a row: its first field (every table starts with `block : u64`). -/
def blockOf (r : Row) : Nat := match r.headD .none with | .nat n => n | _ => 0

/-- Per column `(codecIndex, rawLen, payload)`: column `i` goes through
    `codecs.getD (choice.getD i 0) Codec.raw`. -/
def encodeColumns (codecs : List Codec) (choice : List Nat) (i : Nat) :
    List ColType → List (List Value) → Option (List (Nat × Nat × Bytes))
  | [], [] => some []
  | t :: ts, c :: cs =>
      match encodeColumn t c, encodeColumns codecs choice (i + 1) ts cs with
      | some raw, some rest =>
          let ci := choice.getD i 0
          some ((ci, raw.length, (codecs.getD ci Codec.raw).comp raw) :: rest)
      | _, _ => none
  | _, _ => none

/-- Payload bytes of the encoded columns, in order. -/
def payloadOf (cols : List (Nat × Nat × Bytes)) : Bytes := (cols.map fun (_, _, p) => p).flatten

/-- The directory entries the header carries for the encoded columns. -/
def dirOf (cols : List (Nat × Nat × Bytes)) : Bytes :=
  (cols.map fun (ci, rl, p) => encLE 1 ci ++ encLE 4 rl ++ encLE 4 p.length).flatten

/-- Everything the header's fixed-width fields must hold. -/
def fits (ts : List ColType) (rows : List Row) (cols : List (Nat × Nat × Bytes)) : Bool :=
  ts.length < 2 ^ 8 && rows.length < 2 ^ 32 && rows.all (·.length == ts.length)
    && headerLen ts.length + (payloadOf cols).length < 2 ^ 32
    && cols.all fun (ci, rl, p) => ci < 2 ^ 8 && rl < 2 ^ 32 && p.length < 2 ^ 32

def encodeGroup (codecs : List Codec) (choice : List Nat) (ts : List ColType) (rows : List Row) :
    Option Bytes :=
  match encodeColumns codecs choice 0 ts (columns ts.length rows) with
  | some cols =>
      if fits ts rows cols then
        some (magic ++ encLE 4 (headerLen ts.length + (payloadOf cols).length) ++ encLE 4 rows.length
              ++ encLE 8 (blockOf (rows.headD [])) ++ encLE 8 (blockOf (rows.getLastD []))
              ++ encLE 1 ts.length ++ dirOf cols ++ payloadOf cols)
      else none
  | none => none

/-- Parse the directory: `ncols` triples `(codec, rawLen, encLen)`. -/
def decodeDir : Nat → Bytes → Option (List (Nat × Nat × Nat) × Bytes)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
      pipe (takeFixed 1 bs) fun c bs => pipe (takeFixed 4 bs) fun rl bs => pipe (takeFixed 4 bs) fun el bs =>
        pipe (decodeDir n bs) fun rest bs => some ((decLE c, decLE rl, decLE el) :: rest, bs)

/-- Decode the payloads into columns of `n` values each. -/
def decodeColumns (codecs : List Codec) (n : Nat) : List ColType → List (Nat × Nat × Nat) → Bytes →
    Option (List (List Value) × Bytes)
  | [], _, bs => some ([], bs)
  | t :: ts, (ci, _, el) :: dir, bs =>
      pipe (takeFixed el bs) fun p bs =>
        match (codecs.getD ci Codec.raw).decomp p with
        | some raw =>
            pipe (decodeColumn t n raw) fun vs tail =>
              if tail.isEmpty then
                pipe (decodeColumns codecs n ts dir bs) fun cs bs => some (vs :: cs, bs)
              else none
        | none => none
  | _ :: _, [], _ => none

/-- One group off the front of `bs`: its rows and the remaining bytes. `none` when the bytes
    do not start with a complete, well-formed group (a torn tail, or garbage). -/
def decodeGroup (codecs : List Codec) (ts : List ColType) (bs : Bytes) : Option (List Row × Bytes) :=
  pipe (takeFixed 4 bs) fun m bs =>
    if m = magic then
      pipe (takeFixed 4 bs) fun tot bs =>
        pipe (takeFixed 4 bs) fun n bs =>
          pipe (takeFixed 16 bs) fun _firstLast bs =>
            pipe (takeFixed 1 bs) fun k bs =>
              if decLE k = ts.length then
                pipe (decodeDir ts.length bs) fun dir bs =>
                  pipe (takeFixed (decLE tot - headerLen ts.length) bs) fun payload rest =>
                    pipe (decodeColumns codecs (decLE n) ts dir payload) fun cs tail =>
                      if tail.isEmpty then some (rowsOf (decLE n) cs, rest) else none
              else none
    else none

/-- A shard file: complete groups from the front, the undecodable tail returned. `fuel`
    bounds the recursion (one group per unit; a file has fewer groups than bytes). -/
def decodeShard (codecs : List Codec) (ts : List ColType) : Nat → Bytes → List Row × Bytes
  | 0, bs => ([], bs)
  | fuel + 1, bs =>
      match decodeGroup codecs ts bs with
      | some (rows, rest) => (rows ++ (decodeShard codecs ts fuel rest).1, (decodeShard codecs ts fuel rest).2)
      | none => ([], bs)

/-! ## The schema -/

structure Table where
  name : String
  cols : List ColType
  deriving Repr

/-- The seven tables, columns in row order (the writer: src/factlog/writer.lisp).
    Every table starts with `block : u64`; all but `block` continue with `tx : i64`
    (−1 for pre-block system effects, 10^9 for post-block ones). -/
def tables : List Table := [
  ⟨"block", [.u64, .u64, .addr, .u256, .u64, .u64, .u256, .optU64, .optU64]⟩,
    -- block timestamp coinbase base_fee gas_used gas_limit prev_randao
    -- blob_gas_used excess_blob_gas (EIP-4844 header fields: absent before Cancun; appended
    -- to the table, so an older group has the first 7 columns — `colsAt`)
  ⟨"tx", [.u64, .i64, .u256, .addr, .optAddr, .u256, .u8, .u64, .i64, .u256]⟩,
    -- block tx hash from to value type gas_used status effective_gas_price
  ⟨"call", [.u64, .i64, .u32, .i64, .u16, .u8, .addr, .addr, .u256, .i64, .u64, .u64, .u64, .u8]⟩,
    -- block tx frame parent depth kind from to value selector input_len gas gas_used status
  ⟨"log", [.u64, .i64, .u32, .addr, .u256list, .bytes]⟩,
    -- block tx log_index address topics data
  ⟨"transfer", [.u64, .i64, .u8, .u16, .addr, .addr, .u256]⟩,
    -- block tx kind depth from to value
  ⟨"storage_diff", [.u64, .i64, .addr, .u256, .u256, .u256]⟩,
    -- block tx address slot pre post
  ⟨"account_diff", [.u64, .i64, .addr, .u64, .u64, .u256, .u256, .u256, .u256]⟩]
    -- block tx address nonce_pre nonce_post balance_pre balance_post code_pre code_post

/-! ## Schema evolution: a table gains optional columns at its end

A table may only grow by appending `optional` columns. A group records how many columns it
was written with (its header's `ncols`), so the files need no other version mark: a group of
`k` columns is read with the table's first `k` (`colsAt`), its rows have `k` fields, and the
columns it lacks are absent — "not recorded", which a reader can tell from "recorded as
absent" (a full-width row with `.none`) by the row's width. A `k` that would drop a required
column, or exceed the table, is not a group of this table. -/

/-- The columns a group of `k` columns of the table `ts` is read with, if `k` is a width the
    table admits: at most its length, every column beyond `k` optional. -/
def colsAt (ts : List ColType) (k : Nat) : Option (List ColType) :=
  if k ≤ ts.length ∧ (ts.drop k).all ColType.optional then some (ts.take k) else none

theorem colsAt_self (ts : List ColType) : colsAt ts ts.length = some ts := by
  simp [colsAt]

theorem length_of_colsAt (ts ts' : List ColType) (k : Nat) (h : colsAt ts k = some ts') : ts'.length = k := by
  simp only [colsAt] at h
  split at h
  · rename_i hk; cases h; simp only [List.length_take]; omega
  · cases h

/-! ## Shard invariants the readers rely on -/

/-- The tx index of a row: its second field (`i64`); the `block` table has none (0). -/
def txOf (r : Row) : Int := match r.getD 1 .none with | .int z => z | _ => 0

/-- Row order: `(block, tx)` non-decreasing — the writer emits a block's rows per tx, in tx
    order, and blocks in order; within a tx, file order is the ordinal. -/
def Ordered (rows : List Row) : Prop :=
  rows.Pairwise fun a b => blockOf a < blockOf b ∨ (blockOf a = blockOf b ∧ txOf a ≤ txOf b)

/-- Every row of a shard `[lo, hi]` lies in its range, and rows are ordered. -/
structure WellFormed (lo hi : Nat) (rows : List Row) : Prop where
  inRange : ∀ r ∈ rows, lo ≤ blockOf r ∧ blockOf r ≤ hi
  ordered : Ordered rows

/-- The rows of blocks ≤ `n` are a prefix of an ordered shard: what the resume pull-back
    keeps (`factlog-scan-prefix`, src/factlog/writer.lisp) is exactly `filter`, computed as
    `takeWhile`. -/
theorem takeWhile_block_le (rows : List Row) (n : Nat) (h : Ordered rows) :
    rows.takeWhile (fun r => decide (blockOf r ≤ n)) = rows.filter (fun r => decide (blockOf r ≤ n)) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    have h' : Ordered rs := (List.pairwise_cons.mp h).2
    have hrel := (List.pairwise_cons.mp h).1
    by_cases hr : blockOf r ≤ n
    · rw [List.takeWhile_cons_of_pos (by simpa using hr), List.filter_cons_of_pos (by simpa using hr), ih h']
    · -- every later row has a block ≥ this one's, so none of them is ≤ n either
      have hnone : ∀ x ∈ rs, ¬ blockOf x ≤ n := by
        intro x hx hxn; have := hrel x hx; omega
      rw [List.takeWhile_cons_of_neg (by simpa using hr), List.filter_cons_of_neg (by simpa using hr)]
      symm; rw [List.filter_eq_nil_iff]
      intro x hx; simpa using hnone x hx

/-! ## Content hash: FNV-1a 64 over the canonical rows -/

def fnvStep (h : UInt64) (b : UInt8) : UInt64 := (h ^^^ b.toUInt64) * 0x100000001b3

def fnv1a (bs : Bytes) : UInt64 := bs.foldl fnvStep 0xcbf29ce484222325

/-- A row's canonical bytes: its fields under the table's first `r.length` columns, so a row
    of an older, narrower group hashes as it was written. -/
def encodeRowAt (ts : List ColType) (r : Row) : Option Bytes :=
  (colsAt ts r.length).bind (encodeRow · r)

def encodeRows (ts : List ColType) : List Row → Option Bytes
  | [] => some []
  | r :: rs =>
      match encodeRowAt ts r, encodeRows ts rs with
      | some e, some es => some (e ++ es)
      | _, _ => none

/-- The shard's content hash: the canonical row bytes in row order. It depends on the rows
    alone — not on the grouping, the codecs, or the file bytes — so a converted shard and
    the one the writer produced carry the same `:content`; a shard written before a table
    gained a column keeps its `:content` (its rows are as narrow as its groups). -/
def contentHash (ts : List ColType) (rows : List Row) : Option UInt64 :=
  (encodeRows ts rows).map fnv1a

/-! ## The round trips -/

theorem encodeColumns_length (codecs : List Codec) (choice : List Nat) (i : Nat) (ts : List ColType)
    (cs : List (List Value)) (out : List (Nat × Nat × Bytes))
    (h : encodeColumns codecs choice i ts cs = some out) : out.length = ts.length := by
  induction ts generalizing i cs out with
  | nil => cases cs with
    | nil => simp only [encodeColumns] at h; cases h; rfl
    | cons _ _ => simp [encodeColumns] at h
  | cons t ts ih =>
    cases cs with
    | nil => simp [encodeColumns] at h
    | cons c cs =>
      simp only [encodeColumns] at h
      split at h
      · rename_i raw rest _ hrest
        cases h; simp [ih (i + 1) cs rest hrest]
      · cases h

theorem decodeDir_dirOf (dir : List (Nat × Nat × Bytes)) (rest : Bytes)
    (hb : ∀ x ∈ dir, x.1 < 2 ^ 8 ∧ x.2.1 < 2 ^ 32 ∧ x.2.2.length < 2 ^ 32) :
    decodeDir dir.length (dirOf dir ++ rest) = some (dir.map (fun (ci, rl, p) => (ci, rl, p.length)), rest) := by
  induction dir with
  | nil => simp [decodeDir, dirOf]
  | cons x dir ih =>
    obtain ⟨ci, rl, p⟩ := x
    have hx := hb (ci, rl, p) (List.mem_cons_self ..)
    have h1 : ci < 256 ^ 1 := by simpa using hx.1
    have h2 : rl < 256 ^ 4 := by have : (256 : Nat) ^ 4 = 2 ^ 32 := by norm_num
                                 rw [this]; exact hx.2.1
    have h3 : p.length < 256 ^ 4 := by have : (256 : Nat) ^ 4 = 2 ^ 32 := by norm_num
                                       rw [this]; exact hx.2.2
    have := ih (fun y hy => hb y (List.mem_cons_of_mem _ hy))
    simp only [dirOf, List.append_assoc] at this
    simp only [List.length_cons, dirOf, List.map_cons, List.flatten_cons, List.append_assoc, decodeDir]
    rw [takeFixed_append 1 _ _ (length_encLE 1 ci), pipe_some, takeFixed_append 4 _ _ (length_encLE 4 rl),
      pipe_some, takeFixed_append 4 _ _ (length_encLE 4 p.length), pipe_some]
    rw [this, pipe_some, decLE_encLE 1 ci h1, decLE_encLE 4 rl h2, decLE_encLE 4 p.length h3]

theorem decodeColumns_encodeColumns (codecs : List Codec) (choice : List Nat) (i : Nat) (ts : List ColType)
    (cs : List (List Value)) (n : Nat) (out : List (Nat × Nat × Bytes)) (rest : Bytes)
    (h : encodeColumns codecs choice i ts cs = some out) (hn : ∀ c ∈ cs, c.length = n) :
    decodeColumns codecs n ts (out.map fun (ci, rl, p) => (ci, rl, p.length)) (payloadOf out ++ rest)
      = some (cs, rest) := by
  induction ts generalizing i cs out with
  | nil =>
    cases cs with
    | nil => simp only [encodeColumns] at h; cases h; simp [decodeColumns, payloadOf]
    | cons _ _ => simp [encodeColumns] at h
  | cons t ts ih =>
    cases cs with
    | nil => simp [encodeColumns] at h
    | cons c cs =>
      simp only [encodeColumns] at h
      split at h
      · rename_i raw more hraw hmore
        cases h
        have hc : c.length = n := hn c (List.mem_cons_self ..)
        simp only [List.map_cons, decodeColumns, payloadOf, List.flatten_cons, List.append_assoc]
        rw [takeFixed_append _ _ _ rfl, pipe_some, Codec.roundtrip]
        dsimp only
        have hcol := decodeColumn_encodeColumn t c raw [] hraw
        rw [List.append_nil, hc] at hcol
        rw [hcol, pipe_some]
        simp only [List.isEmpty_nil, ↓reduceIte]
        have ihm := ih (i + 1) cs more hmore (fun x hx => hn x (List.mem_cons_of_mem c hx))
        simp only [payloadOf] at ihm
        rw [ihm, pipe_some]
      · cases h

theorem fits_spec (ts : List ColType) (rows : List Row) (cols : List (Nat × Nat × Bytes))
    (h : fits ts rows cols = true) :
    ts.length < 2 ^ 8 ∧ rows.length < 2 ^ 32 ∧ Rect ts.length rows
      ∧ headerLen ts.length + (payloadOf cols).length < 2 ^ 32
      ∧ ∀ x ∈ cols, x.1 < 2 ^ 8 ∧ x.2.1 < 2 ^ 32 ∧ x.2.2.length < 2 ^ 32 := by
  simp only [fits, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro x hx
  have := h5 x hx
  obtain ⟨ci, rl, p⟩ := x
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- The main theorem: a group decodes to the rows it was encoded from, for any codec choice
    whose codecs invert themselves, leaving the bytes after the group untouched. -/
theorem decodeGroup_encodeGroup (codecs : List Codec) (choice : List Nat) (ts : List ColType)
    (rows : List Row) (e rest : Bytes) (h : encodeGroup codecs choice ts rows = some e) :
    decodeGroup codecs ts (e ++ rest) = some (rows, rest) := by
  simp only [encodeGroup] at h
  split at h
  · rename_i out hout
    split at h
    · cases h
      rename_i hfits
      obtain ⟨hnc, hnr, hrect, htot, hdirb⟩ := fits_spec ts rows out hfits
      have hlen := encodeColumns_length codecs choice 0 ts _ out hout
      have hnc' : ts.length < 256 ^ 1 := by simpa using hnc
      have hnr' : rows.length < 256 ^ 4 := by
        have : (256 : Nat) ^ 4 = 2 ^ 32 := by norm_num
        rw [this]; exact hnr
      have htot' : headerLen ts.length + (payloadOf out).length < 256 ^ 4 := by
        have : (256 : Nat) ^ 4 = 2 ^ 32 := by norm_num
        rw [this]; exact htot
      -- walk the header
      simp only [decodeGroup, List.append_assoc]
      rw [takeFixed_append 4 _ _ rfl, pipe_some]
      simp only [↓reduceIte]
      rw [takeFixed_append 4 _ _ (length_encLE 4 _), pipe_some, takeFixed_append 4 _ _ (length_encLE 4 _), pipe_some]
      rw [← List.append_assoc (encLE 8 _), takeFixed_append 16 _ _ (by simp), pipe_some,
        takeFixed_append 1 _ _ (length_encLE 1 _), pipe_some, decLE_encLE 1 _ hnc']
      simp only [↓reduceIte]
      rw [← hlen, decodeDir_dirOf out _ hdirb, hlen, pipe_some]
      rw [decLE_encLE 4 _ htot', Nat.add_sub_cancel_left, takeFixed_append _ _ _ rfl, pipe_some]
      rw [decLE_encLE 4 _ hnr']
      have hcols := decodeColumns_encodeColumns codecs choice 0 ts (columns ts.length rows) rows.length out []
        hout (length_columns_entries ts.length rows hrect)
      rw [List.append_nil] at hcols
      rw [hcols, pipe_some]
      simp only [List.isEmpty_nil, ↓reduceIte]
      rw [rowsOf_columns ts.length rows hrect]
    · cases h
  · cases h

theorem decodeGroup_nil (codecs : List Codec) (ts : List ColType) : decodeGroup codecs ts [] = none := by
  simp [decodeGroup, takeFixed, pipe]

/-- Shards: encoding a partition of the rows into groups, one after another. -/
def encodeShard (codecs : List Codec) (choice : List Nat) (ts : List ColType) :
    List (List Row) → Option Bytes
  | [] => some []
  | g :: gs =>
      match encodeGroup codecs choice ts g, encodeShard codecs choice ts gs with
      | some e, some es => some (e ++ es)
      | _, _ => none

/-- Reading a shard returns the rows of every group, whatever the partition, and leaves a
    tail that is not a group (here: nothing). The resume reader and the live tailer rely on
    exactly this: group boundaries are the only consistent cut points, and the grouping is
    invisible to a consumer of rows. -/
theorem decodeShard_encodeShard (codecs : List Codec) (choice : List Nat) (ts : List ColType)
    (gs : List (List Row)) (e : Bytes) (h : encodeShard codecs choice ts gs = some e) :
    decodeShard codecs ts (gs.length + 1) e = (gs.flatten, []) := by
  induction gs generalizing e with
  | nil => simp only [encodeShard] at h; cases h; simp [decodeShard, decodeGroup_nil]
  | cons g gs ih =>
    simp only [encodeShard] at h
    split at h
    · rename_i eg es heg hes
      cases h
      rw [List.length_cons, decodeShard, decodeGroup_encodeGroup codecs choice ts g eg es heg]
      dsimp only
      rw [ih es hes]
      simp
    · cases h

/-- A torn tail — bytes after the last complete group that do not form a group — is left
    exactly where it starts: a tailer that stops at the first undecodable position has read
    every complete group and nothing else. -/
theorem decodeShard_append_tail (codecs : List Codec) (choice : List Nat) (ts : List ColType)
    (gs : List (List Row)) (e tail : Bytes) (fuel : Nat)
    (h : encodeShard codecs choice ts gs = some e) (htail : decodeGroup codecs ts tail = none) :
    decodeShard codecs ts (gs.length + fuel + 1) (e ++ tail) = (gs.flatten, tail) := by
  induction gs generalizing e with
  | nil => simp only [encodeShard] at h; cases h; simp [decodeShard, htail]
  | cons g gs ih =>
    simp only [encodeShard] at h
    split at h
    · rename_i eg es heg hes
      cases h
      have hd := decodeGroup_encodeGroup codecs choice ts g eg (es ++ tail) heg
      rw [List.append_assoc]
      simp only [List.length_cons]
      rw [show gs.length + 1 + fuel + 1 = (gs.length + fuel + 1) + 1 by omega, decodeShard, hd]
      dsimp only
      rw [ih es hes]
      simp
    · cases h

/-! ## Reading a group of any width the table admits -/

/-- The column count a group's header declares (the byte after the 28 fixed ones). -/
def groupCols (bs : Bytes) : Option Nat :=
  pipe (takeFixed 28 bs) fun _ bs => pipe (takeFixed 1 bs) fun k _ => some (decLE k)

/-- One group of the table `ts`, written at any width it admits (`colsAt`): rows of the
    group's width. What every reader decodes with (src/factlog/format.lisp `decode-group`). -/
def decodeGroupAny (codecs : List Codec) (ts : List ColType) (bs : Bytes) : Option (List Row × Bytes) :=
  match (groupCols bs).bind (colsAt ts) with
  | some ts' => decodeGroup codecs ts' bs
  | none => none

theorem groupCols_header (a b c d n : Nat) (hn : n < 256 ^ 1) (tail : Bytes) :
    groupCols (magic ++ (encLE 4 a ++ (encLE 4 b ++ (encLE 8 c ++ (encLE 8 d ++ (encLE 1 n ++ tail))))))
      = some n := by
  rw [show magic ++ (encLE 4 a ++ (encLE 4 b ++ (encLE 8 c ++ (encLE 8 d ++ (encLE 1 n ++ tail)))))
        = (magic ++ encLE 4 a ++ encLE 4 b ++ encLE 8 c ++ encLE 8 d) ++ (encLE 1 n ++ tail) by
        simp only [List.append_assoc]]
  simp only [groupCols]
  rw [takeFixed_append 28 _ _ (by simp [magic]), pipe_some, takeFixed_append 1 _ _ (length_encLE 1 n),
    pipe_some, decLE_encLE 1 n hn]

/-- A group's header declares the width it was encoded at. -/
theorem groupCols_encodeGroup (codecs : List Codec) (choice : List Nat) (ts : List ColType)
    (rows : List Row) (e rest : Bytes) (h : encodeGroup codecs choice ts rows = some e) :
    groupCols (e ++ rest) = some ts.length := by
  simp only [encodeGroup] at h
  split at h
  · rename_i out hout
    split at h
    · cases h
      rename_i hfits
      have hnc : ts.length < 256 ^ 1 := by simpa using (fits_spec ts rows out hfits).1
      simp only [List.append_assoc]
      exact groupCols_header _ _ _ _ _ hnc _
    · cases h
  · cases h

/-- Schema evolution, the reader's side: a group written with the table's first `k` columns
    (any width `colsAt` admits — the full one included, `colsAt_self`) decodes, under the
    current table, to exactly its rows. So shards written before a table gained a column stay
    readable, and a shard holding groups of both widths (a writer upgraded mid-range) too. -/
theorem decodeGroupAny_encodeGroup (codecs : List Codec) (choice : List Nat) (ts ts' : List ColType)
    (k : Nat) (rows : List Row) (e rest : Bytes) (hk : colsAt ts k = some ts')
    (h : encodeGroup codecs choice ts' rows = some e) :
    decodeGroupAny codecs ts (e ++ rest) = some (rows, rest) := by
  have hlen := length_of_colsAt ts ts' k hk
  simp only [decodeGroupAny, groupCols_encodeGroup codecs choice ts' rows e rest h, Option.bind_some, hlen, hk]
  exact decodeGroup_encodeGroup codecs choice ts' rows e rest h

end Evm.FactLog
