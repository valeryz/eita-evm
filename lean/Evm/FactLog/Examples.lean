import Evm.FactLog.History
/-! # Evm/FactLog/Examples — sample rows per table, round-tripped by `native_decide`

One realistic row set per table (a pre-block system row with tx −1, a creation with
`to = NIL`, a four-topic log and an empty-data log, a reverted call with selector −1, a
post-block row with tx 10^9, 256-bit values), encoded as one group under the raw codec and
decoded back — kernel-checked instances of `decodeGroup_encodeGroup`, and the vectors
`lake exe emitFactLog vectors` prints for the Lisp and Python decoders
(`scripts/verify-factlog-emit.sh`). -/

namespace Evm.FactLog

def addrA : Nat := 0x52bc44d5378309ee2abf1539bf71de1b7d7be3b5
def addrB : Nat := 0x2693a99a52a3df7d16f41e5dad2e4e9a8ccb6a1d
def addrC : Nat := 0xf3dfc2d5d9eacbb81d4165b3a83e1a9fda1d3e0b
def hashA : Nat := 0x51862e4ef1b8b1d6a6b0ed4a13d7c7d6b8f2a5b07c2b6c7a7b8d1e3f5a6c7d8e
def topicT : Nat := 0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef
def big : Nat := 0xf0e1d2c3b4a5968778695a4b3c2d1e0f0f1e2d3c4b5a69788796a5b4c3d2e1f0

/-- The rows the vectors are built from, by table name. -/
def samples : String → List Row
  | "block" =>
    [[.nat 5900000, .nat 1530646642, .nat addrA, .nat 0, .nat 4104427, .nat 8000029, .nat 3459938843300437, .none, .none],
     [.nat 5900001, .nat 1530646660, .nat addrB, .nat 7, .nat 7988079, .nat 7992222, .nat big, .nat 786432, .nat 0],
     [.nat 5900002, .nat 1530646672, .nat addrC, .nat 7, .nat 0, .nat 7992222, .nat 0, .nat 0, .nat 395575296]]
  | "tx" =>
    [[.nat 5900000, .int 0, .nat hashA, .nat addrA, .nat addrB, .nat 100304115660702000, .nat 0, .nat 21000, .int 1, .nat 1000000000],
     [.nat 5900000, .int 1, .nat big, .nat addrB, .none, .nat 0, .nat 2, .nat 778212, .int 0, .nat 30000000000],
     [.nat 5900001, .int 0, .nat 0, .nat addrC, .nat addrA, .nat 1, .nat 4, .nat 0, .int (-1), .nat 0]]
  | "call" =>
    [[.nat 5900000, .int 0, .nat 0, .int (-1), .nat 0, .nat 0, .nat addrA, .nat addrB, .nat 100304115660702000, .int (-1), .nat 0, .nat 29000, .nat 0, .nat 0],
     [.nat 5900000, .int 0, .nat 1, .int 0, .nat 1, .nat 3, .nat addrB, .nat addrC, .nat 0, .int 0xa9059cbb, .nat 68, .nat 250000, .nat 24913, .nat 1],
     [.nat 5900000, .int 2, .nat 0, .int (-1), .nat 0, .nat 4, .nat addrC, .nat addrA, .nat 0, .int (-1), .nat 3, .nat 1000000, .nat 1000000, .nat 2]]
  | "log" =>
    [[.nat 5900000, .int 9, .nat 0, .nat addrA, .nats [topicT, addrA, addrB], .bytes (encLE 32 0 ++ [0x12, 0x34])],
     [.nat 5900000, .int 9, .nat 1, .nat addrB, .nats [topicT, addrA, addrB, 7], .bytes []],
     [.nat 5900001, .int 0, .nat 0, .nat addrC, .nats [], .bytes [0xff]]]
  | "transfer" =>
    [[.nat 5900000, .int 0, .nat 0, .nat 0, .nat addrA, .nat addrB, .nat 100304115660702000],
     [.nat 5900000, .int 1, .nat 3, .nat 2, .nat addrB, .nat 0, .nat big]]
  | "storage_diff" =>
    [[.nat 5900000, .int (-1), .nat addrA, .nat 7888, .nat 0, .nat big],
     [.nat 5900000, .int 23, .nat addrB, .nat 0, .nat 14825731600144445158283816798790678541682266951, .nat 1530676800],
     [.nat 5900001, .int 1000000000, .nat addrC, .nat big, .nat big, .nat 0]]
  | "account_diff" =>
    [[.nat 5900000, .int 0, .nat addrA, .nat 16, .nat 17, .nat 406689967679992056, .nat 506994083340694056, .nat 0, .nat 0],
     [.nat 5900000, .int 1000000000, .nat addrB, .nat 0, .nat 0, .nat 0, .nat 3000000000000000000, .nat 0, .nat hashA]]
  | _ => []

/-- Block rows in the 7-column form that precedes the blob columns: the legacy vector. -/
def legacyBlockRows : List Row := (samples "block").map (·.take 7)

def colsOf (name : String) : List ColType := ((tables.find? (·.name == name)).map (·.cols)).getD []

/-- Encode the samples of a table as one raw-codec group. -/
def sampleGroup (name : String) : Option Bytes := encodeGroup [Codec.raw] [] (colsOf name) (samples name)

/-- Every table's samples round-trip through one group, with nothing left over. -/
example : ∀ t ∈ tables, (sampleGroup t.name).bind (fun e => decodeGroup [Codec.raw] t.cols (e ++ [0xaa]))
    = some (samples t.name, [0xaa]) := by native_decide

/-- A legacy 7-column block group reads back under the current table as 7-field rows (its
    blob columns not recorded); a 6-column one is not a block group (it would drop a required
    column); and a shard of a legacy group then a current one (a writer upgraded mid-range)
    reads back as both, each row as wide as its group. -/
def legacyBlockGroup : Option Bytes := encodeGroup [Codec.raw] [] ((colsOf "block").take 7) legacyBlockRows

example : legacyBlockGroup.bind (fun e => decodeGroupAny [Codec.raw] (colsOf "block") (e ++ [0xaa]))
    = some (legacyBlockRows, [0xaa]) := by native_decide

example : (encodeGroup [Codec.raw] [] ((colsOf "block").take 6) ((samples "block").map (·.take 6))).bind
    (fun e => decodeGroupAny [Codec.raw] (colsOf "block") e) = none := by native_decide

example : (legacyBlockGroup.bind fun e1 => (sampleGroup "block").bind fun e2 =>
      (decodeGroupAny [Codec.raw] (colsOf "block") (e1 ++ e2)).bind fun (r1, rest) =>
        (decodeGroupAny [Codec.raw] (colsOf "block") rest).map fun (r2, tail) => (r1 ++ r2, tail))
    = some (legacyBlockRows ++ samples "block", []) := by native_decide

/-- A legacy row hashes as it was written, not padded: the old footers' `:content` stand. -/
example : contentHash (colsOf "block") legacyBlockRows = contentHash ((colsOf "block").take 7) legacyBlockRows := by
  native_decide

/-- A shard of two groups reads back as the concatenation of the rows, whatever the split. -/
example : (encodeShard [Codec.raw] [] (colsOf "tx") [(samples "tx").take 1, (samples "tx").drop 1]).map
    (decodeShard [Codec.raw] (colsOf "tx") 3) = some (samples "tx", []) := by native_decide

/-- A torn tail (half a header) is left where it starts. -/
example : (sampleGroup "log").map (fun e => decodeShard [Codec.raw] (colsOf "log") 4 (e ++ magic ++ [1, 2]))
    = some (samples "log", magic ++ [1, 2]) := by native_decide

/-- The content hash does not see the grouping. -/
example : contentHash (colsOf "tx") ((samples "tx").take 1 ++ (samples "tx").drop 1)
    = contentHash (colsOf "tx") (samples "tx") := rfl

/-- The samples are in `(block, tx)` order, so "blocks ≤ 5900000" is a prefix. -/
example : (samples "storage_diff").takeWhile (fun r => decide (blockOf r ≤ 5900000))
    = (samples "storage_diff").filter (fun r => decide (blockOf r ≤ 5900000)) := by native_decide

/-- The sample storage changes, as the history index sees them. -/
def storageChanges : List (Change (Nat × Nat) Nat) := (samples "storage_diff").filterMap storageChange

/-- The index section round-trips (perm of the sample keys, a 64-bit filter). -/
example : (encodeIndex [0, 2, 1] 7 [1, 2, 3, 4, 5, 6, 7, 8]).bind (fun e => decodeIndex (e ++ [9]))
    = some (([0, 2, 1], 7, [1, 2, 3, 4, 5, 6, 7, 8]), [9]) := by native_decide

/-- The index answer equals the fold on the samples: the key `(addrA, 7888)` changed at
    block 5900000 from 0 to `big`; before, at and after. -/
example : lookup 0 (addrA, 7888) 5899999 storageChanges = foldValue 0 (addrA, 7888) 5899999 storageChanges
    ∧ lookup 0 (addrA, 7888) 5899999 storageChanges = 0
    ∧ lookup 0 (addrA, 7888) 5900000 storageChanges = big
    ∧ lookup 0 (addrA, 7888) 5900005 storageChanges = big
    ∧ lookup 42 (addrC, 1) 5900005 storageChanges = 42 := by native_decide

/-- Every sample key is admitted by the filter built over them. -/
example : let keys := storageChanges.map fun c => storageKeyBytes c.key.1 c.key.2
    let m := bloomBitsFor keys.eraseDups.length
    keys.all (mayContain m bloomK (bloomOf m bloomK keys)) = true := by native_decide

end Evm.FactLog
