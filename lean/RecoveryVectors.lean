/-
  RecoveryVectors.lean — `lake exe recoveryVectors` prints Lean-oracle vectors for the
  restart decisions proved in `Evm.Persist.Recovery` (a refinement check).

  One s-expression per line:

    ((anchors…) (dumps…) resume (gc…))

  anchors are `(block t|nil)`, dumps `(block . :sealed|:torn|:corrupt)`, resume is a block
  number, `:genesis` or `:refuse`, gc is `gcSet` (ascending). Blocks are drawn from a small
  range so that duplicates, a block with both a plain and a corrupt dump, verified blocks
  without dumps and dumps without verdicts all occur. `tests/recovery-vectors.lisp`
  feeds each view to `src/state/recovery.lisp` and requires identical decisions.

  Layered files (`Evm.Persist.Layered`, Part D), one line each:

    (:layered (anchors…) (files…) (points…) resume (gcfiles…))

  files are `((:base b) . status)` / `((:layer p n) . status)` / `((:frontier n) . status)`,
  points `(b comp…)`; resume
  is `resumePoint` over `dumpsOf`, gcfiles is `gcFiles` (in file order).

  Key-range merges (`Evm.Persist.Layered`, Part E: snapshot v2's `compose-range`), one line
  each:

    (:compose ((((k v)…) stop)…) ((k v)…) ((k v)…))

  the sources newest first, each an ascending run of keys below 12 with values 0..3 (0 a
  tombstone) and its wipe flag, then `composeRuns` of them, then that merge with the
  tombstones dropped (the filter of `viewRange_slot`).
-/
import Evm.Persist.Recovery
import Evm.Persist.Layered
import Mathlib.Data.Nat.Basic

open Evm.Persist.Recovery
open Evm.Persist.Layered

def lcg (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Draw a value below `n` from the high bits of the next state. -/
def draw (s n : Nat) : Nat × Nat := let s' := lcg s; ((s' / 2 ^ 33) % n, s')

def genAnchors : Nat → Nat → List Anchor × Nat
  | 0, s => ([], s)
  | k + 1, s =>
    let (b, s) := draw s 12
    let (ok, s) := draw s 3
    let (rest, s) := genAnchors k s
    (⟨b, ok != 0, none⟩ :: rest, s)

def genDumps : Nat → Nat → List Dump × Nat
  | 0, s => ([], s)
  | k + 1, s =>
    let (b, s) := draw s 12
    let (st, s) := draw s 5
    let status := if st < 3 then DumpStatus.sealed else if st = 3 then .torn else .corrupt
    let (rest, s) := genDumps k s
    ((b, status) :: rest, s)

def showAnchor (a : Anchor) : String := s!"({a.block} {if a.ok then "t" else "nil"})"

def showDump (d : Dump) : String :=
  let st := match d.2 with | .sealed => ":sealed" | .torn => ":torn" | .corrupt => ":corrupt"
  s!"({d.1} . {st})"

def showResume : Resume → String
  | .block n => toString n
  | .genesis => ":genesis"
  | .refuse  => ":refuse"

def sexpList (xs : List String) : String := "(" ++ " ".intercalate xs ++ ")"

def genComp (s : Nat) : Comp × Nat :=
  let (k, s) := draw s 3
  let (b, s) := draw s 4
  if k = 0 then (.base b, s) else if k = 1 then (.frontier b, s) else
    let (d, s) := draw s 2
    (.layer b (b + d + 1), s)

def genFiles : Nat → Nat → List FileEntry × Nat
  | 0, s => ([], s)
  | k + 1, s =>
    let (c, s) := genComp s
    let (st, s) := draw s 5
    let status := if st < 3 then DumpStatus.sealed else if st = 3 then .torn else .corrupt
    let (rest, s) := genFiles k s
    ((c, status) :: rest, s)

def genComps : Nat → Nat → List Comp × Nat
  | 0, s => ([], s)
  | k + 1, s =>
    let (c, s) := genComp s
    let (rest, s) := genComps k s
    (c :: rest, s)

def genPoints : Nat → Nat → List Point × Nat
  | 0, s => ([], s)
  | k + 1, s =>
    let (b, s) := draw s 6
    let (n, s) := draw s 3
    let (cs, s) := genComps (n + 1) s
    let (rest, s) := genPoints k s
    ((b, cs) :: rest, s)

def showComp : Comp → String
  | .base b => s!"(:base {b})"
  | .layer p n => s!"(:layer {p} {n})"
  | .frontier n => s!"(:frontier {n})"

def showFile (e : FileEntry) : String :=
  let st := match e.2 with | .sealed => ":sealed" | .torn => ":torn" | .corrupt => ":corrupt"
  s!"({showComp e.1} . {st})"

def showPoint (p : Point) : String := sexpList (toString p.1 :: p.2.map showComp)

def genRun : Nat → Nat → List (Nat × Nat) × Nat
  | 0, s => ([], s)
  | k + 1, s =>
    let (rest, s) := genRun k s
    let (keep, s) := draw s 3
    let (v, s) := draw s 4
    (if keep = 0 then (11 - k, v) :: rest else rest, s)

def genSources : Nat → Nat → List (List (Nat × Nat) × Bool) × Nat
  | 0, s => ([], s)
  | k + 1, s =>
    let (r, s) := genRun 12 s
    let (stop, s) := draw s 4
    let (rest, s) := genSources k s
    ((r, stop = 0) :: rest, s)

def showRun (r : List (Nat × Nat)) : String := sexpList (r.map fun (k, v) => s!"({k} {v})")

def main : IO Unit := do
  let mut s := 20261018
  for _ in [0:20000] do
    let (na, s1) := draw s 7
    let (as, s2) := genAnchors na s1
    let (nd, s3) := draw s2 8
    let (ds, s4) := genDumps nd s3
    s := s4
    IO.println <| sexpList [sexpList (as.map showAnchor), sexpList (ds.map showDump),
      showResume (resumePoint as ds), sexpList ((gcSet as ds).map toString)]
  for _ in [0:20000] do
    let (na, s1) := draw s 7
    let (as, s2) := genAnchors na s1
    let (nf, s3) := draw s2 14
    let (fs, s4) := genFiles nf s3
    let (np, s5) := draw s4 8
    let (ps, s6) := genPoints np s5
    s := s6
    IO.println <| sexpList [":layered", sexpList (as.map showAnchor), sexpList (fs.map showFile),
      sexpList (ps.map showPoint), showResume (resumePoint as (dumpsOf fs ps)),
      sexpList ((gcFiles as fs ps).map showComp)]
  for _ in [0:20000] do
    let (n, s1) := draw s 5
    let (srcs, s2) := genSources n s1
    s := s2
    let merged := composeRuns srcs
    IO.println <| sexpList [":compose",
      sexpList (srcs.map fun (r, stop) => sexpList [showRun r, if stop then "t" else "nil"]),
      showRun merged, showRun (merged.filter fun e => e.2 != 0)]
