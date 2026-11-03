/-
  InterpFixtures.lean — generate fixture s-expressions for the CL audit.

  For each Form opcode, emits N (pre, post) state pairs where:
    pre  := a seeded-random CLState set up appropriately for that opcode
    post := stepOf opForm pre   (i.e., Form.interp's result)

  Output is consumed by scripts/audit-macros.lisp, which builds an SBCL
  evm-state matching `pre`, runs the CL macro, and verifies the result
  matches `post`. This closes the interp ↔ toCL gap directly.

  Build: lake exe interpFixtures > tests/interp-fixtures.sexp
-/

import Evm.CL.Extract
import Evm.CL.MacroSpec

open Evm.CL.Extract
open Evm.CL.MacroSpec

namespace Evm.CL.InterpFixtures

/-! ## Deterministic RNG (xorshift64) -/

structure Rng where
  state : UInt64
  deriving Inhabited

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x0 := r.state
  let x1 := x0 ^^^ (x0 <<< 13)
  let x2 := x1 ^^^ (x1 >>> 7)
  let x3 := x2 ^^^ (x2 <<< 17)
  (x3, { state := x3 })

def Rng.u256 (r : Rng) : Evm.U256 × Rng :=
  let p1 := r.next
  let p2 := p1.snd.next
  let p3 := p2.snd.next
  let p4 := p3.snd.next
  let n : Nat :=
    p1.fst.toNat |||
    (p2.fst.toNat <<< 64) |||
    (p3.fst.toNat <<< 128) |||
    (p4.fst.toNat <<< 192)
  (Evm.U256.ofNat n, p4.snd)

def Rng.natRange (r : Rng) (n : Nat) : Nat × Rng :=
  let p := r.next
  if n = 0 then (0, p.snd) else (p.fst.toNat % n, p.snd)

def Rng.u8 (r : Rng) : UInt8 × Rng :=
  let p := r.next
  (UInt8.ofNat (p.fst.toNat % 256), p.snd)

def Rng.byteArray (r : Rng) (len : Nat) : ByteArray × Rng := Id.run do
  let mut bs : ByteArray := ByteArray.empty
  let mut r := r
  for _ in [0:len] do
    let p := r.u8
    bs := bs.push p.fst
    r := p.snd
  return (bs, r)

/-! ## CLState specialization

We use `Nat` for Addr, `Evm.U256` for Val so we can serialize. -/

abbrev FState := CLState Nat Evm.U256

def emptyState : FState := {
  stack := [], pc := 0, gasLeft := 1000000,
  halted := false, reverted := false,
  addr := 0,
  cache   := fun _ _ => none,
  journal := [],
  staticp := false,
  memory := .empty, code := .empty, output := .empty,
  jumpCount := 0, calldata := .empty, mp := 0,
  origin := 0, caller := 0, callvalue := 0, gasprice := 0,
  chainid := 1, coinbase := 0, timestamp := 0,
  blockNumber := 0, gaslimit := 0, basefee := 0,
  prevRandao := 0, blobBaseFee := 0,
  returndata := .empty,
  tstorage := fun _ => none,
  worldBalance := fun _ => 0, worldCodeSize := fun _ => 0,
  worldCode := fun _ => .empty, worldCodeHash := fun _ => 0,
  worldBlockHash := fun _ => 0,
  worldBalanceByVal   := fun _ => 0,
  worldCodeSizeByVal  := fun _ => 0,
  worldCodeByVal      := fun _ => .empty,
  worldCodeHashByVal  := fun _ => 0,
  worldBlockHashByVal := fun _ => 0,
  addrToVal := Evm.U256.ofNat }

/-! ## S-expression serialization -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + '0'.toNat)
  else Char.ofNat (n - 10 + 'a'.toNat)

partial def natToHexAux (n : Nat) (acc : String) : String :=
  if n = 0 then acc
  else natToHexAux (n / 16) (String.ofList [hexDigit (n % 16)] ++ acc)

def natToHex (n : Nat) : String :=
  if n = 0 then "0" else natToHexAux n ""

def u256ToSexp (v : Evm.U256) : String := s!"#x{natToHex v.toNat}"

def stackToSexp (st : List Evm.U256) : String :=
  "(" ++ String.intercalate " " (st.map u256ToSexp) ++ ")"

def byteArrayToHex (ba : ByteArray) : String := Id.run do
  let mut s : String := ""
  for i in [0:ba.size] do
    let b := ba.get! i
    s := s ++ String.ofList [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]
  return s

structure GenMeta where
  cacheEntries : List (Nat × Evm.U256 × Evm.U256) := []
  worldBalanceByValEntries : List (Evm.U256 × Evm.U256) := []
  worldCodeSizeByValEntries : List (Evm.U256 × Nat) := []
  worldCodeByValEntries : List (Evm.U256 × ByteArray) := []
  worldCodeHashByValEntries : List (Evm.U256 × Evm.U256) := []
  worldBlockHashByValEntries : List (Evm.U256 × Evm.U256) := []
  tstorageEntries : List (Evm.U256 × Evm.U256) := []
  deriving Inhabited

abbrev GenState := FState × GenMeta

def cacheToSexp (entries : List (Nat × Evm.U256 × Evm.U256)) : String :=
  "(" ++ String.intercalate " " (entries.map fun e =>
    s!"({e.fst} {u256ToSexp e.snd.fst} {u256ToSexp e.snd.snd})") ++ ")"

def valNatListToSexp (entries : List (Evm.U256 × Nat)) : String :=
  "(" ++ String.intercalate " " (entries.map fun e =>
    s!"({u256ToSexp e.fst} {e.snd})") ++ ")"

def valValListToSexp (entries : List (Evm.U256 × Evm.U256)) : String :=
  "(" ++ String.intercalate " " (entries.map fun e =>
    s!"({u256ToSexp e.fst} {u256ToSexp e.snd})") ++ ")"

def valBaListToSexp (entries : List (Evm.U256 × ByteArray)) : String :=
  "(" ++ String.intercalate " " (entries.map fun e =>
    s!"({u256ToSexp e.fst} \"{byteArrayToHex e.snd}\")") ++ ")"

def stateToSexp (s : FState) (m : GenMeta) : String :=
  let parts : List String := List.filterMap id [
    some s!":pc {s.pc}",
    some s!":gas-left {s.gasLeft}",
    some s!":stack {stackToSexp s.stack}",
    if s.halted   then some ":halted t"   else none,
    if s.reverted then some ":reverted t" else none,
    if s.staticp  then some ":staticp t"  else none,
    if s.addr ≠ 0 then some s!":address {s.addr}" else none,
    if s.memory.size > 0 then some s!":memory-hex \"{byteArrayToHex s.memory}\"" else none,
    if s.code.size > 0   then some s!":code-hex \"{byteArrayToHex s.code}\""     else none,
    if s.calldata.size > 0 then some s!":calldata-hex \"{byteArrayToHex s.calldata}\"" else none,
    if s.returndata.size > 0 then some s!":returndata-hex \"{byteArrayToHex s.returndata}\"" else none,
    if s.output.size > 0 then some s!":output-hex \"{byteArrayToHex s.output}\"" else none,
    if s.mp ≠ 0 then some s!":mp {s.mp}" else none,
    if m.cacheEntries ≠ [] then some s!":cache {cacheToSexp m.cacheEntries}" else none,
    if s.journal.length ≠ 0 then some s!":journal-len {s.journal.length}" else none,
    if m.worldBalanceByValEntries ≠ [] then
      some s!":world-balance-by-val {valValListToSexp m.worldBalanceByValEntries}" else none,
    if m.worldCodeSizeByValEntries ≠ [] then
      some s!":world-code-size-by-val {valNatListToSexp m.worldCodeSizeByValEntries}" else none,
    if m.worldCodeByValEntries ≠ [] then
      some s!":world-code-by-val {valBaListToSexp m.worldCodeByValEntries}" else none,
    if m.worldCodeHashByValEntries ≠ [] then
      some s!":world-code-hash-by-val {valValListToSexp m.worldCodeHashByValEntries}" else none,
    if m.worldBlockHashByValEntries ≠ [] then
      some s!":world-block-hash-by-val {valValListToSexp m.worldBlockHashByValEntries}" else none,
    if m.tstorageEntries ≠ [] then
      some s!":tstorage {valValListToSexp m.tstorageEntries}" else none,
    if s.callvalue ≠ 0 then some s!":callvalue {u256ToSexp s.callvalue}" else none,
    if s.gasprice ≠ 0 then some s!":gasprice {u256ToSexp s.gasprice}" else none,
    if s.chainid ≠ 1 then some s!":chainid {u256ToSexp s.chainid}" else none,
    if s.timestamp ≠ 0 then some s!":timestamp {u256ToSexp s.timestamp}" else none,
    if s.blockNumber ≠ 0 then some s!":block-number {u256ToSexp s.blockNumber}" else none,
    if s.gaslimit ≠ 0 then some s!":gaslimit {u256ToSexp s.gaslimit}" else none,
    if s.basefee ≠ 0 then some s!":basefee {u256ToSexp s.basefee}" else none,
    if s.origin ≠ 0 then some s!":origin {s.origin}" else none,
    if s.caller ≠ 0 then some s!":caller {s.caller}" else none,
    if s.coinbase ≠ 0 then some s!":coinbase {s.coinbase}" else none
  ]
  "(" ++ String.intercalate " " parts ++ ")"

def postToSexp (post : Option FState) (preMeta : GenMeta) : String :=
  match post with
  | none => "(:none t)"
  | some s' => stateToSexp s' preMeta

/-! ## Pre-state generators

Each returns `(pre, meta, r')`. Generators are split per shape; some
opcodes share the same generator (binary arith → genBinaryStack). -/

def genBinaryStack (r : Rng) : GenState × Rng :=
  let p1 := r.u256
  let p2 := p1.snd.u256
  let s : FState := { emptyState with stack := [p1.fst, p2.fst] }
  ((s, {}), p2.snd)

def genTernaryStack (r : Rng) : GenState × Rng :=
  let p1 := r.u256
  let p2 := p1.snd.u256
  let p3 := p2.snd.u256
  let s : FState := { emptyState with stack := [p1.fst, p2.fst, p3.fst] }
  ((s, {}), p3.snd)

def genUnaryStack (r : Rng) : GenState × Rng :=
  let p := r.u256
  let s : FState := { emptyState with stack := [p.fst] }
  ((s, {}), p.snd)

def genEmptyStack (r : Rng) : GenState × Rng :=
  ((emptyState, {}), r)

/-- For SIGNEXTEND/EXP — small first operand. -/
def genBinarySmall (r : Rng) : GenState × Rng :=
  let p1 := r.u256
  let p2 := p1.snd.natRange 64
  let s : FState := { emptyState with stack := [p1.fst, Evm.U256.ofNat p2.fst] }
  ((s, {}), p2.snd)

/-- BYTE/SHL/SHR/SAR — small first operand (shift count / byte index). -/
def genShiftStack (r : Rng) : GenState × Rng :=
  let p1 := r.natRange 300
  let p2 := p1.snd.u256
  let s : FState := { emptyState with stack := [Evm.U256.ofNat p1.fst, p2.fst] }
  ((s, {}), p2.snd)

def genWithAddr (r : Rng) (field : String) : GenState × Rng :=
  let p := r.natRange (1 <<< 160)
  let s : FState := match field with
    | "address"  => { emptyState with addr := p.fst }
    | "origin"   => { emptyState with origin := p.fst }
    | "caller"   => { emptyState with caller := p.fst }
    | "coinbase" => { emptyState with coinbase := p.fst }
    | _ => emptyState
  ((s, {}), p.snd)

def genWithVal (r : Rng) (field : String) : GenState × Rng :=
  let p := r.u256
  let s : FState := match field with
    | "callvalue"    => { emptyState with callvalue := p.fst }
    | "gasprice"     => { emptyState with gasprice := p.fst }
    | "chainid"      => { emptyState with chainid := p.fst }
    | "timestamp"    => { emptyState with timestamp := p.fst }
    | "block-number" => { emptyState with blockNumber := p.fst }
    | "gaslimit"     => { emptyState with gaslimit := p.fst }
    | "basefee"      => { emptyState with basefee := p.fst }
    | _ => emptyState
  ((s, {}), p.snd)

def genWithPc (r : Rng) : GenState × Rng :=
  let p := r.natRange 10000
  ((({ emptyState with pc := p.fst } : FState), ({} : GenMeta)), p.snd)

def genWithGas (r : Rng) : GenState × Rng :=
  let p := r.natRange 10000000
  let g := max p.fst 1000
  ((({ emptyState with gasLeft := g } : FState), ({} : GenMeta)), p.snd)

def genWithMemory (r : Rng) (len : Nat) : GenState × Rng :=
  let p := r.byteArray len
  ((({ emptyState with memory := p.fst, mp := len } : FState), ({} : GenMeta)), p.snd)

def genWithCalldata (r : Rng) (len : Nat) : GenState × Rng :=
  let p := r.byteArray len
  ((({ emptyState with calldata := p.fst } : FState), ({} : GenMeta)), p.snd)

def genWithCode (r : Rng) (len : Nat) : GenState × Rng :=
  let p := r.byteArray len
  ((({ emptyState with code := p.fst } : FState), ({} : GenMeta)), p.snd)

def genWithReturndata (r : Rng) (len : Nat) : GenState × Rng :=
  let p := r.byteArray len
  ((({ emptyState with returndata := p.fst } : FState), ({} : GenMeta)), p.snd)

def genMemOp (r : Rng) (offsetMax : Nat) : GenState × Rng :=
  let p1 := r.natRange offsetMax
  let p2 := p1.snd.u256
  let p3 := p2.snd.byteArray (offsetMax + 32)
  let s : FState := { emptyState with
    stack := [Evm.U256.ofNat p1.fst, p2.fst],
    memory := p3.fst, mp := offsetMax + 32 }
  ((s, {}), p3.snd)

def genSloadStack (r : Rng) : GenState × Rng :=
  let p1 := r.u256
  let p2 := p1.snd.u256
  let addr : Nat := 42
  let slot := p1.fst
  let v := p2.fst
  let cache : Evm.CL.StorageCache.Cache Nat Evm.U256 Evm.U256 :=
    fun a k => if a = addr ∧ k = slot then some v else none
  let s : FState := { emptyState with stack := [slot], addr := addr, cache := cache }
  ((s, { cacheEntries := [(addr, slot, v)] }), p2.snd)

def genSstoreStack (r : Rng) : GenState × Rng :=
  let p1 := r.u256
  let p2 := p1.snd.u256
  let p3 := p2.snd.u256
  let addr : Nat := 42
  let slot := p1.fst
  let newVal := p2.fst
  let oldVal := p3.fst
  let cache : Evm.CL.StorageCache.Cache Nat Evm.U256 Evm.U256 :=
    fun a k => if a = addr ∧ k = slot then some oldVal else none
  let s : FState := { emptyState with stack := [slot, newVal], addr := addr, cache := cache }
  ((s, { cacheEntries := [(addr, slot, oldVal)] }), p3.snd)

def genTloadStack (r : Rng) : GenState × Rng :=
  let p1 := r.u256
  let p2 := p1.snd.u256
  let slot := p1.fst
  let v := p2.fst
  let tstorage : Evm.U256 → Option Evm.U256 :=
    fun k => if k = slot then some v else none
  let s : FState := { emptyState with stack := [slot], tstorage := tstorage }
  ((s, { tstorageEntries := [(slot, v)] }), p2.snd)

def genTstoreStack (r : Rng) : GenState × Rng :=
  let p1 := r.u256
  let p2 := p1.snd.u256
  let s : FState := { emptyState with stack := [p1.fst, p2.fst] }
  ((s, {}), p2.snd)

def genPushState (r : Rng) (n : Nat) : GenState × Rng :=
  let p := r.byteArray (n + 1)
  ((({ emptyState with code := p.fst, pc := 0 } : FState), ({} : GenMeta)), p.snd)

def genDupState (r : Rng) (n : Nat) : GenState × Rng := Id.run do
  let mut stk : List Evm.U256 := []
  let mut r := r
  for _ in [0:n] do
    let p := r.u256
    stk := stk ++ [p.fst]
    r := p.snd
  return ((({ emptyState with stack := stk } : FState), ({} : GenMeta)), r)

def genSwapState (r : Rng) (n : Nat) : GenState × Rng := Id.run do
  let mut stk : List Evm.U256 := []
  let mut r := r
  for _ in [0:n + 1] do
    let p := r.u256
    stk := stk ++ [p.fst]
    r := p.snd
  return ((({ emptyState with stack := stk } : FState), ({} : GenMeta)), r)

def genJumpState (r : Rng) (withCond : Bool) : GenState × Rng :=
  let codeLen : Nat := 64
  let p1 := r.natRange codeLen
  let p2 := p1.snd.byteArray codeLen
  let p3 := p2.snd.u256
  let dest := p1.fst
  let code := p2.fst.set! dest 0x5b
  let stk : List Evm.U256 :=
    if withCond then [Evm.U256.ofNat dest, p3.fst] else [Evm.U256.ofNat dest]
  let s : FState := { emptyState with stack := stk, code := code }
  ((s, {}), if withCond then p3.snd else p2.snd)

def genBalanceState (r : Rng) : GenState × Rng :=
  let p1 := r.u256
  let p2 := p1.snd.u256
  let addrV := p1.fst
  let v := p2.fst
  let lookup : Evm.U256 → Evm.U256 := fun k => if k = addrV then v else 0
  let s : FState := { emptyState with stack := [addrV], worldBalanceByVal := lookup }
  ((s, { worldBalanceByValEntries := [(addrV, v)] }), p2.snd)

def genExtcodesizeState (r : Rng) : GenState × Rng :=
  let p1 := r.u256
  let p2 := p1.snd.natRange 24576
  let addrV := p1.fst
  let sz := p2.fst
  let lookup : Evm.U256 → Nat := fun k => if k = addrV then sz else 0
  let s : FState := { emptyState with stack := [addrV], worldCodeSizeByVal := lookup }
  ((s, { worldCodeSizeByValEntries := [(addrV, sz)] }), p2.snd)

def genExtcodehashState (r : Rng) : GenState × Rng :=
  let p1 := r.u256
  let p2 := p1.snd.u256
  let addrV := p1.fst
  let v := p2.fst
  let lookup : Evm.U256 → Evm.U256 := fun k => if k = addrV then v else 0
  let s : FState := { emptyState with stack := [addrV], worldCodeHashByVal := lookup }
  ((s, { worldCodeHashByValEntries := [(addrV, v)] }), p2.snd)

def genBlockhashState (r : Rng) : GenState × Rng :=
  let p1 := r.u256
  let p2 := p1.snd.u256
  let n := p1.fst
  let v := p2.fst
  let lookup : Evm.U256 → Evm.U256 := fun k => if k = n then v else 0
  let s : FState := { emptyState with stack := [n], worldBlockHashByVal := lookup }
  ((s, { worldBlockHashByValEntries := [(n, v)] }), p2.snd)

def genSelfbalanceState (r : Rng) : GenState × Rng :=
  let p := r.u256
  let addr : Nat := 100
  let addrV : Evm.U256 := Evm.U256.ofNat addr
  let lookup : Evm.U256 → Evm.U256 := fun k => if k = addrV then p.fst else 0
  let s : FState := { emptyState with addr := addr, worldBalanceByVal := lookup }
  ((s, { worldBalanceByValEntries := [(addrV, p.fst)] }), p.snd)

def genCalldataLoadState (r : Rng) : GenState × Rng :=
  let p1 := r.natRange 96
  let p2 := p1.snd.byteArray 128
  let s : FState := { emptyState with
    stack := [Evm.U256.ofNat p1.fst], calldata := p2.fst }
  ((s, {}), p2.snd)

def genBufferCopyCalldata (r : Rng) : GenState × Rng :=
  let p1 := r.natRange 96
  let p2 := p1.snd.natRange 96
  let p3 := p2.snd.natRange 32
  let p4 := p3.snd.byteArray 128
  let stk : List Evm.U256 :=
    [Evm.U256.ofNat p1.fst, Evm.U256.ofNat p2.fst, Evm.U256.ofNat p3.fst]
  let s : FState := { emptyState with stack := stk, calldata := p4.fst }
  ((s, {}), p4.snd)

def genBufferCopyCode (r : Rng) : GenState × Rng :=
  let p1 := r.natRange 96
  let p2 := p1.snd.natRange 96
  let p3 := p2.snd.natRange 32
  let p4 := p3.snd.byteArray 128
  let stk : List Evm.U256 :=
    [Evm.U256.ofNat p1.fst, Evm.U256.ofNat p2.fst, Evm.U256.ofNat p3.fst]
  let s : FState := { emptyState with stack := stk, code := p4.fst }
  ((s, {}), p4.snd)

def genBufferCopyReturndata (r : Rng) : GenState × Rng :=
  let p1 := r.natRange 96
  let p2 := p1.snd.natRange 96
  let p3 := p2.snd.natRange 32
  let p4 := p3.snd.byteArray 128
  -- Force in-bounds: clamp len so src + len ≤ size
  let len := if p2.fst + p3.fst > p4.fst.size then 0 else p3.fst
  let stk : List Evm.U256 :=
    [Evm.U256.ofNat p1.fst, Evm.U256.ofNat p2.fst, Evm.U256.ofNat len]
  let s : FState := { emptyState with stack := stk, returndata := p4.fst }
  ((s, {}), p4.snd)

def genMcopyState (r : Rng) : GenState × Rng :=
  let p1 := r.natRange 96
  let p2 := p1.snd.natRange 96
  let p3 := p2.snd.natRange 32
  let p4 := p3.snd.byteArray 256
  let stk : List Evm.U256 :=
    [Evm.U256.ofNat p1.fst, Evm.U256.ofNat p2.fst, Evm.U256.ofNat p3.fst]
  let s : FState := { emptyState with
    stack := stk, memory := p4.fst, mp := p4.fst.size }
  ((s, {}), p4.snd)

def genExtcodecopyState (r : Rng) : GenState × Rng :=
  let p1 := r.u256
  let p2 := p1.snd.natRange 96
  let p3 := p2.snd.natRange 96
  let p4 := p3.snd.natRange 32
  let p5 := p4.snd.byteArray 128
  let addrV := p1.fst
  let stk : List Evm.U256 :=
    [addrV, Evm.U256.ofNat p2.fst, Evm.U256.ofNat p3.fst, Evm.U256.ofNat p4.fst]
  let lookup : Evm.U256 → ByteArray := fun k => if k = addrV then p5.fst else .empty
  let s : FState := { emptyState with stack := stk, worldCodeByVal := lookup }
  ((s, { worldCodeByValEntries := [(addrV, p5.fst)] }), p5.snd)

def genHaltOutputState (r : Rng) : GenState × Rng :=
  let p1 := r.natRange 64
  let p2 := p1.snd.natRange 32
  let p3 := p2.snd.byteArray 128
  let stk : List Evm.U256 := [Evm.U256.ofNat p1.fst, Evm.U256.ofNat p2.fst]
  let s : FState := { emptyState with
    stack := stk, memory := p3.fst, mp := p3.fst.size }
  ((s, {}), p3.snd)

/-- KECCAK256: pop off+len; memory pre-populated. -/
def genKeccakState (r : Rng) : GenState × Rng :=
  let p1 := r.natRange 64
  let p2 := p1.snd.natRange 64
  let p3 := p2.snd.byteArray 128
  let stk : List Evm.U256 := [Evm.U256.ofNat p1.fst, Evm.U256.ofNat p2.fst]
  let s : FState := { emptyState with
    stack := stk, memory := p3.fst, mp := p3.fst.size, gasLeft := 1000000 }
  ((s, {}), p3.snd)

/-- LOG-N: stack = off :: len :: n topics; memory pre-populated. -/
def genLogState (r : Rng) (n : Nat) : GenState × Rng := Id.run do
  let p1 := r.natRange 64
  let p2 := p1.snd.natRange 32
  let p3 := p2.snd.byteArray 128
  let mut stk : List Evm.U256 := [Evm.U256.ofNat p1.fst, Evm.U256.ofNat p2.fst]
  let mut r := p3.snd
  for _ in [0:n] do
    let p := r.u256
    stk := stk ++ [p.fst]
    r := p.snd
  let s : FState := { emptyState with
    stack := stk, memory := p3.fst, mp := p3.fst.size, gasLeft := 10000000 }
  return ((s, {}), r)

/-! ## Adversarial pairs

   Random u256s almost always differ in the high limb, which hides bugs in
   carry/zero-flag propagation across the four 64-bit limbs of u256
   operations. Specifically, the EQ handler's subs/sbcs/cset-eq chain
   returned 1 on (small, small') because the Z flag after the highest-limb
   `sbcs xzr, 0, 0` was set — masking real inequality in limb0. Random
   trials missed it for ~weeks of replay work.

   These pairs deliberately exercise:
     * both values fit in u32 (selectors, function dispatch)
     * high limbs match but low limb differs (the EQ trap)
     * differences confined to limb1, limb2, or limb3 individually
     * sign-bit pairs for SLT/SGT
     * 2^256-1 boundary
-/

def u256Of (n : Nat) : Evm.U256 := Evm.U256.ofNat n
def u256OfHex (s : String) : Evm.U256 :=
  Id.run do
    let mut n : Nat := 0
    for c in s.toList do
      let d :=
        if c.toNat ≥ '0'.toNat ∧ c.toNat ≤ '9'.toNat then c.toNat - '0'.toNat
        else if c.toNat ≥ 'a'.toNat ∧ c.toNat ≤ 'f'.toNat then c.toNat - 'a'.toNat + 10
        else if c.toNat ≥ 'A'.toNat ∧ c.toNat ≤ 'F'.toNat then c.toNat - 'A'.toNat + 10
        else 0
      n := n * 16 + d
    return u256Of n

/-- u256 with `1` in limb `i` (0 = low, 3 = high). -/
def limbBit (i : Nat) : Evm.U256 := u256Of (1 <<< (i * 64))

def adversarialU256Pairs : List (Evm.U256 × Evm.U256) :=
  let max := u256OfHex "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
  let signBit := u256Of (1 <<< 255)
  [ -- Tiny values (the EQ bug fired here)
    (u256Of 0, u256Of 0),
    (u256Of 0, u256Of 1),
    (u256Of 1, u256Of 0),
    (u256Of 1, u256Of 1),
    (u256Of 1, u256Of 2),
    (u256Of 2, u256Of 1),
    -- 32-bit selectors (high 3 limbs all zero)
    (u256OfHex "7065cb48", u256OfHex "7065cb48"),
    (u256OfHex "7065cb48", u256OfHex "173825d9"),
    (u256OfHex "173825d9", u256OfHex "7065cb48"),
    (u256OfHex "ba51a6df", u256OfHex "7065cb48"),
    -- High limbs match, only low differs
    (limbBit 3 + u256Of 1, limbBit 3 + u256Of 2),
    (limbBit 3 + limbBit 2, limbBit 3 + limbBit 2 + u256Of 1),
    -- Only middle limbs differ
    (limbBit 1, limbBit 1 + u256Of 1),
    (limbBit 2, limbBit 2 + limbBit 1),
    -- Adjacent values
    (u256OfHex "ff", u256OfHex "fe"),
    (u256OfHex "fe", u256OfHex "ff"),
    -- 2^256 boundary
    (max, max),
    (max, max - u256Of 1),
    (max - u256Of 1, max),
    -- Sign bit for SLT/SGT
    (signBit, u256Of 1),
    (u256Of 1, signBit),
    (signBit + u256Of 1, signBit),
    -- Matching huge values
    (limbBit 3 + limbBit 2 + limbBit 1, limbBit 3 + limbBit 2 + limbBit 1) ]

def adversarialBinaryStates : List GenState :=
  adversarialU256Pairs.map fun (a, b) =>
    ({ emptyState with stack := [a, b] }, {})

/-! ## Op registry -/

structure FixtureCase where
  name        : String
  gen         : Rng → GenState × Rng
  runForm     : FState → Option FState
  adversarial : List GenState := []

def runFixtureCase (fc : FixtureCase) (r : Rng) :
    FState × GenMeta × Option FState × Rng :=
  let g := fc.gen r
  let pre := g.fst.fst
  let mta := g.fst.snd
  let post := fc.runForm pre
  (pre, mta, post, g.snd)

def allFixtures : List FixtureCase := [
  { name := "ADD",  gen := genBinaryStack, runForm := stepOf addForm,
    adversarial := adversarialBinaryStates },
  { name := "SUB",  gen := genBinaryStack, runForm := stepOf subForm,
    adversarial := adversarialBinaryStates },
  { name := "MUL",  gen := genBinaryStack, runForm := stepOf mulForm,
    adversarial := adversarialBinaryStates },
  { name := "DIV",  gen := genBinaryStack, runForm := stepOf divForm,
    adversarial := adversarialBinaryStates },
  { name := "MOD",  gen := genBinaryStack, runForm := stepOf modForm,
    adversarial := adversarialBinaryStates },
  { name := "SDIV", gen := genBinaryStack, runForm := stepOf sdivForm,
    adversarial := adversarialBinaryStates },
  { name := "SMOD", gen := genBinaryStack, runForm := stepOf smodForm,
    adversarial := adversarialBinaryStates },
  { name := "LT",   gen := genBinaryStack, runForm := stepOf ltForm,
    adversarial := adversarialBinaryStates },
  { name := "GT",   gen := genBinaryStack, runForm := stepOf gtForm,
    adversarial := adversarialBinaryStates },
  { name := "SLT",  gen := genBinaryStack, runForm := stepOf sltForm,
    adversarial := adversarialBinaryStates },
  { name := "SGT",  gen := genBinaryStack, runForm := stepOf sgtForm,
    adversarial := adversarialBinaryStates },
  { name := "EQ",   gen := genBinaryStack, runForm := stepOf eqForm,
    adversarial := adversarialBinaryStates },
  { name := "AND",  gen := genBinaryStack, runForm := stepOf andForm,
    adversarial := adversarialBinaryStates },
  { name := "OR",   gen := genBinaryStack, runForm := stepOf orForm,
    adversarial := adversarialBinaryStates },
  { name := "XOR",  gen := genBinaryStack, runForm := stepOf xorForm,
    adversarial := adversarialBinaryStates },
  { name := "EXP",        gen := genBinarySmall, runForm := stepOf expForm },
  { name := "SIGNEXTEND", gen := genBinarySmall, runForm := stepOf signextendForm },
  { name := "SHL",  gen := genShiftStack, runForm := stepOf shlForm },
  { name := "SHR",  gen := genShiftStack, runForm := stepOf shrForm },
  { name := "SAR",  gen := genShiftStack, runForm := stepOf sarForm },
  { name := "BYTE", gen := genShiftStack, runForm := stepOf byteForm },
  { name := "ISZERO", gen := genUnaryStack, runForm := stepOf iszeroForm },
  { name := "NOT",    gen := genUnaryStack, runForm := stepOf notForm },
  { name := "POP",    gen := genUnaryStack, runForm := stepOf popForm },
  { name := "ADDMOD", gen := genTernaryStack, runForm := stepOf addmodForm },
  { name := "MULMOD", gen := genTernaryStack, runForm := stepOf mulmodForm },
  { name := "ADDRESS",  gen := fun r => genWithAddr r "address",  runForm := stepOf addressForm },
  { name := "ORIGIN",   gen := fun r => genWithAddr r "origin",   runForm := stepOf originForm },
  { name := "CALLER",   gen := fun r => genWithAddr r "caller",   runForm := stepOf callerForm },
  { name := "COINBASE", gen := fun r => genWithAddr r "coinbase", runForm := stepOf coinbaseForm },
  { name := "CALLVALUE", gen := fun r => genWithVal r "callvalue",    runForm := stepOf callvalueForm },
  { name := "GASPRICE",  gen := fun r => genWithVal r "gasprice",     runForm := stepOf gaspriceForm },
  { name := "CHAINID",   gen := fun r => genWithVal r "chainid",      runForm := stepOf chainidForm },
  { name := "TIMESTAMP", gen := fun r => genWithVal r "timestamp",    runForm := stepOf timestampForm },
  { name := "NUMBER",    gen := fun r => genWithVal r "block-number", runForm := stepOf numberForm },
  { name := "GASLIMIT",  gen := fun r => genWithVal r "gaslimit",     runForm := stepOf gaslimitForm },
  { name := "BASEFEE",   gen := fun r => genWithVal r "basefee",      runForm := stepOf basefeeForm },
  { name := "PC",  gen := genWithPc,  runForm := stepOf pcForm },
  { name := "GAS", gen := genWithGas, runForm := stepOf gasForm },
  { name := "MSIZE",          gen := fun r => genWithMemory r 128,     runForm := stepOf msizeForm },
  { name := "CALLDATASIZE",   gen := fun r => genWithCalldata r 128,   runForm := stepOf calldatasizeForm },
  { name := "CODESIZE",       gen := fun r => genWithCode r 256,       runForm := stepOf codesizeForm },
  { name := "RETURNDATASIZE", gen := fun r => genWithReturndata r 128, runForm := stepOf returndatasizeForm },
  { name := "STOP",     gen := genEmptyStack, runForm := stepOf stopForm },
  { name := "JUMPDEST", gen := genEmptyStack, runForm := stepOf jumpdestForm },
  { name := "INVALID",  gen := genEmptyStack, runForm := stepOf invalidForm },
  { name := "SLOAD",  gen := genSloadStack,  runForm := stepOf sloadForm },
  { name := "SSTORE", gen := genSstoreStack, runForm := stepOf sstoreForm },
  { name := "TLOAD",  gen := genTloadStack,  runForm := stepOf tloadForm },
  { name := "TSTORE", gen := genTstoreStack, runForm := stepOf tstoreForm },
  { name := "MLOAD",   gen := fun r => genMemOp r 64, runForm := stepOf mloadForm },
  { name := "MSTORE",  gen := fun r => genMemOp r 64, runForm := stepOf mstoreForm },
  { name := "MSTORE8", gen := fun r => genMemOp r 64, runForm := stepOf mstore8Form },
  { name := "JUMP",  gen := fun r => genJumpState r false, runForm := stepOf jumpForm },
  { name := "JUMPI", gen := fun r => genJumpState r true,  runForm := stepOf jumpiForm },
  { name := "DUP1",  gen := fun r => genDupState r 1,  runForm := stepOf (dupForm 1) },
  { name := "DUP3",  gen := fun r => genDupState r 3,  runForm := stepOf (dupForm 3) },
  { name := "SWAP1", gen := fun r => genSwapState r 1, runForm := stepOf (swapForm 1) },
  { name := "SWAP3", gen := fun r => genSwapState r 3, runForm := stepOf (swapForm 3) },
  { name := "CALLDATALOAD",   gen := genCalldataLoadState,    runForm := stepOf calldataloadForm },
  { name := "CALLDATACOPY",   gen := genBufferCopyCalldata,   runForm := stepOf calldatacopyForm },
  { name := "CODECOPY",       gen := genBufferCopyCode,       runForm := stepOf codecopyForm },
  { name := "RETURNDATACOPY", gen := genBufferCopyReturndata, runForm := stepOf returndatacopyForm },
  { name := "MCOPY",          gen := genMcopyState,           runForm := stepOf mcopyForm },
  { name := "BALANCE",     gen := genBalanceState,      runForm := stepOf balanceForm },
  { name := "SELFBALANCE", gen := genSelfbalanceState,  runForm := stepOf selfbalanceForm },
  { name := "EXTCODESIZE", gen := genExtcodesizeState,  runForm := stepOf extcodesizeForm },
  { name := "EXTCODEHASH", gen := genExtcodehashState,  runForm := stepOf extcodehashForm },
  { name := "BLOCKHASH",   gen := genBlockhashState,    runForm := stepOf blockhashForm },
  { name := "EXTCODECOPY", gen := genExtcodecopyState,  runForm := stepOf extcodecopyForm },
  { name := "RETURN", gen := genHaltOutputState, runForm := stepOf returnForm },
  { name := "REVERT", gen := genHaltOutputState, runForm := stepOf revertForm },
  { name := "PUSH0",  gen := fun r => genPushState r 0,  runForm := stepOf (pushForm 0) },
  { name := "PUSH1",  gen := fun r => genPushState r 1,  runForm := stepOf (pushForm 1) },
  { name := "PUSH2",  gen := fun r => genPushState r 2,  runForm := stepOf (pushForm 2) },
  { name := "PUSH3",  gen := fun r => genPushState r 3,  runForm := stepOf (pushForm 3) },
  { name := "PUSH4",  gen := fun r => genPushState r 4,  runForm := stepOf (pushForm 4) },
  { name := "PUSH5",  gen := fun r => genPushState r 5,  runForm := stepOf (pushForm 5) },
  { name := "PUSH8",  gen := fun r => genPushState r 8,  runForm := stepOf (pushForm 8) },
  { name := "PUSH9",  gen := fun r => genPushState r 9,  runForm := stepOf (pushForm 9) },
  { name := "PUSH16", gen := fun r => genPushState r 16, runForm := stepOf (pushForm 16) },
  { name := "PUSH17", gen := fun r => genPushState r 17, runForm := stepOf (pushForm 17) },
  { name := "PUSH24", gen := fun r => genPushState r 24, runForm := stepOf (pushForm 24) },
  { name := "PUSH25", gen := fun r => genPushState r 25, runForm := stepOf (pushForm 25) },
  { name := "PUSH32", gen := fun r => genPushState r 32, runForm := stepOf (pushForm 32) },
  { name := "LOG0", gen := fun r => genLogState r 0, runForm := stepOf (logForm 0) },
  { name := "LOG1", gen := fun r => genLogState r 1, runForm := stepOf (logForm 1) },
  { name := "LOG2", gen := fun r => genLogState r 2, runForm := stepOf (logForm 2) },
  { name := "LOG3", gen := fun r => genLogState r 3, runForm := stepOf (logForm 3) },
  { name := "LOG4", gen := fun r => genLogState r 4, runForm := stepOf (logForm 4) },
  { name := "KECCAK256", gen := genKeccakState, runForm := stepOf keccakForm }
]

/-! ## Main driver -/

def trialsPerOp : Nat := 50

def emitOpFixtures (fc : FixtureCase) (rInit : Rng) : IO Rng := do
  IO.println s!"  (:name \"{fc.name}\" :cases ("
  -- Adversarial pre-baked cases come first.
  for g in fc.adversarial do
    let pre := g.fst
    let mta := g.snd
    let post := fc.runForm pre
    let preStr := stateToSexp pre mta
    let postStr := postToSexp post mta
    IO.println s!"    (:pre {preStr} :post {postStr})"
  let mut r := rInit
  for _ in [0:trialsPerOp] do
    let res := runFixtureCase fc r
    let pre := res.fst
    let mta := res.snd.fst
    let post := res.snd.snd.fst
    r := res.snd.snd.snd
    let preStr := stateToSexp pre mta
    let postStr := postToSexp post mta
    IO.println s!"    (:pre {preStr} :post {postStr})"
  IO.println "  ))"
  return r

def runMain : IO Unit := do
  IO.println ";;; Auto-generated by lake exe interpFixtures. Do not edit."
  IO.println "(:opcodes ("
  let mut r : Rng := { state := 0x9E3779B97F4A7C15 }
  for fc in allFixtures do
    r ← emitOpFixtures fc r
  IO.println "))"

end Evm.CL.InterpFixtures

def main : IO Unit := Evm.CL.InterpFixtures.runMain
