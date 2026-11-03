/-
  X86RunVectors.lean — `lake exe x86RunVectors` emits small x86-64 programs
  assembled by `X86Asm.assemble`, each with arguments and the value Lean says
  it must return:

      <name>\t<hex bytes>\t<arg0>\t<arg1>\t<expected>

  `scripts/verify-x86-run.sh` runs each under Rosetta 2 through `c/x86_run.c`
  and compares. This is the first EXECUTION of bytes the pipeline produced: the
  encoder, the relaxation pass, the addressing-mode rules and the flag
  semantics all meet the hardware here. Each program targets one of those:

    memcost     the memory-expansion formula 3w + w²/512 — imul/shr/lea/add
    sumloop     a backward rel8 branch that actually loops (sum 1..n)
    nearjump    a forward branch kept short, taken and not taken
    farjump     the same over 130 bytes of padding — widened to rel32 by
                relaxation, and it still lands
    maxcmov     cmp + cmovb — the carry polarity, as a conditional move
    sibbase     a load through [r12 + r13 - 48]: SIB-forced base, disp-forced
                index register, negative disp8, the NOS addressing shape
    memalu      an ALU op with a memory operand, [rdi + 8]
    shl1        the dedicated shift-by-one encoding
    lzcnt       the clz lowering (also probes whether the oracle has LZCNT)

  Arguments `@N` are addresses of element N of the harness's u64 array, whose
  element i holds 1000 + i.
-/

import Evm.CL.X86Asm
import Evm.CL.X86Run
import Evm.CL.X86Dispatch
import Evm.CL.X86Handler

open Evm.CL.AsmCore Evm.CL.X86Encode Evm.CL.X86Items Evm.CL.X86Asm

def hex2 (b : UInt8) : String :=
  let s := String.ofList (Nat.toDigits 16 b.toNat)
  if s.length == 1 then "0" ++ s else s

def hexOf (its : List XItem) : String :=
  String.join ((assemble its).1.toList.map hex2)

structure Vec where
  name : String
  prog : List XItem
  a0 : String
  a1 : String
  expected : Nat
  /-- extra harness tokens: `N=V` presets, `?N` readbacks -/
  extra : String := ""
  /-- expected readbacks, appended to the result -/
  expectedExtra : String := ""
  syms : List (String × String) := []

/-- A plain vector: two register arguments, one expected result. -/
def v (name : String) (prog : List XItem) (a0 a1 : String) (expected : Nat) : Vec :=
  { name, prog, a0, a1, expected }

def hexWith (syms : List (String × String)) (its : List XItem) : String :=
  String.join ((assembleWith syms its).1.toList.map hex2)

/-- The abs64 relocations as harness tokens: `!sym:off`. -/
def relocTokens (syms : List (String × String)) (its : List XItem) : String :=
  String.intercalate " " ((assembleWith syms its).2.filterMap (fun r =>
    if r.kind == .abs64 then some s!"!{r.sym}:{r.byteOff}" else none))

/-! ## The memexpand gadget, end to end

`AsmCore.memExpandInstrs` lowered through `x86Items`, wrapped in a SysV
prologue that puts the state pointer in rbx (x20's role) and `newEnd` in rax
(x0's), zeroes the accumulator rsi (x17's), and after the gadget returns the
accumulated cost. `_eita_oog` is bound to a local stub returning a sentinel.
The state lives in the harness array: `[rbx+48]` = element 6 (memory_size),
`[rbx+56]` = element 7 (cap). Expectations are the gadget's contract —
`cost(w) = 3w + w²/512`, delta on growth, size rounded up to words — which
`MemExpandSpec.memExpand_acc_refines` ties to `Gas.memoryExpansionCost`. -/

def oogSentinel : Nat := 4294967295

def memExpandProg : List XItem :=
  [.I (.push .rbx), .I (.movRR .rbx .rdi), .I (.movRR .rax .rsi), .I (.movRI .rsi 0)]
  ++ progItems memExpandInstrs
  ++ [.I (.movRR .rax .rsi), .I (.pop .rbx), .I .ret,
      .L "oog", .I (.movRI .rax (Int.ofNat oogSentinel)), .I (.pop .rbx), .I .ret]

def words (x : Nat) : Nat := (x + 31) / 32

/-- (cost charged, memory_size afterwards) -/
def memExpandExpect (oldSize cap newEnd : Nat) : Nat × Nat :=
  if newEnd > cap then (oogSentinel, oldSize)
  else
    let wn := words newEnd
    let wo := oldSize / 32
    if wn ≤ wo then (0, oldSize)
    else (memCost wn - memCost wo, wn * 32)

/-! ## The frame, end to end

`X86Run.prologueBody ++ body ++ X86Run.syncAndRet` as one function. The state
lives at element 0 of the harness array (pc=7, gas=9, depth as given,
stackBase → element 16), the stack from element 16 (word k at 16+4k). The
epilogue leaves the depth in rax; the readbacks are pc, gas, depth and the
word at stack[depth-1] (or word 0 when the stack is empty, which must be
untouched). -/

/-- `expected` is the readbacks only (pc gas depth limb0 limb1 limb2 limb3), with
    a leading space; the result column is the depth. -/
def frameVec (nm : String) (body : List XItem) (depth : Nat) (expected : String) : Vec :=
  let top := if depth = 0 then 16 else 16 + 4 * (depth - 1)
  { name := s!"frame_{nm}", prog := Evm.CL.X86Run.prologueBody ++ body ++ Evm.CL.X86Run.syncAndRet,
    a0 := "@0", a1 := "0", expected := depth,
    extra := s!"0=7 1=9 2={depth} 4=@16 ?0 ?1 ?2 ?{top} ?{top+1} ?{top+2} ?{top+3}",
    expectedExtra := expected }

/-! ## MSTORE, the whole handler

State at element 0: gas (1), depth (2), mp (3), stackBase → element 16 (4),
memory base → element 32 (5), memory_size (6), cap (7). The stack's word k is
at elements 16+4k; MSTORE pops offset (TOS, word depth-1) then value (NOS, word
depth-2). The memory is 128 bytes from element 32. The result column is the
depth after the handler; readbacks are chosen per case. -/

def mstoreVec (nm : String) (gas depth mp cap size : Nat) (value : Nat × Nat × Nat × Nat)
    (offset : Nat) (reads : String) (expected : String) : Vec :=
  let (l0, l1, l2, l3) := value
  let nosAt := 16 + 4 * (depth - 2)
  let tosAt := 16 + 4 * (depth - 1)
  let hiOff := if nm == "oog_hi_offset" then 1 else 0
  { name := s!"mstore_{nm}", prog := Evm.CL.X86Handler.mstoreX86,
    a0 := "@0", a1 := "0", expected := if depth ≥ 2 && gas ≥ 6 && hiOff = 0 then depth - 2 else depth,
    extra := s!"1={gas} 2={depth} 3={mp} 4=@16 5=@32 6={size} 7={cap} " ++
             s!"{nosAt}={l0} {nosAt+1}={l1} {nosAt+2}={l2} {nosAt+3}={l3} " ++
             s!"{tosAt}={offset} {tosAt+1}={hiOff} {tosAt+2}=0 {tosAt+3}=0 {reads}",
    expectedExtra := expected, syms := Evm.CL.X86Handler.faultSyms }

/-- MLOAD: pops the offset (TOS), pushes the word at memory[offset..+32],
    big-endian: limb k of the result is the byte-swapped u64 at +8·(3-k). -/
def mloadVec (nm : String) (gas depth mp cap size : Nat) (mem : Nat × Nat × Nat × Nat)
    (offset hiOff : Nat) (reads : String) (expected : String) : Vec :=
  let (m0, m1, m2, m3) := mem
  let tosAt := 16 + 4 * (depth - 1)
  { name := s!"mload_{nm}", prog := Evm.CL.X86Handler.mloadX86,
    a0 := "@0", a1 := "0", expected := depth,
    extra := s!"1={gas} 2={depth} 3={mp} 4=@16 5=@32 6={size} 7={cap} " ++
             s!"32={m0} 33={m1} 34={m2} 35={m3} " ++
             s!"{tosAt}={offset} {tosAt+1}={hiOff} {tosAt+2}=0 {tosAt+3}=0 {reads}",
    expectedExtra := expected, syms := Evm.CL.X86Handler.faultSyms }

/-- A compute helper: like `binVec` but with the helper's gas and the
    relocations; TOS = `a`, NOS = `b`, result = helper(a, b). -/
def helperVec (nm : String) (prog : List XItem) (gas : Nat) (a b : Nat × Nat × Nat × Nat)
    (expected : Nat × Nat × Nat × Nat) : Vec :=
  let (a0, a1, a2, a3) := a
  let (b0, b1, b2, b3) := b
  let (e0, e1, e2, e3) := expected
  { name := s!"helper_{nm}", prog, a0 := "@0", a1 := "0", expected := 1,
    extra := s!"1=100 2=2 4=@16 16={b0} 17={b1} 18={b2} 19={b3} 20={a0} 21={a1} 22={a2} 23={a3} ?1 ?2 ?16 ?17 ?18 ?19 " ++
             relocTokens Evm.CL.X86Handler.faultSyms prog,
    expectedExtra := s!" {100 - gas} 1 {e0} {e1} {e2} {e3}", syms := Evm.CL.X86Handler.faultSyms }

/-- A ternary helper: depth 3, word 0 = n (third), word 1 = b, word 2 = a (TOS). -/
def helper3Vec (nm : String) (prog : List XItem) (gas : Nat) (a b n : Nat) (expected : Nat) : Vec :=
  { name := s!"helper_{nm}", prog, a0 := "@0", a1 := "0", expected := 1,
    extra := s!"1=100 2=3 4=@16 16={n} 17=0 18=0 19=0 20={b} 21=0 22=0 23=0 24={a} 25=0 26=0 27=0 ?1 ?2 ?16 ?17 ?18 ?19 " ++
             relocTokens Evm.CL.X86Handler.faultSyms prog,
    expectedExtra := s!" {100 - gas} 1 {expected} 0 0 0", syms := Evm.CL.X86Handler.faultSyms }

/-- A binary op: depth 2, NOS = `b` (word 0), TOS = `a` (word 1); the result
    replaces word 0 and depth becomes 1. Readbacks: gas, depth, the four
    limbs of word 0. `exitGas 3` charges 3. -/
def binVec (nm : String) (prog : List XItem) (a b : Nat × Nat × Nat × Nat)
    (expected : Nat × Nat × Nat × Nat) : Vec :=
  let (a0, a1, a2, a3) := a
  let (b0, b1, b2, b3) := b
  let (e0, e1, e2, e3) := expected
  { name := s!"binop_{nm}", prog, a0 := "@0", a1 := "0", expected := 1,
    extra := s!"1=100 2=2 4=@16 16={b0} 17={b1} 18={b2} 19={b3} 20={a0} 21={a1} 22={a2} 23={a3} ?1 ?2 ?16 ?17 ?18 ?19",
    expectedExtra := s!" 97 1 {e0} {e1} {e2} {e3}", syms := Evm.CL.X86Handler.faultSyms }

def M : Nat := 18446744073709551615   -- 2^64 - 1

/-- Stack-family vectors. The state: pc (0), gas (1), depth (2), stackBase
    → element 16 (4), code base → element 40 (8), code_size (9); stack word
    k at elements 16+4k; code bytes packed little-endian into elements 40+.
    Result column = depth after; readbacks per case. -/
def stackVec (nm : String) (prog : List XItem) (gas depth : Nat) (presets reads expected : String)
    (depthAfter : Nat) : Vec :=
  { name := s!"stack_{nm}", prog, a0 := "@0", a1 := "0", expected := depthAfter,
    extra := s!"0=0 1={gas} 2={depth} 4=@16 8=@40 9=0 {presets} {reads}",
    expectedExtra := expected, syms := Evm.CL.X86Handler.faultSyms }

/-- The 2 KB layout: state at elements 0..63 (offsets up to 504), stack base →
    element 64 (word k at 64+4k), memory base → element 96, code base → element
    128; gas 100 unless preset, pc 7; the result column is the depth after. -/
def bigVec (nm : String) (prog : List XItem) (depth : Nat) (presets reads expected : String)
    (depthAfterDefault : Option Nat := none) : Vec :=
  { name := s!"big_{nm}", prog, a0 := "@0", a1 := "0",
    expected := depthAfterDefault.getD 0,
    extra := s!"0=7 1=100 2={depth} 4=@64 5=@96 8=@128 9=0 {presets} " ++
             relocTokens Evm.CL.X86Handler.faultSyms prog ++ s!" {reads}",
    expectedExtra := expected, syms := Evm.CL.X86Handler.faultSyms }

/-- The 600-byte state (elements 0..74): stack base → element 80 (word k at 80+4k), the
    tx's blob-hash table → element 96 (hash j at 96+4j; `blob_hashes` is element 69, the
    count element 70) and the blob base fee at elements 71..74 (offset 568). -/
def blobVec (nm : String) (prog : List XItem) (depth : Nat) (presets reads expected : String)
    (depthAfter : Nat) : Vec :=
  { name := s!"blob_{nm}", prog, a0 := "@0", a1 := "0", expected := depthAfter,
    extra := s!"0=7 1=100 2={depth} 4=@80 69=@96 {presets} {reads}",
    expectedExtra := expected, syms := Evm.CL.X86Handler.faultSyms }

def memExpandVec (nm : String) (oldSize cap newEnd : Nat) : Vec :=
  let (c, sz) := memExpandExpect oldSize cap newEnd
  { name := s!"memexpand_{nm}", prog := memExpandProg, a0 := "@0", a1 := toString newEnd,
    expected := c, extra := s!"6={oldSize} 7={cap} ?6", expectedExtra := s!" {sz}",
    syms := [("_eita_oog", "oog")] }


def pad (n : Nat) : List XItem := List.replicate n (XItem.I .ret)

def vecs : List Vec :=
  let memcostP : List XItem :=
    [.I (.movRR .rax .rdi), .I (.imulRR .rax .rdi), .I (.shiftRI .shr .rax 9),
     .I (.lea .rax { base := .rax, index := some .rdi, scale := 2 }),
     .I (.aluRR .add .rax .rdi), .I .ret]
  let sumloopP : List XItem :=
    [.I (.movRI .rax 0), .L "top", .I (.aluRR .add .rax .rdi), .I (.aluRI .sub .rdi 1),
     .Jcc .ne "top", .I .ret]
  let jumpP (n : Nat) : List XItem :=
    [.I (.aluRI .cmp .rdi 0), .Jcc .e "far", .I (.movRI .rax 1), .I .ret] ++ pad n ++
    [.L "far", .I (.movRI .rax 2), .I .ret]
  let maxP : List XItem :=
    [.I (.movRR .rax .rdi), .I (.aluRR .cmp .rax .rsi), .I (.cmovRR .b .rax .rsi), .I .ret]
  let sibP : List XItem :=
    [.I (.push .r12), .I (.push .r13), .I (.movRR .r12 .rdi), .I (.movRR .r13 .rsi),
     .I (.movRM .rax { base := .r12, index := some .r13, disp := -48 }),
     .I (.pop .r13), .I (.pop .r12), .I .ret]
  let memaluP : List XItem :=
    [.I (.movRR .rax .rsi), .I (.aluRM .or_ .rax { base := .rdi, disp := 8 }), .I .ret]
  let shl1P : List XItem := [.I (.movRR .rax .rdi), .I (.shiftRI .shl .rax 1), .I .ret]
  let lzcntP : List XItem := [.I (.lzcnt .rax .rdi), .I .ret]
  [ v "memcost_100" memcostP "100" "0" (memCost 100),
    v "memcost_1000" memcostP "1000" "0" (memCost 1000),
    v "memcost_65536" memcostP "65536" "0" (memCost 65536),
    v "sumloop_1" sumloopP "1" "0" (1),
    v "sumloop_100" sumloopP "100" "0" (5050),
    v "nearjump_taken" (jumpP 10) "0" "0" (2),
    v "nearjump_not" (jumpP 10) "5" "0" (1),
    v "farjump_taken" (jumpP 130) "0" "0" (2),
    v "farjump_not" (jumpP 130) "5" "0" (1),
    v "maxcmov_lt" maxP "3" "9" (9),
    v "maxcmov_gt" maxP "9" "3" (9),
    v "maxcmov_eq" maxP "7" "7" (7),
    -- rdi = &arr[8] (byte 64), rsi = 32: [r12 + r13 - 48] = byte 48 = arr[6]
    v "sibbase" sibP "@8" "32" (1006),
    -- [rdi + 8] with rdi = &arr[0] is arr[1] = 1001; 1001 | 2 = 1003
    v "memalu" memaluP "@0" "2" (1003),
    v "shl1" shl1P "21" "0" (42),
    v "lzcnt_1" lzcntP "1" "0" (63),
    v "lzcnt_0" lzcntP "0" "0" (64),
    memExpandVec "nogrowth" 64 1024 32,
    memExpandVec "from_zero" 0 1024 100,
    memExpandVec "grow_2_to_32_words" 64 1024 1000,
    memExpandVec "unaligned_end" 0 4096 1001,
    memExpandVec "big" 0 2000000 1000000,
    memExpandVec "oog_over_cap" 0 512 600,
    frameVec "roundtrip" [] 2 " 7 9 2 1020 1021 1022 1023",
    frameVec "mutate" [.I (.aluRI .add .r8 5), .I (.aluRI .sub .r15 3), .I (.aluRI .add .rbp 1)]
      2 " 8 6 2 1025 1021 1022 1023",
    frameVec "empty_stack" [.I (.aluRI .add .r15 1)] 0 " 7 10 0 1016 1017 1018 1019",
    v "dispatch_0" Evm.CL.X86Dispatch.demo "0" "0" 10,
    v "dispatch_1" Evm.CL.X86Dispatch.demo "1" "0" 20,
    v "dispatch_2" Evm.CL.X86Dispatch.demo "2" "0" 30,
    v "dispatch_3" Evm.CL.X86Dispatch.demo "3" "0" 40,
    mstoreVec "basic" 100 2 0 1024 0 (0x11, 0x22, 0x33, 0x44) 0 "?1 ?2 ?3 ?6 ?32 ?33 ?34 ?35"
      s!" {100 - 3 - (memCost 1 - memCost 0)} 0 32 32 {(0x44:Nat) <<< 56} {(0x33:Nat) <<< 56} {(0x22:Nat) <<< 56} {(0x11:Nat) <<< 56}",
    mstoreVec "offset64" 100 2 0 1024 0 (0xAB, 0, 0, 0) 64 "?1 ?2 ?3 ?6 ?40 ?41 ?42 ?43"
      s!" {100 - 3 - (memCost 3 - memCost 0)} 0 96 96 0 0 0 {(0xAB:Nat) <<< 56}",
    mstoreVec "underflow" 100 1 0 1024 0 (1, 0, 0, 0) 0 "?1 ?2"
      s!" {Evm.CL.X86Handler.underflowGas} 1",
    mstoreVec "oog_hi_offset" 100 2 0 1024 0 (1, 0, 0, 0) 0 "?1 ?2"
      s!" {Evm.CL.X86Handler.oogGas} 2",
    mstoreVec "oog_gas" 5 2 0 1024 0 (1, 0, 0, 0) 0 "?1 ?2"
      s!" {Evm.CL.X86Handler.oogGas} 2",
    -- memory holds 0x44,0x33,0x22,0x11 in the top bytes of successive u64s;
    -- read big-endian, the word is limbs (0x11, 0x22, 0x33, 0x44)
    mloadVec "basic" 100 1 0 1024 0 ((0x44:Nat) <<< 56, (0x33:Nat) <<< 56, (0x22:Nat) <<< 56, (0x11:Nat) <<< 56)
      0 0 "?1 ?2 ?3 ?6 ?16 ?17 ?18 ?19"
      s!" {100 - 3 - (memCost 1 - memCost 0)} 1 32 32 17 34 51 68",
    -- memory already 64 bytes: no expansion, no growth cost
    mloadVec "no_growth" 100 1 64 1024 64 (1, 2, 3, 4) 0 0 "?1 ?2 ?3 ?6 ?19"
      s!" {100 - 3} 1 64 64 {(1:Nat) <<< 56}",
    mloadVec "oog_hi_offset" 100 1 0 1024 0 (0, 0, 0, 0) 0 1 "?1 ?2"
      s!" {Evm.CL.X86Handler.oogGas} 1",
    mloadVec "underflow" 100 0 0 1024 0 (0, 0, 0, 0) 0 0 "?1 ?2"
      s!" {Evm.CL.X86Handler.underflowGas} 0",
    -- ADD: a carry rippling across every limb boundary
    binVec "add_ripple" Evm.CL.X86Handler.addX86 (M, M, M, 0) (1, 0, 0, 0) (0, 0, 0, 1),
    binVec "add_plain"  Evm.CL.X86Handler.addX86 (5, 6, 7, 8) (10, 20, 30, 40) (15, 26, 37, 48),
    -- SUB: TOS − NOS, a borrow rippling down
    binVec "sub_ripple" Evm.CL.X86Handler.subX86 (0, 0, 0, 1) (1, 0, 0, 0) (M, M, M, 0),
    binVec "sub_plain"  Evm.CL.X86Handler.subX86 (10, 20, 30, 40) (5, 6, 7, 8) (5, 14, 23, 32),
    binVec "and" Evm.CL.X86Handler.andX86 (0xFF, 0xF0F0, 1, 0) (0x0F, 0xFFFF, 1, 1) (0x0F, 0xF0F0, 1, 0),
    binVec "or"  Evm.CL.X86Handler.orX86  (0xF0, 1, 0, 0) (0x0F, 2, 0, 4) (0xFF, 3, 0, 4),
    binVec "xor" Evm.CL.X86Handler.xorX86 (0xFF, 1, 2, 3) (0x0F, 1, 2, 3) (0xF0, 0, 0, 0),
    -- NOT: depth 1, in place
    { name := "unop_not", prog := Evm.CL.X86Handler.notX86, a0 := "@0", a1 := "0", expected := 1,
      extra := "1=100 2=1 4=@16 16=0 17=1 18=2 19=3 ?1 ?2 ?16 ?17 ?18 ?19",
      expectedExtra := s!" 97 1 {M} {M - 1} {M - 2} {M - 3}", syms := Evm.CL.X86Handler.faultSyms },
    -- EQ: the Z-flag counterexample — values differing only in limb 0 are NOT equal
    binVec "eq_equal"     Evm.CL.X86Handler.eqX86 (1, 2, 3, 4) (1, 2, 3, 4) (1, 0, 0, 0),
    binVec "eq_limb0"     Evm.CL.X86Handler.eqX86 (1, 0, 0, 0) (0, 0, 0, 0) (0, 0, 0, 0),
    binVec "eq_limb3"     Evm.CL.X86Handler.eqX86 (0, 0, 0, 1) (0, 0, 0, 2) (0, 0, 0, 0),
    -- LT is TOS < NOS (unsigned); GT swaps the operands
    binVec "lt_true"      Evm.CL.X86Handler.ltX86 (1, 0, 0, 0) (2, 0, 0, 0) (1, 0, 0, 0),
    binVec "lt_high_limb" Evm.CL.X86Handler.ltX86 (0, 0, 0, 1) (M, M, M, 0) (0, 0, 0, 0),
    binVec "lt_equal"     Evm.CL.X86Handler.ltX86 (5, 5, 5, 5) (5, 5, 5, 5) (0, 0, 0, 0),
    binVec "gt_true"      Evm.CL.X86Handler.gtX86 (2, 0, 0, 0) (1, 0, 0, 0) (1, 0, 0, 0),
    -- SLT: −1 < 0 signed, where unsigned LT says the opposite
    binVec "slt_neg"      Evm.CL.X86Handler.sltX86 (M, M, M, M) (0, 0, 0, 0) (1, 0, 0, 0),
    binVec "lt_neg_unsigned" Evm.CL.X86Handler.ltX86 (M, M, M, M) (0, 0, 0, 0) (0, 0, 0, 0),
    binVec "sgt_pos_vs_neg" Evm.CL.X86Handler.sgtX86 (1, 0, 0, 0) (M, M, M, M) (1, 0, 0, 0),
    { name := "unop_iszero_zero", prog := Evm.CL.X86Handler.iszeroX86, a0 := "@0", a1 := "0", expected := 1,
      extra := "1=100 2=1 4=@16 16=0 17=0 18=0 19=0 ?1 ?2 ?16 ?17 ?18 ?19",
      expectedExtra := " 97 1 1 0 0 0", syms := Evm.CL.X86Handler.faultSyms },
    -- nonzero only in limb 2: the fold over x7-x9 must see it
    { name := "unop_iszero_limb2", prog := Evm.CL.X86Handler.iszeroX86, a0 := "@0", a1 := "0", expected := 1,
      extra := "1=100 2=1 4=@16 16=0 17=0 18=7 19=0 ?1 ?2 ?16 ?17 ?18 ?19",
      expectedExtra := " 97 1 0 0 0 0", syms := Evm.CL.X86Handler.faultSyms },
    -- POP: TOS becomes the old NOS (word 0); gas 2
    stackVec "pop" Evm.CL.X86Handler.popX86 100 2 "16=11 17=12 18=13 19=14 20=21 21=22 22=23 23=24"
      "?1 ?2 ?16 ?17 ?18 ?19" " 98 1 11 12 13 14" 1,
    -- PUSH0: a zero word on an empty stack; pc unchanged; gas 2
    stackVec "push0" Evm.CL.X86Handler.push0X86 100 0 "16=5 17=5 18=5 19=5"
      "?0 ?1 ?2 ?16 ?17 ?18 ?19" " 0 98 1 0 0 0 0" 1,
    -- PUSH1 0xAB at pc 0 (code element 40 = 0xAB, code_size 1)
    stackVec "push1" Evm.CL.X86Handler.push1X86 100 0 "9=1 40=171"
      "?0 ?1 ?2 ?16 ?17 ?18 ?19" " 1 97 1 171 0 0 0" 1,
    -- PUSH2 0x12 0x34: bytes 0x12,0x34 → element 40 = 0x3412 → value 0x1234
    stackVec "push2" Evm.CL.X86Handler.push2X86 100 0 "9=2 40=13330"
      "?0 ?1 ?2 ?16 ?17 ?18 ?19" " 2 97 1 4660 0 0 0" 1,
    -- PUSH2 past the end of code: only one byte exists → 0xAB00
    stackVec "push2_truncated" Evm.CL.X86Handler.push2X86 100 0 "9=1 40=171"
      "?0 ?1 ?2 ?16 ?17 ?18 ?19" " 2 97 1 43776 0 0 0" 1,
    -- PUSH8 bytes 01..08: element 40 = 0x0807060504030201 → value 0x0102030405060708
    stackVec "push8" Evm.CL.X86Handler.push8X86 100 0 "9=8 40=578437695752307201"
      "?0 ?1 ?2 ?16 ?17 ?18 ?19" " 8 97 1 72623859790382856 0 0 0" 1,
    -- PUSH9 bytes 01..09: crosses into limb 1 — limb1 = 0x01, limb0 = 0x0203040506070809
    stackVec "push9" Evm.CL.X86Handler.push9X86 100 0 "9=9 40=578437695752307201 41=9"
      "?0 ?1 ?2 ?16 ?17 ?18 ?19" " 9 97 1 144964032628459529 1 0 0" 1,
    -- PUSH32 of all 0xFF: every limb all-ones
    stackVec "push32" Evm.CL.X86Handler.push32X86 100 0 s!"9=32 40={M} 41={M} 42={M} 43={M}"
      "?0 ?1 ?2 ?16 ?17 ?18 ?19" s!" 32 97 1 {M} {M} {M} {M}" 1,
    -- PUSH32 at the end of the code (code_size 1): the wide loads read the zero
    -- padding (elements 41..43 = 0, the code-pad contract) → 0xAB << 248
    stackVec "push32_at_end" Evm.CL.X86Handler.push32X86 100 0 "9=1 40=171 41=0 42=0 43=0"
      "?0 ?1 ?2 ?16 ?17 ?18 ?19" " 32 97 1 0 0 0 12321848580485677056" 1,
    -- PUSH9 straddling the end (5 of 9 bytes; the partial limb then a whole one)
    stackVec "push9_straddle" Evm.CL.X86Handler.push9X86 100 0 "9=5 40=21542142465 41=0"
      "?0 ?1 ?2 ?16 ?17 ?18 ?19" " 9 97 1 144964032527335424 1 0 0" 1,
    -- PUSH1 on top of an existing word: the old TOS stays in word 0
    stackVec "push1_over" Evm.CL.X86Handler.push1X86 100 1 "9=1 40=7 16=99 17=98 18=97 19=96"
      "?0 ?2 ?16 ?17 ?18 ?19 ?20 ?21 ?22 ?23" " 1 2 99 98 97 96 7 0 0 0" 2,
    -- DUP1: word 1 = copy of word 0; DUP2: word 2 = copy of word 0
    stackVec "dup1" Evm.CL.X86Handler.dup1X86 100 1 "16=1 17=2 18=3 19=4"
      "?2 ?16 ?17 ?18 ?19 ?20 ?21 ?22 ?23" " 2 1 2 3 4 1 2 3 4" 2,
    stackVec "dup2" Evm.CL.X86Handler.dup2X86 100 2 "16=1 17=2 18=3 19=4 20=5 21=6 22=7 23=8"
      "?2 ?24 ?25 ?26 ?27" " 3 1 2 3 4" 3,
    -- SWAP1: words 0 and 1 exchanged; SWAP2: words 0 and 2
    stackVec "swap1" Evm.CL.X86Handler.swap1X86 100 2 "16=1 17=2 18=3 19=4 20=5 21=6 22=7 23=8"
      "?2 ?16 ?17 ?18 ?19 ?20 ?21 ?22 ?23" " 2 5 6 7 8 1 2 3 4" 2,
    stackVec "swap2" Evm.CL.X86Handler.swap2X86 100 3 "16=1 17=2 18=3 19=4 20=5 21=6 22=7 23=8 24=9 25=10 26=11 27=12"
      "?2 ?16 ?17 ?18 ?19 ?24 ?25 ?26 ?27" " 3 9 10 11 12 1 2 3 4" 3,
    -- the compute helpers, through the SysV call sequence into c/eita_compute.c
    helperVec "mul" Evm.CL.X86Handler.mulX86 5 (6, 0, 0, 0) (7, 0, 0, 0) (42, 0, 0, 0),
    helperVec "mul_wide" Evm.CL.X86Handler.mulX86 5 (M, 0, 0, 0) (M, 0, 0, 0) (1, M - 1, 0, 0),
    helperVec "div" Evm.CL.X86Handler.divX86 5 (100, 0, 0, 0) (7, 0, 0, 0) (14, 0, 0, 0),
    helperVec "div_by_zero" Evm.CL.X86Handler.divX86 5 (100, 0, 0, 0) (0, 0, 0, 0) (0, 0, 0, 0),
    helperVec "sdiv_neg" Evm.CL.X86Handler.sdivX86 5 (M - 7, M, M, M) (2, 0, 0, 0) (M - 3, M, M, M),
    helperVec "mod" Evm.CL.X86Handler.modX86 5 (100, 0, 0, 0) (7, 0, 0, 0) (2, 0, 0, 0),
    helperVec "smod_neg" Evm.CL.X86Handler.smodX86 5 (M - 7, M, M, M) (3, 0, 0, 0) (M - 1, M, M, M),
    -- SHL/SHR/SAR: TOS is the shift, NOS the value
    helperVec "shl_64" Evm.CL.X86Handler.shlX86 3 (64, 0, 0, 0) (1, 0, 0, 0) (0, 1, 0, 0),
    helperVec "shr_64" Evm.CL.X86Handler.shrX86 3 (64, 0, 0, 0) (0, 1, 0, 0) (1, 0, 0, 0),
    helperVec "sar_neg" Evm.CL.X86Handler.sarX86 3 (1, 0, 0, 0) (M - 7, M, M, M) (M - 3, M, M, M),
    -- BYTE 31 is the least significant byte
    helperVec "byte_31" Evm.CL.X86Handler.byteX86 3 (31, 0, 0, 0) (0xAB, 0, 0, 0) (0xAB, 0, 0, 0),
    -- SIGNEXTEND 0 of 0x80: byte 0 sign-extended to all ones
    helperVec "signextend" Evm.CL.X86Handler.sextX86 5 (0, 0, 0, 0) (0x80, 0, 0, 0) (M - 127, M, M, M),
    helper3Vec "addmod" Evm.CL.X86Handler.addmodX86 8 5 7 10 2,
    helper3Vec "mulmod" Evm.CL.X86Handler.mulmodX86 8 5 7 10 5,
    -- PC pushes pc−1 (pc is pre-incremented at fetch); depth 0 → 1
    stackVec "pc" Evm.CL.X86Handler.pcX86 100 0 "0=7" "?0 ?1 ?2 ?16 ?17 ?18 ?19" " 7 98 1 6 0 0 0" 1,
    -- GAS pushes the gas AFTER its own charge; no exitGas afterwards
    stackVec "gas" Evm.CL.X86Handler.gasX86 100 0 "" "?1 ?2 ?16 ?17 ?18 ?19" " 98 1 98 0 0 0" 1,
    -- a u64 field push (offset 8 = the gas FIELD in memory, stale until sync)
    stackVec "env_u64" Evm.CL.X86Handler.envU64X86 100 0 "" "?1 ?2 ?16 ?17 ?18 ?19" " 98 1 100 0 0 0" 1,
    -- a u256 field push (offset 320 = elements 40..43)
    stackVec "env_u256" Evm.CL.X86Handler.envU256X86 100 0 "40=11 41=22 42=33 43=44"
      "?1 ?2 ?16 ?17 ?18 ?19" " 98 1 11 22 33 44" 1,
    -- SLOAD through a host-callback slot: [state+496] → table at element 59,
    -- table[0] = the stub, which returns 42 gas and writes 0xC0FFEE + key
    { name := "cb_sload", prog := Evm.CL.X86Handler.sloadX86, a0 := "@0", a1 := "0", expected := 1,
      extra := "1=100 2=1 4=@16 16=5 17=0 18=0 19=0 62=@59 59=!eita_test_cb_sload 63=0 ?1 ?2 ?16 ?17 ?18 ?19",
      expectedExtra := s!" 58 1 {0xC0FFEE + 5} 0 0 0", syms := Evm.CL.X86Handler.faultSyms },
    -- ---- the 2 KB layout: state = elements 0..63, stack from 64, memory from 96, code from 128 ----
    -- STOP: pc−1, halted byte (offset 128 = element 16, low byte) set, depth unchanged
    bigVec "stop" Evm.CL.X86Handler.stopX86 0 "0=7 16=0" "?0 ?16" " 6 1" (some 0),
    bigVec "jumpdest" Evm.CL.X86Handler.jumpdestX86 0 "" "?1" " 99" (some 0),
    bigVec "invalid" Evm.CL.X86Handler.invalidX86 0 "" "?1" s!" {Evm.CL.X86Handler.oogGas}" (some 0),
    -- RETURN: TOS = offset 0 (word 1), NOS = length 32 (word 0): memexp 3 gas, output len 32,
    -- mp 32, halted, two words popped
    bigVec "return" Evm.CL.X86Handler.returnX86 2 "0=7 3=0 6=0 7=1024 16=0 64=32 65=0 66=0 67=0 68=0 69=0 70=0 71=0" "?0 ?1 ?3 ?15 ?16" " 6 97 32 32 1" (some 0),
    -- REVERT: as RETURN, plus the reverted byte (offset 129 = element 16, byte 1)
    bigVec "revert" Evm.CL.X86Handler.revertX86 2 "0=7 3=0 6=0 7=1024 16=0 64=32 65=0 66=0 67=0 68=0 69=0 70=0 71=0" "?0 ?1 ?3 ?15 ?16" s!" 6 97 32 32 {1 + (1 <<< 8)}" (some 0),
    -- JUMP to 4, where the code has a JUMPDEST (0x5b at byte 4 → element 128 = 0x5b << 32)
    -- and the host's valid-JUMPDEST map (state #136 = element 17 → element 144) marks it
    bigVec "jump_ok" Evm.CL.X86Handler.jumpX86 1 s!"0=7 9=8 128={(0x5b : Nat) <<< 32} 17=@144 144={(1 : Nat) <<< 32} 64=4 65=0 66=0 67=0" "?0 ?1 ?2" " 4 92 0" (some 0),
    bigVec "jump_invalid" Evm.CL.X86Handler.jumpX86 1 "0=7 9=8 128=0 17=@144 144=0 64=4 65=0 66=0 67=0" "?0 ?1 ?2" s!" 7 {Evm.CL.X86Handler.invalidJumpGas} 1" (some 1),
    -- the byte at 4 IS 0x5b but the map does not mark it: PUSH data (5,800,596 tx 117) — invalid
    bigVec "jump_into_push_data" Evm.CL.X86Handler.jumpX86 1 s!"0=7 9=8 128={(0x5b : Nat) <<< 32} 17=@144 144=0 64=4 65=0 66=0 67=0" "?0 ?1 ?2" s!" 7 {Evm.CL.X86Handler.invalidJumpGas} 1" (some 1),
    bigVec "jump_high_limb" Evm.CL.X86Handler.jumpX86 1 s!"0=7 9=8 128={(0x5b : Nat) <<< 32} 17=@144 144={(1 : Nat) <<< 32} 64=4 65=1 66=0 67=0" "?0 ?1 ?2" s!" 7 {Evm.CL.X86Handler.invalidJumpGas} 1" (some 1),
    -- JUMPI: TOS = dest (word 1), NOS = cond (word 0)
    bigVec "jumpi_taken" Evm.CL.X86Handler.jumpiX86 2 s!"0=7 9=8 128={(0x5b : Nat) <<< 32} 17=@144 144={(1 : Nat) <<< 32} 64=1 65=0 66=0 67=0 68=4 69=0 70=0 71=0" "?0 ?1 ?2" " 4 90 0" (some 0),
    bigVec "jumpi_not_taken" Evm.CL.X86Handler.jumpiX86 2 s!"0=7 9=8 128={(0x5b : Nat) <<< 32} 17=@144 144={(1 : Nat) <<< 32} 64=0 65=0 66=0 67=0 68=4 69=0 70=0 71=0" "?0 ?1 ?2" " 7 90 0" (some 0),
    -- a condition that is nonzero only in limb 3 still takes the branch
    bigVec "jumpi_hi_cond" Evm.CL.X86Handler.jumpiX86 2 s!"0=7 9=8 128={(0x5b : Nat) <<< 32} 17=@144 144={(1 : Nat) <<< 32} 64=0 65=0 66=0 67=9 68=4 69=0 70=0 71=0" "?0 ?1 ?2" " 4 90 0" (some 0),
    -- MSTORE8: TOS = offset 3, NOS = value 0x1234 → the byte 0x34 lands at memory[3]
    bigVec "mstore8" Evm.CL.X86Handler.mstore8X86 2 "3=0 5=@96 6=0 7=1024 64=4660 65=0 66=0 67=0 68=3 69=0 70=0 71=0 96=0" "?1 ?2 ?3 ?6 ?96" s!" 94 0 4 32 {(0x34 : Nat) <<< 24}" (some 0),
    -- CLZ: nonzero only in limb 2 → 64 + 63; zero → 256; 1 → 255
    bigVec "clz_limb2" Evm.CL.X86Handler.clzX86 1 "64=0 65=0 66=1 67=0" "?1 ?2 ?64 ?65 ?66 ?67" " 95 1 127 0 0 0" (some 1),
    bigVec "clz_zero" Evm.CL.X86Handler.clzX86 1 "64=0 65=0 66=0 67=0" "?1 ?2 ?64" " 95 1 256" (some 1),
    bigVec "clz_one" Evm.CL.X86Handler.clzX86 1 "64=1 65=0 66=0 67=0" "?1 ?2 ?64" " 95 1 255" (some 1),
    -- MSIZE pushes the memory_size field (offset 48 = element 6)
    bigVec "msize" Evm.CL.X86Handler.msizeX86 0 "6=96" "?1 ?2 ?64 ?65 ?66 ?67" " 98 1 96 0 0 0" (some 1),
    -- TLOAD through a direct callback: charges 100, pushes 0xBEEF + key
    bigVec "tload" Evm.CL.X86Handler.tloadX86 1 "1=150 63=@40 64=5 65=0 66=0 67=0" "?1 ?2 ?64 ?65 ?66 ?67"
      s!" 50 1 {0xBEEF + 5} 0 0 0" (some 1),
    -- ---- EIP-4844: the 600-byte state, two hashes in the table (hash 0 = 5,6,7,8; hash 1 = 17,34,51,68) ----
    -- BLOBHASH 1 of 2: the second entry replaces the index in place; gas 3
    blobVec "hash_in_range" Evm.CL.X86Handler.blobhashX86 1
      "70=2 96=5 97=6 98=7 99=8 100=17 101=34 102=51 103=68 80=1 81=0 82=0 83=0"
      "?1 ?2 ?80 ?81 ?82 ?83" " 97 1 17 34 51 68" 1,
    -- BLOBHASH 2 of 2: past the count → 0, whatever the table holds there
    blobVec "hash_out_of_range" Evm.CL.X86Handler.blobhashX86 1
      "70=2 96=5 97=6 98=7 99=8 100=17 101=34 102=51 103=68 104=9 105=9 106=9 107=9 80=2 81=0 82=0 83=0"
      "?1 ?2 ?80 ?81 ?82 ?83" " 97 1 0 0 0 0" 1,
    -- index 2^64 + 1: low limb 1 is in range, the high limb makes it out of range → 0
    blobVec "hash_high_limb" Evm.CL.X86Handler.blobhashX86 1
      "70=2 96=5 97=6 98=7 99=8 100=17 101=34 102=51 103=68 80=1 81=1 82=0 83=0"
      "?1 ?2 ?80 ?81 ?82 ?83" " 97 1 0 0 0 0" 1,
    -- a non-blob tx: count 0, index 0 → 0
    blobVec "hash_empty" Evm.CL.X86Handler.blobhashX86 1
      "70=0 96=5 97=6 98=7 99=8 80=0 81=0 82=0 83=0"
      "?1 ?2 ?80 ?81 ?82 ?83" " 97 1 0 0 0 0" 1,
    blobVec "hash_underflow" Evm.CL.X86Handler.blobhashX86 0 "70=2" "?1 ?2"
      s!" {Evm.CL.X86Handler.underflowGas} 0" 0,
    -- BLOBBASEFEE pushes the four limbs at offset 568 (elements 71..74); gas 2
    blobVec "basefee" Evm.CL.X86Handler.blobbasefeeX86 0 "71=11 72=22 73=33 74=44"
      "?1 ?2 ?80 ?81 ?82 ?83" " 98 1 11 22 33 44" 1 ]

/-- The far jump really is the long form and the near one the short form —
    checked here so a run failure is not confused with a layout question. -/
theorem far_is_relaxed :
    (assemble ([XItem.I (.aluRI .cmp .rdi 0), .Jcc .e "far", .I (.movRI .rax 1), .I .ret] ++ pad 130 ++
      [.L "far", .I (.movRI .rax 2), .I .ret])).1.size
    = (assemble ([XItem.I (.aluRI .cmp .rdi 0), .Jcc .e "far", .I (.movRI .rax 1), .I .ret] ++ pad 10 ++
      [.L "far", .I (.movRI .rax 2), .I .ret])).1.size + 120 + 4 := by native_decide

def main : IO Unit := do
  for v in vecs do
    IO.println s!"{v.name}\t{hexWith v.syms v.prog}\t{v.a0} {v.a1} {v.extra}\t{v.expected}{v.expectedExtra}"
