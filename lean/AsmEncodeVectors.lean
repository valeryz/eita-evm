/-
  AsmEncodeVectors — differential test battery for `Evm.CL.AsmEncode`.
  Prints `<encode-hex>\t<asm-text>` per line. A script assembles the asm column
  and checks the resulting machine bytes equal the hex column. Run:
    lake exe asmEncodeVectors | scripts/verify-asm-encode.sh
-/
import Evm.CL.AsmEncode
import Evm.CL.ARM64.JIT
import Evm.CL.AsmItems
open Evm.CL.AsmEncode Evm.CL.AsmEncode.Insn

private def allConds : List Cond :=
  [.eq, .ne, .cs, .cc, .mi, .pl, .vs, .vc, .hi, .ls, .ge, .lt, .gt, .le]

/-- The battery: exercise every constructor + edge operands (reg 0/13/30/31,
    imm extremes, shifts, signed offsets). -/
def vectors : List Insn :=
  [strbReg 10 14 6, strbReg 14 20 21] ++
  -- moves
  [ movz 0 0 0, movz 6 0xffff 0, movz 13 0x1234 1, movz 30 0xabcd 3,
    movk 0 0 0, movk 9 0xbeef 2, movReg 6 10, movReg 0 31, movReg 23 24,
    -- add/sub immediate
    addImm false false 6 6 0 false, addImm false false 23 31 4095 false,
    addImm true false 22 22 1 false, addImm false false 14 20 1 true,
    addImm false true 22 22 5 false, addImm true true 22 22 100 false,
    -- arith/logical register
    reg .add 10 6 10 0, reg .sub 13 9 13 0, reg .adds 6 6 10 0, reg .subs 7 7 11 0,
    reg .adc 11 7 11 0, reg .sbc 11 7 11 0, reg .adcs 8 8 12 0, reg .sbcs 9 9 13 0,
    reg .and 10 10 6 0, reg .orr 14 14 15 0, reg .eor 6 6 10 0,
    reg .add 21 21 21 1, reg .orr 14 11 0 0,
    mvn 6 6, mvn 9 9,
    -- shifts
    lslImm 6 6 8, lslImm 14 14 5, lsrImm 17 17 5, lsrImm 14 14 9,
    lslReg 6 6 16, lsrReg 0 0 8,
    rev 6 6, rev 9 9,
    -- mul / madd
    madd 16 14 15 31, madd 0 1 2 3,
    -- compares
    cmpImm 23 1024, cmpImm 6 0, cmpReg 0 14, cmpReg 23 1,
    -- conditional set/select
    cset 6 .eq, cset 6 .ne, cset 6 .cc, cset 6 .hi, cset 6 .lt, cset 6 .ge,
    csel 6 14 31 .eq, csinv 15 15 31 .eq,
    -- loads/stores (unsigned imm)
    ldr 6 20 0, ldr 22 20 8, str 21 20 16, str 22 20 104,
    ldrb 14 26 0, strb 14 20 0,
    ldrReg 14 25 1 false, ldrReg 14 25 1 true, ldrbReg 4 26 21,
    -- pairs (signed offsets)
    ldp 6 7 14 0, ldp 8 9 14 16, stp 6 7 14 0, stp 29 30 31 16,
    stp 29 30 31 (-16), ldp 27 28 31 80,
    -- pre/post-index pairs + LSR-shifted add
    stpPre 29 30 31 (-16), stpPre 19 20 31 16, ldpPost 29 30 31 16, ldpPost 19 20 31 96,
    addLsrReg 16 14 16 9, addLsrReg 14 15 14 9, addLsrReg 0 1 2 0,
    -- extended-register add/sub (SP source/dest)
    addExtReg false 14 31 14, addExtReg true 31 31 15, addExtReg false 31 31 15,
    addExtReg false 9 31 9,
    -- branches
    br 27, blr 14, ret,
    -- PC-relative branches (target = pc + off; off must be /4)
    bImm 0, bImm 8, bImm (-8), bImm 4096, blImm (-4),
    bcondImm .lt 8, bcondImm .cs (-12), bcondImm .ls 16, bcondImm .cc (-256),
    cbzImm 14 8, cbnzImm 6 (-8), cbzImm 0 1024,
    -- adr (local PC-relative, byte offset, ±1MB)
    adrImm 6 8, adrImm 27 (-16), adrImm 14 4096, adrImm 9 (-1048576), adrImm 0 1048572 ]

/-- A labeled program exercising the assembler: forward + backward local
    branches and an external relocation. -/
def prog : List Item :=
  [ .L "start",
    .I (movz 0 1 0),
    .Bc .eq "end",          -- forward
    .I (movz 1 2 0),
    .Cbnz 0 "start",        -- backward
    .I (addImm false false 0 0 4 false),
    .B "_eita_oog",         -- EXTERNAL (relocation)
    .L "end",
    .I ret ]

def progArgsAsm : List String :=
  -- the clang-equivalent .S body (external target stays a symbol — we only
  -- compare the LOCAL-branch words, which clang resolves identically).
  ["start:", "movz x0, #1", "b.eq end", "movz x1, #2", "cbnz x0, start",
   "add x0, x0, #4", "b _eita_oog", "end:", "ret"]

open Evm.CL.AsmCore Evm.CL.ARM64.JIT in
/-- The leaf cores of the chunk algebra, lowered to Items (instructions only —
    no labels/branches), so the differential gate assembles each and checks it
    byte-exact. -/
def coreItems : List Item :=
  Evm.CL.AsmItems.progItems (
    movImmInstrs .x6 0 ++ movImmInstrs .x7 0x1234 ++ movImmInstrs .x9 0xdeadbeefcafe ++
    spAddrA .x14 0 ++ spAddrA .x14 3 ++ spAddrA .x14 200 ++
    spAddrA .x14 128 ++ spAddrA .x0 4096 ++   -- LARGE offsets: exercise the sp-register path
    loadSlotA .x6 130 ++ storeSlotA 200 ++    -- slot*32 > 4095 → movImm + add sp
    loadSlotA .x6 2 ++ loadSlotA .x10 5 ++ storeSlotA 1 ++ zeroHiA ++
    addCoreA ++ subCoreA ++ bitCoreA .and3 ++ bitCoreA .orr3 ++ bitCoreA .eor3 ++
    notCoreA ++ isZeroCoreA ++ eqCoreA ++
    cmpCoreA false .lo ++ cmpCoreA true .lo ++ cmpCoreA false .lt ++ cmpCoreA true .lt)

def main (args : List String) : IO Unit := do
  if args.head? == some "cores" then
    for it in coreItems do
      match it with
      | .I i => IO.println s!"{i.encode.toNat}\t{i.asm}"
      | _ => pure ()
  else if args.head? == some "prog" then
    let (bytes, relocs) := assemble prog
    -- print the resolved 32-bit words (little-endian)
    for k in List.range (bytes.size / 4) do
      let b0 := (bytes.get! (4*k)).toNat
      let b1 := (bytes.get! (4*k+1)).toNat
      let b2 := (bytes.get! (4*k+2)).toNat
      let b3 := (bytes.get! (4*k+3)).toNat
      IO.println s!"{b0 + b1*256 + b2*65536 + b3*16777216}"
    IO.eprintln s!"relocs: {relocs.map (fun r => (r.sym, r.byteOff, repr r.kind))}"
  else
    for i in vectors do
      IO.println s!"{i.encode.toNat}\t{i.asm}"
