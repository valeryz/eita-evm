/-
  Evm.CL.Lowering — one emitter, two targets.

  Stage 2 of #238. The gadgets are `List AInstr`; today `AInstr.emitARM64`
  turns them into ARM64 text. This introduces the target as a PARAMETER — a
  `Lowering` record — instantiates it for ARM64 (proved to reproduce the
  existing emitter exactly, so `handlers.S` cannot move) and for x86-64, and
  then checks the thing that actually matters: that the x86-64 instantiation
  covers every instruction the gadgets contain.

  Coverage is checked, not assumed. Anything the x86 lowering does not handle
  emits a `«unlowered»` marker, and `every_gadget_instruction_lowers` says no
  marker survives in the gadget set — the same discipline as the precompile
  coverage gate, where an unimplemented case is a loud error rather than a
  silent fallthrough.

  ## The NOS problem

  x86-64 does not cache NOS (`Evm.CL.Target`: no registers left for it), but the
  gadgets read x10-x13 directly. That turns out to cost NOTHING, for two
  measured reasons:

   * no gadget instruction ever WRITES a NOS register — they are read-only
     operands throughout (`no_gadget_writes_nos`);
   * x86-64 arithmetic takes one MEMORY operand, so a NOS read is just an
     addressing mode: `or rcx, [r12 + r13 - 56]`. No load, no temporary, no
     pressure.

  …with one correction the ASSEMBLER had to make, not me: the scale must be 1,
  because x86's SIB byte offers 1/2/4/8 only. So r13 holds sp as a byte offset
  on x86-64 rather than a word index — see `nosMem`. My hand spot-checks read
  right past a scale of 32; `scripts/verify-x86-emit.sh` assembles every gadget
  now, which is the gate that catches this class.

  So the register budget is untouched by dropping the NOS cache — which is a
  better outcome than the "load into a free scratch" plan I started with, and
  the reason to check the target's addressing modes before assuming a RISC
  shape.
-/

import Evm.CL.X86Lower

namespace Evm.CL.Lowering

open Evm.CL.AsmCore Evm.CL.Pressure Evm.CL.X86Lower

/-- A code-generation target: how it names registers and how it emits one
    instruction. The instruction set is shared; only this record changes. -/
structure Target where
  name : String
  reg  : Reg → String
  emit : AInstr → String

/-- Emit a whole gadget for a target. -/
def emitProg (t : Target) (p : List AInstr) : String :=
  String.join (p.map t.emit)

/-! ## ARM64 — the existing emitter, as an instance -/

def arm64 : Target where
  name := "arm64"
  reg  := Reg.s
  emit := AInstr.emitARM64

/-- **The ARM64 instantiation IS the current emitter**, so routing the gadgets
    through `Lowering` cannot change a byte of `handlers.S`. -/
theorem arm64_emit_is_unchanged (i : AInstr) : arm64.emit i = AInstr.emitARM64 i := rfl

theorem arm64_prog_is_unchanged (p : List AInstr) :
    emitProg arm64 p = String.join (p.map AInstr.emitARM64) := rfl

/-! ## x86-64 -/

/-- Named registers, from `Evm.CL.Target`'s role assignment: TOS in r8-r11, and
    the singletons in rbx/r15/r13/r12/r14. Temporaries come from
    `Pressure.x86Temp`, the forced colouring. NOS has no register — `none`
    means "must be loaded from the stack", handled per instruction below. -/
def x86Reg? : Reg → Option String
  | .x6 => some "r8"  | .x7 => some "r9"  | .x8 => some "r10" | .x9 => some "r11"
  | .x20 => some "rbx" | .x22 => some "r15" | .x23 => some "r13" | .x24 => some "r12"
  | .x10 | .x11 | .x12 | .x13 => none        -- NOS: not cached on x86-64
  -- x1-x3 share homes with x15/x17/x4,x16: sound only while no two are live
  -- together, which `X86Alias.no_alias_hazards` checks over every emitted body
  | .x1 => some "rdx" | .x2 => some "rsi" | .x3 => some "rdi"
  | .x21 => some "rbp" | .x26 => some "r14"
  | .x27 => none                             -- the continuation has no x86 home
  | .x5 => none                              -- an ARM argument register; x86 programs are explicit
  | r => if isTemp r then some (x86Temp r) else none

/-- Which NOS limb a register is, if it is one. -/
def nosLimb : Reg → Option Nat
  | .x10 => some 0 | .x11 => some 1 | .x12 => some 2 | .x13 => some 3
  | _ => none

def x86Reg (r : Reg) : String := (x86Reg? r).getD "«unlowered-reg»"

/-- The byte name of a register's home (`setcc` writes a byte). -/
def x86Reg8 (r : Reg) : String :=
  match x86Reg? r with
  | some "rax" => "al" | some "rcx" => "cl" | some "rdx" => "dl" | some "rbx" => "bl"
  | some "rsi" => "sil" | some "rdi" => "dil"
  | some n => n ++ "b"            -- r8 … r15 → r8b … r15b
  | none => "«unlowered-reg»"

/-- Pad a mnemonic to the column the rest of the emitter uses, so the output
    reads like the hand-written asm beside it. -/
def pad (m : String) : String :=
  m ++ ("".pushn ' ' (if m.length < 5 then 5 - m.length else 1))

/-- A NOS limb AS AN ADDRESSING MODE: `stack[sp-2]`'s limb, off the stack base
    (r12) and the cached sp (r13). x86 arithmetic accepts this directly as a
    source operand.

    **The scale must be 1.** x86's SIB byte allows scale 1, 2, 4 or 8 only, so
    `[r12 + r13*32 - 48]` — the obvious transcription, with r13 a word index —
    is not an encodable address, and the system assembler rejects it. The
    consequence is a representation difference between the targets rather than
    a lost addressing mode: on x86-64, **r13 holds sp as a BYTE offset**
    (32·sp), so the same access is `[r12 + r13 - 48]` with scale 1. Stack
    pushes and pops then adjust r13 by ±32 instead of ±1, which costs nothing —
    an immediate either way.

    I had this wrong in the first version of this file, with a scale of 32, and
    found it only when the assembler saw it. See `scripts/verify-x86-emit.sh`,
    which now assembles every gadget for exactly this reason. -/
def nosMem (limb : Nat) : String :=
  s!"[r12 + r13 - {64 - 8 * limb}]"

/-- A source operand: a register, or a NOS limb's memory address. -/
def operand (r : Reg) : String :=
  match nosLimb r with
  | some l => nosMem l
  | none => x86Reg r

def setcondX86 : SetCond → String
  | .eq => "e" | .lo => "b" | .lt => "l"

def bcondX86 : BCond → String
  | .lo => "b" | .hs => "ae" | .hi => "a" | .ls => "be" | .eq => "e" | .ne => "ne" | .lt => "l"

/-- The negated condition, for `csel d, a, d, c` = `cmov¬c d, a`'s twin. -/
def nbcondX86 : BCond → String
  | .lo => "ae" | .hs => "b" | .hi => "be" | .ls => "a" | .eq => "ne" | .ne => "e" | .lt => "ge"

/-- The temporary a NOS-source store goes through: the first scratch whose
    home is neither the base nor the index of the store. rax (x0) unless the
    store is INTO x0's target (the SSTORE journal entry, based on x0), then rcx. -/
def nosStoreTemp (base : Reg) (idx : Option Reg) : String :=
  let used := [x86Reg base] ++ (idx.map (fun r => [x86Reg r])).getD []
  (["rax", "rcx", "rdx", "rsi"].find? (fun t => !used.contains t)).getD "rdi"

/-- The 32-bit name of a register's home. -/
def x86Reg32 (r : Reg) : String :=
  match x86Reg? r with
  | some "rax" => "eax" | some "rcx" => "ecx" | some "rdx" => "edx" | some "rbx" => "ebx"
  | some "rsi" => "esi" | some "rdi" => "edi" | some "rbp" => "ebp" | some "rsp" => "esp"
  | some n => n ++ "d" | none => "«unlowered-reg»"

def byteName : String → String
  | "rax" => "al" | "rcx" => "cl" | "rdx" => "dl" | "rsi" => "sil" | "rdi" => "dil" | n => n ++ "b"

/-- One instruction to x86-64 text. Multi-instruction expansions follow
    `X86Lower.form`; anything unhandled emits a marker that the coverage
    theorem below rules out for the gadget set. -/
def emitX86 : AInstr → String
  | .label l      => s!"{l}:\n"
  | .movImm d i   => s!"    mov   {x86Reg d}, {i}\n"
  | .ldrBase d b  => s!"    mov   {x86Reg d}, [{x86Reg b}]\n"
  | .ldrOff d b o => s!"    mov   {x86Reg d}, [{x86Reg b} + {o}]\n"
  | .strOff s b o =>
      match nosLimb s with
      | some l => let t := nosStoreTemp b none
                  s!"    mov   {t}, {nosMem l}\n    mov   [{x86Reg b} + {o}], {t}\n"
      | none => s!"    mov   [{x86Reg b} + {o}], {x86Reg s}\n"
  | .ldpOff r1 r2 b o =>
      s!"    mov   {x86Reg r1}, [{x86Reg b} + {o}]\n" ++
      s!"    mov   {x86Reg r2}, [{x86Reg b} + {o + 8}]\n"
  | .lsrImm d a sh =>
      if d == a then s!"    shr   {x86Reg d}, {sh}\n"
      else s!"    mov   {x86Reg d}, {x86Reg a}\n    shr   {x86Reg d}, {sh}\n"
  | .lslImm d a sh =>
      if d == a then s!"    shl   {x86Reg d}, {sh}\n"
      else s!"    mov   {x86Reg d}, {x86Reg a}\n    shl   {x86Reg d}, {sh}\n"
  | .clzReg d a   =>
      match nosLimb a with
      | some l => s!"    lzcnt {x86Reg d}, qword ptr {nosMem l}\n"
      | none => s!"    lzcnt {x86Reg d}, {x86Reg a}\n"
  | .cmpReg a b   => s!"    cmp   {operand a}, {operand b}\n"
  -- the OOG branches: ARM64's condition codes map directly
  | .bcsOog => "    jc    _eita_oog\n"
  | .bhiOog => "    ja    _eita_oog\n"
  | .bloOog => "    jb    _eita_oog\n"
  | .blsLbl l => s!"    jbe   {l}\n"
  | .bLbl l   => s!"    jmp   {l}\n"
  | .bTramp sym => s!"    jmp   {AsmCore.trampLabel sym}\n"
  | .bcTramp c sym => s!"    {pad ("j" ++ bcondX86 c)} {AsmCore.trampLabel sym}\n"
  | .cbzLbl r l =>
      match nosLimb r with
      | some lm => s!"    cmp   qword ptr {nosMem lm}, 0\n    jz    {l}\n"
      | none => s!"    cmp   {x86Reg r}, 0\n    jz    {l}\n"
  | .cbnzOog r =>
      match nosLimb r with
      | some lm => s!"    cmp   qword ptr {nosMem lm}, 0\n    jnz   _eita_oog\n"
      | none => s!"    cmp   {x86Reg r}, 0\n    jnz   _eita_oog\n"
  | .cmpImm a i    => s!"    cmp   {x86Reg a}, {i}\n"
  | .bSym c sym    => s!"    {pad ("j" ++ (bcondX86 c))} {sym}\n"
  -- `adds` sets the carry the following branch reads, so the destination-
  -- differs case is mov+add, never lea (which sets no flags)
  | .addsImm d a i =>
      if d == a then s!"    add   {x86Reg d}, {i}\n"
      else s!"    mov   {x86Reg d}, {x86Reg a}\n    add   {x86Reg d}, {i}\n"
  | .rev d a =>
      -- the source may be a NOS limb (mstoreTail: `rev x0, x13`): memory operand
      if d == a then s!"    bswap {x86Reg d}\n"
      else s!"    mov   {x86Reg d}, {operand a}\n    bswap {x86Reg d}\n"
  | .movReg d a    => s!"    mov   {x86Reg d}, {operand a}\n"
  | .stpOff r1 r2 b o =>
      let one := fun (r : Reg) (off : Nat) =>
        match nosLimb r with
        | some l => let t := nosStoreTemp b none
                    s!"    mov   {t}, {nosMem l}\n    mov   [{x86Reg b} + {off}], {t}\n"
        | none => s!"    mov   [{x86Reg b} + {off}], {x86Reg r}\n"
      one r1 o ++ one r2 (o + 8)
  -- ARM64 continues through x27 (adr+br is how it gets a computed return);
  -- x86-64 uses call/ret, so the continuation IS the return address
  | .brCont        => "    ret\n"
  -- carry chains: `adc`/`sbb` consume the carry the previous op left; the
  -- polarities match the ARM forms limb for limb (Flags.chains_agree)
  | .adcs d a b    => twoOp "adc" d a b true
  | .adc d a b     => twoOp "adc" d a b true
  | .sbcs d a b    => twoOp "sbb" d a b false
  | .sbc d a b     => twoOp "sbb" d a b false
  | .and3 d a b    => twoOp "and" d a b true
  | .eor3 d a b    => twoOp "xor" d a b true
  | .subsImm d a i =>
      if d == a then s!"    sub   {x86Reg d}, {i}\n"
      else s!"    mov   {x86Reg d}, {x86Reg a}\n    sub   {x86Reg d}, {i}\n"
  | .mvn d a =>
      if d == a then s!"    not   {x86Reg d}\n"
      else s!"    mov   {x86Reg d}, {operand a}\n    not   {x86Reg d}\n"
  -- compare chains: `cmp` is a destination-less sub; `sbb` always writes, so
  -- the with-borrow step goes through rcx (x14's home — a scratch here)
  | .subsZr a b    => s!"    cmp   {operand a}, {operand b}\n"
  | .sbcsZr a b    => s!"    mov   rcx, {operand a}\n    sbb   rcx, {operand b}\n"
  | .ldrbReg d b i => s!"    movzx {x86Reg d}, byte ptr [{x86Reg b} + {x86Reg i}]\n"
  | .bcLbl c l     => s!"    {pad ("j" ++ bcondX86 c)} {l}\n"
  | .movImmW d i   => s!"    mov   {x86Reg d}, {i}\n"
  | .spSub n       => s!"    sub   rsp, {n}\n"
  | .spAdd n       => s!"    add   rsp, {n}\n"
  -- no frame pointer / link register to save on x86-64: the return address is
  -- already on the stack, and rbp is pc here, not a frame pointer
  | .stpFpLr       => ""
  | .ldpFpLr       => ""
  | .addSp d n     => s!"    lea   {x86Reg d}, [rsp + {n}]\n"
  | .ldrSp d o     => s!"    mov   {x86Reg d}, [rsp + {o}]\n"
  -- the helper's absolute address sits in a table slot the loader patches;
  -- one relocation kind for the whole image, no distance constraint
  | .blSym sym     => s!"    call  qword ptr [rip + Lsym_{sym}]\n"
  | .blr r         => s!"    call  {x86Reg r}\n"
  | .bSymU sym     => s!"    jmp   {sym}\n"
  | .ldrbOff d b o => s!"    movzx {x86Reg d}, byte ptr [{x86Reg b} + {o}]\n"
  | .strbOff s b o => s!"    mov   byte ptr [{x86Reg b} + {o}], {x86Reg8 s}\n"
  -- a NOS source byte goes through al (x0's home; x0 is dead where this is used)
  | .strbReg s b i =>
      match nosLimb s with
      | some l => let t := nosStoreTemp b (some i)
                  s!"    mov   {t}, {nosMem l}\n    mov   byte ptr [{x86Reg b} + {x86Reg i}], {byteName t}\n"
      | none => s!"    mov   byte ptr [{x86Reg b} + {x86Reg i}], {x86Reg8 s}\n"
  | .madd d a b c  =>
      if d != a && d != b && d != c then
        s!"    mov   {x86Reg d}, {x86Reg a}\n    imul  {x86Reg d}, {x86Reg b}\n    add   {x86Reg d}, {x86Reg c}\n"
      else "    «unlowered: madd with an aliased destination»\n"
  | .strZr b o     => s!"    mov   qword ptr [{x86Reg b} + {o}], 0\n"
  | .strWSp s o    => s!"    mov   dword ptr [rsp + {o}], {x86Reg32 s}\n"
  | .strWzrSp o    => s!"    mov   dword ptr [rsp + {o}], 0\n"
  | .stpZrSp o     => s!"    mov   qword ptr [rsp + {o}], 0\n    mov   qword ptr [rsp + {o + 8}], 0\n"
  | .stpSp r1 r2 o => s!"    mov   [rsp + {o}], {x86Reg r1}\n    mov   [rsp + {o + 8}], {x86Reg r2}\n"
  | .strSp s o     => s!"    mov   [rsp + {o}], {x86Reg s}\n"
  | .ldrWSp d o    => s!"    mov   {x86Reg32 d}, dword ptr [rsp + {o}]\n"
  | .cbzWLbl r l   => s!"    cmp   {x86Reg32 r}, 0\n    jz    {l}\n"
  | .andImmHex d a i =>
      if d == a then s!"    and   {x86Reg d}, {i}\n"
      else s!"    mov   {x86Reg d}, {x86Reg a}\n    and   {x86Reg d}, {i}\n"
  -- csinv d, a, xzr, eq: keep a when equal, else all ones (through rax)
  | .csinvEqZr d a =>
      (if d == a then "" else s!"    mov   {x86Reg d}, {x86Reg a}\n") ++
      s!"    mov   rax, -1\n    cmovne {x86Reg d}, rax\n"
  -- the ARM64 frame has its own x86-64 frame (`X86Run`); these never lower
  | .global _ | .p2align2 | .symLabel _ | .stpPreSp _ _ _ | .ldpPostSp _ _ _ | .ldpSp _ _ _
  | .movToSp _ | .movFromSp _ | .ldrLsl3 _ _ _ | .loadSymValue _ _ | .loadSymGotValue _ _ =>
      "    «unlowered: ARM64 frame»\n"
  | .ret           => "    ret\n"
  -- the ARM64 chunk algebra; the x86-64 chunk JIT has its own (stage 5)
  | .movkImm _ _ _ | .addSpReg _ | .spAddReg _ | .spSubReg _ | .adrLbl _ _ | .brk0
  | .strBase _ _ | .strbBase _ _ | .bFar _ | .blFar _ =>
      "    «unlowered: ARM64 chunk algebra»\n"
  -- the gas routines' forms (stage 4w): x86-64 twins exist for the register
  -- selects, the bit test and the compare-and-branch; the ZERO selects do not
  -- (cmov takes no immediate, and a hidden temporary would be a register the
  -- `AsmSem` semantics does not see) — an x86-64 program writes `mov x0, 0`
  -- and selects x0 instead
  | .tstImm r i    => s!"    test  {x86Reg r}, {i}\n"
  | .cbnzLbl r l   => s!"    cmp   {x86Reg r}, 0\n    jnz   {l}\n"
  | .cbnzWLbl r l  => s!"    cmp   {x86Reg32 r}, 0\n    jnz   {l}\n"
  | .eorImm1 d a   =>
      if d == a then s!"    xor   {x86Reg d}, 1\n"
      else s!"    mov   {x86Reg d}, {x86Reg a}\n    xor   {x86Reg d}, 1\n"
  | .csel d a b c  =>
      if d == b then s!"    {pad ("cmov" ++ bcondX86 c)} {x86Reg d}, {x86Reg a}\n"
      else if d == a then s!"    {pad ("cmov" ++ nbcondX86 c)} {x86Reg d}, {x86Reg b}\n"
      else s!"    mov   {x86Reg d}, {x86Reg b}\n    {pad ("cmov" ++ bcondX86 c)} {x86Reg d}, {x86Reg a}\n"
  | .cselZrA _ _ _ | .cselZrB _ _ _ =>
      "    «unlowered: zero select (write mov x0, 0 ; csel … x0 on x86-64)»\n"
  | .blank | .textSection | .dataSection | .p2align3 | .quadSym _ | .quadPair _ _ _ | .commentLine _ =>
      "    «unlowered: ARM64 routines»\n"
  | .cbnzSym r sym => s!"    cmp   {x86Reg r}, 0\n    jnz   {sym}\n"
  | .cmpImmWHex r i => s!"    cmp   {x86Reg r}, {i}\n"
  | .loadSymAddr _ _ => "    «unlowered: loadSymAddr (ARM64 continuation only)»\n"
  | .brReg r       => s!"    jmp   {x86Reg r}\n"
  | .cbnzSymW r sym => s!"    cmp   {x86Reg r}, 0\n    jnz   {sym}\n"
  | .movzImm d i   => s!"    mov   {x86Reg d}, {i}\n"
  | .cselNe d a b  =>
      if d == b then s!"    cmovne {x86Reg d}, {x86Reg a}\n"
      else if d == a then s!"    cmove {x86Reg d}, {x86Reg b}\n"
      else s!"    mov   {x86Reg d}, {x86Reg b}\n    cmovne {x86Reg d}, {x86Reg a}\n"
  | .cset d c      =>
      s!"    {pad ("set" ++ setcondX86 c)} {x86Reg8 d}\n" ++
      s!"    movzx {x86Reg d}, {x86Reg8 d}\n"
  -- three-operand arithmetic, per X86Lower.form
  | .addImm d a i =>
      if d == a then s!"    add   {x86Reg d}, {i}\n"
      else match nosLimb a with
        | some l => s!"    mov   {x86Reg d}, {nosMem l}\n    add   {x86Reg d}, {i}\n"
        | none => s!"    lea   {x86Reg d}, [{x86Reg a} + {i}]\n"
  | .subImm d a i =>
      if d == a then s!"    sub   {x86Reg d}, {i}\n"
      else s!"    lea   {x86Reg d}, [{x86Reg a} - {i}]\n"
  | .addReg d a b => twoOp "add" d a b true
  | .adds d a b   => twoOp "add" d a b true
  | .orr3 d a b   => twoOp "or"  d a b true
  | .mulReg d a b => twoOp "imul" d a b true
  | .subReg d a b  => twoOp "sub" d a b false
  | .subsReg d a b => twoOp "sub" d a b false
  | .addLsl d a b sh =>
      if sh ≤ 3 then s!"    lea   {x86Reg d}, [{x86Reg a} + {x86Reg b}*{2 ^ sh}]\n"
      else if d == b then s!"    shl   {x86Reg d}, {sh}\n    add   {x86Reg d}, {x86Reg a}\n"
      else if d != a then
        s!"    mov   {x86Reg d}, {x86Reg b}\n    shl   {x86Reg d}, {sh}\n" ++
        s!"    add   {x86Reg d}, {x86Reg a}\n"
      else "    «unlowered: addLsl into left operand, shift > 3»\n"
  | .addLsl5 d a b =>
      if d == b then s!"    shl   {x86Reg d}, 5\n    add   {x86Reg d}, {x86Reg a}\n"
      else if d != a then
        s!"    mov   {x86Reg d}, {x86Reg b}\n    shl   {x86Reg d}, 5\n" ++
        s!"    add   {x86Reg d}, {x86Reg a}\n"
      else "    «unlowered: addLsl5 into left operand»\n"
  | .addLsr d a b sh =>
      if d == b then s!"    shr   {x86Reg d}, {sh}\n    add   {x86Reg d}, {x86Reg a}\n"
      else if d != a then
        s!"    mov   {x86Reg d}, {x86Reg b}\n    shr   {x86Reg d}, {sh}\n" ++
        s!"    add   {x86Reg d}, {x86Reg a}\n"
      else "    «unlowered: addLsr into left operand»\n"
  -- cmov, with the condition inverted when the destination is the TRUE operand
  | .cselHi d a b =>
      if d == b then s!"    cmova {x86Reg d}, {x86Reg a}\n"
      else if d == a then s!"    cmovbe {x86Reg d}, {x86Reg b}\n"
      else s!"    mov   {x86Reg d}, {x86Reg b}\n    cmova {x86Reg d}, {x86Reg a}\n"
where
  /-- Two-operand expansion. `comm` says the op is commutative, which is what
      lets the destination sit on the right for one instruction. -/
  twoOp (mnem : String) (d a b : Reg) (comm : Bool) : String :=
    if d == a then s!"    {pad mnem} {x86Reg d}, {operand b}\n"
    else if d == b && comm then s!"    {pad mnem} {x86Reg d}, {operand a}\n"
    else if d == b then s!"    «unlowered: {mnem} with destination = right operand»\n"
    else s!"    mov   {x86Reg d}, {operand a}\n    {pad mnem} {x86Reg d}, {operand b}\n"

def x86 : Target where
  name := "x86-64"
  reg  := x86Reg
  emit := emitX86

/-! ## Coverage

The marker is the point: an instruction the x86 lowering cannot handle says so
in its output, and this theorem says none of the gadgets produce one. -/

/-- **The x86-64 lowering covers every instruction in the gadget set.** -/
theorem every_gadget_instruction_lowers :
    gadgetSet.all (fun p => ((emitProg x86 p).splitOn "«").length == 1) = true := by
  native_decide

/-- Every register the gadgets mention has an x86 home — except NOS, which is
    handled by loading rather than by a register. -/
theorem every_mentioned_register_has_a_home :
    gadgetSet.all (fun p => p.all (fun it =>
      (mentions it).all (fun r => (x86Reg? r).isSome || (nosLimb r).isSome))) = true := by
  native_decide

/-- The markers really do fire when they should, so the coverage theorem is not
    vacuous: the two forms `X86Lower` classified `needsTemp` emit one. -/
theorem marker_fires_on_reversed_sub :
    ((emitX86 (.subReg .x14 .x15 .x14)).splitOn "«").length = 2 := by native_decide

theorem marker_fires_on_big_shift_into_left :
    ((emitX86 (.addLsl .x14 .x14 .x15 5)).splitOn "«").length = 2 := by native_decide

/-! ## Spot checks against hand-written x86

A few instructions whose lowering is worth reading, to catch a silly mistake
that coverage alone would not. -/

theorem lea_for_small_shift :
    emitX86 (.addLsl .x16 .x16 .x14 1) = "    lea   rdi, [rdi + rcx*2]\n" := by
  native_decide

theorem shift_in_place_for_addLsl5 :
    emitX86 (.addLsl5 .x14 .x24 .x14) = "    shl   rcx, 5\n    add   rcx, r12\n" := by
  native_decide

theorem cmov_inverts_for_true_operand :
    emitX86 (.cselHi .x0 .x0 .x14) = "    cmovbe rax, rcx\n" := by native_decide

/-- A NOS read is an addressing mode, not a load: no register consumed. -/
theorem nos_read_is_an_addressing_mode :
    emitX86 (.cbzLbl .x10 "4f")
      = "    cmp   qword ptr [r12 + r13 - 64], 0\n    jz    4f\n" := by
  native_decide

/-- …and as an arithmetic source it is folded straight into the instruction. -/
theorem nos_or_is_one_instruction :
    emitX86 (.orr3 .x14 .x14 .x12) = "    or    rcx, [r12 + r13 - 48]\n" := by
  native_decide

/-- No gadget WRITES a NOS register — they are read-only operands throughout,
    which is what makes the addressing-mode treatment complete rather than a
    partial trick. -/
theorem no_gadget_writes_nos :
    gadgetSet.all (fun p => p.all (fun it =>
      match it with
      | .ldpOff r1 r2 _ _ => (nosLimb r1).isNone && (nosLimb r2).isNone
      | .subImm d _ _ | .movImm d _ | .ldrOff d _ _ | .ldrBase d _ | .clzReg d _
      | .lsrImm d _ _ | .lslImm d _ _ | .addImm d _ _ | .addLsl5 d _ _
      | .orr3 d _ _ | .adds d _ _ | .cselHi d _ _ | .subsReg d _ _
      | .subReg d _ _ | .addReg d _ _ | .mulReg d _ _
      | .addLsr d _ _ _ | .addLsl d _ _ _ => (nosLimb d).isNone
      | _ => true)) = true := by
  native_decide

/-! ## Size, measured from the emitted text

How much bigger the x86 code is matters because these gadgets are inlined at
every op site, and `Evm.CL.Relax` lays out whatever the encoder charges. These
count the emitter's own output — `scripts/verify-x86-emit.sh` confirms the same
file assembles, at the same count. -/

/-- Instruction lines in an emitted gadget: everything but the labels. -/
def insnLines (text : String) : Nat :=
  ((text.splitOn "\n").filter (fun l => l.startsWith "    ")).length

def arm64Insns : Nat :=
  (gadgetSet.map (fun p => insnLines (emitProg arm64 p))).foldl (· + ·) 0

def x86Insns : Nat :=
  (gadgetSet.map (fun p => insnLines (emitProg x86 p))).foldl (· + ·) 0

/-- The measured sizes: 257 ARM64 instructions become 320, i.e. just under 25%
    more (`scripts/verify-x86-emit.sh` adds the eight `ret`s of its standalone harness). -/
theorem insn_counts : arm64Insns = 257 ∧ x86Insns = 320 := by native_decide

/-- Under a quarter more instructions — a constant factor from the two-operand
    ISA, not a multiple. The margin is thin (32000 vs 32125), so this is a real
    bound rather than a comfortable one. -/
theorem expansion_under_a_quarter : x86Insns * 100 ≤ arm64Insns * 125 := by
  native_decide

end Evm.CL.Lowering
