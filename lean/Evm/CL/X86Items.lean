/-
  Evm.CL.X86Items — the byte lowering of `AInstr` for x86-64.

  The x86-64 counterpart of `Evm.CL.AsmItems`. `Lowering.emitX86` produces the
  text; this produces the structured instructions `X86Encode.encode` turns into
  bytes, from the SAME `AInstr`, with the same aliasing decisions
  (`X86Lower.form`). The two are gated against each other through the
  assembler — `scripts/verify-x86-items.sh` requires `encode (x86Items i)` to
  equal clang's bytes for `emitX86 i`, instruction by instruction over the
  gadget set — which is the check that was missing on ARM64 until `AsmItems`.

      AInstr ──emitX86──▶ text   ──clang──▶ bytes ─┐
             ──x86Items─▶ XItem ──encode─▶ bytes ─┴─ must agree

  Branches are layout-dependent (rel8 vs rel32, which `Relax` decides), so they
  are items rather than instructions here, exactly as on ARM64.

  NOS reads become memory operands (`nosMemX`), and the one two-memory-operand
  form x86 has no encoding for — comparing two NOS limbs directly — is an
  `unlowered` item, which `every_gadget_instruction_lowers` rules out for the
  gadget set rather than assuming.
-/

import Evm.CL.X86Encode

namespace Evm.CL.X86Items

open Evm.CL.AsmCore Evm.CL.Pressure Evm.CL.X86Encode

/-- x86-64 layout items: instructions, labels, and the branches whose width the
    relaxation pass decides. -/
inductive XItem where
  | I       (i : XInsn)
  | L       (name : String)
  | Jcc     (c : XCond) (target : String)     -- local label
  | Jmp     (target : String)                 -- local label
  | JccSym  (c : XCond) (sym : String)        -- external symbol (_eita_oog)
  | JmpSym  (sym : String)                    -- unconditional, external symbol
  /-- `lea dst, [rip + target]`: the address of a local label, position-
      independently (7 bytes; the disp32 is resolved by the assembler) -/
  | LeaRip  (dst : XReg) (target : String)
  /-- `lea dst, [rip + sym]` for an EXTERNAL symbol (a data table in another
      part of the image): zero displacement plus a `rel32` relocation, as
      `JmpSym` — the text is the same as `LeaRip`'s -/
  | LeaRipSym (dst : XReg) (sym : String)
  /-- an 8-byte datum holding the OFFSET of `target` from the program's start —
      a relocation-free table entry -/
  | QuadOff (target : String)
  /-- `call target` (E8 rel32, 5 bytes): the frame calls a handler, which
      returns with `brCont` = `ret` -/
  | Call    (target : String)
  /-- `call qword ptr [rip + slot]` (FF 15 disp32, 6 bytes): an indirect call
      through an 8-byte slot holding a helper's absolute address -/
  | CallRip (slot : String)
  /-- an 8-byte slot the LOADER fills with `sym`'s absolute address (an abs64
      relocation) — the only relocation kind an image needs -/
  | QuadSym (sym : String)
  /-- a form this lowering has no encoding for; the coverage theorem below says
      the gadgets never produce one -/
  | unlowered (why : String)
  deriving Repr

/-- The register map, as registers rather than names: `Target`'s roles for the
    pinned caches, `Pressure.x86Temp`'s forced colouring for the temporaries.
    NOS (x10-x13) has no register — `none` — and is read from memory. -/
def xreg? : Reg → Option XReg
  | .x6 => some .r8  | .x7 => some .r9  | .x8 => some .r10 | .x9 => some .r11
  | .x20 => some .rbx | .x22 => some .r15 | .x23 => some .r13 | .x24 => some .r12
  | .x0 => some .rax | .x14 => some .rcx | .x15 => some .rdx | .x17 => some .rsi
  | .x4 => some .rdi | .x16 => some .rdi
  | .x10 | .x11 | .x12 | .x13 => none
  | .x19 | .x25 | .x28 | .x29 | .x30 => none   -- the ARM64 frame's registers
  | .x1 => some .rdx | .x2 => some .rsi | .x3 => some .rdi   -- provisional, see Lowering
  | .x21 => some .rbp | .x26 => some .r14
  | .x27 => none
  | .x5 => none

def setcondXc : SetCond → XCond
  | .eq => .e | .lo => .b | .lt => .l

def bcondXc : BCond → XCond
  | .lo => .b | .hs => .ae | .hi => .a | .ls => .be | .eq => .e | .ne => .ne | .lt => .l

/-- The negated condition. -/
def nbcondXc : BCond → XCond
  | .lo => .ae | .hs => .b | .hi => .be | .ls => .a | .eq => .ne | .ne => .e | .lt => .ge

/-- The register map agrees with the text lowering's names on every register
    that has one. -/
theorem xreg_matches_text :
    [Reg.x0, .x4, .x6, .x7, .x8, .x9, .x14, .x15, .x16, .x17, .x20, .x22, .x23, .x24,
     .x1, .x2, .x3, .x21, .x26].all
      (fun r => (xreg? r).map XReg.name == Evm.CL.Lowering.x86Reg? r) = true := by
  native_decide

def nosLimb : Reg → Option Nat
  | .x10 => some 0 | .x11 => some 1 | .x12 => some 2 | .x13 => some 3
  | _ => none

/-- NOS limb `l` as a memory operand: `[r12 + r13 - (64 - 8l)]`, scale 1, with
    r13 holding sp as a byte offset (see `Lowering.nosMem`). -/
def nosMemX (l : Nat) : Mem :=
  { base := .r12, index := some .r13, disp := -(Int.ofNat (64 - 8 * l)) }

/-- The NOS addresses are all encodable — in particular the scale is 1. -/
theorem nos_addresses_encodable :
    [0, 1, 2, 3].all (fun l => (nosMemX l).ok) = true := by native_decide

/-- A register the lowering writes to. NOS is never a destination
    (`AsmItems.no_gadget_writes_nos` on the ARM64 side says the same), so this
    is total on the gadgets; elsewhere it marks the instruction unlowered. -/
def dst (r : Reg) : XReg := (xreg? r).getD .rax

/-- `op d, src` where `src` may be a NOS limb in memory. -/
def aluFrom (o : AluOp) (d : XReg) (src : Reg) : XItem :=
  match xreg? src, nosLimb src with
  | some s, _ => .I (.aluRR o d s)
  | none, some l => .I (.aluRM o d (nosMemX l))
  | none, none => .unlowered "alu source has no home"

/-- `mov d, src`, likewise. -/
def movFrom (d : XReg) (src : Reg) : XItem :=
  match xreg? src, nosLimb src with
  | some s, _ => .I (.movRR d s)
  | none, some l => .I (.movRM d (nosMemX l))
  | none, none => .unlowered "mov source has no home"

/-- `cmp a, b` where either side may be a NOS limb in memory (never both). -/
def cmpFrom (a b : Reg) : XItem :=
  match xreg? a, nosLimb a, xreg? b, nosLimb b with
  | some ra, _, _, _ => aluFrom .cmp ra b
  | none, some la, some rb, _ => .I (.aluMR .cmp (nosMemX la) rb)
  | _, _, _, _ => .unlowered "cmp of two NOS limbs"

/-- The temporary a NOS-source store goes through (mirrors `Lowering.nosStoreTemp`). -/
def nosStoreTempX (base : Reg) (idx : Option Reg) : XReg :=
  let used := [dst base] ++ (idx.map (fun r => [dst r])).getD []
  ([XReg.rax, .rcx, .rdx, .rsi].find? (fun t => !used.contains t)).getD .rdi

/-- Two-operand expansion, mirroring `Lowering.emitX86.twoOp` case for case. -/
def twoOp (o : AluOp) (d a b : Reg) (comm : Bool) : List XItem :=
  if d == a then [aluFrom o (dst d) b]
  else if d == b && comm then [aluFrom o (dst d) a]
  else if d == b then [.unlowered s!"{o.mnem} with destination = right operand"]
  else [movFrom (dst d) a, aluFrom o (dst d) b]

/-- A shift into `d` then add `a`: `d = (d << sh) + a` or with `>>`. -/
def shiftThenAdd (o : ShiftOp) (d : XReg) (sh : Nat) (a : Reg) : List XItem :=
  [.I (.shiftRI o d sh), aluFrom .add d a]

/-- The lowering. One arm per constructor, in `emitX86`'s order. -/
def x86Items : AInstr → List XItem
  | .label l      => [.L l]
  | .movImm d i   => [.I (.movRI (dst d) (Int.ofNat i))]
  | .ldrBase d b  => [.I (.movRM (dst d) { base := dst b })]
  | .ldrOff d b o => [.I (.movRM (dst d) { base := dst b, disp := Int.ofNat o })]
  | .strOff s b o =>
      match nosLimb s with
      | some l => let t := nosStoreTempX b none
                  [.I (.movRM t (nosMemX l)), .I (.movMR { base := dst b, disp := Int.ofNat o } t)]
      | none => [.I (.movMR { base := dst b, disp := Int.ofNat o } (dst s))]
  | .ldpOff r1 r2 b o =>
      [.I (.movRM (dst r1) { base := dst b, disp := Int.ofNat o }),
       .I (.movRM (dst r2) { base := dst b, disp := Int.ofNat (o + 8) })]
  | .lsrImm d a sh =>
      if d == a then [.I (.shiftRI .shr (dst d) sh)]
      else [.I (.movRR (dst d) (dst a)), .I (.shiftRI .shr (dst d) sh)]
  | .lslImm d a sh =>
      if d == a then [.I (.shiftRI .shl (dst d) sh)]
      else [.I (.movRR (dst d) (dst a)), .I (.shiftRI .shl (dst d) sh)]
  | .clzReg d a   =>
      match nosLimb a with
      | some l => [.I (.lzcntRM (dst d) (nosMemX l))]
      | none => [.I (.lzcnt (dst d) (dst a))]
  | .cmpReg a b   =>
      match xreg? a, nosLimb a, xreg? b, nosLimb b with
      | some ra, _, _, _ => [aluFrom .cmp ra b]
      | none, some la, some rb, _ => [.I (.aluMR .cmp (nosMemX la) rb)]
      | none, some _, none, some _ => [.unlowered "cmp of two NOS limbs"]
      | _, _, _, _ => [.unlowered "cmp operand has no home"]
  | .bcsOog       => [.JccSym .b "_eita_oog"]       -- `jc` is `jb`
  | .bhiOog       => [.JccSym .a "_eita_oog"]
  | .bloOog       => [.JccSym .b "_eita_oog"]
  | .blsLbl l     => [.Jcc .be l]
  | .bLbl l       => [.Jmp l]
  | .bTramp sym   => [.Jmp (trampLabel sym)]
  | .bcTramp c sym => [.Jcc (bcondXc c) (trampLabel sym)]
  | .cbzLbl r l   =>
      match nosLimb r with
      | some lm => [.I (.aluMI .cmp (nosMemX lm) 0), .Jcc .e l]
      | none => [.I (.aluRI .cmp (dst r) 0), .Jcc .e l]
  | .cbnzOog r    =>
      match nosLimb r with
      | some lm => [.I (.aluMI .cmp (nosMemX lm) 0), .JccSym .ne "_eita_oog"]
      | none => [.I (.aluRI .cmp (dst r) 0), .JccSym .ne "_eita_oog"]
  | .addImm d a i =>
      if d == a then [.I (.aluRI .add (dst d) (Int.ofNat i))]
      else match nosLimb a with
        | some l => [.I (.movRM (dst d) (nosMemX l)), .I (.aluRI .add (dst d) (Int.ofNat i))]
        | none => [.I (.lea (dst d) { base := dst a, disp := Int.ofNat i })]
  | .subImm d a i =>
      if d == a then [.I (.aluRI .sub (dst d) (Int.ofNat i))]
      else [.I (.lea (dst d) { base := dst a, disp := -(Int.ofNat i) })]
  | .addReg d a b  => twoOp .add d a b true
  | .adds d a b    => twoOp .add d a b true
  | .orr3 d a b    => twoOp .or_ d a b true
  | .subReg d a b  => twoOp .sub d a b false
  | .subsReg d a b => twoOp .sub d a b false
  | .mulReg d a b  =>
      if d == a then [.I (.imulRR (dst d) (dst b))]
      else if d == b then [.I (.imulRR (dst d) (dst a))]
      else [.I (.movRR (dst d) (dst a)), .I (.imulRR (dst d) (dst b))]
  | .addLsl d a b sh =>
      if sh ≤ 3 then [.I (.lea (dst d) { base := dst a, index := some (dst b), scale := 2 ^ sh })]
      else if d == b then shiftThenAdd .shl (dst d) sh a
      else if d != a then .I (.movRR (dst d) (dst b)) :: shiftThenAdd .shl (dst d) sh a
      else [.unlowered "addLsl into left operand, shift > 3"]
  | .addLsl5 d a b =>
      if d == b then shiftThenAdd .shl (dst d) 5 a
      else if d != a then .I (.movRR (dst d) (dst b)) :: shiftThenAdd .shl (dst d) 5 a
      else [.unlowered "addLsl5 into left operand"]
  | .addLsr d a b sh =>
      if d == b then shiftThenAdd .shr (dst d) sh a
      else if d != a then .I (.movRR (dst d) (dst b)) :: shiftThenAdd .shr (dst d) sh a
      else [.unlowered "addLsr into left operand"]
  | .cselHi d a b =>
      if d == b then [.I (.cmovRR .a (dst d) (dst a))]
      else if d == a then [.I (.cmovRR .be (dst d) (dst b))]
      else [.I (.movRR (dst d) (dst b)), .I (.cmovRR .a (dst d) (dst a))]
  | .cmpImm a i    => [.I (.aluRI .cmp (dst a) (Int.ofNat i))]
  | .bSym c sym    => [.JccSym (bcondXc c) sym]
  | .addsImm d a i =>
      if d == a then [.I (.aluRI .add (dst d) (Int.ofNat i))]
      else [.I (.movRR (dst d) (dst a)), .I (.aluRI .add (dst d) (Int.ofNat i))]
  | .rev d a =>
      if d == a then [.I (.bswap (dst d))]
      else [movFrom (dst d) a, .I (.bswap (dst d))]      -- NOS-safe source
  | .movReg d a    => [movFrom (dst d) a]
  | .stpOff r1 r2 b o =>
      let one := fun (r : Reg) (off : Nat) =>
        match nosLimb r with
        | some l => let t := nosStoreTempX b none
                    [XItem.I (.movRM t (nosMemX l)), .I (.movMR { base := dst b, disp := Int.ofNat off } t)]
        | none => [XItem.I (.movMR { base := dst b, disp := Int.ofNat off } (dst r))]
      one r1 o ++ one r2 (o + 8)
  | .brCont        => [.I .ret]
  | .adcs d a b    => twoOp .adc d a b true
  | .adc d a b     => twoOp .adc d a b true
  | .sbcs d a b    => twoOp .sbb d a b false
  | .sbc d a b     => twoOp .sbb d a b false
  | .and3 d a b    => twoOp .and_ d a b true
  | .eor3 d a b    => twoOp .xor_ d a b true
  | .subsImm d a i =>
      if d == a then [.I (.aluRI .sub (dst d) (Int.ofNat i))]
      else [.I (.movRR (dst d) (dst a)), .I (.aluRI .sub (dst d) (Int.ofNat i))]
  | .mvn d a =>
      if d == a then [.I (.notR (dst d))]
      else [movFrom (dst d) a, .I (.notR (dst d))]
  | .subsZr a b    => [cmpFrom a b]
  | .sbcsZr a b    => [movFrom .rcx a, aluFrom .sbb .rcx b]
  | .cset d c      => [.I (.setcc (setcondXc c) (dst d)), .I (.movzxB (dst d) (dst d))]
  | .ldrbReg d b i => [.I (.movzxBM (dst d) { base := dst b, index := some (dst i) })]
  | .bcLbl c l     => [.Jcc (bcondXc c) l]
  | .movImmW d i   => [.I (.movRI (dst d) (Int.ofNat i))]
  | .spSub n       => [.I (.aluRI .sub .rsp (Int.ofNat n))]
  | .spAdd n       => [.I (.aluRI .add .rsp (Int.ofNat n))]
  | .stpFpLr       => []
  | .ldpFpLr       => []
  | .addSp d n     => [.I (.lea (dst d) { base := .rsp, disp := Int.ofNat n })]
  | .ldrSp d o     => [.I (.movRM (dst d) { base := .rsp, disp := Int.ofNat o })]
  | .blSym sym     => [.CallRip s!"Lsym_{sym}"]
  | .blr r         => [.I (.callReg (dst r))]
  | .bSymU sym     => [.JmpSym sym]
  | .ldrbOff d b o => [.I (.movzxBM (dst d) { base := dst b, disp := Int.ofNat o })]
  | .strbOff s b o => [.I (.movMR8 { base := dst b, disp := Int.ofNat o } (dst s))]
  | .strbReg s b i =>
      match nosLimb s with
      | some l => let t := nosStoreTempX b (some i)
                  [.I (.movRM t (nosMemX l)), .I (.movMR8 { base := dst b, index := some (dst i) } t)]
      | none => [.I (.movMR8 { base := dst b, index := some (dst i) } (dst s))]
  | .madd d a b c  =>
      if d != a && d != b && d != c then
        [.I (.movRR (dst d) (dst a)), .I (.imulRR (dst d) (dst b)), .I (.aluRR .add (dst d) (dst c))]
      else [.unlowered "madd with an aliased destination"]
  | .strZr b o     => [.I (.movMI { base := dst b, disp := Int.ofNat o } 0)]
  | .strWSp s o    => [.I (.movMR32 { base := .rsp, disp := Int.ofNat o } (dst s))]
  | .strWzrSp o    => [.I (.movMI32 { base := .rsp, disp := Int.ofNat o } 0)]
  | .stpZrSp o     => [.I (.movMI { base := .rsp, disp := Int.ofNat o } 0), .I (.movMI { base := .rsp, disp := Int.ofNat (o + 8) } 0)]
  | .stpSp r1 r2 o => [.I (.movMR { base := .rsp, disp := Int.ofNat o } (dst r1)), .I (.movMR { base := .rsp, disp := Int.ofNat (o + 8) } (dst r2))]
  | .strSp s o     => [.I (.movMR { base := .rsp, disp := Int.ofNat o } (dst s))]
  | .ldrWSp d o    => [.I (.movRM32 (dst d) { base := .rsp, disp := Int.ofNat o })]
  | .cbzWLbl r l   => [.I (.cmpRI32 (dst r) 0), .Jcc .e l]
  | .andImmHex d a i =>
      if d == a then [.I (.aluRI .and_ (dst d) (Int.ofNat i))]
      else [.I (.movRR (dst d) (dst a)), .I (.aluRI .and_ (dst d) (Int.ofNat i))]
  | .csinvEqZr d a =>
      (if d == a then [] else [XItem.I (.movRR (dst d) (dst a))]) ++
      [.I (.movRI .rax (-1)), .I (.cmovRR .ne (dst d) .rax)]
  | .global _ | .p2align2 | .symLabel _ | .stpPreSp _ _ _ | .ldpPostSp _ _ _ | .ldpSp _ _ _
  | .movToSp _ | .movFromSp _ | .ldrLsl3 _ _ _ | .loadSymValue _ _ | .loadSymGotValue _ _ =>
      [.unlowered "ARM64 frame"]
  | .ret           => [.I .ret]
  | .movkImm _ _ _ | .addSpReg _ | .spAddReg _ | .spSubReg _ | .adrLbl _ _ | .brk0
  | .strBase _ _ | .strbBase _ _ | .bFar _ | .blFar _ =>
      [.unlowered "ARM64 chunk algebra"]
  | .tstImm r i    => [.I (.testRI (dst r) (Int.ofNat i))]
  | .cbnzLbl r l   => [.I (.aluRI .cmp (dst r) 0), .Jcc .ne l]
  | .cbnzWLbl r l  => [.I (.cmpRI32 (dst r) 0), .Jcc .ne l]
  | .eorImm1 d a   =>
      if d == a then [.I (.aluRI .xor_ (dst d) 1)]
      else [.I (.movRR (dst d) (dst a)), .I (.aluRI .xor_ (dst d) 1)]
  | .csel d a b c  =>
      if d == b then [.I (.cmovRR (bcondXc c) (dst d) (dst a))]
      else if d == a then [.I (.cmovRR (nbcondXc c) (dst d) (dst b))]
      else [.I (.movRR (dst d) (dst b)), .I (.cmovRR (bcondXc c) (dst d) (dst a))]
  | .cselZrA _ _ _ | .cselZrB _ _ _ => [.unlowered "zero select"]
  | .blank | .textSection | .dataSection | .p2align3 | .quadSym _ | .quadPair _ _ _ | .commentLine _ =>
      [.unlowered "ARM64 routines"]
  | .cbnzSym r sym => [.I (.aluRI .cmp (dst r) 0), .JccSym .ne sym]
  | .cmpImmWHex r i => [.I (.aluRI .cmp (dst r) (Int.ofNat i))]
  | .loadSymAddr _ _ => [.unlowered "loadSymAddr (ARM64 continuation only)"]
  | .brReg r       => [.I (.jmpReg (dst r))]
  | .cbnzSymW r sym => [.I (.aluRI .cmp (dst r) 0), .JccSym .ne sym]
  | .movzImm d i   => [.I (.movRI (dst d) (Int.ofNat i))]
  | .cselNe d a b  =>
      if d == b then [.I (.cmovRR .ne (dst d) (dst a))]
      else if d == a then [.I (.cmovRR .e (dst d) (dst b))]
      else [.I (.movRR (dst d) (dst b)), .I (.cmovRR .ne (dst d) (dst a))]

def progItems (p : List AInstr) : List XItem := p.flatMap x86Items

/-! ## Coverage and alignment, checked -/

def isUnlowered : XItem → Bool
  | .unlowered _ => true
  | _ => false

/-- **Every gadget instruction has a byte lowering.** -/
theorem every_gadget_instruction_lowers :
    gadgetSet.all (fun p => (progItems p).all (fun it => !isUnlowered it)) = true := by
  native_decide

/-- The instructions (not labels, not branches) an item list contains. -/
def insns (its : List XItem) : List XInsn :=
  its.filterMap (fun it => match it with | .I i => some i | _ => none)

/-- The instruction lines of the text lowering: drop labels and branches. -/
def textInsnLines (i : AInstr) : List String :=
  ((Evm.CL.Lowering.emitX86 i).splitOn "\n").filter (fun l =>
    l.startsWith "    " && !(l.startsWith "    j") && !(l.startsWith "    call  qword ptr [rip"))

/-- **The two lowerings emit the same number of instructions for every gadget
    instruction**, which is what lets the byte gate pair them one to one. A
    mismatch here is a lowering that expanded differently on the two sides. -/
theorem lowerings_align :
    gadgetSet.all (fun p => p.all (fun i =>
      (insns (x86Items i)).length == (textInsnLines i).length)) = true := by
  native_decide

/-- The register-or-memory helpers never produce a label, whichever arm the
    source register selects — stated as the shape `same_labels` needs. -/
theorem movFrom_no_label (d : XReg) (a : Reg) :
    (match movFrom d a with | XItem.L l => some l | _ => none) = (none : Option String) := by
  unfold movFrom; cases xreg? a <;> cases nosLimb a <;> rfl

theorem aluFrom_no_label (o : AluOp) (d : XReg) (a : Reg) :
    (match aluFrom o d a with | XItem.L l => some l | _ => none) = (none : Option String) := by
  unfold aluFrom; cases xreg? a <;> cases nosLimb a <;> rfl

theorem cmpFrom_no_label (a b : Reg) :
    (match cmpFrom a b with | XItem.L l => some l | _ => none) = (none : Option String) := by
  unfold cmpFrom aluFrom
  cases xreg? a <;> cases nosLimb a <;> cases xreg? b <;> cases nosLimb b <;> rfl

/-- Every label the text lowering defines, this one defines, in order — so the
    relaxation pass sees the same layout on both. -/
theorem same_labels (p : List AInstr) :
    (p.filterMap (fun i => match i with | .label l => some l | _ => none))
      = (progItems p).filterMap (fun it => match it with | .L l => some l | _ => none) := by
  induction p with
  | nil => rfl
  | cons i rest ih =>
    have hsplit : progItems (i :: rest) = x86Items i ++ progItems rest := by
      simp [progItems]
    rw [hsplit, List.filterMap_append, ← ih]
    cases i <;> simp [x86Items, twoOp, shiftThenAdd, movFrom_no_label, aluFrom_no_label, cmpFrom_no_label] <;>
      (repeat' split) <;> simp_all [movFrom_no_label, aluFrom_no_label]

/-- Every address this lowering emits is encodable — the scale rule, enforced
    structurally over the gadget set. -/
theorem every_address_encodable :
    gadgetSet.all (fun p => (insns (progItems p)).all (fun i =>
      match i with
      | .movRM _ m | .movMR m _ | .aluRM _ _ m | .aluMR _ m _ | .aluMI _ m _ | .lea _ m => m.ok
      | _ => true)) = true := by
  native_decide

end Evm.CL.X86Items
