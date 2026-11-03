/-
  Evm.CL.AsmItems — the second lowering of `AInstr`: machine code.

  Until now the two ARM64 output paths went through two different instruction
  vocabularies:

    AsmCore.AInstr  ──emitARM64──▶ text  ──clang, BUILD time──▶ c/handlers.S
    AsmEncode.Item  ──assemble───▶ bytes ──────RUN time───────▶ the code arena

  `AsmCore` carries all of stage 1's denotations, and never mentions `Item`;
  `JIT.lean` builds `Item` lists directly and never mentions `AsmCore`. So every
  gadget that appears in both paths was written twice, and the two copies could
  disagree — which is not hypothetical: `ARM64.ChunkGas` records that `retake`
  was written with a bare `sub`, no borrow check, on the `Item` side only. That
  was the second JIT gas bug, and it existed because there were two hand-written
  copies rather than one.

  `ChunkGas` fixed that case the right way — one denoted constructor (`GInstr`)
  with two lowerings (`.emit` and `.items`) — but only for the gas gadgets. This
  module generalises it to the whole instruction vocabulary:

      AInstr ──emitARM64──▶ String      (unchanged, byte-for-byte)
             ──items─────▶ List Item ──▶ bytes

  `Item` is not a rival to `AInstr`; it is the layer BELOW it, carrying labels,
  symbol branches and relocations — the things `Evm.CL.Relax` reasons about. So
  this is an added lowering, not a merge.

  The gate is `scripts/verify-asm-items.sh`: for every instruction in the
  structured gadget set, the bytes of `assemble (items i)` must equal what clang
  produces from `emitARM64 i`. That is the same differential check
  `verify-asm-encode.sh` runs over a battery of 100 instructions, but driven off
  the vocabulary, so it covers what the emitters actually emit rather than a
  sample.

  One addition was needed: `Insn` had no `clz`, so `AInstr.clzReg` had no byte
  form at all (the interpreter's text path has used it all along). Added to
  `AsmEncode` and gated like everything else.
-/

import Evm.CL.AsmCore
import Evm.CL.AsmEncode
import Evm.CL.ARM64.JITEmit
import Evm.CL.Pressure

namespace Evm.CL.AsmItems

open Evm.CL.AsmCore Evm.CL.AsmEncode Evm.CL.AsmEncode.Insn Evm.CL.AsmEncode.Item

/-- Register number behind a role. `AsmCore.Reg` is already the ARM64 register
    set, so this is just its index. -/
def regNum : Reg → Nat
  | .x0 => 0  | .x4 => 4   | .x6 => 6   | .x7 => 7
  | .x8 => 8  | .x9 => 9   | .x10 => 10 | .x11 => 11
  | .x12 => 12 | .x13 => 13 | .x14 => 14 | .x15 => 15
  | .x16 => 16 | .x17 => 17 | .x20 => 20 | .x22 => 22
  | .x23 => 23 | .x24 => 24
  | .x1 => 1 | .x2 => 2 | .x3 => 3
  | .x21 => 21 | .x26 => 26 | .x27 => 27 | .x5 => 5
  | .x19 => 19 | .x25 => 25 | .x28 => 28 | .x29 => 29 | .x30 => 30

def setcondArm : SetCond → Cond
  | .eq => .eq | .lo => .cc | .lt => .lt

def bcondArm : BCond → Cond
  | .lo => .cc | .hs => .cs | .hi => .hi | .ls => .ls | .eq => .eq | .ne => .ne | .lt => .lt

/-- `mov xd, #n`: one `movz` while it fits in 16 bits, otherwise the
    `movz`/`movk` chain the JIT already uses. The text path emits a single `mov`,
    which the assembler itself expands — so for values over 16 bits the two
    paths differ in INSTRUCTION COUNT, and the gate below restricts itself to
    the values the gadgets actually use. -/
def movImmItems (rd : Nat) (n : Nat) : List Item :=
  if n < 65536 then [I (movz rd n 0)] else Evm.CL.ARM64.JITEmit.movImmI rd n

/-- `some p` when `i = 2^p` with p < 64. -/
def log2Pow (i : Nat) : Option Nat :=
  (List.range 64).find? (fun p => 2 ^ p == i)

/-- `some k` when `i = 2^k − 1` with 1 ≤ k ≤ 63. -/
def maskBits (i : Nat) : Option Nat :=
  (List.range 63).find? (fun k => k ≥ 1 && 2 ^ k - 1 == i)

/-- The byte lowering. One arm per `AInstr` constructor, in the same order as
    `AInstr.emitARM64`, so the two can be read side by side. -/
def items : AInstr → List Item
  | .subImm d a i   => [I (addImm true false (regNum d) (regNum a) i false)]
  | .addImm d a i   => [I (addImm false false (regNum d) (regNum a) i false)]
  | .addLsl5 d a b  => [I (reg .add (regNum d) (regNum a) (regNum b) 5)]
  | .addLsl d a b sh => [I (reg .add (regNum d) (regNum a) (regNum b) sh)]
  | .addLsr d a b sh => [I (addLsrReg (regNum d) (regNum a) (regNum b) sh)]
  | .ldrOff d b o   => [I (ldr (regNum d) (regNum b) o)]
  | .ldrBase d b    => [I (ldr (regNum d) (regNum b) 0)]
  | .strOff s b o   => [I (str (regNum s) (regNum b) o)]
  | .ldpOff r1 r2 b o => [I (ldp (regNum r1) (regNum r2) (regNum b) (Int.ofNat o))]
  | .movImm d i     => movImmItems (regNum d) i
  | .orr3 d a b     => [I (reg .orr (regNum d) (regNum a) (regNum b) 0)]
  | .adds d a b     => [I (reg .adds (regNum d) (regNum a) (regNum b) 0)]
  | .addReg d a b   => [I (reg .add (regNum d) (regNum a) (regNum b) 0)]
  | .subReg d a b   => [I (reg .sub (regNum d) (regNum a) (regNum b) 0)]
  | .subsReg d a b  => [I (reg .subs (regNum d) (regNum a) (regNum b) 0)]
  -- `mul xd, xn, xm` is `madd xd, xn, xm, xzr`; 31 is XZR here.
  | .mulReg d a b   => [I (madd (regNum d) (regNum a) (regNum b) 31)]
  | .clzReg d a     => [I (clz (regNum d) (regNum a))]
  | .lsrImm d a sh  => [I (lsrImm (regNum d) (regNum a) sh)]
  | .lslImm d a sh  => [I (lslImm (regNum d) (regNum a) sh)]
  | .cmpReg a b     => [I (cmpReg (regNum a) (regNum b))]
  | .cselHi d a b   => [I (csel (regNum d) (regNum a) (regNum b) .hi)]
  | .label l        => [L l]
  | .bLbl l         => [B l]
  | .blsLbl l       => [Bc .ls l]
  | .cbzLbl r l     => [Cbz (regNum r) l]
  | .cbnzOog r      => [Cbnz (regNum r) "_eita_oog"]
  -- `lo` and `cc` are the same condition; `AsmEncode.Cond` spells it `cc`.
  | .bcsOog         => [Bc .cs "_eita_oog"]
  | .bhiOog         => [Bc .hi "_eita_oog"]
  | .bloOog         => [Bc .cc "_eita_oog"]
  | .cmpImm a i     => [I (cmpImm (regNum a) i)]
  | .bSym c sym     => [Bc (bcondArm c) sym]
  | .addsImm d a i  => [I (addImm false true (regNum d) (regNum a) i false)]
  | .rev d a        => [I (rev (regNum d) (regNum a))]
  | .movReg d a     => [I (movReg (regNum d) (regNum a))]
  | .stpOff r1 r2 b o => [I (stp (regNum r1) (regNum r2) (regNum b) (Int.ofNat o))]
  | .brCont         => [I (br 27)]
  | .adcs d a b     => [I (reg .adcs (regNum d) (regNum a) (regNum b) 0)]
  | .adc d a b      => [I (reg .adc (regNum d) (regNum a) (regNum b) 0)]
  | .sbcs d a b     => [I (reg .sbcs (regNum d) (regNum a) (regNum b) 0)]
  | .sbc d a b      => [I (reg .sbc (regNum d) (regNum a) (regNum b) 0)]
  | .and3 d a b     => [I (reg .and (regNum d) (regNum a) (regNum b) 0)]
  | .eor3 d a b     => [I (reg .eor (regNum d) (regNum a) (regNum b) 0)]
  | .subsImm d a i  => [I (addImm true true (regNum d) (regNum a) i false)]
  | .mvn d a        => [I (mvn (regNum d) (regNum a))]
  -- rd = 31 is XZR in the shifted-register forms
  | .subsZr a b     => [I (reg .subs 31 (regNum a) (regNum b) 0)]
  | .sbcsZr a b     => [I (reg .sbcs 31 (regNum a) (regNum b) 0)]
  | .cset d c       => [I (cset (regNum d) (setcondArm c))]
  | .ldrbReg d b i  => [I (ldrbReg (regNum d) (regNum b) (regNum i))]
  | .bcLbl c l      => [Bc (bcondArm c) l]
  -- `mov w, #0` zero-extends; the 64-bit movz is the same register state
  -- (the text path keeps the w form; this is the byte path only)
  | .movImmW d i    => if i < 65536 then [I (movzW (regNum d) i)] else movImmItems (regNum d) i
  -- 31 is SP in the immediate add/sub forms
  | .spSub n        => [I (addImm true false 31 31 n false)]
  | .spAdd n        => [I (addImm false false 31 31 n false)]
  | .stpFpLr        => [I (stpPre 29 30 31 (-16))]
  | .ldpFpLr        => [I (ldpPost 29 30 31 16)]
  | .addSp d n      => [I (addImm false false (regNum d) 31 n false)]
  | .ldrSp d o      => [I (ldr (regNum d) 31 o)]
  | .blSym sym      => [Bl sym]
  | .blr r          => [I (blr (regNum r))]
  | .bSymU sym      => [B sym]
  | .ldrbOff d b o  => [I (ldrb (regNum d) (regNum b) o)]
  | .strbOff s b o  => [I (strb (regNum s) (regNum b) o)]
  | .strbReg s b i  => [I (strbReg (regNum s) (regNum b) (regNum i))]
  | .cbnzSym r sym  => [Cbnz (regNum r) sym]
  -- the 64-bit compare: the operand was zero-extended by the byte load
  | .cmpImmWHex r i => [I (cmpImmW (regNum r) i)]
  -- the in-process form of adrp+add is the absolute materialisation
  | .loadSymAddr d sym => [AbsSym (regNum d) sym]
  | .brReg r        => [I (br (regNum r))]
  | .cselNe d a b   => [I (csel (regNum d) (regNum a) (regNum b) .ne)]
  -- the operand is a zero-extended byte, so the 64-bit test is the same test
  | .cbnzSymW r sym => [CbnzW (regNum r) sym]
  | .movzImm d i    => [I (movz (regNum d) i 0)]
  | .madd d a b c   => [I (madd (regNum d) (regNum a) (regNum b) (regNum c))]
  | .strZr b o      => [I (str 31 (regNum b) o)]          -- rt = 31 is XZR for str
  | .strWSp s o     => [I (strW (regNum s) 31 o)]
  | .strWzrSp o     => [I (strW 31 31 o)]
  | .stpZrSp o      => [I (stp 31 31 31 (Int.ofNat o))]
  | .stpSp r1 r2 o  => [I (stp (regNum r1) (regNum r2) 31 (Int.ofNat o))]
  | .strSp s o      => [I (str (regNum s) 31 o)]
  | .ldrWSp d o     => [I (ldrW (regNum d) 31 o)]
  | .cbzWLbl r l    => [CbzW (regNum r) l]
  -- logical immediates: only the low-ones masks 2^k − 1 occur; anything else
  -- is an unlowered instruction (raw 0 = udf #0, loud at the first execution)
  | .andImmHex d a i =>
      match maskBits i with
      | some k => [I (andMask (regNum d) (regNum a) k)]
      | none => [I (raw 0)]
  -- the frame: directives are text-only; a symbol label is a label; the
  -- Mach-O page/GOT pairs become an absolute-address materialisation
  -- (`AbsSym` = &sym; the GOT entry IS &sym, the @PAGE pair then loads *sym)
  | .global _ | .p2align2 => []
  | .symLabel s     => [L s]
  | .stpPreSp r1 r2 n => [I (stpPre (regNum r1) (regNum r2) 31 (-(Int.ofNat n)))]
  | .ldpPostSp r1 r2 n => [I (ldpPost (regNum r1) (regNum r2) 31 (Int.ofNat n))]
  | .ldpSp r1 r2 o  => [I (ldp (regNum r1) (regNum r2) 31 (Int.ofNat o))]
  | .movToSp r      => [I (addImm false false 31 (regNum r) 0 false)]
  | .movFromSp r    => [I (addImm false false (regNum r) 31 0 false)]
  | .ret            => [I ret]
  | .ldrLsl3 d b i  => [I (ldrReg (regNum d) (regNum b) (regNum i) true)]
  | .loadSymValue d s => [AbsSym (regNum d) s, I (ldr (regNum d) (regNum d) 0)]
  | .loadSymGotValue d s => [AbsSym (regNum d) s]
  -- the JIT chunk algebra
  | .movkImm d i hw => [I (movk (regNum d) i hw)]
  | .addSpReg r     => [I (addExtReg false (regNum r) 31 (regNum r))]
  | .spAddReg r     => [I (addExtReg false 31 31 (regNum r))]
  | .spSubReg r     => [I (addExtReg true 31 31 (regNum r))]
  | .adrLbl d l     => [Adr (regNum d) l]
  | .brk0           => [I (raw 0xD4200000)]
  | .strBase s b    => [I (str (regNum s) (regNum b) 0)]
  | .strbBase s b   => [I (strb (regNum s) (regNum b) 0)]
  | .bFar sym       => [BrSym sym]
  | .bTramp sym     => [BrSym sym]
  | .bcTramp c sym  => [Bc (bcondArm c) sym]
  | .blFar sym      => [BlSym sym]
  -- the gas routines, the program loop, the data tables (directives and data
  -- are text-only: the in-process image carries code)
  | .csel d a b c   => [I (csel (regNum d) (regNum a) (regNum b) (bcondArm c))]
  | .cselZrA d b c  => [I (csel (regNum d) 31 (regNum b) (bcondArm c))]
  | .cselZrB d a c  => [I (csel (regNum d) (regNum a) 31 (bcondArm c))]
  | .eorImm1 d a    => [I (eorMask (regNum d) (regNum a) 1)]
  | .tstImm r i     =>
      match log2Pow i with
      | some p => [I (tstBit (regNum r) p)]
      | none => [I (raw 0)]
  | .cbnzLbl r l    => [Cbnz (regNum r) l]
  | .cbnzWLbl r l   => [CbnzW (regNum r) l]
  | .blank | .textSection | .dataSection | .p2align3 | .quadSym _ | .quadPair _ _ _ | .commentLine _ => []
  | .csinvEqZr d a  => [I (csinv (regNum d) (regNum a) 31 .eq)]

/-- A whole gadget's machine code. -/
def progItems (p : List AInstr) : List Item := p.flatMap items

/-! ## Structural agreement between the two lowerings

The byte-level gate lives in `scripts/verify-asm-items.sh`, because only the
assembler can say what a mnemonic encodes to. These are the properties that can
be settled here, and they are the ones that would silently break a migration:
the two lowerings must agree about SIZE and about LABELS, or the text path and
the byte path lay code out differently and every branch offset drifts. -/

/-- Instruction count: one item per `AInstr`, except labels (zero bytes) and a
    wide `movImm` (a movz/movk chain). Over the gadget set, every instruction
    lowers to exactly one item. -/
theorem one_item_per_instruction :
    Evm.CL.Pressure.gadgetSet.all (fun p => p.all (fun i =>
      match i with
      | .label _ => (items i).length == 1      -- the `L` marker, 0 bytes
      | _ => (items i).length == 1)) = true := by
  native_decide

/-- Labels contribute no bytes, so the two paths agree on size. -/
theorem labels_are_weightless (l : String) :
    ((items (.label l)).map Item.width).sum = 0 := by
  simp [items, Item.width]

/-- A `movImm` lowers to instructions only — never a label — so it cannot
    perturb label positions however wide the immediate is. -/
theorem movImm_has_no_labels (rd n : Nat) :
    (movImmItems rd n).filterMap (fun it => match it with | .L l => some l | _ => none)
      = [] := by
  unfold movImmItems Evm.CL.ARM64.JITEmit.movImmI
  split
  · simp
  · apply List.filterMap_eq_nil_iff.mpr
    intro a ha
    simp only [List.mem_cons, List.mem_filterMap, List.mem_range] at ha
    rcases ha with rfl | ⟨i, _, hi⟩
    · rfl
    · split at hi
      · cases hi; rfl
      · exact absurd hi (by simp)

/-- The logical-immediate arm never produces a label, whichever way the mask
    test goes. -/
theorem andImm_has_no_labels (d a : Reg) (i : Nat) :
    (items (.andImmHex d a i)).filterMap (fun it => match it with | .L l => some l | _ => none) = [] := by
  simp only [items]; cases maskBits i <;> rfl

theorem tst_has_no_labels (r : Reg) (i : Nat) :
    (items (.tstImm r i)).filterMap (fun it => match it with | .L l => some l | _ => none) = [] := by
  simp only [items]; cases log2Pow i <;> rfl

/-- **Every label the text path defines, the byte path defines, in the same
    order** — which is what makes the two paths lay code out identically and
    every branch offset transfer. -/
theorem same_labels (p : List AInstr) :
    (p.filterMap (fun i => match i with | .label l | .symLabel l => some l | _ => none))
      = (progItems p).filterMap (fun it => match it with | .L l => some l | _ => none) := by
  induction p with
  | nil => rfl
  | cons i rest ih =>
    have hsplit : progItems (i :: rest) = items i ++ progItems rest := by
      simp [progItems]
    rw [hsplit, List.filterMap_append, ← ih]
    cases i
    -- the logical-immediate arm: whichever way the mask test goes, no label
    case andImmHex d a n => rw [andImm_has_no_labels]; simp
    case tstImm r n => rw [tst_has_no_labels]; simp
    case movImmW d n => simp only [items]; split <;> simp [movImm_has_no_labels]
    all_goals simp [items, movImm_has_no_labels]

/-- The gadget set's total code size in bytes, by the byte path — the number the
    code arena allocates and `Relax` lays out. -/
def gadgetBytes : Nat :=
  (Evm.CL.Pressure.gadgetSet.map (fun p =>
    ((progItems p).map Item.width).sum)).foldl (· + ·) 0

/-- 257 instructions at 4 bytes each, and labels free. The text path's own count
    (`Evm.CL.Lowering.arm64Insns = 257`, `insn_counts`) agrees, which is the size half
    of the two paths matching. (Pinned at 242 until 2026-10-25 while the gadget set had
    grown to 257: `lake build` does not reach this module, so only the
    `verify-asm-items.sh` gate saw it, and it failed silently.) -/
theorem gadget_bytes_match_instruction_count : gadgetBytes = 257 * 4 := by
  native_decide

/-! ## GNU numeric local labels, and the whole-gadget gate

`verify-asm-items.sh` pairs instructions one to one and SKIPS branch items, so
it never exercised a branch's target. The x86-64 side found what that hides
(`X86Asm`, stage 4a): the gadgets branch to `7f` — "the next `7:`" — and a
literal-name lookup finds no label called `7f`, so `AsmEncode.assemble` emits
the branch with a zero field and a relocation to a symbol `7f` that nothing
will ever define. The in-process ARM64 JIT path was never bitten only because
`JIT.lean` names its labels explicitly (`Lj_…`); the gadgets' byte lowering was
wrong for every numeric branch and no gate said so.

`resolveLocals` renames each numeric definition uniquely (`7@k`) and each
`7f`/`7b` reference to the definition it means, exactly as `X86Asm` does, and
`assembleGadget` applies it. `scripts/verify-asm-gadgets.sh` then assembles
every gadget whole — labels, branches, relocations — and compares against
clang targeting ELF, the x86-64 gate's twin. -/

open Evm.CL.AsmEncode in
def isNumeric (s : String) : Bool := s.length > 0 && s.all Char.isDigit

def localRef? (t : String) : Option (String × Bool) :=
  if t.length ≥ 2 then
    let n := (t.dropEnd 1).toString
    let d := t.back
    if isNumeric n then
      if d == 'f' then some (n, true) else if d == 'b' then some (n, false) else none
    else none
  else none

def resolveLocals (its : List Item) : List Item :=
  (its.foldl (fun (acc : List Item × List (String × Nat)) it =>
    let (out, counts) := acc
    let count := fun (n : String) => (counts.lookup n).getD 0
    let bump := fun (n : String) => (n, count n + 1) :: counts.filter (fun p => p.1 != n)
    let ref := fun (t : String) =>
      match localRef? t with
      | some (n, true)  => s!"{n}@{count n}"
      | some (n, false) => s!"{n}@{count n - 1}"
      | none => t
    match it with
    | .L n => if isNumeric n then (out ++ [.L s!"{n}@{count n}"], bump n) else (out ++ [it], counts)
    | .B t => (out ++ [.B (ref t)], counts)
    | .Bc c t => (out ++ [.Bc c (ref t)], counts)
    | .Cbz r t => (out ++ [.Cbz r (ref t)], counts)
    | .Cbnz r t => (out ++ [.Cbnz r (ref t)], counts)
    | .CbzW r t => (out ++ [.CbzW r (ref t)], counts)
    | .CbnzW r t => (out ++ [.CbnzW r (ref t)], counts)
    | .Adr r t => (out ++ [.Adr r (ref t)], counts)
    | _ => (out ++ [it], counts)) ([], [])).1

/-- Every LOCAL branch target names a defined label. External symbols
    (`_eita_…`) are not labels and are excluded. -/
def allTargetsDefined (its : List Item) : Bool :=
  let marks := its.filterMap (fun it => match it with | .L n => some n | _ => none)
  let isSym := fun (t : String) => t.startsWith "_"
  its.all (fun it => match it with
    | .B t | .Bc _ t | .Cbz _ t | .Cbnz _ t | .CbzW _ t | .CbnzW _ t | .Adr _ t => isSym t || marks.contains t
    | _ => true)

/-- The gadgets' byte lowering: resolve locals, then the existing assembler. -/
def assembleGadget (p : List AInstr) : ByteArray × List Reloc :=
  Evm.CL.AsmEncode.assemble (resolveLocals (progItems p))

def tag : Item → String
  | .L n => s!"L:{n}" | .B t => s!"b:{t}" | .Bc _ t => s!"bc:{t}"
  | .Cbz _ t => s!"cbz:{t}" | .Cbnz _ t => s!"cbnz:{t}"
  | .CbzW _ t => s!"cbz:{t}" | .CbnzW _ t => s!"cbnz:{t}" | _ => "·"

theorem numeric_locals_resolve :
    (resolveLocals [.L "7", .B "7b", .B "7f", .L "7"]).map tag
      = ["L:7@0", "b:7@0", "b:7@1", "L:7@1"] := by native_decide

/-- The bug, on record: before resolution the gadgets' branches had no defined
    target. -/
theorem gadget_targets_undefined_before_resolution :
    Evm.CL.Pressure.gadgetSet.any (fun p => !allTargetsDefined (progItems p)) = true := by
  native_decide

theorem gadget_targets_defined_after_resolution :
    Evm.CL.Pressure.gadgetSet.all (fun p => allTargetsDefined (resolveLocals (progItems p))) = true := by
  native_decide

/-- Resolution never changes the layout: labels are zero-width and renaming
    is width-preserving, so the gadget set is still 242 × 4 bytes. -/
theorem resolution_preserves_size :
    Evm.CL.Pressure.gadgetSet.all (fun p =>
      (assembleGadget p).1.size == ((progItems p).map Item.width).sum) = true := by
  native_decide

/-- Only the external symbol is left for the loader: every relocation the
    gadgets carry names `_eita_oog`, none a numeric label. -/
theorem only_oog_relocates :
    Evm.CL.Pressure.gadgetSet.all (fun p => (assembleGadget p).2.all (fun r => r.sym == "_eita_oog")) = true := by
  native_decide

end Evm.CL.AsmItems
