/-
  Evm.CL.X86Asm — the x86-64 assembler: `XItem` lists to bytes, with branch
  relaxation.

  Stage 4 of #238. ARM64's `AsmEncode.assemble` is a single pass, because every
  instruction is four bytes and every branch has one form. x86-64 branches come
  in two widths — `7x rel8` (2 bytes) and `0F 8x rel32` (6) — so an offset
  depends on widths that depend on offsets. `Evm.CL.Relax` settled the
  algorithm abstractly (stage 2a: start all-short, widen what does not reach,
  never narrow, fuel = branch count); this is its first instantiation.

      XItem ──toLItem──▶ LItem ──Relax.layout──▶ Choice
                                                      │
      XItem ──emitWith (that Choice)──▶ bytes + relocations

  The displacement convention: x86 measures a relative branch from the END of
  the branch instruction. `Relax.fits` measures |target − start| against
  `reach`, so `rel8Reach` is 126 — conservative by one byte on the forward side
  — which guarantees −128 ≤ rel8 ≤ 127 in both directions once the instruction's
  own width is subtracted (`rel8_reach_is_sound`).

  External symbols (`_eita_oog`) are always the long form with a zero field and
  a relocation, as on ARM64's `BrSym`: the loader knows the distance, the
  assembler does not.

  Gate: `scripts/verify-x86-asm.sh` assembles every structured gadget — labels,
  local branches, symbol branches and all — and compares the WHOLE function's
  bytes against clang's. That is the x86-64 analogue of `verify-jit-emit.sh`,
  and it checks the relaxation choice too: clang's MC layer runs the same
  start-short-and-widen algorithm, so a branch we leave short that clang
  widens, or vice versa, shows up as a byte difference.
-/

import Evm.CL.X86Items
import Evm.CL.Relax

namespace Evm.CL.X86Asm

open Evm.CL.X86Encode Evm.CL.X86Items Evm.CL.Relax

inductive XRelocKind where
  | rel32   -- a branch displacement, relative to the end of the field
  | abs64   -- an 8-byte slot to be filled with the symbol's absolute address
  deriving Repr, DecidableEq

/-- A relocation the loader patches at `byteOff` against `sym`'s runtime
    address. Helper calls go through `abs64` slots (`QuadSym`), so an image's
    calls need no distance constraint and only one relocation kind. -/
structure XReloc where
  sym     : String
  byteOff : Nat
  kind    : XRelocKind := .rel32
  deriving Repr

def jccShortW : Nat := 2     -- 7x rel8
def jccLongW  : Nat := 6     -- 0F 8x rel32
def jmpShortW : Nat := 2     -- EB rel8
def jmpLongW  : Nat := 5     -- E9 rel32

/-- The short form's reach. x86 measures a displacement from the END of the
    branch instruction, while `Relax.fits` measures |target − position| from
    the item's own position — so each branch is laid out below as its short
    bytes FOLLOWED by a zero-short-width `br`: the relaxation point is then
    exactly the end of the short form, and the reach is the rel8 range itself.
    127 rather than 128 because one number serves both directions; the
    backward side is conservative by one byte. -/
def rel8Reach : Nat := 127

/-- The width-and-reach view the relaxation pass works on. A branch becomes two
    items: its short form's bytes, then a `br` of short width 0 and long width
    (long − short), positioned at the short form's end — see `rel8Reach`. -/
def toLItem : XItem → List LItem
  | .I i          => [.bytes (encode i).length]
  | .L n          => [.mark n]
  | .Jcc _ t      => [.bytes jccShortW, .br t 0 (jccLongW - jccShortW) rel8Reach]
  | .Jmp t        => [.bytes jmpShortW, .br t 0 (jmpLongW - jmpShortW) rel8Reach]
  | .JccSym _ _   => [.bytes jccLongW]
  | .JmpSym _     => [.bytes jmpLongW]
  | .LeaRip _ _   => [.bytes 7]
  | .LeaRipSym _ _ => [.bytes 7]
  | .QuadOff _    => [.bytes 8]
  | .Call _       => [.bytes 5]
  | .CallRip _    => [.bytes 6]
  | .QuadSym _    => [.bytes 8]
  | .unlowered _  => []

def toLItems (its : List XItem) : List LItem := its.flatMap toLItem

/-- Emit under a given choice (one bit per local branch, in order). -/
def emitWith (its : List XItem) (ch : Choice) : ByteArray × List XReloc := Id.run do
  let lits := toLItems its
  let mut out : ByteArray := ByteArray.empty
  let mut relocs : List XReloc := []
  let mut c := ch
  let mut pos : Nat := 0
  let put := fun (o : ByteArray) (bs : List UInt8) => o ++ ⟨bs.toArray⟩
  for it in its do
    match it with
    | .I i =>
        out := put out (encode i); pos := pos + (encode i).length
    | .L _ => pure ()
    | .Jcc cc t =>
        let isLong := c.headD false
        c := c.tail
        let tgt := labelOffset lits ch t
        if isLong then
          let d : Int := Int.ofNat tgt - Int.ofNat (pos + jccLongW)
          out := put out ([0x0F, UInt8.ofNat (0x80 + cc.code)] ++ imm32 d)
          pos := pos + jccLongW
        else
          let d : Int := Int.ofNat tgt - Int.ofNat (pos + jccShortW)
          out := put out ([UInt8.ofNat (0x70 + cc.code)] ++ imm8 d)
          pos := pos + jccShortW
    | .Jmp t =>
        let isLong := c.headD false
        c := c.tail
        let tgt := labelOffset lits ch t
        if isLong then
          let d : Int := Int.ofNat tgt - Int.ofNat (pos + jmpLongW)
          out := put out ([0xE9] ++ imm32 d)
          pos := pos + jmpLongW
        else
          let d : Int := Int.ofNat tgt - Int.ofNat (pos + jmpShortW)
          out := put out ([0xEB] ++ imm8 d)
          pos := pos + jmpShortW
    | .JccSym cc sym =>
        relocs := relocs ++ [⟨sym, pos + 2, .rel32⟩]
        out := put out ([0x0F, UInt8.ofNat (0x80 + cc.code)] ++ imm32 0)
        pos := pos + jccLongW
    | .JmpSym sym =>
        relocs := relocs ++ [⟨sym, pos + 1, .rel32⟩]
        out := put out ([0xE9] ++ imm32 0)
        pos := pos + jmpLongW
    | .LeaRip dst t =>
        -- REX.W 8D /r, mod=00 rm=101: [rip + disp32], disp from the END
        let d : Int := Int.ofNat (labelOffset lits ch t) - Int.ofNat (pos + 7)
        out := put out (rex true dst.hi false false :: 0x8D :: modrm 0 dst.lo 5 :: imm32 d)
        pos := pos + 7
    | .LeaRipSym dst sym =>
        relocs := relocs ++ [⟨sym, pos + 3, .rel32⟩]
        out := put out (rex true dst.hi false false :: 0x8D :: modrm 0 dst.lo 5 :: imm32 0)
        pos := pos + 7
    | .QuadOff t =>
        out := put out (imm64 (Int.ofNat (labelOffset lits ch t)))
        pos := pos + 8
    | .Call t =>
        let d : Int := Int.ofNat (labelOffset lits ch t) - Int.ofNat (pos + 5)
        out := put out (0xE8 :: imm32 d)
        pos := pos + 5
    | .CallRip slot =>
        -- FF /2 with mod=00 rm=101: [rip + disp32], disp from the END
        let d : Int := Int.ofNat (labelOffset lits ch slot) - Int.ofNat (pos + 6)
        out := put out (0xFF :: 0x15 :: imm32 d)
        pos := pos + 6
    | .QuadSym sym =>
        relocs := relocs ++ [⟨sym, pos, .abs64⟩]
        out := put out (imm64 0)
        pos := pos + 8
    | .unlowered _ => pure ()
  return (out, relocs)

/-! ## GNU numeric local labels

The gadgets use the assembler's numeric local labels: `7:` defines label 7 (any
number of times), `7f` refers to the NEXT definition after the reference and
`7b` to the PREVIOUS one. A lookup by literal name finds no mark called `7f`,
and `Relax.labelOffset` then answers 0 — so every such branch pointed back to
the start of the function. The whole-gadget gate caught it on its first run
(0/6, every displacement backward where clang's was forward).

`resolveLocals` renames each numeric definition to a unique name (`7@k` for
the k-th definition of 7) and each `7f`/`7b` reference to the definition it
means, so the plain lookup is right afterwards and `Relax` is untouched. -/

def isNumeric (s : String) : Bool := s.length > 0 && s.all Char.isDigit

/-- `some (n, forward?)` for a `Nf`/`Nb` reference. -/
def localRef? (t : String) : Option (String × Bool) :=
  if t.length ≥ 2 then
    let n := (t.dropEnd 1).toString
    let d := t.back
    if isNumeric n then
      if d == 'f' then some (n, true) else if d == 'b' then some (n, false) else none
    else none
  else none

def resolveLocals (its : List XItem) : List XItem :=
  (its.foldl (fun (acc : List XItem × List (String × Nat)) it =>
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
    | .Jcc c t => (out ++ [.Jcc c (ref t)], counts)
    | .Jmp t => (out ++ [.Jmp (ref t)], counts)
    | .LeaRip d t => (out ++ [.LeaRip d (ref t)], counts)
    | .QuadOff t => (out ++ [.QuadOff (ref t)], counts)
    | .Call t => (out ++ [.Call (ref t)], counts)
    | .CallRip t => (out ++ [.CallRip (ref t)], counts)
    | _ => (out ++ [it], counts)) ([], [])).1

/-- Every local branch target names a defined label after resolution. -/
def allTargetsDefined (its : List XItem) : Bool :=
  let marks := its.filterMap (fun it => match it with | .L n => some n | _ => none)
  its.all (fun it => match it with
    | .Jcc _ t | .Jmp t | .LeaRip _ t | .QuadOff t | .Call t | .CallRip t => marks.contains t
    | _ => true)

/-- Bind external symbols to local labels: a `JccSym` whose symbol is in the
    map becomes an ordinary local `Jcc`, relaxed and resolved like any other.
    This is how a test program links its own `_eita_oog` stub; the runtime
    leaves the map empty and lets the loader patch the relocation. -/
def resolveSyms (syms : List (String × String)) (its : List XItem) : List XItem :=
  its.map (fun it => match it with
    | .JccSym c sym => match syms.lookup sym with
        | some lbl => .Jcc c lbl
        | none => it
    | .JmpSym sym => match syms.lookup sym with
        | some lbl => .Jmp lbl
        | none => it
    | _ => it)

/-- The assembler: bind symbols, resolve local labels, relax, then emit. -/
def assembleWith (syms : List (String × String)) (its : List XItem) : ByteArray × List XReloc :=
  let its := resolveLocals (resolveSyms syms its)
  emitWith its (layout (toLItems its))

def assemble (its : List XItem) : ByteArray × List XReloc := assembleWith [] its

/-- With `_eita_oog` bound, nothing is left for the loader. -/
theorem bound_symbol_leaves_no_relocation :
    (assembleWith [("_eita_oog", "oog")] [.I .ret, .JccSym .b "_eita_oog", .L "oog", .I .ret]).2 = [] := by
  native_decide

/-- A forward and a backward reference to the same number resolve to different
    definitions — the two `7:`s around them. -/
def tag : XItem → String
  | .L n => s!"L:{n}" | .Jmp t => s!"jmp:{t}" | .Jcc _ t => s!"jcc:{t}" | _ => "·"

theorem numeric_locals_resolve :
    (resolveLocals [.L "7", .Jmp "7b", .Jmp "7f", .L "7"]).map tag
      = ["L:7@0", "jmp:7@0", "jmp:7@1", "L:7@1"] := by native_decide

/-- Before resolution the gadgets' branches had no defined target — which is
    the bug — and after it every one does. -/
theorem gadget_targets_undefined_before_resolution :
    Evm.CL.Pressure.gadgetSet.any (fun p => !allTargetsDefined (progItems p)) = true := by
  native_decide

theorem gadget_targets_defined_after_resolution :
    Evm.CL.Pressure.gadgetSet.all (fun p => allTargetsDefined (resolveLocals (progItems p))) = true := by
  native_decide

/-! ## Soundness of the reach constant -/

/-- The relaxation point is the short form's end, so "fits" is
    |target − end| ≤ 127, and the rel8 displacement `target − end` lies in
    [−128, 127] in both directions. -/
theorem rel8_reach_is_sound (end_ target : Nat)
    (h : (if target ≥ end_ then target - end_ else end_ - target) ≤ rel8Reach) :
    -128 ≤ ((target : Int) - (end_ : Int)) ∧ ((target : Int) - (end_ : Int)) ≤ 127 := by
  simp only [rel8Reach] at h
  split at h <;> omega

/-- A forward branch of exactly 127 stays short — the case the earlier
    start-measured reach of 126 widened and clang did not. -/
theorem forward_127_is_short :
    (assemble ([XItem.Jcc .e "L"] ++ (List.replicate 127 (XItem.I .ret)) ++ [.L "L"])).1.size
      = 2 + 127 := by native_decide

/-- …and 128 is widened. -/
theorem forward_128_is_widened :
    (assemble ([XItem.Jcc .e "L"] ++ (List.replicate 128 (XItem.I .ret)) ++ [.L "L"])).1.size
      = 6 + 128 := by native_decide

/-! ## Every branch in every gadget resolves

Checked, not assumed: under the layout the assembler picks, every short branch's
displacement is a legal rel8 and every long one a legal rel32. -/

/-- Walk the items under the final choice and check every local branch's
    displacement against its chosen form. -/
def branchesResolve (its₀ : List XItem) : Bool := Id.run do
  let its := resolveLocals its₀
  let lits := toLItems its
  let ch := layout lits
  let mut c := ch
  let mut pos : Nat := 0
  let mut ok := true
  for it in its do
    match it with
    | .I i => pos := pos + (encode i).length
    | .L _ => pure ()
    | .JccSym _ _ => pos := pos + jccLongW
    | .JmpSym _ => pos := pos + jmpLongW
    | .LeaRip _ _ | .LeaRipSym _ _ => pos := pos + 7
    | .QuadOff _ => pos := pos + 8
    | .Call _ => pos := pos + 5
    | .CallRip _ => pos := pos + 6
    | .QuadSym _ => pos := pos + 8
    | .unlowered _ => pure ()
    | .Jcc _ t | .Jmp t =>
        let isLong := c.headD false
        c := c.tail
        let w := match it with
          | .Jcc _ _ => if isLong then jccLongW else jccShortW
          | _ => if isLong then jmpLongW else jmpShortW
        let d : Int := Int.ofNat (labelOffset lits ch t) - Int.ofNat (pos + w)
        ok := ok && (if isLong then true else (-128 ≤ d && d ≤ 127))
        pos := pos + w
  return ok

theorem every_gadget_branch_resolves :
    Evm.CL.Pressure.gadgetSet.all (fun p => branchesResolve (progItems p)) = true := by
  native_decide

/-- The bytes the assembler emits are exactly as many as the layout says. -/
theorem assembled_size_is_layout_size :
    Evm.CL.Pressure.gadgetSet.all (fun p =>
      let its := resolveLocals (progItems p)
      (assemble its).1.size == size (toLItems its) (layout (toLItems its))) = true := by
  native_decide

/-! ## Relaxation is engaged, not vestigial -/

/-- A branch over two bytes stays short: 2-byte `jz`. -/
theorem near_branch_is_short :
    (assemble [.Jcc .e "L", .I .ret, .I .ret, .L "L"]).1.size = 2 + 2 := by native_decide

/-- A branch over 200 bytes of code is widened to the 6-byte form. The 200
    bytes are 100 `ret`s. -/
theorem far_branch_is_widened :
    (assemble ([XItem.Jcc .e "L"] ++ (List.replicate 200 (XItem.I .ret)) ++ [.L "L"])).1.size
      = 6 + 200 := by native_decide

/-- And the widened branch's displacement is the one the long form needs:
    200 from the end of a 6-byte instruction, little-endian. -/
theorem far_branch_bytes :
    ((assemble ([XItem.Jcc .e "L"] ++ (List.replicate 200 (XItem.I .ret)) ++ [.L "L"])).1.toList.take 6)
      = [0x0F, 0x84, 0xC8, 0x00, 0x00, 0x00] := by native_decide

/-- A symbol branch is always long, and recorded for the loader. -/
theorem symbol_branch_relocates :
    let r := assemble [.I .ret, .JccSym .b "_eita_oog"]
    r.1.size = 1 + 6 ∧ r.2.length = 1 ∧ (r.2.headD ⟨"", 0, .rel32⟩).byteOff = 3 := by native_decide

end Evm.CL.X86Asm
