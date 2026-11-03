/-
  X86AsmVectors.lean — `lake exe x86AsmVectors` dumps, per structured gadget,
  the bytes `X86Asm.assemble` produces and the text `Lowering.emitX86`
  produces, as blocks:

      === <name>
      <hex bytes of the whole gadget>
      <text, one instruction or label per line>

  `scripts/verify-x86-asm.sh` assembles each block's text as its own function
  — with no local definition of `_eita_oog`, so symbol branches are rel32 with
  a relocation on both sides — and compares the whole function's bytes. Labels,
  local branches (and the width the relaxation pass chose for them), symbol
  branches: all of it, against clang.
-/

import Evm.CL.X86Asm
import Evm.CL.X86Interp
import Evm.CL.X86CallGas
import Evm.CL.X86SstoreGas
import Evm.CL.X86JIT

open Evm.CL.AsmCore Evm.CL.Pressure Evm.CL.X86Items Evm.CL.X86Asm

def hex2 (b : UInt8) : String :=
  let s := String.ofList (Nat.toDigits 16 b.toNat)
  if s.length == 1 then "0" ++ s else s

def named : List (String × List AInstr) :=
  [ ("memexpand", memExpandInstrs),
    ("memrange", memRangeInstrs 3 1 .x0 ".Lzero" ".Ldone"),
    ("keccakgas", keccakGasInstrs 30),
    ("copygas", copyGasInstrs 3),
    ("mcopygas", mcopyGasInstrs 3),
    ("extcodecopygas", extcodecopyGasInstrs) ]

def main : IO Unit := do
  for (nm, p) in named do
    let (bs, _) := assemble (progItems p)
    IO.println s!"=== {nm}"
    IO.println (String.join (bs.toList.map hex2))
    IO.print (Evm.CL.Lowering.emitProg Evm.CL.Lowering.x86 p)
  -- the x86-64 gas routines (X86CallGas): AInstr programs through the lowering
  for (nm, b) in Evm.CL.X86CallGas.routines ++ Evm.CL.X86SstoreGas.routines do
    let (bs, _) := assemble (progItems b)
    IO.println s!"=== gas{nm}"
    IO.println (String.join (bs.toList.map hex2))
    IO.print (Evm.CL.Lowering.emitProg Evm.CL.Lowering.x86 b)
  -- the x86-64 frame (X86Interp): items printed by X86Print, bytes by X86Asm
  for (nm, its) in Evm.CL.X86Interp.frameUnits do
    let (bs, _) := assemble (resolveLocals its)
    IO.println s!"=== frame_{nm}"
    IO.println (String.join (bs.toList.map hex2))
    IO.print (Evm.CL.X86Print.text its)
  -- the x86-64 chunk JIT (X86JIT) over the fixture corpus: items by X86Print,
  -- bytes by X86Asm; `.quad sym` slots are zero in both (relocated)
  match Evm.CL.ARM64.JIT.corpusChunks with
  | some cs =>
    let mut k := 0
    for c in cs do
      let its := Evm.CL.X86JIT.emitChunkX86 .cancun c
      let (bs, _) := assemble its
      IO.println s!"=== chunk{k}_pc{c.startPc}"
      IO.println (String.join (bs.toList.map hex2))
      IO.print (Evm.CL.X86Print.text its)
      k := k + 1
  | none => IO.println "=== corpus: COMPILE ERROR"
