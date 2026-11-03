/-
  AsmGadgetVectors.lean — `lake exe asmGadgetVectors` dumps, per structured
  gadget, the bytes `AsmItems.assembleGadget` produces and the text
  `AInstr.emitARM64` produces, as blocks (`=== name`, hex, text lines).
  `scripts/verify-asm-gadgets.sh` assembles each block with clang targeting
  ELF and compares the whole function — the ARM64 twin of verify-x86-asm.sh.
-/

import Evm.CL.AsmItems

open Evm.CL.AsmCore Evm.CL.Pressure Evm.CL.AsmItems

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
    let (bs, _) := assembleGadget p
    IO.println s!"=== {nm}"
    IO.println (String.join (bs.toList.map hex2))
    IO.print (String.join (p.map AInstr.emitARM64))
