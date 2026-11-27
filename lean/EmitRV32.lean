/-
  EmitRV32.lean — `lake exe emitRV32` writes the rv32imac lowering of every
  structured gadget, as an assembly file the RISC-V assembler can check.

  The oracle gate for `Evm.CL.RV32.Lower`, exactly as `EmitX86` is for the
  x86-64 lowering: Lean proves coverage (no «unlowered» marker) and spot-checks
  text, but only a real assembler knows whether what came out is rv32. On
  x86-64 that gate caught an unencodable addressing mode the proofs accepted.

  Output: stdout (see scripts/verify-rv32-emit.sh).
-/

import Evm.CL.RV32.Lower
import Evm.CL.RV32.Run

open Evm.CL.AsmCore Evm.CL.Pressure Evm.CL.RV32

/-- Each gadget as its own function, so a label collision or a stray
    fallthrough is an assembler error rather than a silent link. -/
def gadgetUnits : List (String × List AInstr) :=
  [ ("memexpand", memExpandInstrs),
    ("memrange", memRangeInstrs 3 1 .x0 ".Lzero" ".Ldone"),
    ("keccakgas", keccakGasInstrs 30),
    ("copygas", copyGasInstrs 3),
    ("mcopygas", mcopyGasInstrs 3),
    ("extcodecopygas", extcodecopyGasInstrs) ]

/-- A handler name as an assembler symbol. -/
def symOf (nm : String) : String :=
  String.join ((nm.toList.map (fun c =>
    if c.isAlphanum then c.toString.toLower else "_")))

/-- The whole threaded interpreter: the frame, the loop, the epilogue, the fault
    stubs, the fork tables, and every handler body that lowers. -/
def interpFile : IO Unit := do
  let mut body := Evm.CL.RV32.Run.emit
  let mut k := 0
  for (nm, p) in coveredHandlers do
    body := body ++ ".text\n" ++ s!".globl _eita_handler_{nm}\n" ++ ".p2align 2\n"
                 ++ s!"_eita_handler_{nm}:\n" ++ emitProgRV32From k p
    k := k + 2 * p.length + 2
  -- ELF spells the C symbols without the Mach-O underscore, and AsmCore's
  -- symbols carry it (`_eita_helper_mul`): the same rewrite `X86Interp.emitELF`
  -- applies for x86-64 Linux. Local labels (`.L…`) are untouched.
  IO.print (body.replace "_eita" "eita")
  -- an object without this note makes the linker assume an executable stack
  IO.println ".section .note.GNU-stack,\"\",@progbits"

/-- The gadget / handler harness: each unit its own function, with `ret` stubs
    standing in for the faults so the file assembles on its own. -/
def harnessFile (handlers : Bool) : IO Unit := do
  IO.println ".text"
  IO.println ".option nopic"
  IO.println "_eita_oog:"
  IO.println "    ret"
  IO.println "_eita_static_violation:"
  IO.println "    ret"
  let units := if handlers then coveredHandlers.map (fun (nm, p) => (symOf nm, p))
               else gadgetUnits
  let mut n := 0
  for (nm, p) in units do
    IO.println s!".globl _eita_rv32_{nm}"
    IO.println s!"_eita_rv32_{nm}:"
    IO.print (emitProgRV32From n p)
    IO.println "    ret"
    n := n + 2 * p.length + 2

def main (args : List String) : IO Unit := do
  if args.contains "--interp" then interpFile
  else harnessFile (args.contains "--handlers")
