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

def main (args : List String) : IO Unit := do
  IO.println ".text"
  IO.println ".option nopic"
  -- the gadgets branch to these on overflow / out-of-gas
  IO.println "_eita_oog:"
  IO.println "    ret"
  IO.println "_eita_static_violation:"
  IO.println "    ret"
  -- one label counter for the whole file: the fused sequences emit local labels
  let units := if args.contains "--handlers" then
                 coveredHandlers.map (fun (nm, p) => (symOf nm, p))
               else gadgetUnits
  let mut n := 0
  for (nm, p) in units do
    IO.println s!".globl _eita_rv32_{nm}"
    IO.println s!"_eita_rv32_{nm}:"
    IO.print (emitProgRV32From n p)
    IO.println "    ret"
    -- one label space for the whole file: each instruction may emit up to two
    n := n + 2 * p.length + 2
