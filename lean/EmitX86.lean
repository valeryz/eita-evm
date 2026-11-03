/-
  EmitX86.lean — `lake exe emitX86` writes the x86-64 lowering of every
  structured gadget, as an assembly file the system assembler can check.

  This is the oracle gate for `Evm.CL.Lowering`: the Lean side proves coverage
  (no «unlowered» marker) and spot-checks text, but only a real assembler knows
  whether an addressing mode is encodable. It found a scale-32 SIB address the
  proofs happily accepted.

  Output: stdout (caller redirects; see scripts/verify-x86-emit.sh).
-/

import Evm.CL.Lowering

open Evm.CL.AsmCore Evm.CL.Pressure Evm.CL.Lowering

/-- Each gadget as its own function, so a label collision or a stray fallthrough
    shows up as an assembler error rather than silently linking. -/
def gadgetUnits : List (String × List AInstr) :=
  [ ("memexpand", memExpandInstrs),
    ("memrange", memRangeInstrs 3 1 .x0 ".Lzero" ".Ldone"),
    ("keccakgas", keccakGasInstrs 30),
    ("copygas", copyGasInstrs 3),
    ("mcopygas", mcopyGasInstrs 3),
    ("extcodecopygas", extcodecopyGasInstrs) ]

def main : IO Unit := do
  IO.println ".text"
  IO.println ".intel_syntax noprefix"
  -- the gadgets branch to these on overflow / out-of-gas
  IO.println "_eita_oog:"
  IO.println "    ret"
  IO.println "_eita_static_violation:"
  IO.println "    ret"
  for (nm, p) in gadgetUnits do
    IO.println s!".globl _eita_x86_{nm}"
    IO.println s!"_eita_x86_{nm}:"
    IO.print (emitProg x86 p)
    IO.println "    ret"
