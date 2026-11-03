/-
  EmitX86Interp.lean — `lake exe emitX86Interp [macho|elf]` writes the x86-64
  threaded interpreter (`Evm.CL.X86Interp`): Mach-O text for the clang gate on
  the Mac, ELF text for `libeita.so` on Linux/x86-64.
-/

import Evm.CL.X86Interp

def main (args : List String) : IO Unit := do
  match args with
  | ["elf"] => IO.print Evm.CL.X86Interp.emitELF
  | _       => IO.print Evm.CL.X86Interp.emitMachO
