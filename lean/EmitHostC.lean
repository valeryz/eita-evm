/- The host-layer gas formulas as freestanding C, for consumers with no Lisp:

     lake exe emitHostC            > ../c/generated/host.c
     lake exe emitHostC --header   > ../c/generated/host.h
     lake exe emitHostC --vectors  > ../c/test_host_gas.c

   The same `Evm.CL.GasEmit` terms `emitHostCL` prints as Common Lisp
   (src/generated/host.lisp), printed by `Evm.CL.GasEmitC` as C. One formula,
   owned by Lean, for both hosts. -/
import Evm.CL.GasEmitC

def main (args : List String) : IO UInt32 := do
  let out := if args.contains "--header" then Evm.CL.GasEmit.headerFile
             else if args.contains "--vectors" then Evm.CL.GasEmit.vectorsFile
             else Evm.CL.GasEmit.cFile
  match out with
  | .ok s   => IO.print s; pure 0
  | .error e => IO.eprintln e; pure 1
