/- `lake exe emitLimbC > ../c/generated/limb_ops.h` — the native storage path's limb
   primitives (Evm.CL.LimbC), printed from the proved terms. -/
import Evm.CL.LimbC

def main : IO Unit := IO.print Evm.CL.LimbC.header
