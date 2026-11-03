/-
  EmitARM64.lean — `lake exe emitARM64` writes the handlers assembly file.

  Output: stdout (caller redirects to `c/handlers.S`).
-/

import Evm.CL.ARM64.Interp

def main : IO Unit := IO.println Evm.CL.ARM64.Interp.emit
