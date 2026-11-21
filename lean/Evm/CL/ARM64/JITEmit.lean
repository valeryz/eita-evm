import Evm.CL.AsmEncode
/-!
# Evm.CL.ARM64.JITEmit — the `movz`/`movk` primitive of the byte path.

The chunk algebra is written once as `AInstr` (`JIT.instrOut`) and lowered
through `AsmItems`, so only the immediate materialiser that `AsmItems` itself
uses lives here. -/
namespace Evm.CL.ARM64.JITEmit
open Evm.CL.AsmEncode Evm.CL.AsmEncode.Insn Evm.CL.AsmEncode.Item

/-- `movz`+`movk` sequence for a 64-bit immediate (matches `AsmCore.movImmInstrs`). -/
def movImmI (rd : Nat) (v : Nat) : List Item :=
  I (movz rd (v % 65536) 0) ::
  ((List.range 3).filterMap (fun i =>
    let f := (v >>> (16 * (i+1))) % 65536
    if f > 0 then some (I (movk rd f (i+1))) else none))

end Evm.CL.ARM64.JITEmit
