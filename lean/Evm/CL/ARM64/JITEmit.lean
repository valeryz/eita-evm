import Evm.CL.AsmEncode
/-!
# Evm.CL.ARM64.JITEmit — the `movz`/`movk` primitive of the byte path.

Once the mechanical `List Item` transcription of the chunk emitter (#235); the
chunk algebra is now written once as `AInstr` (`JIT.instrOut`, stage 4s) and
lowered through `AsmItems`, so only the immediate materialiser that `AsmItems`
itself uses remains here. -/
namespace Evm.CL.ARM64.JITEmit
open Evm.CL.AsmEncode Evm.CL.AsmEncode.Insn Evm.CL.AsmEncode.Item

/-- `movz`+`movk` sequence for a 64-bit immediate (matches `ARM64.movImm`). -/
def movImmI (rd : Nat) (v : Nat) : List Item :=
  I (movz rd (v % 65536) 0) ::
  ((List.range 3).filterMap (fun i =>
    let f := (v >>> (16 * (i+1))) % 65536
    if f > 0 then some (I (movk rd f (i+1))) else none))

end Evm.CL.ARM64.JITEmit
