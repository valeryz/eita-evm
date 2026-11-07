/- `lake exe emitStorageC > ../c/generated/storage_effect.c` — the native storage path's
   effect functions, printed from the effect IR (Evm.CL.EffectC). -/
import Evm.CL.EffectC

def main : IO UInt32 := do
  match Evm.CL.EffectC.file with
  | .ok s => IO.print s; pure 0
  | .error e => IO.eprintln e; pure 1
