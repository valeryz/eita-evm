/-
  AsmItemsVectors.lean — `lake exe asmItemsVectors` dumps, for every instruction
  in the structured gadget set, the BYTE lowering next to the TEXT lowering:

      <hex word>\t<asm text>

  `scripts/verify-asm-items.sh` assembles the text column with clang and
  requires the words to match. That is the differential check between
  `AsmCore.AInstr`'s two lowerings — the one thing that was missing while the
  interpreter's text path and the JIT's byte path were written independently.
-/

import Evm.CL.AsmItems
import Evm.CL.OpInstrs

open Evm.CL.AsmCore Evm.CL.AsmEncode Evm.CL.AsmItems

/-- A label-free instruction's single encoded word, plus its text. Branch and
    label items are skipped: their encoding depends on layout, which
    `verify-jit-emit.sh` already covers end to end. -/
def vectorOf (i : AInstr) : Option (UInt32 × String) :=
  match items i with
  | [Item.I ins] =>
      -- the text lowering carries indentation and a newline; strip both
      -- the text lowering carries indentation and a trailing newline; the
      -- indentation is fine for the assembler, the newline is not
      let t := (i.emitARM64).replace "\n" ""
      some (ins.encode, t)
  | _ => none

def main : IO Unit := do
  for p in Evm.CL.Pressure.gadgetSet ++ Evm.CL.OpInstrs.handlerBodies do
    for i in p do
      match vectorOf i with
      | some (w, t) => IO.println s!"{w.toNat}\t{t}"
      | none => pure ()
