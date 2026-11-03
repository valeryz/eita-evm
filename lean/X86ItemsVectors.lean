/-
  X86ItemsVectors.lean — `lake exe x86ItemsVectors` pairs, for every
  instruction in the structured gadget set, the x86-64 BYTE lowering with the
  TEXT lowering:

      <hex bytes>\t<asm text line>

  `X86Items.lowerings_align` proves the two emit the same number of
  instructions per `AInstr`, so they pair one to one; the text comes from
  `Lowering.emitX86` (not from the encoder's own printer), so the script that
  assembles the text column and compares the bytes is checking the two
  lowerings AGAINST EACH OTHER, not the encoder against itself.
-/

import Evm.CL.X86Items
import Evm.CL.X86Handler

open Evm.CL.X86Encode Evm.CL.X86Items

def hex2 (b : UInt8) : String :=
  let s := String.ofList (Nat.toDigits 16 b.toNat)
  if s.length == 1 then "0" ++ s else s

def main : IO Unit := do
  for p in Evm.CL.Pressure.gadgetSet ++ Evm.CL.X86Handler.x86Bodies do
    for i in p do
      let bs := insns (x86Items i)
      let ts := textInsnLines i
      for (b, t) in bs.zip ts do
        IO.println s!"{String.join ((encode b).map hex2)}\t{t}"
