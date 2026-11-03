/-
  JitChunkSnapshot.lean — `lake exe jitChunkSnapshot` dumps BOTH chunk
  lowerings for a fixture set: the clang-path text (`emitChunk`) and the
  in-process bytes (`assemble (emitChunkItems …)`).

  The two are deliberately NOT byte-identical — `b <sym>` is four bytes through
  the linker, while the in-process path has no linker and materialises an
  absolute address in twenty. So they cannot be diffed against each other; this
  is a GOLDEN snapshot instead, used to prove that making both paths share one
  body changes neither of them.
-/

import Evm.CL.ARM64.JIT
import Evm.IR.Compile

open Evm.CL.ARM64 Evm.CL.AsmEncode

def fixtures := JIT.fixtureCorpus

def hex (b : ByteArray) : String :=
  String.join (b.toList.map (fun x =>
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    if s.length == 1 then "0" ++ s else s))

def main : IO Unit := do
  let f : Evm.Fork := .cancun
  for (nm, bytes) in fixtures do
    let code : ByteArray := ⟨(bytes.map (fun n => UInt8.ofNat n)).toArray⟩
    match Evm.IR.compileProgram f code with
    | .error e => IO.println s!"=== {nm}: COMPILE ERROR {repr e}"
    | .ok prog =>
      for (_, c) in prog.chunks do
        IO.println s!"=== {nm}@{c.startPc} TEXT"
        IO.println (JIT.emitChunk f c)
        let (bs, rs) := Evm.CL.AsmEncode.assemble (JIT.emitChunkItems f c)
        IO.println s!"=== {nm}@{c.startPc} BYTES {hex bs}"
        IO.println s!"=== {nm}@{c.startPc} RELOCS {rs.length}"
        for r in rs do IO.println s!"    {r.sym} @{r.byteOff} {repr r.kind}"
