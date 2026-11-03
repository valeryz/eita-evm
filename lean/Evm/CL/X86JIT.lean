/-
  Evm.CL.X86JIT — the chunk JIT at x86-64 (#238, stage 6).

  `ARM64.JIT.emitChunkGen` is one algorithm over a `ChunkOut` algebra; this is
  its x86-64 instance, at `List XItem`, and the loader image around it. The
  AInstr-producing pieces — the region flush (`emitRegionFlushT` at
  `x86Flush`), `setPc`, the gas gadgets — go through the handlers' own
  lowering (`OpInstrs.spScale`, then `X86Items.x86Items`), so a chunk is made
  of the same instruction forms the x86-64 Linux batteries already run.

  What differs from ARM64, and why:

  * **No NOS registers, no continuation register.** The right operand of a
    binary core is loaded into four temporaries (x15, x17, x16, x0 — rdx, rsi,
    rdi, rax); x14 (rcx) stays the address scratch, which `sbcsZr` also needs.
    An op site is `call [rip + Lsym_handler_f]` and the flat handler returns
    with `ret`; a terminator is the same call followed by `jmp Lx_sync`.
  * **Every external reference goes through an abs64 slot** (`QuadSym`), as the
    handlers' helper calls do: a mapped image may be anywhere relative to
    `libeita.so`, so there is no `rel32` reach to rely on. The fault symbols
    and `_eita_sync_and_ret` are reached through per-chunk trampolines
    (`Lx_oog: lea rax, [rip + Lsym__eita_oog]; jmp [rax]`); `rax` is dead on
    every path that takes one.
  * **The scratch frame is `32·n + 8` bytes**: the chunk runs at rsp ≡ 8 (mod
    16), like the interpreter's loop, so a helper call site inside the frame
    lands at ≡ 0 (SysV).
  * **The depth register is a byte offset** (`r13 = 32·sp`, `X86Run`), which
    `spScale` applies to every sp-derived immediate; the TOS cache is reloaded
    at a flush's end, there is no NOS cache to reload.

  The image is the ARM64 blob layout (`emitProgramImage`) with relocation kind
  5 = abs64, which the SBCL loader patches by writing eight bytes; the chunk
  runner at offset 0 is `X86Run`'s production prologue plus `jmp rsi`.
-/

import Evm.CL.ARM64.JIT
import Evm.CL.X86Items
import Evm.CL.X86Asm
import Evm.CL.X86Run
import Evm.CL.X86Alias
import Evm.CL.OpInstrs

namespace Evm.CL.X86JIT

open Evm.CL.AsmCore Evm.CL.ARM64.JIT Evm.CL.X86Items Evm.CL.X86Asm Evm.CL.X86Encode
open Evm.IR

/-- The handlers' x86-64 lowering, applied to a chunk piece. -/
def lowerX (l : List AInstr) : List XItem :=
  (l.flatMap Evm.CL.OpInstrs.spScale).flatMap x86Items

/-- The per-chunk trampolines: fault symbols and the exit (`AsmCore.trampLabel`). -/
abbrev trampLabel := AsmCore.trampLabel

def trampSyms : List String :=
  ["_eita_oog", "_eita_stack_underflow", "_eita_stack_overflow", "_eita_sync_and_ret"]

/-- The x86-64 flush target (see the module header). -/
def x86Flush : FlushTarget where
  rq := (.x15, .x17, .x16, .x0)
  movImm r v := [.movImm r v]
  spAddr r slot := [.addSp r (32 * slot)]
  frameOpen n := [.spSub (32 * n + 8)]
  frameClose n := [.spAdd (32 * n + 8)]
  far sym := [.bTramp sym]
  helperArgs := (.x3, .x2, .x1, .x14)
  call h := [.blSym h]
  storeWord s b := [.strOff s b 0]
  storeByte s b := [.strbOff s b 0]
  cacheReload :=
    [ .cmpImm .x23 1, .bcLbl .lt "8f", .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14,
      .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16, .label "8" ]

/-- The gas gadgets: `sub r15, n` sets CF on borrow, exactly `GInstr.denote`'s
    `n ≤ gas` test; the fault branch is a local jump to the trampoline. -/
def gasX86 : Evm.CL.ARM64.ChunkGas.GInstr → List AInstr
  | .charge n _   => [.subsImm .x22 .x22 n, .bcTramp .lo "_eita_oog"]
  | .handBack rem => [.movImm .x15 rem, .addReg .x22 .x22 .x15]
  | .retake rem _ => [.movImm .x15 rem, .subsReg .x22 .x22 .x15, .bcTramp .lo "_eita_oog"]

/-- The algebra. -/
def xOut : ChunkOut (List XItem) where
  nil      := []
  cat      := (· ++ ·)
  head id  := [.L (chunkSym id)]
  setPc n  := lowerX [.movImm .x21 n]
  gas g    := lowerX (gasX86 g)
  flush _ r := lowerX (emitRegionFlushT x86Flush r)
  adrCont _ := []
  label l  := [.L l]
  callSym sym := [.CallRip s!"Lsym_{sym}"]
  tailSym sym := [.CallRip s!"Lsym_{sym}", .Jmp "Lx_sync"]
  brCont   := [.Jmp "Lx_sync"]
  syncCont := []
  brk      := [.Jmp "Lx_oog"]

/-- The symbols a body calls through slots. -/
def slotSyms (its : List XItem) : List String :=
  (its.filterMap (fun i => match i with
    | .CallRip s => if s.startsWith "Lsym_" then some (s.drop 5).toString else none
    | _ => none)).eraseDups

/-- Trampolines, then one slot per referenced symbol. -/
def chunkTail (its : List XItem) : List XItem :=
  trampSyms.flatMap (fun s =>
    [XItem.L (trampLabel s), .LeaRip .rax s!"Lsym_{s}", .I (.jmpMem { base := .rax })]) ++
  (trampSyms ++ slotSyms its).eraseDups.flatMap (fun s => [XItem.L s!"Lsym_{s}", .QuadSym s])

/-- A chunk as items. -/
def emitChunkX86 (f : Evm.Fork) (c : Chunk) : List XItem :=
  let body := emitChunkGen xOut f c
  body ++ chunkTail body

/-- The same algorithm, keeping the AInstr pieces (for the alias gate). -/
def pieceOut : ChunkOut (List (List AInstr)) where
  nil := []
  cat := (· ++ ·)
  head _ := []
  setPc n := [[.movImm .x21 n]]
  gas g := [gasX86 g]
  flush _ r := [(emitRegionFlushT x86Flush r).flatMap Evm.CL.OpInstrs.spScale]
  adrCont _ := []
  label _ := []
  callSym _ := []
  tailSym _ := []
  brCont := []
  syncCont := []
  brk := []

def chunkPieces (f : Evm.Fork) (c : Chunk) : List (List AInstr) := emitChunkGen pieceOut f c

/-- `eita_run_chunk(state*, chunk_fn)`: the production prologue, then the chunk. -/
def runChunkProd : List XItem :=
  Evm.CL.X86Run.prologueBodyAt Evm.CL.X86Run.frameSpProd ++ [.I (.jmpReg .rsi)]

/-! ## The image -/

private def pushU64 (ba : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut b := ba
  for i in List.range 8 do
    b := b.push (UInt8.ofNat ((n >>> (8 * i)) % 256))
  return b

private def pad8 (ba : ByteArray) : ByteArray := Id.run do
  let mut b := ba
  while b.size % 8 != 0 do b := b.push 0
  return b

/-- `nop` padding to the next 16-byte boundary. -/
private def padNops (size : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate ((16 - size % 16) % 16) 0x90)

/-- Relocation kind 5: an abs64 slot (the ARM64 kinds are 0-4). -/
def relocAbs64 : Nat := 5

/-- The loader blob (layout as `ARM64.JIT.emitProgramImage`, parts concatenated
    once as there); an error if a chunk needs a reach-limited relocation,
    which by construction none does. -/
def emitProgramImageX86 (f : Evm.Fork) (p : Program) : Except String ByteArray := do
  let chunks := dedupByPc p.chunks
  let (rcBytes, rcRelocs) := assemble runChunkProd
  if !rcRelocs.isEmpty then throw "run_chunk has relocations"
  let mut parts : Array ByteArray := #[rcBytes, padNops rcBytes.size]
  let mut size := rcBytes.size + (padNops rcBytes.size).size
  let mut relocs : Array (Nat × String) := #[]
  let mut entries : Array (Nat × Nat) := #[]
  for (pc, c) in chunks do
    let base := size
    let (cb, cr) := assemble (emitChunkX86 f c)
    for r in cr do
      if r.kind != .abs64 then throw s!"chunk {pc}: rel32 relocation against {r.sym}"
      relocs := relocs.push (base + r.byteOff, r.sym)
    parts := parts.push cb
    parts := parts.push (padNops cb.size)
    size := size + cb.size + (padNops cb.size).size
    entries := entries.push (pc, base)
  let image := concatParts parts size
  let mut out := ByteArray.emptyWithCapacity (image.size + 64 + 16 * entries.size + 48 * relocs.size)
  out := pushU64 out 0x314A_4154_4945      -- "EITAJ1"
  out := pushU64 out image.size
  out := pushU64 out 0                      -- runChunkOff
  out := pushU64 out entries.size
  out := pushU64 out relocs.size
  out := pad8 (image.copySlice 0 out out.size image.size)
  for (pc, off) in entries do
    out := pushU64 out pc; out := pushU64 out off
  for (off, sym) in relocs do
    out := pushU64 out relocAbs64
    out := pushU64 out off
    out := pushU64 out sym.toUTF8.size
    out := pad8 (out ++ sym.toUTF8)
  return out

/-! ## Gates over the corpus -/

/-- Every chunk of the corpus lowers completely. -/
theorem x86_chunks_lower :
    (match corpusChunks with
     | some cs => cs.all (fun c => !(emitChunkX86 .cancun c).any isUnlowered)
     | none => false) = true := by native_decide

/-- …and needs only abs64 relocations. -/
theorem x86_chunks_only_abs64 :
    (match corpusChunks with
     | some cs => cs.all (fun c => (assemble (emitChunkX86 .cancun c)).2.all (·.kind == .abs64))
     | none => false) = true := by native_decide

/-- …and no piece stages two ARM names into one x86-64 home while both are
    live (`X86Alias`, the stage-5 register-aliasing gate). -/
theorem x86_chunks_no_alias :
    (match corpusChunks with
     | some cs => cs.all (fun c => (chunkPieces .cancun c).all (fun p => (Evm.CL.X86Alias.hazards p).isEmpty))
     | none => false) = true := by native_decide

/-- The run-chunk entry has no relocations. -/
theorem run_chunk_no_relocs : (assemble runChunkProd).2.isEmpty = true := by native_decide

end Evm.CL.X86JIT
