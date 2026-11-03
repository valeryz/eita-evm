/-
  Evm.CL.X86Dispatch — the x86-64 dispatch: an offset table, no relocations.

  Stage 4 of #238. ARM64 keeps the dispatch table's address in x25, loaded at
  entry through an absolute symbol the loader patches (`AbsSym
  _eita_dispatch_ptr`). Stage 0 noted x86-64 has no register to spare for it
  and would reach the table RIP-relatively. This is that, one step further:
  the table holds OFFSETS from the image's start rather than addresses, so a
  mapped image needs no relocation at all for its dispatch —

      lea  rcx, [rip + table]        ; the table, wherever the image landed
      mov  rdx, [rcx + rax*8]        ; the handler's offset
      lea  rsi, [rip + base]         ; the image's start, likewise
      add  rdx, rsi
      jmp  rdx

  which is five instructions, every one position-independent. The entries are
  `QuadOff` items, filled by the assembler from the labels' offsets
  (`table_entries_are_the_stub_offsets`), and the whole thing runs under
  Rosetta in `X86RunVectors` (`dispatch_0..3`).
-/

import Evm.CL.X86Asm

namespace Evm.CL.X86Dispatch

open Evm.CL.X86Encode Evm.CL.X86Items Evm.CL.X86Asm Evm.CL.Relax

/-- The dispatch sequence: index in `idx`, image start at label `base`, table
    at label `table`. Clobbers rcx, rdx, rsi. -/
def dispatch (idx : XReg) (base table : String) : List XItem :=
  [ .LeaRip .rcx table,
    .I (.movRM .rdx { base := .rcx, index := some idx, scale := 8 }),
    .LeaRip .rsi base,
    .I (.aluRR .add .rdx .rsi),
    .I (.jmpReg .rdx) ]

/-- A table of offsets for the given stub labels. -/
def table (lbl : String) (stubs : List String) : List XItem :=
  .L lbl :: stubs.map XItem.QuadOff

/-- A self-contained test image: dispatch on rdi over four stubs that return
    10, 20, 30, 40. -/
def demoStubs : List String := ["Ls0", "Ls1", "Ls2", "Ls3"]

def demo : List XItem :=
  [.L "Lbase"] ++ dispatch .rdi "Lbase" "Ltable" ++
  (demoStubs.zipIdx.flatMap (fun (l, k) =>
    [XItem.L l, .I (.movRI .rax (Int.ofNat (10 * (k + 1)))), .I .ret])) ++
  table "Ltable" demoStubs

/-- Read an 8-byte little-endian word out of the assembled image. -/
def readQuad (bs : ByteArray) (off : Nat) : Nat :=
  (List.range 8).foldr (fun k acc => acc * 256 + (bs.get! (off + k)).toNat) 0

/-- **The table entries are the stubs' offsets**: what the assembler filled in
    equals where the labels actually landed. -/
theorem table_entries_are_the_stub_offsets :
    let its := resolveLocals demo
    let lits := toLItems its
    let ch := layout lits
    let bs := (assemble demo).1
    let t := labelOffset lits ch "Ltable"
    (demoStubs.zipIdx.map (fun (_l, k) => readQuad bs (t + 8 * k)))
      = demoStubs.map (labelOffset lits ch) := by
  native_decide

/-- Nothing for a loader to patch. -/
theorem demo_has_no_relocations : (assemble demo).2 = [] := by native_decide

end Evm.CL.X86Dispatch
