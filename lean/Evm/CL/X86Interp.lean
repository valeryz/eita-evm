/-
  Evm.CL.X86Interp — the x86-64 threaded interpreter, as one assembly file.

  Stage 4 of #238: the x86-64 twin of `ARM64.Interp.emit`. The same program
  registry (`Interp.handlerProgs`, `flatProgs`, `variantProgs`) is taken
  through `Op.instrsX86?` (`X86Handler.x86Body`) and the x86-64 text lowering;
  the frame is `X86Run`'s role-map prologue and epilogue with the production
  slot for the saved rsp; the dispatch is the ARM64 design (address tables
  per fork, a mutable `_eita_dispatch_ptr`, `_eita_set_fork`) printed with
  the same directive printers, because the table TEXT is target-neutral.

  The run loop. ARM64 keeps a continuation register (x27 = `_eita_next`) and
  every handler ends `br x27`. x86-64 has no register to spare, so the frame
  CALLS each handler (`brCont` = `ret`) and the loop body is `_eita_next`'s
  job: the `trace_step` hook, fetch, pre-increment, dispatch. A terminator
  does not return: it `jmp`s to `_eita_sync_and_ret` with its return address
  still pushed, and `sync_and_ret` — like the fault stubs — first restores
  rsp from `EvmState.frame_sp` (offset 544, `c/evm_state.h`).

  `_eita_execute_program` (the JIT-tier dispatcher) is here too; the JIT
  entry `_eita_run_chunk` is per image (`X86JIT.runChunkProd`). The
  host-facing gas routines are here (`X86CallGas`, `X86SstoreGas`; proven in
  `X86CallGasSem`, `X86SstoreGasSem`).

  Two flavours of the same text: Mach-O (what `clang -arch x86_64` on the Mac
  assembles, the oracle gate) and ELF (what links into `libeita.so` on x86-64 Linux):
  `.text` for the section, `eita_*` for `_eita_*`, and `.protected` on every
  symbol this file defines, so RIP-relative and direct references to them are
  legal inside a shared object while they stay in `.dynsym` for `dlsym`.
-/

import Evm.CL.X86Print
import Evm.CL.X86Run
import Evm.CL.X86Handler
import Evm.CL.ARM64.Interp
import Evm.CL.ARM64.SstoreGas
import Evm.CL.Lowering
import Evm.CL.X86CallGas
import Evm.CL.X86SstoreGas

namespace Evm.CL.X86Interp

open Evm.CL.AsmCore Evm.CL.X86Encode Evm.CL.X86Items Evm.CL.X86Print Evm.CL.X86Run
open Evm.CL.ARM64 Evm.CL.ARM64.Interp

/-! ## EvmState / EvmCallbacks slots the frame touches -/

def fsp : Int := frameSpProd                       -- 544: EvmState.frame_sp
def frameSp : Mem := { base := .rbx, disp := fsp }
def cbOff : Int := 496                             -- EvmState.cb
def traceStepSlot : Int := 112                     -- EvmCallbacks.trace_step
def haltedOff : Int := 128
def revertedOff : Int := 129

/-- Rename the local labels of an item list, so one template can be
    instantiated twice in a file. -/
def suffixItems (suf : String) : XItem → XItem
  | .L n        => .L (n ++ suf)
  | .Jcc c t    => .Jcc c (t ++ suf)
  | .Jmp t      => .Jmp (t ++ suf)
  | .LeaRip d t => .LeaRip d (t ++ suf)
  | i           => i

/-! ## The frame -/

/-- `_eita_next` as the loop body: if `cb->trace_step` is set, call it with
    (state, pc, gas, depth, opcode) around a save of the TOS cache; then fetch,
    pre-increment, dispatch through the active fork's table, loop. The two
    `rsp` adjustments keep the SysV alignment: the loop runs at rsp ≡ 8 (mod
    16), four pushes keep that, one more word makes the call site ≡ 0. -/
def nextLoop : List XItem :=
  [ .L "Lnext",
    .I (.movRM .rax { base := .rbx, disp := cbOff }),
    .I (.movRM .rax { base := .rax, disp := traceStepSlot }),
    .I (.aluRI .cmp .rax 0), .Jcc .e "Lfetch",
    .I (.push .r8), .I (.push .r9), .I (.push .r10), .I (.push .r11),
    .I (.aluRI .sub .rsp 8),
    .I (.movRR .rdi .rbx), .I (.movRR .rsi .rbp), .I (.movRR .rdx .r15),
    .I (.movRR .rcx .r13), .I (.shiftRI .shr .rcx 5),
    .I (.movzxBM .r8 { base := .r14, index := some .rbp }),
    .I (.callReg .rax),
    .I (.aluRI .add .rsp 8),
    .I (.pop .r11), .I (.pop .r10), .I (.pop .r9), .I (.pop .r8),
    .L "Lfetch",
    .I (.movzxBM .rcx { base := .r14, index := some .rbp }),
    .I (.aluRI .add .rbp 1),
    .LeaRipSym .rax "_eita_dispatch_ptr", .I (.movRM .rax { base := .rax }),
    .I (.movRM .rax { base := .rax, index := some .rcx, scale := 8 }),
    .I (.callReg .rax),
    .Jmp "Lnext" ]

/-- `eita_run(state*)`: the production entry. -/
def run : List XItem := (prologueBodyAt fsp).map (suffixItems "_r") ++ nextLoop

/-- `eita_run_one(state*, opcode)`: cache, pre-increment pc, dispatch the
    requested opcode once, exit. `rsi` (SysV arg 1) survives the prologue. -/
def runOne : List XItem :=
  (prologueBodyAt fsp).map (suffixItems "_1") ++
  [ .I (.aluRI .add .rbp 1),
    .LeaRipSym .rax "_eita_dispatch_ptr", .I (.movRM .rax { base := .rax }),
    .I (.movRM .rax { base := .rax, index := some .rsi, scale := 8 }),
    .I (.callReg .rax),
    .JmpSym "_eita_sync_and_ret" ]

/-- `eita_sync_and_ret`: unwind to the frame, write the caches back, return. -/
def syncAndRetProd : List XItem := .I (.movRM .rsp frameSp) :: syncAndRet

/-- A fault stub: unwind, gas = 0, halted = reverted = 1, exit. -/
def faultStub : List XItem :=
  [ .I (.movRM .rsp frameSp), .I (.movRI .r15 0), .I (.movRI .rax 1),
    .I (.movMR8 { base := .rbx, disp := haltedOff } .rax),
    .I (.movMR8 { base := .rbx, disp := revertedOff } .rax),
    .JmpSym "_eita_sync_and_ret" ]

def faultSyms : List String :=
  ["_eita_oog", "_eita_stack_overflow", "_eita_stack_underflow", "_eita_static_violation"]

/-- `eita_set_fork(ord)`: `_eita_dispatch_ptr := _eita_fork_tables[min ord 21]`
    (21 = amsterdam; `ARM64.Interp.forkTablesInstrs` is the table). -/
def setFork : List XItem :=
  [ .I (.movRI .rax 21), .I (.aluRR .cmp .rdi .rax), .I (.cmovRR .be .rax .rdi),
    .LeaRipSym .rcx "_eita_fork_tables",
    .I (.movRM .rax { base := .rcx, index := some .rax, scale := 8 }),
    .LeaRipSym .rcx "_eita_dispatch_ptr", .I (.movMR { base := .rcx } .rax),
    .I .ret ]

/-- `eita_execute_program(state*, entries, run_chunk, fuel)` — the native
    binding of `IR.executeProgram` (`ARM64.RunProgram`), SysV: rdi, rsi, rdx,
    rcx. Loop: halted → 0; fuel out → 2; look the pc up in the pc-indexed
    dispatch table `{n; fn[n]}` (0 = no chunk; pc ≥ n or 0 → miss → 1; the
    table the loader builds, `RunProgramDenote.build`); call
    `run_chunk(state, fn)`. The manifest
    and the runner live in r12/r13 (SIB-encoded bases, never a zero-disp rbp);
    four pushes and one word keep the call site at rsp ≡ 0 (mod 16). -/
def executeProgram : List XItem :=
  [ .I (.push .rbx), .I (.push .rbp), .I (.push .r12), .I (.push .r13), .I (.aluRI .sub .rsp 8),
    .I (.movRR .rbx .rdi), .I (.movRR .r12 .rsi), .I (.movRR .r13 .rdx), .I (.movRR .rbp .rcx),
    .L "Lrp_loop",
    .I (.movzxBM .rax { base := .rbx, disp := haltedOff }), .I (.aluRI .cmp .rax 0), .Jcc .ne "Lrp_halted",
    .I (.aluRI .cmp .rbp 0), .Jcc .e "Lrp_fuel",
    .I (.aluRI .sub .rbp 1),
    .I (.movRM .rax { base := .rbx }),                      -- pc
    .I (.aluRM .cmp .rax { base := .r12 }), .Jcc .ae "Lrp_miss",   -- pc past the table
    .I (.movRM .rsi { base := .r12, index := some .rax, scale := 8, disp := 8 }),  -- fn[pc]
    .I (.aluRI .cmp .rsi 0), .Jcc .e "Lrp_miss",           -- no chunk starts at pc
    .I (.movRR .rdi .rbx), .I (.callReg .r13),
    .Jmp "Lrp_loop",
    .L "Lrp_halted", .I (.movRI .rax 0), .Jmp "Lrp_ret",
    .L "Lrp_miss",   .I (.movRI .rax 1), .Jmp "Lrp_ret",
    .L "Lrp_fuel",   .I (.movRI .rax 2),
    .L "Lrp_ret",
    .I (.aluRI .add .rsp 8), .I (.pop .r13), .I (.pop .r12), .I (.pop .rbp), .I (.pop .rbx), .I .ret ]

/-- The frame units, for the byte-vs-assembler gate. -/
def frameUnits : List (String × List XItem) :=
  [ ("run", run), ("run_one", runOne), ("sync_and_ret", syncAndRetProd),
    ("fault_stub", faultStub), ("set_fork", setFork), ("execute_program", executeProgram) ]

/-! ## Text -/

def globalFn (sym : String) (body : String) : String :=
  s!".globl {sym}\n.p2align 4\n{sym}:\n" ++ body ++ "\n"

/-- A handler: the registry body through `Op.instrsX86?`, named labels
    suffixed for the twin it links as. -/
def handlerInstrs (suf : String) (p : Prog) : List AInstr :=
  (Evm.CL.X86Handler.x86Body p).map (Evm.CL.OpInstrs.suffixLabels suf)

/-- Every handler the file defines: (name, suffix, body). -/
def handlerList : List (String × String × Prog) :=
  (handlerProgs opCost).map (fun (n, p) => (n, "", p)) ++ flatProgs ++ variantProgs

def handlerText (nm suf : String) (p : Prog) : String :=
  globalFn s!"_eita_handler_{nm}" (Evm.CL.Lowering.emitProg Evm.CL.Lowering.x86 (handlerInstrs suf p))

/-- The helper symbols every body calls, once each: the abs64 slots
    `call qword ptr [rip + Lsym_sym]` reads. -/
def helperSlots : List String :=
  (handlerList.flatMap (fun (_, suf, p) =>
    Evm.CL.X86Handler.helperSyms (handlerInstrs suf p))).eraseDups

def slotsText : String :=
  ".data\n.p2align 3\n" ++
  String.join (helperSlots.map (fun s => s!"Lsym_{s}:\n    .quad   {s}\n"))

/-- Which registry ops the default (Cancun) table routes to a real handler. -/
def present (nm : String) : Bool := handlerSymbol interpFork nm != "_eita_handler_invalid"

/-- The tables: the default table + `_eita_dispatch_ptr`, one named table per
    fork, the table of tables, the access-cost table. -/
def tablesText : String :=
  dispatchTable allHandlersP present ++
  String.join (tableForks.map fun (f, nm) =>
    dispatchTableNamed s!"_eita_dispatch_table_{nm}" (handlerSymbol f)) ++
  dispatchTableNamed "_eita_dispatch_table_osaka" (handlerSymbol .osaka) ++
  Frame.text forkTablesInstrs ++
  Frame.text SstoreGas.accessTableA

/-- The Mach-O text. -/
def emitMachO : String :=
  ".section __TEXT,__text,regular,pure_instructions\n.intel_syntax noprefix\n" ++
  globalFn "_eita_run_one" (text runOne) ++
  globalFn "_eita_run" (text run) ++
  globalFn "_eita_sync_and_ret" (text syncAndRetProd) ++
  String.join (faultSyms.map (fun s => globalFn s (text faultStub))) ++
  globalFn "_eita_invalid_jump" "    jmp   _eita_oog\n" ++
  String.join (handlerList.map (fun (n, suf, p) => handlerText n suf p)) ++
  globalFn "_eita_set_fork" (text setFork) ++
  globalFn "_eita_execute_program" (text executeProgram) ++
  String.join ((Evm.CL.X86CallGas.routines ++ Evm.CL.X86SstoreGas.routines).map (fun (sym, b) =>
    globalFn sym (Evm.CL.Lowering.emitProg Evm.CL.Lowering.x86 b))) ++
  slotsText ++ tablesText

/-- Every symbol the file defines, for `.protected`. -/
def definedSymbols : List String :=
  ["_eita_run_one", "_eita_run", "_eita_sync_and_ret", "_eita_invalid_jump", "_eita_set_fork",
   "_eita_execute_program",
   "_eita_dispatch_table", "_eita_dispatch_ptr", "_eita_fork_tables", "_eita_access_costs",
   "_eita_dispatch_table_osaka"] ++
  faultSyms ++ (Evm.CL.X86CallGas.routines ++ Evm.CL.X86SstoreGas.routines).map Prod.fst ++
  handlerList.map (fun (n, _, _) => s!"_eita_handler_{n}") ++
  tableForks.map (fun (_, nm) => s!"_eita_dispatch_table_{nm}")

/-- The ELF text: the Makefile's rewrite for the aarch64 port, in Lean. -/
def emitELF : String :=
  let body := emitMachO.replace ".section __TEXT,__text,regular,pure_instructions" ".text"
  body.replace "_eita" "eita" ++
  String.join (definedSymbols.map (fun s => s!".protected {s.replace "_eita" "eita"}\n")) ++
  -- no executable stack (the linker assumes one for an object without this note)
  ".section .note.GNU-stack,\"\",@progbits\n"

end Evm.CL.X86Interp
