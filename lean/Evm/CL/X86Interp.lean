/-
  Evm.CL.X86Interp — the x86-64 threaded interpreter, as one assembly file.

  Stage 4 of #238: the x86-64 twin of `ARM64.Interp.emit`. The same program
  registry (`Interp.handlerProgs`, `flatProgs`, `variantProgs`) is taken
  through `Op.instrsX86?` (`X86Handler.x86Body`) and the x86-64 text lowering;
  the frame is `X86Run`'s role-map prologue and epilogue with the production
  slot for the saved rsp; the dispatch is the ARM64 design (address tables
  per fork, a mutable `_eita_dispatch_ptr`, `_eita_set_fork`) printed with
  the same directive printers, because the table TEXT is target-neutral.

  The run loop is direct-threaded, like ARM64's (every handler ends `br x27`).
  x86-64 has no register to spare for the continuation, so it lives in the
  state: every dispatch-table handler's `brCont` is `nextItems` — fetch,
  pre-increment, `jmp [cont_table + op*8]` (`EvmState.cont_table`, offset
  600). `eita_run` picks the table once per frame (the fork's, or the trace
  table when `cb->trace_step` is set: the hook is off the per-op path); the
  callers that CALL one handler (`eita_run_one`, the JIT tier) install the
  return table. A terminator `jmp`s to `_eita_sync_and_ret`, which — like
  the fault stubs — first restores rsp from `EvmState.frame_sp` (offset 544).

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
def contOff : Int := Offset.contTable             -- 600: EvmState.cont_table

/-- Rename the local labels of an item list, so one template can be
    instantiated twice in a file. -/
def suffixItems (suf : String) : XItem → XItem
  | .L n        => .L (n ++ suf)
  | .Jcc c t    => .Jcc c (t ++ suf)
  | .Jmp t      => .Jmp (t ++ suf)
  | .LeaRip d t => .LeaRip d (t ++ suf)
  | i           => i

/-! ## The frame -/

/-- The continuation every interpreter handler ends with, in place of `ret`
    (direct threading, the x86 twin of ARM64's `br x27`): fetch the next
    opcode, pre-increment, jump through `EvmState.cont_table`. rax and rcx
    are scratch at a `brCont` (the old loop clobbered both after the `ret`).
    The table is the frame's choice: the fork table (`eita_run`), the trace
    table (`eita_run` with `cb->trace_step` set), or the return table
    (`eita_run_one`, the JIT tier), whose one entry undoes the pre-increment
    and returns to a caller that CALLED the handler. -/
def nextItems : List XItem :=
  [ .I (.movzxBM .rcx { base := .r14, index := some .rbp }),
    .I (.aluRI .add .rbp 1),
    .I (.movRM .rax { base := .rbx, disp := contOff }),
    .I (.jmpMem { base := .rax, index := some .rcx, scale := 8 }) ]

/-- The hook, called around a save of the TOS cache with (state, pc, gas,
    depth, opcode). Entered at the loop's rsp ≡ 8 (mod 16): four pushes keep
    that, one more word makes the call site ≡ 0. -/
def traceCall : List XItem :=
  [ .I (.movRM .rax { base := .rbx, disp := cbOff }),
    .I (.movRM .rax { base := .rax, disp := traceStepSlot }),
    .I (.push .r8), .I (.push .r9), .I (.push .r10), .I (.push .r11),
    .I (.aluRI .sub .rsp 8),
    .I (.movRR .rdi .rbx), .I (.movRR .rsi .rbp), .I (.movRR .rdx .r15),
    .I (.movRR .rcx .r13), .I (.shiftRI .shr .rcx 5),
    .I (.movzxBM .r8 { base := .r14, index := some .rbp }),
    .I (.callReg .rax),
    .I (.aluRI .add .rsp 8),
    .I (.pop .r11), .I (.pop .r10), .I (.pop .r9), .I (.pop .r8) ]

/-- `eita_run`'s loop start. The hook is decided once per frame, not per op:
    `cb->trace_step` set → the trace table, else the active fork's table. The
    handlers run one word below the loop's rsp, where the old loop's `call`
    put them, so their SysV alignment is unchanged. -/
def startLoop : List XItem :=
  [ .I (.aluRI .sub .rsp 8),
    .I (.movRM .rax { base := .rbx, disp := cbOff }),
    .I (.movRM .rax { base := .rax, disp := traceStepSlot }),
    .I (.aluRI .cmp .rax 0), .Jcc .ne "Lrun_traced",
    .LeaRipSym .rax "_eita_dispatch_ptr", .I (.movRM .rax { base := .rax }),
    .Jmp "Lrun_go",
    .L "Lrun_traced", .LeaRipSym .rax "_eita_trace_table",
    .L "Lrun_go", .I (.movMR { base := .rbx, disp := contOff } .rax) ] ++ nextItems

/-- `eita_trace_next`: every trace-table entry. Back to the loop's rsp and
    the opcode's pc, the hook, then the fork table's handler for it. -/
def traceNext : List XItem :=
  [ .I (.aluRI .add .rsp 8), .I (.aluRI .sub .rbp 1) ] ++ traceCall ++
  [ .I (.movzxBM .rcx { base := .r14, index := some .rbp }),
    .I (.aluRI .add .rbp 1),
    .LeaRipSym .rax "_eita_dispatch_ptr", .I (.movRM .rax { base := .rax }),
    .I (.movRM .rax { base := .rax, index := some .rcx, scale := 8 }),
    .I (.aluRI .sub .rsp 8),
    .I (.jmpReg .rax) ]

/-- `eita_cont_ret`: every return-table entry. Undo the continuation's
    pre-increment; return to the caller that CALLED the handler. -/
def contRet : List XItem := [ .I (.aluRI .sub .rbp 1), .I .ret ]

/-- `eita_run(state*)`: the production entry. -/
def run : List XItem := (prologueBodyAt fsp).map (suffixItems "_r") ++ startLoop

/-- `eita_run_one(state*, opcode)`: cache, pre-increment pc, dispatch the
    requested opcode once, exit. `rsi` (SysV arg 1) survives the prologue. -/
def runOne : List XItem :=
  (prologueBodyAt fsp).map (suffixItems "_1") ++
  [ .LeaRipSym .rax "_eita_cont_ret_table", .I (.movMR { base := .rbx, disp := contOff } .rax),
    .I (.aluRI .add .rbp 1),
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
    .LeaRipSym .rax "_eita_cont_ret_table", .I (.movMR { base := .rbx, disp := contOff } .rax),
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
    ("fault_stub", faultStub), ("set_fork", setFork), ("execute_program", executeProgram),
    ("trace_next", traceNext), ("cont_ret", contRet) ]

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

/-- The x86 text lowering with `brCont` as the threaded continuation
    (`nextItems`) instead of `ret`. -/
def x86Threaded : Evm.CL.Lowering.Target :=
  { Evm.CL.Lowering.x86 with
    name := "x86-64-threaded"
    emit := fun i => match i with
      | .brCont => text nextItems
      | i => Evm.CL.Lowering.x86.emit i }

/-- Dispatch-table handlers are threaded; the JIT tier's flat (`_f`) twins
    keep `ret`, since a chunk CALLS them. -/
def handlerText (nm suf : String) (p : Prog) : String :=
  let t := if suf.endsWith "_f" then Evm.CL.Lowering.x86 else x86Threaded
  globalFn s!"_eita_handler_{nm}" (Evm.CL.Lowering.emitProg t (handlerInstrs suf p))

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

/-- A continuation table: all 256 entries one stub. -/
def contTable (sym target : String) : String :=
  Frame.text ([ .dataSection, .global sym, .p2align3, .symLabel sym ] ++
    List.replicate 256 (Evm.CL.AsmCore.AInstr.quadSym target))

/-- The tables: the default table + `_eita_dispatch_ptr`, one named table per
    fork, the table of tables, the access-cost table. -/
def tablesText : String :=
  dispatchTable allHandlersP present ++
  String.join (tableForks.map fun (f, nm) =>
    dispatchTableNamed s!"_eita_dispatch_table_{nm}" (handlerSymbol f)) ++
  dispatchTableNamed "_eita_dispatch_table_osaka" (handlerSymbol .osaka) ++
  Frame.text forkTablesInstrs ++
  Frame.text SstoreGas.accessTableA ++
  contTable "_eita_trace_table" "_eita_trace_next" ++
  contTable "_eita_cont_ret_table" "_eita_cont_ret"

/-- The Mach-O text. -/
def emitMachO : String :=
  ".section __TEXT,__text,regular,pure_instructions\n.intel_syntax noprefix\n" ++
  globalFn "_eita_run_one" (text runOne) ++
  globalFn "_eita_run" (text run) ++
  globalFn "_eita_trace_next" (text traceNext) ++
  globalFn "_eita_cont_ret" (text contRet) ++
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
   "_eita_trace_next", "_eita_cont_ret", "_eita_trace_table", "_eita_cont_ret_table",
   "_eita_execute_program",
   "_eita_dispatch_table", "_eita_dispatch_ptr", "_eita_fork_tables", "_eita_access_costs",
   "_eita_dispatch_table_osaka"] ++
  faultSyms ++ (Evm.CL.X86CallGas.routines ++ Evm.CL.X86SstoreGas.routines).map Prod.fst ++
  handlerList.map (fun (n, _, _) => s!"_eita_handler_{n}") ++
  tableForks.map (fun (_, nm) => s!"_eita_dispatch_table_{nm}")

/-! ## The register-cached TOS stays coherent (x86-64)

The x86-64 counterpart of `ARM64.Interp.handler_stack_cache_coherent`: entered with
r8-r11 (x6-x9) = stack[sp-1], every threaded continuation (`brCont`) leaves them equal
to the top word for the sp it leaves (`cacheIncoherent … true`: sp in bytes, the SysV
caller-saved homes killed by a call, NOS not register-cached on x86-64). The threaded
tail (`nextItems`) reads only r14/rbp/rbx and writes rax, rcx and rbp, so it keeps
what the body left. -/

open Evm.CL.OpInstrs in
theorem x86_handler_tos_cache_coherent :
    handlerList.all (fun (_, suf, p) => (cacheIncoherent (handlerInstrs suf p) true).isEmpty) = true := by
  native_decide

open Evm.CL.OpInstrs in
/-- …and it rejects a TOS left stale: DIV's helper result reloaded into r8-r11 but its
    low half never stored to the top word. -/
theorem x86_tos_coherence_rejects_unstored_result :
    (match (handlerProgs opCost).lookup "div" with
     | some p => (cacheIncoherent ((handlerInstrs "" p).filter (· != .stpOff .x6 .x7 .x14 0)) true).isEmpty
     | none => true) = false := by
  native_decide

/-- The ELF text: the Makefile's rewrite for the aarch64 port, in Lean. -/
def emitELF : String :=
  let body := emitMachO.replace ".section __TEXT,__text,regular,pure_instructions" ".text"
  body.replace "_eita" "eita" ++
  String.join (definedSymbols.map (fun s => s!".protected {s.replace "_eita" "eita"}\n")) ++
  -- no executable stack (the linker assumes one for an object without this note)
  ".section .note.GNU-stack,\"\",@progbits\n"

end Evm.CL.X86Interp
