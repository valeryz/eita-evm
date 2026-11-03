/-
  Evm.CL.Frame — the ARM64 runtime scaffolding as `AInstr` programs: the two
  entry trampolines (`_eita_run_one`, `_eita_run`), the production dispatcher
  (`_eita_next`), the exit (`_eita_sync_and_ret`), the fault stubs, the JIT's
  chunk entry (`_eita_run_chunk`) and its continuation load.

  Stage 4r of #238. Until now these were the last assembly in the tree written
  as STRINGS (`Evm/CL/ARM64.lean`, `Evm/CL/ARM64/JIT.lean`), and the JIT's
  byte path re-wrote `_eita_run_chunk` a second time as `Item`s — the
  text/bytes duplication the handler work retired. Each program here is gated
  text-identical against the string it replaces (the string stays as the
  specification) and, for the JIT entry, bytes-identical against the
  hand-written item list; the emitters then print the program.

  Two forms carry the only genuine per-path difference: the Mach-O
  `@PAGE`/`@GOTPAGE` pairs the linker resolves become an absolute-address
  materialisation (`AbsSym`) in the in-process byte path — see `AsmItems`.
-/

import Evm.CL.AsmCore

namespace Evm.CL.Frame

open Evm.CL.AsmCore

/-- `.global sym` / `.p2align 2` / `sym:` — a function's header. -/
def header (sym : String) : List AInstr := [.global sym, .p2align2, .symLabel sym]

/-- Save x29/x30 and x19–x28 in a 96-byte frame. -/
def saveCalleeSaved : List AInstr :=
  [ .stpPreSp .x29 .x30 96, .stpSp .x19 .x20 16, .stpSp .x21 .x22 32,
    .stpSp .x23 .x24 48, .stpSp .x25 .x26 64, .stpSp .x27 .x28 80 ]

/-- The mirror image, then return. -/
def restoreCalleeSavedRet : List AInstr :=
  [ .ldpSp .x27 .x28 80, .ldpSp .x25 .x26 64, .ldpSp .x23 .x24 48,
    .ldpSp .x21 .x22 32, .ldpSp .x19 .x20 16, .ldpPostSp .x29 .x30 96, .ret ]

/-- Cache the state (x0) into the register file: pc, gas, sp, stack base,
    code base. -/
def cacheState : List AInstr :=
  [ .movReg .x20 .x0, .ldrOff .x21 .x0 0, .ldrOff .x22 .x0 8, .ldrOff .x23 .x0 16,
    .ldrOff .x24 .x0 32, .ldrOff .x26 .x0 64 ]

/-- Load TOS (if sp ≥ 1) and NOS (if sp ≥ 2) into the caches, through the two
    numeric labels the caller names. -/
def loadCaches (l1 l2 : String) : List AInstr :=
  [ .cmpImm .x23 1, .bcLbl .lt (l1 ++ "f"), .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14,
    .ldpOff .x6 .x7 .x14 0, .ldpOff .x8 .x9 .x14 16, .label l1,
    .cmpImm .x23 2, .bcLbl .lt (l2 ++ "f"), .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14,
    .ldpOff .x10 .x11 .x14 0, .ldpOff .x12 .x13 .x14 16, .label l2 ]

/-- Write the caches back (same guards, `stp` for `ldp`). -/
def storeCaches (l1 l2 : String) : List AInstr :=
  [ .cmpImm .x23 1, .bcLbl .lt (l1 ++ "f"), .subImm .x14 .x23 1, .addLsl5 .x14 .x24 .x14,
    .stpOff .x6 .x7 .x14 0, .stpOff .x8 .x9 .x14 16, .label l1,
    .cmpImm .x23 2, .bcLbl .lt (l2 ++ "f"), .subImm .x14 .x23 2, .addLsl5 .x14 .x24 .x14,
    .stpOff .x10 .x11 .x14 0, .stpOff .x12 .x13 .x14 16, .label l2 ]

/-- `eita_run_one(state*, opcode_byte)`: cache, pre-increment pc, continuation =
    sync_and_ret, dispatch the requested opcode through the active fork's
    table. -/
def runOne : List AInstr :=
  header "_eita_run_one" ++ saveCalleeSaved ++ cacheState ++ loadCaches "1" "2" ++
  [ .addImm .x21 .x21 1,
    .loadSymAddr .x27 "_eita_sync_and_ret",
    .loadSymValue .x25 "_eita_dispatch_ptr",
    .ldrLsl3 .x14 .x25 .x1, .brReg .x14 ]

/-- `eita_run(state*)`: the production entry. Stashes the post-prologue sp in
    x28 for the fault stubs, continuation = next, fetches and dispatches. -/
def run : List AInstr :=
  header "_eita_run" ++ saveCalleeSaved ++ [ .movFromSp .x28 ] ++ cacheState ++
  loadCaches "10" "11" ++
  [ .loadSymAddr .x27 "_eita_next",
    .loadSymValue .x25 "_eita_dispatch_ptr",
    .ldrbReg .x14 .x26 .x21, .addImm .x21 .x21 1, .ldrLsl3 .x14 .x25 .x14, .brReg .x14 ]

/-- `next`: the production continuation. If `cb->trace_step` (slot 112) is set,
    call it with (state, pc, gas, sp, opcode) around a save of the caches;
    then fetch, pre-increment, dispatch. -/
def next : List AInstr :=
  header "_eita_next" ++
  [ .ldrOff .x14 .x20 496, .ldrOff .x14 .x14 112, .cbzLbl .x14 "1f",
    .stpPreSp .x29 .x30 96, .stpSp .x6 .x7 16, .stpSp .x8 .x9 32, .stpSp .x10 .x11 48, .stpSp .x12 .x13 64,
    .movReg .x0 .x20, .movReg .x1 .x21, .movReg .x2 .x22, .movReg .x3 .x23, .ldrbReg .x4 .x26 .x21,
    .blr .x14,
    .ldpSp .x6 .x7 16, .ldpSp .x8 .x9 32, .ldpSp .x10 .x11 48, .ldpSp .x12 .x13 64, .ldpPostSp .x29 .x30 96,
    .label "1",
    .ldrbReg .x14 .x26 .x21, .addImm .x21 .x21 1, .ldrLsl3 .x14 .x25 .x14, .brReg .x14 ]

/-- `sync_and_ret`: pc/gas/sp back to the state, caches back to the stack,
    restore, return. -/
def syncAndRet : List AInstr :=
  header "_eita_sync_and_ret" ++
  [ .strOff .x21 .x20 0, .strOff .x22 .x20 8, .strOff .x23 .x20 16 ] ++
  storeCaches "3" "4" ++ restoreCalleeSavedRet

/-- A fault stub: restore sp from x28 (handlers may have scratch frames open),
    gas = 0, halted = reverted = 1, exit through sync_and_ret. -/
def faultStub (sym : String) : List AInstr :=
  header sym ++
  [ .movToSp .x28, .movImm .x22 0, .movImmW .x14 1,
    .strbOff .x14 .x20 128, .strbOff .x14 .x20 129,
    .loadSymAddr .x27 "_eita_sync_and_ret", .brCont ]

def faultSyms : List String :=
  ["_eita_oog", "_eita_stack_overflow", "_eita_stack_underflow", "_eita_static_violation"]

def faultStubs : List AInstr := faultSyms.flatMap faultStub

/-- An invalid jump is an OOG. -/
def invalidJump : List AInstr := header "_eita_invalid_jump" ++ [ .bSymU "_eita_oog" ]

/-- A handler's header. -/
def handlerHeader (name : String) : List AInstr := header s!"_eita_handler_{name}"

/-! ## The JIT's entry and continuation -/

/-- `eita_run_chunk(state*, chunk_fn)`: the `eita_run` prologue, then enter the
    chunk (x1). Cross-image, so the dispatch pointer comes through the GOT. -/
def runChunk : List AInstr :=
  header "_eita_run_chunk" ++ saveCalleeSaved ++ [ .movFromSp .x28 ] ++ cacheState ++
  loadCaches "20" "21" ++
  [ .loadSymGotValue .x25 "_eita_dispatch_ptr", .ldrBase .x25 .x25, .brReg .x1 ]

/-- x27 = sync_and_ret, through the GOT (the symbol lives in the handlers
    image). -/
def syncCont : List AInstr := [ .loadSymGotValue .x27 "_eita_sync_and_ret" ]

/-- The text of a program. -/
def text (p : List AInstr) : String := String.join (p.map AInstr.emitARM64)

/-! ## Structural facts, on the programs rather than on parsed strings -/

/-- Every pair saved by the prologue is restored by the epilogue at the same
    offset (the lists are mirror images), and the frame is 96 bytes at both
    ends. -/
theorem frame_is_a_bijection :
    (saveCalleeSaved.filterMap (fun i => match i with
      | .stpSp a b o => some (a, b, o) | .stpPreSp a b n => some (a, b, 96 - n) | _ => none)).reverse =
    restoreCalleeSavedRet.filterMap (fun i => match i with
      | .ldpSp a b o => some (a, b, o) | .ldpPostSp a b n => some (a, b, 96 - n) | _ => none) := by
  native_decide

/-- Every fault stub restores sp from x28 before anything else, and exits
    through sync_and_ret. -/
theorem stubs_unwind :
    faultSyms.all (fun s => match faultStub s with
      | _ :: _ :: _ :: .movToSp .x28 :: rest => rest.getLast? == some .brCont
      | _ => false) = true := by native_decide

end Evm.CL.Frame
