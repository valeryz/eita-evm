/-
  Evm.CL.RV32.Run — the rv32 interpreter frame: entry, dispatch, epilogue,
  fault stubs, and the fork-indexed dispatch tables.

  137 handlers are not an interpreter. ARM64 has `_eita_run`, `_eita_next`,
  `_eita_sync_and_ret`, the fault stubs and 22 fork tables
  (`Evm/CL/ARM64/Interp.lean`); x86-64 has `X86Run`/`X86Interp`. This is the
  rv32 equivalent, derived from the same role map (`RV32.Regs`) and the same
  fork-to-handler registry (`ARM64.Interp.handlerSymbol`, which is ISA-neutral).

  Three differences from the ARM64 frame, each already decided elsewhere and
  visible here as instructions:

  * **Subroutine threading.** The continuation is `ra`, so a handler ends in
    `ret` and the dispatch CALLS it (`jalr`) — x86-64's scheme, and the reason
    neither target spends a register on `cont`. ARM64 jump-threads through x27.
  * **`sp` is a byte offset** (32·depth), as on x86-64: rv32 has no scaled
    addressing, so a word index would cost a shift at every stack access. The
    prologue shifts left by 5, the epilogue shifts right.
  * **The dispatch table is read from `EvmState`** (`cont_table`, offset 600)
    at every dispatch, because the register budget (`Regs`: 27 of 27) has
    nothing to hold it and rv32 cannot address it PC-relatively in one
    instruction the way x86-64 can. One load per opcode.

  And one thing neither has: the **gas-width guard**. `Regs` keeps `gas` in a
  single 32-bit register under the side condition `gas_left < 2^32`; the
  prologue checks the incoming high word and refuses the frame if it is set, so
  the condition is enforced rather than assumed.
-/

import Evm.CL.RV32.Items
import Evm.CL.ARM64.Interp
import Evm.CL.ARM64

namespace Evm.CL.RV32.Run

open Evm.CL.RV32 Evm.CL.RV32.Asm Evm.CL.RV32.Items

/-! ## `EvmState` offsets the frame touches (c/evm_state.h) -/

def pcOff : Int := 0
def gasOff : Int := 8
def depthOff : Int := 16
def stackBaseOff : Int := 32
def codeBaseOff : Int := 64
def haltedOff : Int := 128
def revertedOff : Int := 129
def frameSpOff : Int := 544
def contTableOff : Int := 600

/-! ## The registers, by role -/

def pcR : RvReg := rv pc
def gasR : RvReg := rv gas
def spR : RvReg := rv spReg
def sbR : RvReg := rv stackBase
def cbR : RvReg := rv codeBase
def t0R : RvReg := rv "t0"
def t1R : RvReg := rv "t1"
def t2R : RvReg := rv "t2"
def a0R : RvReg := rv "a0"
def raR : RvReg := rv "ra"
def spHw : RvReg := rv "sp"

/-- The TOS words, in memory order: four limbs, low word first. -/
def tosWords : List RvReg :=
  (List.finRange 4).flatMap (fun i => [rv (tos i).lo, rv (tos i).hi])

/-- Callee-saved registers the frame pins and therefore must preserve. -/
def saved : List RvReg := [raR] ++ calleeSaved.map rv

def frameSize : Int := 64

/-! ## The frame -/

def saveRegs : List RvItem :=
  [.insn (.addi spHw spHw (-frameSize))] ++
  (saved.zipIdx.map (fun (r, k) => RvItem.insn (.sw r (4 * k) spHw)))

def restoreRegs : List RvItem :=
  -- `s0` holds the state and is needed to address it, so it is restored with
  -- the rest and only then is the frame popped
  (saved.zipIdx.map (fun (r, k) => RvItem.insn (.lw r (4 * k) spHw))) ++
  [.insn (.addi spHw spHw frameSize)]

/-- Cache `EvmState` into the register file, install the fork's table, load TOS
    when the stack is non-empty, and fall into the dispatch loop. -/
def prologue : List RvItem :=
  [ .dir ".text", .dir ".globl eita_run", .dir ".p2align 2", .label "eita_run" ] ++
  saveRegs ++
  [ .insn (.mv (rv state) a0R),
    .insn (.lw pcR pcOff a0R),
    .insn (.lw gasR gasOff a0R),
    -- the gas-width guard: a frame whose gas does not fit 32 bits is refused
    .insn (.lw t0R (gasOff + 4) a0R),
    .insn (.bnez t0R "_eita_gas_too_wide"),
    .insn (.lw spR depthOff a0R),
    .insn (.slli spR spR 5),                    -- depth → byte offset
    .insn (.lw sbR stackBaseOff a0R),
    .insn (.lw cbR codeBaseOff a0R),
    .insn (.sw spHw frameSpOff (rv state)),     -- for the fault stubs to unwind
    -- install the fork's dispatch table where every dispatch reads it
    .insn (.li t0R 0), .dir "    la   t0, _eita_dispatch_ptr",
    .insn (.lw t0R 0 t0R),
    .insn (.sw t0R contTableOff (rv state)),
    .insn (.beqz spR ".Lrun_nocache") ] ++
  [ .insn (.add t0R sbR spR) ] ++
  (tosWords.zipIdx.map (fun (r, k) => RvItem.insn (.lw r (-32 + 4 * k) t0R))) ++
  [ .label ".Lrun_nocache" ]

/-- The dispatch loop: fetch, advance, index the fork's table, call, repeat.
    A handler returns here because its continuation IS `ra`. -/
def dispatch : List RvItem :=
  [ .dir ".globl _eita_next", .label "_eita_next",
    .insn (.add t0R cbR pcR),
    .insn (.lbu t0R 0 t0R),
    .insn (.addi pcR pcR 1),
    .insn (.lw t1R contTableOff (rv state)),
    .insn (.slli t0R t0R 2),
    .insn (.add t1R t1R t0R),
    .insn (.lw t1R 0 t1R),
    .insn (.jalr t1R),
    .insn (.j "_eita_next") ]

/-- Write the cached state back and return. Reached by a terminator or a fault
    stub from any handler depth, so it restores `sp` from `frame_sp` first. -/
def syncAndRet : List RvItem :=
  [ .dir ".globl _eita_sync_and_ret", .dir ".p2align 2", .label "_eita_sync_and_ret",
    .insn (.lw spHw frameSpOff (rv state)),
    .insn (.sw pcR pcOff (rv state)),
    .insn (.sw (rv "zero") (pcOff + 4) (rv state)),
    .insn (.sw gasR gasOff (rv state)),
    .insn (.sw (rv "zero") (gasOff + 4) (rv state)),   -- gas fits 32 bits, by the guard
    .insn (.srli t0R spR 5),                            -- byte offset → depth
    .insn (.sw t0R depthOff (rv state)),
    .insn (.sw (rv "zero") (depthOff + 4) (rv state)),
    .insn (.beqz spR ".Lsync_nostack"),
    .insn (.add t0R sbR spR) ] ++
  (tosWords.zipIdx.map (fun (r, k) => RvItem.insn (.sw r (-32 + 4 * k) t0R))) ++
  [ .label ".Lsync_nostack" ] ++ restoreRegs ++ [ .insn .ret ]

/-- A fault: gas to zero, halted and reverted set, then the epilogue. Mirrors
    ARM64's `_eita_oog` exactly (`mov sp,x28; mov x22,#0; strb #1 at 128,129`). -/
def faultStub (sym : String) : List RvItem :=
  [ .dir s!".globl {sym}", .dir ".p2align 2", .label sym,
    .insn (.lw spHw frameSpOff (rv state)),
    .insn (.li gasR 0),
    .insn (.li t0R 1),
    .insn (.sb t0R haltedOff (rv state)),
    .insn (.sb t0R revertedOff (rv state)),
    .insn (.j "_eita_sync_and_ret") ]

/-- The faults the lowering branches to, plus two of this port's own: a frame
    whose gas does not fit 32 bits, and an opcode whose handler is not yet
    lowered. Both FAIL the transaction rather than guessing — and a host that
    cannot distinguish "refused" from "reverted" must pre-scan the code, which
    is why they are separate symbols. -/
def faultSyms : List String :=
  [ "_eita_oog", "_eita_stack_overflow", "_eita_stack_underflow",
    "_eita_static_violation", "_eita_invalid_jump",
    "_eita_gas_too_wide", "_eita_unimplemented" ]

def stubs : List RvItem := faultSyms.flatMap faultStub

/-! ## The dispatch tables

The opcode→handler mapping per fork is `ARM64.Interp.handlerSymbol` over
`ARM64.opcodeNameMap`: ISA-neutral, so rv32 reuses it and only the word size
changes (`.word`, 4-byte alignment). An opcode whose handler this port has not
lowered points at `_eita_unimplemented`. -/

def loweredSymbols : List String :=
  coveredHandlers.map (fun (nm, _) => s!"_eita_handler_{nm}")

def tableFor (resolve : String → String) (symbol : String) : List RvItem :=
  [ .dir ".data", .dir s!".globl {symbol}", .dir ".p2align 2", .label symbol ] ++
  (List.range 256).map (fun b =>
    let sym := match Evm.CL.ARM64.opcodeNameMap.find? (fun (op, _) => op == b) with
               | some (_, nm) => resolve nm
               | none => "_eita_handler_invalid"
    RvItem.dir s!"    .word   {if loweredSymbols.contains sym then sym else "_eita_unimplemented"}")

/-- The fork-indexed table of tables and `eita_set_fork`, as on ARM64 (ords
    past 21 clamp). -/
def forkTables : List RvItem :=
  [ .dir ".data", .dir ".globl _eita_fork_tables", .dir ".p2align 2",
    .label "_eita_fork_tables" ] ++
  Evm.CL.ARM64.Interp.tableForks.map (fun (_, nm) =>
    RvItem.dir s!"    .word   _eita_dispatch_table_{nm}") ++
  [ .dir "    .word   _eita_dispatch_table", .dir "    .word   _eita_dispatch_table" ] ++
  ((List.range 4).map (fun _ => RvItem.dir "    .word   _eita_dispatch_table_osaka")) ++
  [ .dir ".globl _eita_dispatch_ptr", .dir ".p2align 2", .label "_eita_dispatch_ptr",
    .dir "    .word   _eita_dispatch_table" ]

def setFork : List RvItem :=
  [ .dir ".text", .dir ".globl eita_set_fork", .dir ".p2align 2", .label "eita_set_fork",
    .insn (.li t0R 21),
    .insn (.bgeu t0R a0R ".Lsf_ok"),
    .insn (.mv a0R t0R),
    .label ".Lsf_ok",
    .dir "    la   t1, _eita_fork_tables",
    .insn (.slli a0R a0R 2),
    .insn (.add t1R t1R a0R),
    .insn (.lw t1R 0 t1R),
    .dir "    la   t2, _eita_dispatch_ptr",
    .insn (.sw t1R 0 t2R),
    .insn .ret ]

/-- The frame, the loop, the epilogue, the stubs and the tables — everything the
    interpreter needs besides the handler bodies themselves. -/
def frameAndTables : List RvItem :=
  prologue ++ dispatch ++ syncAndRet ++ stubs ++ setFork ++
  (Evm.CL.ARM64.Interp.tableForks.flatMap (fun (f, nm) =>
    tableFor (Evm.CL.ARM64.Interp.handlerSymbol f) s!"_eita_dispatch_table_{nm}")) ++
  tableFor (Evm.CL.ARM64.Interp.handlerSymbol Evm.CL.ARM64.Interp.interpFork)
    "_eita_dispatch_table" ++
  tableFor (Evm.CL.ARM64.Interp.handlerSymbol .osaka) "_eita_dispatch_table_osaka" ++
  forkTables

def emit : String := Asm.emitProg frameAndTables

end Evm.CL.RV32.Run
