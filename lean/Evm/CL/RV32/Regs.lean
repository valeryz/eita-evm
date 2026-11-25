/-
  Evm.CL.RV32.Regs — the register budget for a RISC-V (rv32imac) backend.

  Stage 0 of the RISC-V port, and the same question `Evm.CL.Target` asked for
  x86-64: before any instruction is lowered, does the target have the registers
  the handlers assume? On x86-64 the answer cost the NOS cache. Here it costs
  more, for a reason x86-64 did not have: **the machine is 32 bits wide and the
  handlers' data is 64.**

  ## Why `Target.Target` cannot express this target

  `Evm.CL.Target` maps each `RegRole` to at most ONE register name, which is
  exactly right for two 64-bit ISAs. On rv32 a 64-bit datum occupies a PAIR of
  registers, and the pointer-valued roles (state, stack base, code base) occupy
  one — the roles have different widths. Rather than widen the shared record for
  a third target, this module keeps its own allocation and states its own
  budget; the x86-64 instance stays untouched.

  ## What a flagless ISA adds

  RISC-V has no condition flags. `AsmCore`'s carry chains (`adds` → `adcs` →
  `adc`, `subs` → `sbcs` → `sbc`) and its flag-reading branches (`b.lo`,
  `b.cs`) therefore need the carry MATERIALISED in a register that lives from
  the instruction that produces it to the one that consumes it. That is a role
  neither existing target has, and it comes out of the same 27 registers.

  ## The allocation

  Persistent roles go in callee-saved registers so a helper call does not
  disturb them; TOS and the temporaries go in caller-saved ones, which is where
  ARM64 keeps its TOS too (x6-x9 are caller-saved on AArch64), so the handler
  programs already sync TOS to the stack around a call and the lowering inherits
  that discipline rather than inventing it.

  `cont` needs no register: rv32 threads through `jal`/`ret` like x86-64, using
  `ra` and the hardware return-address predictor. `dispatch` needs none either —
  the table address is materialised where it is used (`lui`/`addi`), the rv32
  analogue of x86-64's RIP-relative `jmp *table(,%rax,8)`.
-/

import Evm.CL.Pressure
import Evm.CL.OpInstrs
import Evm.CL.ARM64.Interp

namespace Evm.CL.RV32

open Evm.CL.AsmCore Evm.CL.Pressure

/-! ## The register file -/

/-- `x0`-`x4` are not allocatable by a hand-written handler file: `zero`, `ra`
    (the continuation — see the header), `sp` (the hardware stack, which the
    helper calls use), and `gp`/`tp`, which the toolchain owns (gp-relative
    relaxation and TLS; clobbering either would be a whole-program promise). -/
def reserved : List String := ["zero", "ra", "sp", "gp", "tp"]

/-- Callee-saved: `s0`-`s11`. A role here survives a call to a C helper. -/
def calleeSaved : List String :=
  ["s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7", "s8", "s9", "s10", "s11"]

/-- Caller-saved: `t0`-`t6` and the argument registers `a0`-`a7`. -/
def callerSaved : List String :=
  ["t0", "t1", "t2", "t3", "t4", "t5", "t6",
   "a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]

/-- Everything a handler may allocate: 27 of the 32 registers. -/
def allocatable : List String := calleeSaved ++ callerSaved

/-! ## The allocation -/

/-- A 64-bit datum: two 32-bit registers, least significant first. The halves
    need not be adjacent — the lowering names them explicitly. -/
structure Pair where
  lo : String
  hi : String
  deriving Repr, DecidableEq

def Pair.regs (p : Pair) : List String := [p.lo, p.hi]

/-- Pointer- and index-valued roles: one register each, callee-saved. `pc` and
    `sp` are 64-bit in `EvmState` but index code (< 2^24) and the stack
    (≤ 1024), so the low half is the whole value. -/
def state     : String := "s0"
def pc        : String := "s1"
def spReg     : String := "s2"
def stackBase : String := "s3"
def codeBase  : String := "s4"

/-- `gas_left` in ONE register (the decision of 2026-11-09, option 1 below).

    The side condition is `gas_left < 2^32`, under which the borrow out of the
    32-bit subtraction equals the borrow out of the 64-bit one, so the OOG test
    is unchanged. It is *guarded*, not assumed: a frame whose incoming gas does
    not fit refuses to run (`eita_gas_too_wide`), one compare at frame entry.
    Mainnet's block gas limit is ~4.5·10^7; an unverified transaction's gas
    field is a u64, which is exactly why the guard exists.

    What it buys: the register the NOS pair needs, and a gas charge of ~2
    instructions instead of ~5 — on the one arithmetic every opcode performs. -/
def gas : String := "s5"

/-- The materialised carry/borrow, produced by `adds`/`subs`-class instructions
    and consumed by `adcs`/`sbcs`/`b.lo`. Callee-saved so a chain can span a
    helper call if a program ever needs it to. -/
def carry : String := "s7"

/-- TOS limbs, caller-saved (as on ARM64). -/
def tos : Fin 4 → Pair
  | 0 => ⟨"a0", "a1"⟩ | 1 => ⟨"a2", "a3"⟩
  | 2 => ⟨"a4", "a5"⟩ | 3 => ⟨"a6", "a7"⟩

/-- Where a NOS limb is loaded from `stack[sp-2]`: the pair freed by narrowing
    gas, plus the one register that was spare. Live only inside the lowering of
    a single instruction, so its two halves need not be in one save class. -/
def nos : Pair := ⟨"s6", "t6"⟩

/-- The five-temporary pool `Pressure` measured, as pairs. -/
def temp : Fin 5 → Pair
  | 0 => ⟨"t0", "t1"⟩ | 1 => ⟨"t2", "t3"⟩ | 2 => ⟨"t4", "t5"⟩
  | 3 => ⟨"s8", "s9"⟩ | 4 => ⟨"s10", "s11"⟩

/-- Every register the allocation commits. -/
def pinned : List String :=
  [state, pc, spReg, stackBase, codeBase, carry, gas] ++ nos.regs ++
  ((List.finRange 4).flatMap (fun i => (tos i).regs)) ++
  ((List.finRange 5).flatMap (fun i => (temp i).regs))

/-- What is left over. -/
def spare : List String := allocatable.filter (fun r => !pinned.contains r)

/-- Every pair's LOW half, and every pair's HIGH half. -/
def allLos : List String :=
  [nos.lo] ++ ((List.finRange 4).map (fun i => (tos i).lo))
           ++ ((List.finRange 5).map (fun i => (temp i).lo))
def allHis : List String :=
  [nos.hi] ++ ((List.finRange 4).map (fun i => (tos i).hi))
           ++ ((List.finRange 5).map (fun i => (temp i).hi))

/-! ## The budget, machine-checked

The claims the design rests on, as `decide` rather than as the comment above. -/

/-- 27 allocatable registers, 12 callee-saved and 15 caller-saved. -/
example : allocatable.length = 27 := by native_decide
example : calleeSaved.length = 12 ∧ callerSaved.length = 15 := by native_decide
example : allocatable.length + reserved.length = 32 := by native_decide

/-- No register plays two roles, and none of them is reserved. -/
example : pinned.Nodup := by native_decide
example : reserved.all (fun r => !pinned.contains r) := by native_decide
example : pinned.all (fun r => allocatable.contains r) := by native_decide

/-- **No register is the low half of one pair and the high half of another.**

    `Lower.loadWords` rests on this. Splitting a 64-bit load into two words
    destroys the address when a destination half IS the base register, so the
    colliding slot is deferred to last — and deferring ONE slot suffices only
    if at most one can collide. A base register is some pair's `lo` (an address
    is 32 bits and lives in a low half), so a collision with a destination's
    `hi` would be a second one, and the deferral would be wrong.

    This was a comment until 2026-11-25. It is load-bearing, cheap to decide,
    and the kind of claim that stops being true when someone reshuffles the
    allocation — so it is checked. -/
theorem los_and_his_are_disjoint : allLos.all (fun r => !allHis.contains r) := by
  native_decide

/-- …and no register is the low half of two different pairs, which is the other
    half of "at most one destination can collide". -/
theorem los_are_distinct : allLos.Nodup := by native_decide

/-- **All 27 are committed, with nothing left over** — x86-64's position
    exactly. Seven single-register roles (gas among them, by the decision above)
    and ten pairs: NOS's load pair, four TOS limbs, five temporaries. -/
example : pinned.length = 27 := by native_decide
example : spare = [] := by native_decide

/-- The persistent roles are callee-saved and the caches are caller-saved: a
    helper call preserves state/pc/sp/bases/gas/carry and clobbers TOS, which is
    the ARM64 arrangement the handler programs were written against. -/
example : [state, pc, spReg, stackBase, codeBase, carry].all calleeSaved.contains := by
  native_decide
example : calleeSaved.contains gas := by native_decide
example : ((List.finRange 4).flatMap (fun i => (tos i).regs)).all callerSaved.contains := by
  native_decide

/-! ## The one register that decides the design

NOS is not cached (no room — the same conclusion as x86-64), so a NOS limb must
be READ from `stack[sp-2]`. x86-64 got that for free: its arithmetic takes a
memory operand, so a NOS read is an addressing mode. RISC-V is a load/store
machine, so a NOS read is a `lw` into some register — and `t6`, the one spare,
is a single register where a NOS limb pair needs two.

So the question is whether a NOS read can borrow from the temporary pool, which
it can exactly when no program needs a NOS limb while all five temporaries are
live. That is measurable over the programs the emitters actually emit. -/

/-- The NOS limb registers. -/
def isNos : Reg → Bool
  | .x10 | .x11 | .x12 | .x13 => true
  | _ => false

def readsNos (p : List AInstr) : Bool := p.any (fun it => (mentions it).any isNos)

/-- The `AInstr` stream of a handler program. -/
def progInstrs (p : AsmCore.Prog) : List AInstr :=
  (p.filterMap Evm.CL.OpInstrs.Op.instrs?).flatten

/-- Every handler the threaded interpreter emits, as instruction streams. -/
def handlerStreams : List (List AInstr) :=
  (Evm.CL.ARM64.Interp.handlerProgs Evm.CL.ARM64.Interp.opCost).map
    (fun (_, p) => progInstrs p)

/-- How many handlers there are, and how many of them read a NOS limb. -/
def handlerCount : Nat := handlerStreams.length
def nosReaders : Nat := (handlerStreams.filter readsNos).length

/-- The peak temporary pressure among the handlers that read NOS: if this is
    below five, a NOS read can take a temporary pair and the allocation above
    stands as it is. -/
def nosReaderPeak : Nat :=
  ((handlerStreams.filter readsNos).map pressure).foldl max 0

/-- And among all handlers, for comparison with the gadgets' five. -/
def handlerPeak : Nat := (handlerStreams.map pressure).foldl max 0

/-- The pressure AT the instructions that read a NOS limb — the number that
    actually decides it. A program may peak at five temporaries somewhere and
    still have a pair free at the point it reads NOS, which is all a `lw` pair
    needs. -/
def nosReadPressure : Nat :=
  (handlerStreams.map (fun p =>
    ((p.zipIdx).filterMap (fun (it, i) =>
      if (mentions it).any isNos then some (pressureAt p i) else none)).foldl max 0)).foldl max 0

/-- The same over the structured gadgets, which is where the five-temp peaks
    were measured in the first place. -/
def gadgetNosReadPressure : Nat :=
  (gadgetSet.map (fun p =>
    ((p.zipIdx).filterMap (fun (it, i) =>
      if (mentions it).any isNos then some (pressureAt p i) else none)).foldl max 0)).foldl max 0

/-! ## The shortfall, and the three ways out

Measured over the 150 handler programs the threaded interpreter emits (126 of
which read a NOS limb):

| | |
|---|---|
| allocatable registers | 27 |
| committed before narrowing gas | 26 (6 singles + 10 pairs) |
| left over | 1 (`t6`) |
| temporaries live *at* a NOS read | **5 of 5** |
| …in the structured gadgets | 3 of 5 |

So a NOS limb pair has nowhere to go: the pool is full exactly where it is
needed, and one spare register is half of what a 64-bit load wants. x86-64 had
this for free (a NOS read is an addressing mode); a load/store machine does not.

**Resolved 2026-11-09: option 1.** `gas` is one register, guarded at frame
entry; the pair it freed plus the spare `t6` became `nos`. The allocation above
is the result — 27 of 27, nothing spare.

The ways to find one register, with what each costs:

1. **Narrow `gas` to 32 bits** — TAKEN. — frees `s6`, giving 27 committed and nothing
   spare (x86-64's position exactly). Needs `gas_left < 2^32`, which every real
   chain satisfies (mainnet's block gas limit is ~4.5·10^7) but an *unverified*
   transaction need not: so it becomes a guard at frame entry, one compare, and
   a stated side condition under which the 32-bit borrow equals the 64-bit one.
   It also makes every gas charge ~2 instructions instead of ~5, and gas is
   charged by every opcode — the hottest arithmetic in the interpreter.
2. **Spill a temporary pair** at NOS-read sites: two `sw` and two `lw` on the
   126 handlers that read NOS, which are the common opcodes (ADD, OR, XOR, the
   comparisons). No side condition, no ABI promise.
3. **Claim `gp`** (x3) and build the whole firmware `-mno-relax`. Costs nothing
   in instructions, but it is a promise the *application* must keep too, so it
   leaks out of this repository.

Not an option: re-sequencing the handler programs to need four temporaries.
They are shared with ARM64 and x86-64, and that would move `handlers.S`.
-/

/-- The shortfall, pinned so that a change to the programs or the pool surfaces
    here rather than in a miscompile. -/
example : nosReadPressure = 5 := by native_decide
example : gadgetNosReadPressure = 3 := by native_decide
example : handlerCount = 150 ∧ nosReaders = 126 := by native_decide
/-- The shortfall that forced the decision: before narrowing gas, 26 were
    committed and a NOS limb pair needed two registers from a pool of one. -/
example : 27 - 26 < (nos.regs).length := by native_decide

end Evm.CL.RV32
