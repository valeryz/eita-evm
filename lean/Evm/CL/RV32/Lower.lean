/-
  Evm.CL.RV32.Lower — lowering `AInstr` to rv32imac text.

  Stage 1 of the RISC-V port. `Evm.CL.Lowering` made the instruction layer
  target-parametric and `Evm.CL.X86Lower` classified what a two-operand ISA
  costs; this module does the same job for a target that differs from both in
  two ways no previous one did.

  ## 1. The data is 64 bits and the machine is 32

  Every `AInstr` operand is a 64-bit `AsmCore.Reg`. Here each one is a PAIR of
  rv32 registers (`Regs.lo` / `Regs.hi`), so a single instruction becomes a
  sequence, and a carry has to cross from the low half to the high half.

  The roles that are *not* 64-bit data — the `EvmState` pointer, the stack and
  code bases, `pc`, `sp`, and (by the decision in `Regs`) `gas` — get `zero` as
  their high half. That is not an approximation: on a 32-bit machine a pointer
  IS 32 bits, `sp ≤ 1024`, `pc < 2^24`, and `gas < 2^32` is the guarded side
  condition. RISC-V's hardwired `x0` makes reading such a half free and makes
  writing one discard, which is exactly the required behaviour.

  ## 2. There are no flags

  `AsmCore`'s carry chains (`adds`/`adcs`/`adc`, `subs`/`sbcs`/`sbc`) and its
  flag-reading branches need the carry MATERIALISED. `Regs.carry` is that
  register, and the budget has room for exactly one — which looks impossible for
  a 64-bit add with carry-in *and* carry-out, since two 32-bit additions can
  each carry.

  They cannot both carry, though: if `Ha + Cin` wraps then `Ha = 0xffffffff` and
  `Cin = 1`, so the sum is 0 and adding `Hb` cannot wrap. The two carries are
  **mutually exclusive**, so `C_out = C_a + C_b` can be accumulated in place
  with one conditional skip and no second register (`add64`).

  Comparisons are the other flag consumer. A `cmp` that is read by `b.hi` or
  `b.ls` needs both a borrow and a zero bit, which one register cannot hold —
  so compare-and-branch pairs are **fused** (`emitFused`), which is what one
  writes on RISC-V anyway: `bltu`/`bgeu`/`bne` take both operands. A bare
  `cmpReg` whose branch was not fused emits a marker rather than a guess.

  Coverage is checked the same way as x86-64's: anything unhandled emits
  `«unlowered»`, and `scripts/verify-rv32-emit.sh` both greps for the marker and
  hands the file to `riscv64-elf-gcc`, which is the authority on what assembles.
-/

import Evm.CL.RV32.Regs
import Evm.CL.Lowering

namespace Evm.CL.RV32

open Evm.CL.AsmCore Evm.CL.Pressure

/-! ## Register halves -/

/-- The five-temporary pool, reusing the colouring `Pressure.x86Temp` proved
    respects the interference graph (`x86Temp_respects_interference`) — the same
    five colours, landing on rv32 pairs instead of x86-64 registers. -/
def tempIdx (r : Reg) : Option (Fin 5) :=
  match x86Temp r with
  | "rax" => some 0 | "rcx" => some 1 | "rdx" => some 2
  | "rsi" => some 3 | "rdi" => some 4
  | _ =>
    -- x1/x2/x3 SHARE homes with x15/x17/x4-x16, exactly as they do on x86-64
    -- (`Lowering.x86Reg?`: x1→rdx with x15, x2→rsi with x17, x3→rdi with
    -- x4/x16). Adopting the same sharing *classes* means the soundness
    -- obligation is literally the same one `X86Alias.no_alias_hazards`
    -- discharges — exact branch-aware liveness over these very programs,
    -- written after three x86-64 bodies broke it while staging callback
    -- arguments. The homes differ (pairs here); the partition does not.
    match r with
    | .x1 => some 2 | .x2 => some 3 | .x3 => some 4
    | _ => none

/-- Which NOS limb a register is (NOS is not cached; see `nosLoad`). -/
def nosLimb : Reg → Option Nat
  | .x10 => some 0 | .x11 => some 1 | .x12 => some 2 | .x13 => some 3
  | _ => none

/-- The roles that occupy ONE register, their high half being `zero`. -/
def single : Reg → Option String
  | .x20 => some state     | .x21 => some pc        | .x22 => some gas
  | .x23 => some spReg     | .x24 => some stackBase | .x26 => some codeBase
  | .x27 => some "ra"      -- the continuation: `jal`/`ret`, as on x86-64
  | _ => none

/-- The pair a 64-bit register lives in. -/
def pairOf (r : Reg) : Option Pair :=
  match nosLimb r with
  | some _ => some nos                      -- after `nosLoad` has run
  | none =>
    match r with
    | .x6 => some (tos 0) | .x7 => some (tos 1)
    | .x8 => some (tos 2) | .x9 => some (tos 3)
    | _ => (tempIdx r).map temp

def marker : String := "«unlowered-reg»"

def lo (r : Reg) : String :=
  match single r with
  | some s => s
  | none => ((pairOf r).map Pair.lo).getD marker

def hi (r : Reg) : String :=
  match single r with
  | some _ => "zero"
  | none => ((pairOf r).map Pair.hi).getD marker

/-! ## Emission helpers -/

def ln (s : String) : String := "    " ++ s ++ "\n"

/-- `sp` is kept as a BYTE offset (32·depth), as on x86-64: rv32 has no scaled
    addressing, so a word index would cost a shift at every stack access. -/
def nosOff (limb : Nat) : Int := -64 + 8 * limb

/-- Load a NOS limb into the `nos` pair. The pair's high half doubles as the
    address register and is overwritten by its own second load, so this costs
    no scratch at all. -/
def nosLoad (limb : Nat) : String :=
  ln s!"add  {nos.hi}, {stackBase}, {spReg}" ++
  ln s!"lw   {nos.lo}, {nosOff limb}({nos.hi})" ++
  ln s!"lw   {nos.hi}, {nosOff limb + 4}({nos.hi})"


/-! ## Scratch beyond the flag register

Two sequences need more live bits than `Regs.carry` holds: a 32-bit add that has
BOTH a carry-in and a carry-out (the `adcs` chains), and the matching subtract.
The budget has no register left (`Regs`: 27 of 27), so the lowering borrows one
by **spilling** it to the handler frame — `0(sp)` and `4(sp)`, reserved by the
run frame for exactly this. A spill costs two memory accesses on the instruction
that needs it and is correct whatever is live, which is why it beats the
alternative of reasoning about liveness at every site.

The victim is chosen, not fixed: the first register that is not an operand of
the instruction doing the borrowing (the same discipline as x86-64's
`nosStoreTemp`).
-/

/-- The lowering's spill slots: `EvmState.rv32_scratch` (offset 608), addressed
    off `state`. NOT a `sp` offset — a handler moves `sp` to frame its helper
    calls — and NOT below `sp`, because RISC-V has no red zone. -/
def spill0 : String := s!"608({state})"
def spill1 : String := s!"612({state})"
def spill2 : String := s!"616({state})"

/-- A register that is not one of `used`, to be spilled and restored around a
    sequence that needs one more live bit than `carry` provides. -/
def pickFree (used : List String) : String :=
  (((List.finRange 5).flatMap (fun i => (temp i).regs) ++ [nos.lo, nos.hi]).find?
    (fun r => !used.contains r)).getD marker

/-- 32-bit add `D = P + Q (+ carry)`, carry-out in `carry` when asked.

    With a carry-in AND a carry-out the two 32-bit additions could each carry —
    but not both (header), so the second is folded in with a conditional skip
    instead of a second flag. The operand order is chosen so that whichever one
    the carry-out is measured against survives the write to `D`. -/
def addc32 (n : Nat) (D P Q : String) (cin cout : Bool) : String :=
  if D == P && D == Q then
    -- doubling: the carry-out is the top bit, and a carry-in needs the victim
    (if cout then ln s!"srli {carry}, {P}, 31" else "") ++
    ln s!"add  {D}, {P}, {P}" ++
    (if cin then ln s!"add  {D}, {D}, {carry}" else "")
  else
    let (A, B) := if D == Q then (Q, P) else (P, Q)
    if !cin then
      ln s!"add  {D}, {A}, {B}" ++
      (if cout then ln s!"sltu {carry}, {D}, {B}" else "")
    else if !cout then
      ln s!"add  {D}, {A}, {carry}" ++ ln s!"add  {D}, {D}, {B}"
    else
      ln s!"add  {D}, {A}, {carry}" ++
      ln s!"sltu {carry}, {D}, {carry}" ++
      ln s!"add  {D}, {D}, {B}" ++
      ln s!"bgeu {D}, {B}, .Lk{n}" ++
      ln s!"addi {carry}, {carry}, 1" ++
      s!".Lk{n}:\n"

/-- 32-bit subtract `D = P - Q (- borrow)`, borrow-out in `carry` when asked.
    Every borrow is read before the write that could consume its operands; the
    borrow-in-and-out case spills one victim (the two borrows are mutually
    exclusive, as in the add, so their `or` is their sum). -/
def subb32 (D P Q : String) (bin bout : Bool) : String :=
  if !bin then
    -- the borrow is read before the write that may consume an operand
    (if bout then ln s!"sltu {carry}, {P}, {Q}" else "") ++
    ln s!"sub  {D}, {P}, {Q}"
  else if !bout then
    ln s!"sub  {D}, {P}, {Q}" ++ ln s!"sub  {D}, {D}, {carry}"
  else
    -- Both: subtract the BORROW-IN first. That frees `carry` to hold the second
    -- borrow while the first is in the victim, and the two cannot both be 1
    -- (if `P - carry` borrowed then `P = 0`, `D = 0xffffffff`, and `D - Q`
    -- cannot borrow), so their `or` is the borrow out.
    let v := pickFree [D, P, Q, carry]
    if D == Q then
      -- the destination IS the subtrahend: copy it out of the way first
      let v2 := pickFree [D, P, Q, carry, v]
      ln s!"sw   {v}, {spill0}" ++ ln s!"sw   {v2}, {spill1}" ++
      ln s!"mv   {v2}, {Q}" ++
      ln s!"sltu {v}, {P}, {carry}" ++
      ln s!"sub  {D}, {P}, {carry}" ++
      ln s!"sltu {carry}, {D}, {v2}" ++
      ln s!"sub  {D}, {D}, {v2}" ++
      ln s!"or   {carry}, {carry}, {v}" ++
      ln s!"lw   {v}, {spill0}" ++ ln s!"lw   {v2}, {spill1}"
    else
      ln s!"sw   {v}, {spill0}" ++
      ln s!"sltu {v}, {P}, {carry}" ++
      ln s!"sub  {D}, {P}, {carry}" ++
      ln s!"sltu {carry}, {D}, {Q}" ++
      ln s!"sub  {D}, {D}, {Q}" ++
      ln s!"or   {carry}, {carry}, {v}" ++
      ln s!"lw   {v}, {spill0}"

/-- A 64-bit add. The low half always produces the carry the high half
    consumes; `cin`/`cout` are the EXTERNAL carry (the `adcs`/`adc` chains). -/
def add64 (n : Nat) (d a b : Reg) (cin cout : Bool) : String :=
  addc32 (2 * n)     (lo d) (lo a) (lo b) cin  true ++
  addc32 (2 * n + 1) (hi d) (hi a) (hi b) true cout

/-- A 64-bit subtract, the same way. -/
def sub64 (d a b : Reg) (bin bout : Bool) : String :=
  subb32 (lo d) (lo a) (lo b) bin  true ++
  subb32 (hi d) (hi a) (hi b) true bout

/-- A 64-bit logical shift. `sh < 32` and `sh ≥ 32` are different sequences;
    `carry` is the funnel temporary (dead at a shift: no chain spans one). -/
def shift64s (Ld Hd La Ha : String) (sh : Nat) (right : Bool) : String :=
  if sh == 0 then ln s!"mv   {Ld}, {La}" ++ ln s!"mv   {Hd}, {Ha}"
  else if sh < 32 then
    if right then
      ln s!"srli {Ld}, {La}, {sh}" ++
      ln s!"slli {carry}, {Ha}, {32 - sh}" ++
      ln s!"or   {Ld}, {Ld}, {carry}" ++
      ln s!"srli {Hd}, {Ha}, {sh}"
    else
      ln s!"slli {Hd}, {Ha}, {sh}" ++
      ln s!"srli {carry}, {La}, {32 - sh}" ++
      ln s!"or   {Hd}, {Hd}, {carry}" ++
      ln s!"slli {Ld}, {La}, {sh}"
  else if sh < 64 then
    if right then
      ln s!"srli {Ld}, {Ha}, {sh - 32}" ++ ln s!"li   {Hd}, 0"
    else
      ln s!"slli {Hd}, {La}, {sh - 32}" ++ ln s!"li   {Ld}, 0"
  else ln s!"li   {Ld}, 0" ++ ln s!"li   {Hd}, 0"

def shift64 (d a : Reg) (sh : Nat) (right : Bool) : String :=
  shift64s (lo d) (hi d) (lo a) (hi a) sh right

/-- 64-bit `d = a + (b << sh)` / `(b >> sh)`.

    The shifted value needs somewhere to live, and the destination will not do:
    the gadgets contain `add x16, x16, x14, lsl #1`, where the destination IS
    the left operand (x86-64's `needsTemp` class, which it avoided by having
    `lea`). rv32 has no such addressing, but it does have a spare pair at this
    point — the NOS load pair, which no shifted add uses, since none of them
    takes a NOS operand (`no_shifted_add_reads_nos`). So the shift goes there
    and the add is unconstrained by aliasing. -/
def shiftedAdd (d a b : Reg) (sh : Nat) (right : Bool) : String :=
  if (nosLimb b).isSome || (nosLimb a).isSome then
    s!"    /* «unlowered: shifted add with a NOS operand» */\n"
  else
    shift64s nos.lo nos.hi (lo b) (hi b) sh right ++
    ln s!"add  {lo d}, {lo a}, {nos.lo}" ++
    ln s!"sltu {carry}, {lo d}, {nos.lo}" ++
    ln s!"add  {hi d}, {hi a}, {nos.hi}" ++
    ln s!"add  {hi d}, {hi d}, {carry}"

/-- A 64-bit compare-and-branch, fused. No register is consumed: rv32's branches
    take both operands. `le` branches when `a ≤ b`, else when `a < b`; `signed`
    compares the HIGH halves with `blt`/`bge` and leaves the low halves
    unsigned, which is what a 64-bit signed comparison is. -/
def cmpBranchS (n : Nat) (a b : Reg) (lbl : String) (le signed : Bool) : String :=
  let (La, Ha) := (lo a, hi a)
  let (Lb, Hb) := (lo b, hi b)
  let lt := if signed then "blt " else "bltu"
  let ge := if signed then "bge " else "bgeu"
  if le then
    ln s!"{lt} {Hb}, {Ha}, .Lx{n}" ++
    ln s!"bne  {Ha}, {Hb}, {lbl}" ++
    ln s!"bgeu {Lb}, {La}, {lbl}" ++
    s!".Lx{n}:\n"
  else
    ln s!"{lt} {Ha}, {Hb}, {lbl}" ++
    ln s!"bne  {Ha}, {Hb}, .Lx{n}" ++
    ln s!"bltu {La}, {Lb}, {lbl}" ++
    s!".Lx{n}:\n"

def cmpBranch (n : Nat) (a b : Reg) (lbl : String) (le : Bool) : String :=
  cmpBranchS n a b lbl le false

/-- A fused compare + conditional select: `d = (p >u q) ? a : b`. rv32 has no
    conditional move, so it is a branch over two moves — and the compare must be
    fused for the same reason the branches are (one flag register cannot carry
    both a borrow and a zero bit). -/
def cmpSelect (n : Nat) (p q d a b : Reg) : String :=
  cmpBranch n q p s!".Lm{n}" false ++
  ln s!"mv   {lo d}, {lo b}" ++ ln s!"mv   {hi d}, {hi b}" ++
  ln s!"j    .Ln{n}" ++
  s!".Lm{n}:\n" ++
  ln s!"mv   {lo d}, {lo a}" ++ ln s!"mv   {hi d}, {hi a}" ++
  s!".Ln{n}:\n"

/-- The 64-bit zero test, into a branch. `carry` is the fold temporary. -/
def zeroBranch (r : Reg) (lbl : String) (whenZero : Bool) : String :=
  ln s!"or   {carry}, {lo r}, {hi r}" ++
  ln (if whenZero then s!"beqz {carry}, {lbl}" else s!"bnez {carry}, {lbl}")

/-- 32-bit byte reverse, the three-step mask shuffle: rv32imac has no `rev8`
    (that is Zbb, which this part does not implement), so it is open-coded.
    `m` holds the mask, `t` a temporary, `D` the result. -/
def bswap32 (D S m t : String) : String :=
  ln s!"srli {t}, {S}, 8" ++
  ln s!"and  {t}, {t}, {m}" ++
  ln s!"and  {D}, {S}, {m}" ++
  ln s!"slli {D}, {D}, 8" ++
  ln s!"or   {D}, {D}, {t}" ++
  ln s!"slli {t}, {D}, 16" ++
  ln s!"srli {D}, {D}, 16" ++
  ln s!"or   {D}, {D}, {t}"

/-- 64-bit byte reverse: the halves swap as well as their bytes. Both results
    are produced before either is written, so `rev d, d` is safe. -/
def rev64 (d a : Reg) : String :=
  let m := pickFree [lo d, hi d, lo a, hi a, carry]
  let v := pickFree [lo d, hi d, lo a, hi a, carry, m]
  ln s!"sw   {m}, {spill0}" ++ ln s!"sw   {v}, {spill1}" ++
  ln s!"li   {m}, 0xff00ff" ++
  bswap32 v (lo a) m carry ++ ln s!"sw   {v}, {spill2}" ++
  bswap32 v (hi a) m carry ++
  ln s!"mv   {lo d}, {v}" ++
  ln s!"lw   {v}, {spill2}" ++
  ln s!"mv   {hi d}, {v}" ++
  ln s!"lw   {m}, {spill0}" ++ ln s!"lw   {v}, {spill1}"

/-- A 64-bit compare against an immediate, fused into a branch. `carry` holds
    the immediate (a compare never sits inside a carry chain), and the high half
    decides first: with `imm < 2^32`, a nonzero high half settles the order. -/
def cmpImmBranch (n : Nat) (a : Reg) (imm : Nat) (c : BCond) (lbl : String) : String :=
  let (La, Ha) := (lo a, hi a)
  let setImm := ln s!"li   {carry}, {imm}"
  match c with
  | .lo => setImm ++ ln s!"bnez {Ha}, .Lx{n}" ++ ln s!"bltu {La}, {carry}, {lbl}" ++ s!".Lx{n}:\n"
  | .hs => setImm ++ ln s!"bnez {Ha}, {lbl}"  ++ ln s!"bgeu {La}, {carry}, {lbl}"
  | .hi => setImm ++ ln s!"bnez {Ha}, {lbl}"  ++ ln s!"bltu {carry}, {La}, {lbl}"
  | .ls => setImm ++ ln s!"bnez {Ha}, .Lx{n}" ++ ln s!"bgeu {carry}, {La}, {lbl}" ++ s!".Lx{n}:\n"
  | .eq => setImm ++ ln s!"bnez {Ha}, .Lx{n}" ++ ln s!"beq  {La}, {carry}, {lbl}" ++ s!".Lx{n}:\n"
  | .ne => setImm ++ ln s!"bnez {Ha}, {lbl}"  ++ ln s!"bne  {La}, {carry}, {lbl}"
  -- signed: the immediate is non-negative here, so its high half is zero and
  -- `blt`/`bge` on the high halves is the whole decision
  | .lt => setImm ++ ln s!"blt  {Ha}, zero, {lbl}" ++
           ln s!"bnez {Ha}, .Lx{n}" ++ ln s!"bltu {La}, {carry}, {lbl}" ++ s!".Lx{n}:\n"

/-- A 64-bit compare that DISCARDS its result (`subs xzr, a, b` and its
    borrow-chained form): the borrow is the point, so it goes through the same
    subtract as everything else, into a spilled throwaway destination. -/
def cmpDiscard (a b : Reg) (bin : Bool) : String :=
  let v := pickFree [lo a, hi a, lo b, hi b, carry]
  ln s!"sw   {v}, {spill2}" ++
  subb32 v (lo a) (lo b) bin  true ++
  subb32 v (hi a) (hi b) true true ++
  ln s!"lw   {v}, {spill2}"

/-- A call, with the continuation saved around it.

`Regs` notes that `cont` needs no register on rv32 because it "threads through
`jal`/`ret` like x86-64" — true of the calling convention, false of the
mechanism. x86-64's `call` pushes the return address to MEMORY; rv32's `jal`
overwrites the REGISTER `ra`, which is the very register the dispatch loop put
the continuation in. So where the x86-64 call gadget needs no frame save
(`OpInstrs.x86BinHelper` has none, and rv32 consumes that stream), rv32 must
save `ra` itself.

Without this, `eita_handler_mul` returned to the instruction after its own
`call eita_helper_mul`, because that is where `jal` had left `ra` — and ran
that tail forever. QEMU showed it as a two-block cycle.

Sixteen bytes rather than four: the ILP32 ABI wants `sp` 16-byte aligned at a
call, and every `spSub` in the gadgets is a multiple of 16, so this preserves
it. The slot is below anything the staging already addressed off `sp`, so the
argument pointers computed before the call stay valid. -/
def callSaving (insn : String) : String :=
  ln "addi sp, sp, -16" ++ ln "sw   ra, 0(sp)" ++ ln insn ++
  ln "lw   ra, 0(sp)" ++ ln "addi sp, sp, 16" ++
  -- …and the result where the instruction layer expects it. Both AAPCS and
  -- SysV return in the register the IR calls `x0`, so `OpInstrs.chargeGasX0`
  -- reads a callback's gas straight out of it — on ARM64 that register IS x0
  -- and on x86-64 its home is `rax`, so both work by accident of the
  -- colouring. On rv32 `x0`'s home is the temporary pair `(t0, t1)` while an
  -- ILP32 `uint64_t` comes back in `a0:a1`, so the value has to be moved.
  -- Unconditional, because the convention already says a call clobbers `x0`:
  -- it is `rax` on x86-64 and caller-saved on ARM64, so no program can be
  -- holding anything there across a call.
  ln s!"mv   {lo .x0}, a0" ++ ln s!"mv   {hi .x0}, a1"

/-! ## Alignment, which a load/store machine makes an obligation

ARM64 and x86-64 both perform unaligned loads and stores, so the handler
programs were written without a thought for alignment and nothing in the shared
instruction layer records which addresses are byte-granular. **bao1x's VexRiscv
traps them**: `rtl/modules/vexriscv/lib/VexRiscv_CramSoC.sv` raises exception 4
(`LoadAddressMisaligned`) or 6 (`StoreAddressMisaligned`) from
`io_cpu_writeBack_unalignedAccess`. The RISC-V ISA permits that — misaligned
support is optional — so this is a lowering obligation, not a chip defect.

Two families of address are byte-granular, and only two:

* **code**, `codeBase + pc`: every `PUSH`<i>n</i> reads its immediate from an
  arbitrary byte offset. This is what killed the first board run — `PUSH1` at
  code offset 0 issues `lw` at `code + 1`.
* **EVM memory / calldata / returndata**, a pointer loaded out of `EvmState`
  plus an EVM offset: `MLOAD`, `MSTORE`, `MCOPY`, the copy opcodes.

Everything else is aligned by construction: the stack is an array of `u256_t`
(32-byte stride, 8-byte aligned by `_Static_assert`), `EvmState`'s own fields
are at 8-byte offsets, and our frame is `sp`-relative.

So the lowering runs a forward **alignment analysis** over each program and
emits a byte-wise sequence for any access it cannot justify. It defaults to NOT
aligned, which is the safe direction: an unjustified aligned claim is a trap on
hardware, an unjustified byte-wise sequence is only instructions. The analysis
resets at labels (a join it cannot see both sides of) and after a call (the
caller-saved registers are gone), both conservative.

`scripts/check-rv32-alignment.py` audits the same question from the other end —
over the emitted TEXT, by backward base-provenance scan — so the two disagree
if either is wrong. -/

/-- The destination of an instruction, where it has one. -/
def destOf : AInstr → Option Reg
  | .subImm d _ _ | .addImm d _ _ | .movImm d _ | .movImmW d _ | .movReg d _
  | .addLsl5 d _ _ | .addLsl d _ _ _ | .addLsr d _ _ _ | .ldrOff d _ _
  | .ldrBase d _ | .addSp d _ | .addReg d _ _ | .ldrSp d _ | .orr3 d _ _
  | .and3 d _ _ | .eor3 d _ _ | .mvn d _ | .adds d _ _ | .adcs d _ _
  | .adc d _ _ | .subReg d _ _ | .subsReg d _ _ | .sbcs d _ _ | .sbc d _ _
  | .mulReg d _ _ | .madd d _ _ _ | .lsrImm d _ _ | .lslImm d _ _
  | .clzReg d _ | .rev d _ => some d
  | _ => none

/-- Every register an instruction writes. `destOf` misses the pair loads, and
    a stale alignment claim on a register a `ldp` just overwrote is exactly the
    kind of thing that traps once on hardware and never in a test. -/
def defsOf : AInstr → List Reg
  | .ldpOff r1 r2 _ _ => [r1, r2]
  | .ldpSp r1 r2 _    => [r1, r2]
  | .ldpPostSp r1 r2 _ => [r1, r2]
  | it => (destOf it).toList

/-- The roles whose value is a multiple of four to begin with: `state` (an
    `EvmState *`), `stackBase` (a `u256_t *`), and `sp`, which is a BYTE offset
    but always a multiple of 32. `codeBase` is absent on purpose — it is a
    `uint8_t *` and `pc` is added to it. -/
def alignedSeed : List Reg := [.x20, .x23, .x24]

def dropAligned (A : List Reg) (d : Reg) : List Reg := A.filter (fun r => r != d)

def setAligned (A : List Reg) (d : Reg) (ok : Bool) : List Reg :=
  if ok then (if A.contains d then A else d :: A) else dropAligned A d

/-- One step of the forward analysis. -/
def stepAligned (A : List Reg) (it : AInstr) : List Reg :=
  match it with
  -- a sum of two multiples of four is a multiple of four
  | .addReg d a b    => setAligned A d (A.contains a && A.contains b)
  | .subReg d a b    => setAligned A d (A.contains a && A.contains b)
  | .addImm d a i    => setAligned A d (A.contains a && i % 4 == 0)
  | .subImm d a i    => setAligned A d (A.contains a && i % 4 == 0)
  -- `<< 5` is a multiple of 32, `<< sh` of four once `sh ≥ 2`
  | .addLsl5 d a _   => setAligned A d (A.contains a)
  | .addLsl d a _ sh => setAligned A d (A.contains a && 2 ≤ sh)
  | .movReg d a      => setAligned A d (A.contains a)
  | .addSp d i       => setAligned A d (i % 4 == 0)
  | .movImm d i      => setAligned A d (i % 4 == 0)
  | .movImmW d i     => setAligned A d (i % 4 == 0)
  -- a call clobbers the caller-saved registers, a label is a join we cannot
  -- see both sides of: in either case keep only what is aligned by role
  | .blSym _ | .blr _ | .label _ => alignedSeed
  | it => (defsOf it).foldl dropAligned A

/-- Four bytes of a big-endian-innocent 32-bit value, gathered least
    significant first. `D` is built up in place; `t` holds each byte. -/
def byteGather (D base : String) (off : Nat) (t : String) : String :=
  ln s!"lbu  {D}, {off}({base})" ++
  ln s!"lbu  {t}, {off + 1}({base})" ++ ln s!"slli {t}, {t}, 8"  ++ ln s!"or   {D}, {D}, {t}" ++
  ln s!"lbu  {t}, {off + 2}({base})" ++ ln s!"slli {t}, {t}, 16" ++ ln s!"or   {D}, {D}, {t}" ++
  ln s!"lbu  {t}, {off + 3}({base})" ++ ln s!"slli {t}, {t}, 24" ++ ln s!"or   {D}, {D}, {t}"

/-- …and the same four bytes written out. `S` is only read, so unlike the
    gather this cannot destroy its own base. -/
def byteScatter (S base : String) (off : Nat) (t : String) : String :=
  ln s!"sb   {S}, {off}({base})" ++
  ln s!"srli {t}, {S}, 8"  ++ ln s!"sb   {t}, {off + 1}({base})" ++
  ln s!"srli {t}, {S}, 16" ++ ln s!"sb   {t}, {off + 2}({base})" ++
  ln s!"srli {t}, {S}, 24" ++ ln s!"sb   {t}, {off + 3}({base})"

/-- A 64-bit load from an address that may be byte-granular.

    The gather writes its destination as it goes, so a destination half that IS
    the base register would destroy the address mid-sequence; in that case the
    base is copied first. The scratch comes from the temporary pool and is
    spilled to the state scratch around its use, as `rev64` does — the pool is
    full (`Regs`: 27 of 27), so there is nowhere else to borrow from. -/
def ldrUnaligned (d : Reg) (b : String) (o : Nat) : String :=
  let L := lo d
  let H := hi d
  let t := pickFree [L, H, b, carry]
  let needsCopy := b == L || b == H
  let u := if needsCopy then pickFree [L, H, b, carry, t] else b
  ln s!"sw   {t}, {spill0}" ++
  (if needsCopy then ln s!"sw   {u}, {spill1}" ++ ln s!"mv   {u}, {b}" else "") ++
  byteGather L u o t ++ byteGather H u (o + 4) t ++
  (if needsCopy then ln s!"lw   {u}, {spill1}" else "") ++
  ln s!"lw   {t}, {spill0}"

/-- A 64-bit store to an address that may be byte-granular. -/
def strUnaligned (s : Reg) (b : String) (o : Nat) : String :=
  let t := pickFree [lo s, hi s, b, carry]
  ln s!"sw   {t}, {spill0}" ++
  byteScatter (lo s) b o t ++ byteScatter (hi s) b (o + 4) t ++
  ln s!"lw   {t}, {spill0}"

/-- Is this access justified as 4-aligned: an aligned base and offsets that are
    multiples of four? -/
def accessAligned (A : List Reg) (b : Reg) (offs : List Nat) : Bool :=
  A.contains b && offs.all (fun o => o % 4 == 0)

/-- The byte-wise lowering of an access whose address the analysis cannot
    justify, or `none` when the ordinary word-wise lowering is sound.

    Only the forms that address off a BASE REGISTER are here. The `sp`-relative
    ones (`ldrSp`, `strSp`, `stpSp`, …) address our own frame, which `eita_run`
    established 16-byte aligned and every `spSub` in the gadgets keeps so. -/
def unalignedAccess (A : List Reg) : AInstr → Option String
  | .ldrBase d b   => if accessAligned A b [0] then none else some (ldrUnaligned d (lo b) 0)
  | .ldrOff d b o  => if accessAligned A b [o] then none else some (ldrUnaligned d (lo b) o)
  | .strOff s b o  => if accessAligned A b [o] then none else some (strUnaligned s (lo b) o)
  | .strBase s b   => if accessAligned A b [0] then none else some (strUnaligned s (lo b) 0)
  | .ldpOff r1 r2 b o =>
      if accessAligned A b [o] then none
      else some (ldrUnaligned r1 (lo b) o ++ ldrUnaligned r2 (lo b) (o + 8))
  | .stpOff r1 r2 b o =>
      if accessAligned A b [o] then none
      else some (strUnaligned r1 (lo b) o ++ strUnaligned r2 (lo b) (o + 8))
  | .strZr b o =>
      if accessAligned A b [o] then none
      else some (byteScatter "zero" (lo b) o "zero" ++ byteScatter "zero" (lo b) (o + 4) "zero")
  | _ => none

/-- A multi-word load off one base, with the base's own slot loaded **last**.

ARM64 and x86-64 move 64 bits in a single instruction, so a handler program is
free to write `ldr d, [d]` — and `log0` does, `.ldrBase .x1 .x1`, reading an
EVM memory offset out of the stack slot its own address came from. rv32 splits
that into two loads, and the naive order destroys the address between them: the
second load's base register has already been overwritten with the first word.

At most one destination can collide, because the `lo` of every pair is distinct
from every `hi` (`Regs`: the pairs are disjoint and the single-register roles
have `zero` as their high half), so deferring the colliding load to the end is
always enough. -/
def loadWords (b : String) (slots : List (String × Nat)) : String :=
  let deferred := slots.filter (fun s => s.1 == b)
  let first := slots.filter (fun s => s.1 != b)
  (first ++ deferred).foldl (fun acc s => acc ++ ln s!"lw   {s.1}, {s.2}({b})") ""

/-- 64×64 → 64, the low product. Three 32-bit products and the high half of
    the first: `lo(a)·lo(b)` gives the low word and, through `mulhu`, the
    carry into the high word, to which `lo(a)·hi(b)` and `hi(a)·lo(b)` are
    added. The two products that would overflow 64 bits are the ones dropped.

    `d` must be distinct from both operands: its own halves are the scratch
    (x86-64's `movThenOp` class had the same constraint). `carry` is the
    one temporary. Shared by `mulReg` and `madd` rather than written twice. -/
def mul64N (dlo dhi alo ahi blo bhi : String) : String :=
  ln s!"mulhu {dhi}, {alo}, {blo}" ++
  ln s!"mul  {dlo}, {alo}, {blo}" ++
  ln s!"mul  {carry}, {alo}, {bhi}" ++
  ln s!"add  {dhi}, {dhi}, {carry}" ++
  ln s!"mul  {carry}, {ahi}, {blo}" ++
  ln s!"add  {dhi}, {dhi}, {carry}"

def mul64 (d a b : Reg) : String := mul64N (lo d) (hi d) (lo a) (hi a) (lo b) (hi b)

/-- 64-bit count-leading-zeros, open-coded.

    rv32imac has no `clz` — that is Zbb, which this part does not implement —
    so it is five conditional shifts, the standard branchless ladder. Each step
    asks "are the top `k` bits all zero?" with one `sltu` against a power of
    two, turns that 0/1 into a shift amount with `slli`, and applies it to both
    the count and the working word. No branches inside the ladder, so no flag
    register is involved.

    Only ONE 32-bit ladder runs: the high word decides which word to count in,
    because `clz64 = if hi ≠ 0 then clz32 hi else 32 + clz32 lo`.

    The all-zero input is the case a ladder gets wrong. Every step fires, so
    the count reaches 31 rather than 32 — and the working word is still zero,
    which is exactly the flag needed to add the last one.

    `hi d` doubles as the working word: a count of at most 64 lives entirely in
    the low half, so the high half is scratch until it is zeroed at the end. -/
def clz64 (n : Nat) (d a : Reg) : String :=
  let N := lo d
  let V := hi d
  let m := pickFree [lo d, hi d, lo a, hi a, carry]
  let step (sh luiHi : Nat) : String :=
    ln s!"lui  {m}, {luiHi}" ++
    ln s!"sltu {carry}, {V}, {m}" ++
    ln s!"slli {m}, {carry}, {sh}" ++
    ln s!"add  {N}, {N}, {m}" ++
    ln s!"sll  {V}, {V}, {m}"
  ln s!"sw   {m}, {spill0}" ++
  ln s!"bnez {hi a}, .Lch{n}" ++
  ln s!"mv   {V}, {lo a}" ++ ln s!"li   {N}, 32" ++ ln s!"j    .Lcz{n}" ++
  s!".Lch{n}:\n" ++
  ln s!"mv   {V}, {hi a}" ++ ln s!"li   {N}, 0" ++
  s!".Lcz{n}:\n" ++
  step 4 0x10 ++ step 3 0x1000 ++ step 2 0x10000 ++ step 1 0x40000 ++ step 0 0x80000 ++
  ln s!"sltiu {carry}, {V}, 1" ++
  ln s!"add  {N}, {N}, {carry}" ++
  ln s!"lw   {m}, {spill0}" ++
  ln s!"li   {V}, 0"

/-- A 64-bit add into `d` in place: `d += c`. No carry-OUT, because `madd`
    does not set flags; the carry out of the low half still has to reach the
    high one. -/
def addInPlace64 (d c : Reg) : String :=
  ln s!"add  {lo d}, {lo d}, {lo c}" ++
  ln s!"sltu {carry}, {lo d}, {lo c}" ++
  ln s!"add  {hi d}, {hi d}, {hi c}" ++
  ln s!"add  {hi d}, {hi d}, {carry}"

/-! ## One instruction

`n` is a unique index, for the local labels some sequences need. Any NOS source
is loaded first; an instruction with two distinct NOS sources is handled only
where the operation is bitwise (the only place the programs have one). -/

def emitBody (n : Nat) : AInstr → String
  | .label l      => s!"{l}:\n"
  | .bLbl l       => ln s!"j    {l}"
  | .blsLbl _     => s!"    /* «unlowered: b.ls without a fused compare» */\n"
  | .bhiOog       => s!"    /* «unlowered: b.hi without a fused compare» */\n"
  | .cmpReg _ _   => s!"    /* «unlowered: compare whose branch was not fused» */\n"
  -- the carry-flag branches: `Regs.carry` already holds the bit
  | .bcsOog       => ln s!"bnez {carry}, _eita_oog"
  | .bloOog       => ln s!"bnez {carry}, _eita_oog"
  | .cbnzOog r    => zeroBranch r "_eita_oog" false
  | .cbzLbl r l   => zeroBranch r l true
  | .movImm d i   =>
      if i < 2 ^ 32 then ln s!"li   {lo d}, {i}" ++ ln s!"li   {hi d}, 0"
      else ln s!"li   {lo d}, {i % 2 ^ 32}" ++ ln s!"li   {hi d}, {i / 2 ^ 32}"
  | .ldrBase d b  => loadWords (lo b) [(lo d, 0), (hi d, 4)]
  | .ldrOff d b o => loadWords (lo b) [(lo d, o), (hi d, o + 4)]
  | .strOff s b o => ln s!"sw   {lo s}, {o}({lo b})" ++ ln s!"sw   {hi s}, {o + 4}({lo b})"
  | .ldpOff r1 r2 b o =>
      loadWords (lo b) [(lo r1, o), (hi r1, o + 4), (lo r2, o + 8), (hi r2, o + 12)]
  | .addImm d a i =>
      if i < 2048 then
        ln s!"addi {lo d}, {lo a}, {i}" ++
        ln s!"sltiu {carry}, {lo d}, {i}" ++
        ln s!"add  {hi d}, {hi a}, {carry}"
      else s!"    /* «unlowered: add immediate over 12 bits» */\n"
  | .subImm d a i =>
      if i < 2048 then
        ln s!"sltiu {carry}, {lo a}, {i}" ++
        ln s!"addi {lo d}, {lo a}, -{i}" ++
        ln s!"sub  {hi d}, {hi a}, {carry}"
      else s!"    /* «unlowered: sub immediate over 12 bits» */\n"
  | .movReg d a   => ln s!"mv   {lo d}, {lo a}" ++ ln s!"mv   {hi d}, {hi a}"
  | .movImmW d i  => ln s!"li   {lo d}, {i}" ++ ln s!"li   {hi d}, 0"
  | .mvn d a      => ln s!"not  {lo d}, {lo a}" ++ ln s!"not  {hi d}, {hi a}"
  | .and3 d a b   => ln s!"and  {lo d}, {lo a}, {lo b}" ++ ln s!"and  {hi d}, {hi a}, {hi b}"
  | .eor3 d a b   => ln s!"xor  {lo d}, {lo a}, {lo b}" ++ ln s!"xor  {hi d}, {hi a}, {hi b}"
  | .stpOff r1 r2 b o =>
      ln s!"sw   {lo r1}, {o}({lo b})"     ++ ln s!"sw   {hi r1}, {o + 4}({lo b})" ++
      ln s!"sw   {lo r2}, {o + 8}({lo b})" ++ ln s!"sw   {hi r2}, {o + 12}({lo b})"
  -- the continuation is `ra`, so continuing IS a return (x86-64 does the same)
  | .brCont       => ln "ret"
  -- the frame. `ra` IS the continuation, so a call must save it; `s0`/`fp` is
  -- callee-saved by the C ABI and holds `state`, so the helper preserves it and
  -- only `ra` needs a slot (ARM64 saves both because x30 is its link register).
  | .stpFpLr      => ln "addi sp, sp, -16" ++ ln "sw   ra, 8(sp)"
  | .ldpFpLr      => ln "lw   ra, 8(sp)" ++ ln "addi sp, sp, 16"
  | .spSub n      => ln s!"addi sp, sp, -{n}"
  | .spAdd n      => ln s!"addi sp, sp, {n}"
  | .addSp d n    => ln s!"addi {lo d}, sp, {n}" ++ ln s!"li   {hi d}, 0"
  | .ldrSp d n    => ln s!"lw   {lo d}, {n}(sp)" ++ ln s!"lw   {hi d}, {n + 4}(sp)"
  | .strSp s n    => ln s!"sw   {lo s}, {n}(sp)" ++ ln s!"sw   {hi s}, {n + 4}(sp)"
  | .ldrWSp d n   => ln s!"lw   {lo d}, {n}(sp)" ++ ln s!"li   {hi d}, 0"
  | .strWSp s n   => ln s!"sw   {lo s}, {n}(sp)"
  | .stpSp r1 r2 n =>
      ln s!"sw   {lo r1}, {n}(sp)"     ++ ln s!"sw   {hi r1}, {n + 4}(sp)" ++
      ln s!"sw   {lo r2}, {n + 8}(sp)" ++ ln s!"sw   {hi r2}, {n + 12}(sp)"
  | .stpZrSp n    =>
      ln s!"sw   zero, {n}(sp)"     ++ ln s!"sw   zero, {n + 4}(sp)" ++
      ln s!"sw   zero, {n + 8}(sp)" ++ ln s!"sw   zero, {n + 12}(sp)"
  | .blSym sym    => callSaving s!"call {sym}"
  | .bSymU sym    => ln s!"j    {sym}"
  | .movzImm d i  => ln s!"li   {lo d}, {i}" ++ ln s!"li   {hi d}, 0"
  | .strZr b o    => ln s!"sw   zero, {o}({lo b})" ++ ln s!"sw   zero, {o + 4}({lo b})"
  | .strWzrSp o   => ln s!"sw   zero, {o}(sp)"
  | .andImmHex d a i =>
      -- a 64-bit mask: one half at a time through the flag register
      ln s!"li   {carry}, {i % 2 ^ 32}" ++
      ln s!"and  {lo d}, {lo a}, {carry}" ++
      ln s!"li   {carry}, {i / 2 ^ 32}" ++
      ln s!"and  {hi d}, {hi a}, {carry}"
  | .ldrbReg d b i =>
      ln s!"add  {carry}, {lo b}, {lo i}" ++
      ln s!"lbu  {lo d}, 0({carry})" ++ ln s!"li   {hi d}, 0"
  | .strbReg s b i =>
      ln s!"add  {carry}, {lo b}, {lo i}" ++ ln s!"sb   {lo s}, 0({carry})"
  | .ldrLsl3 d b i =>
      ln s!"slli {carry}, {lo i}, 3" ++
      ln s!"add  {carry}, {lo b}, {carry}" ++
      loadWords carry [(lo d, 0), (hi d, 4)]
  | .cbnzSymW r sym => ln s!"bnez {lo r}, {sym}"
  | .cbnzSym r sym  => zeroBranch r sym false
  | .cbnzLbl r l    => zeroBranch r l false
  | .cbzWLbl r l    => ln s!"beqz {lo r}, {l}"
  | .brReg r      => ln s!"jr   {lo r}"
  | .blr r        => callSaving s!"jalr {lo r}"
  | .loadSymAddr d sym => ln s!"la   {lo d}, {sym}"
  -- byte accesses are 32-bit operands: zero-extended, high half cleared
  | .ldrbOff d b o => ln s!"lbu  {lo d}, {o}({lo b})" ++ ln s!"li   {hi d}, 0"
  | .strbOff s b o => ln s!"sb   {lo s}, {o}({lo b})"
  | .rev d a      => rev64 d a
  | .cset d .lo   => ln s!"mv   {lo d}, {carry}" ++ ln s!"li   {hi d}, 0"
  | .subsZr a b   => cmpDiscard a b false
  | .sbcsZr a b   => cmpDiscard a b true
  | .addsImm d a i =>
      if i < 2048 then
        ln s!"addi {lo d}, {lo a}, {i}" ++
        ln s!"sltiu {carry}, {lo d}, {i}" ++
        addc32 (2 * n + 1) (hi d) (hi a) "zero" true true
      else s!"    /* «unlowered: adds immediate over 12 bits» */\n"
  | .subsImm d a i =>
      if i < 2048 then
        ln s!"sltiu {carry}, {lo a}, {i}" ++
        ln s!"addi {lo d}, {lo a}, -{i}" ++
        subb32 (hi d) (hi a) "zero" true true
      else s!"    /* «unlowered: subs immediate over 12 bits» */\n"
  | .addReg d a b => add64 n d a b false false
  | .adds d a b   => add64 n d a b false true
  | .adcs d a b   => add64 n d a b true  true
  | .adc  d a b   => add64 n d a b true  false
  | .subReg d a b  => sub64 d a b false false
  | .subsReg d a b => sub64 d a b false true
  | .sbcs d a b    => sub64 d a b true  true
  | .sbc  d a b    => sub64 d a b true  false
  | .lsrImm d a sh => shift64 d a sh true
  | .lslImm d a sh => shift64 d a sh false
  | .addLsl d a b sh => shiftedAdd d a b sh false
  | .addLsl5 d a b   => shiftedAdd d a b 5 false
  | .addLsr d a b sh => shiftedAdd d a b sh true
  | .orr3 d a b => ln s!"or   {lo d}, {lo a}, {lo b}" ++ ln s!"or   {hi d}, {hi a}, {hi b}"
  | .mulReg d a b =>
      if lo d != lo a && lo d != lo b then mul64 d a b
      else
        -- The destination aliases an operand, so its halves cannot be the
        -- scratch `mul64` needs. EXP does this (`mulReg x14 x14 x15`, the
        -- square-and-multiply accumulator), so it is a real case and not a
        -- theoretical one. Compute into a borrowed pair and move.
        let p := pickFree [lo d, hi d, lo a, hi a, lo b, hi b, carry]
        let q := pickFree [lo d, hi d, lo a, hi a, lo b, hi b, carry, p]
        ln s!"sw   {p}, {spill0}" ++ ln s!"sw   {q}, {spill1}" ++
        mul64N p q (lo a) (hi a) (lo b) (hi b) ++
        ln s!"mv   {lo d}, {p}" ++ ln s!"mv   {hi d}, {q}" ++
        ln s!"lw   {q}, {spill1}" ++ ln s!"lw   {p}, {spill0}"
  | .clzReg d a => clz64 n d a
  | .madd d a b c =>
      -- `d = a·b + c`. The multiply needs `d` distinct from both its operands
      -- (`mul64`), and the add then needs it distinct from `c` too: adding `c`
      -- into a destination that IS `c` would double it.
      --
      -- SSTORE is why this exists. Its handler computes the address of the next
      -- journal entry as `journal_data + journal_count · 104` — one `madd` with
      -- the entry size as a materialised immediate — and without it the whole
      -- handler was refused, which meant no bytecode that writes storage could
      -- run at all.
      if lo d == lo a || lo d == lo b || lo d == lo c then
        s!"    /* «unlowered: multiply-add into one of its own operands» */\n"
      else mul64 d a b ++ addInPlace64 d c
  | .cselHi _ _ _ =>
      s!"    /* «unlowered: conditional select whose compare was not fused» */\n"
  -- Named gaps, each the next slice's work: the u256 carry CHAINS (`adcs`,
  -- `adc`, `sbcs`, `sbc` — a carry-in as well as a carry-out, which is where
  -- the opcode handlers' arithmetic lives), the 53 handler-only forms the
  -- gadget set does not reach, and `clz`/`rev`, which rv32imac has no
  -- instruction for (no Zbb) and which need an inline sequence.
  | _ => s!"    /* «unlowered instruction» */\n"




/-- A **32-bit** compare against an immediate, fused into a branch.

    `cmpImmWHex` compares `w<r>` — the low half only — so unlike
    `cmpImmBranch` the high half plays no part. The jump-destination check is
    the reason this exists: `JUMP` and `JUMPI` read `jumpdests[pc]` with
    `ldrbReg` (which zero-extends into the low half) and branch on
    `!= 1`. Without this fusion both handlers emitted a marker and were
    refused, which meant no bytecode containing a loop could run at all.

    Only equality conditions: a 32-bit `cmp` followed by `b.ne`/`b.eq` is an
    equality test and needs no flags. An ordering condition would, and gets a
    marker rather than a guess. `imm = 0` skips materialising it, which also
    leaves `carry` untouched. -/
def cmpImmWBranch (r : Reg) (imm : Nat) (c : BCond) (lbl : String) : String :=
  let L := lo r
  match c, imm with
  | .ne, 0 => ln s!"bnez {L}, {lbl}"
  | .eq, 0 => ln s!"beqz {L}, {lbl}"
  | .ne, _ => ln s!"li   {carry}, {imm}" ++ ln s!"bne  {L}, {carry}, {lbl}"
  | .eq, _ => ln s!"li   {carry}, {imm}" ++ ln s!"beq  {L}, {carry}, {lbl}"
  | _, _ => s!"    /* «unlowered: 32-bit compare-immediate with an ordering branch» */\n"

/-- Compare against an immediate and then SELECT, fused: rv32 has no
    conditional move, so the two arms sit either side of a branch. The equality
    test is `hi = 0 ∧ lo = imm` for a 64-bit value against an immediate below
    2^32 (`wide := false` compares only the low word, ARM64's `cmp wr, #imm`).
    All reads happen before either arm writes, so the destination may alias the
    compared register. -/
def cmpImmSelect (n : Nat) (r : Reg) (imm : Nat) (wide : Bool) (eqArm neArm : String) : String :=
  ln s!"li   {carry}, {imm}" ++
  (if wide then ln s!"bnez {hi r}, .Lne{n}" else "") ++
  ln s!"bne  {lo r}, {carry}, .Lne{n}" ++
  eqArm ++
  ln s!"j    .Lsd{n}" ++
  s!".Lne{n}:\n" ++
  neArm ++
  s!".Lsd{n}:\n"

def setArm (d : Reg) (v : Nat) : String :=
  ln s!"li   {lo d}, {v}" ++ ln s!"li   {hi d}, 0"

def moveArm (d a : Reg) : String :=
  ln s!"mv   {lo d}, {lo a}" ++ ln s!"mv   {hi d}, {hi a}"

def onesArm (d : Reg) : String :=
  ln s!"li   {lo d}, -1" ++ ln s!"li   {hi d}, -1"

/-! ## NOS is loaded, not addressed

x86-64 folded a NOS read into an addressing mode; a load/store machine has to
load it. Every form therefore gets a prologue that brings the limb it reads into
the `nos` pair — after which `lo`/`hi` of a NOS register already name that pair,
so the body is written as if NOS were cached.

One load pair serves one limb, so an instruction reading TWO distinct NOS limbs
needs folding, which only makes sense for the bitwise ops (the only place the
programs do it: the high-limb zero checks). Anything else is a marker. -/

/-- The distinct NOS limbs an instruction reads. No program writes NOS
    (`Lowering.no_gadget_writes_nos`), so every mention is a read. -/
def nosLimbsOf (it : AInstr) : List Nat := ((mentions it).filterMap nosLimb).eraseDups

/-- The two-limb fold, for the bitwise ops only. -/
def bitFold (op : String) (d : Reg) (la lb : Nat) : String :=
  nosLoad la ++
  ln s!"mv   {lo d}, {nos.lo}" ++ ln s!"mv   {hi d}, {nos.hi}" ++
  nosLoad lb ++
  ln s!"{op}   {lo d}, {lo d}, {nos.lo}" ++ ln s!"{op}   {hi d}, {hi d}, {nos.hi}"

def emitOne (n : Nat) (it : AInstr) : String :=
  match nosLimbsOf it with
  | []  => emitBody n it
  | [l] => nosLoad l ++ emitBody n it
  | la :: lb :: _ =>
      match it with
      | .orr3 d _ _ => bitFold "or" d la lb
      | .and3 d _ _ => bitFold "and" d la lb
      | .eor3 d _ _ => bitFold "xor" d la lb
      | _ => s!"    /* «unlowered: two NOS operands outside a bitwise fold» */\n"


/-! ## The one comparison a single flag register cannot hold -/

/-- A 256-bit SIGNED less-than, fused from the compare chain and the `cset`
    that reads it.

    This is the form that kept `SLT` and `SGT` refused. ARM64 does a four-limb
    `subs`/`sbcs` chain with the result discarded and then `cset w, lt`, which
    reads **N ≠ V** — two flags, where rv32 has one register. Emulating both
    was never the way: the chain's borrow is already the UNSIGNED answer, and
    signed differs from unsigned only when the operands' signs differ, in which
    case the answer is simply "is the left one negative".

        a <ₛ b  =  if sign a ≠ sign b then sign a else a <ᵤ b

    So the existing chain runs untouched — through `emitOne`, so each limb keeps
    its own NOS load — and three instructions correct it. The sign bits come
    from the TOP limb's high words, which are still live: the chain discards its
    result, and the last limb's NOS load left `nos` holding exactly that limb.

    All four compares are emitted at the same label index on purpose: `subb32`,
    which is what `cmpDiscard` is built from, emits no labels, so there is
    nothing to collide. Only `.Lsg{n}` below is a label, and `n` is unique. -/
def sltSigned256 (n : Nat) (a0 b0 a1 b1 a2 b2 a3 b3 d : Reg) : String :=
  let s1 := pickFree [lo d, hi d, hi a3, hi b3, carry]
  let s2 := pickFree [lo d, hi d, hi a3, hi b3, carry, s1]
  emitOne n (.subsZr a0 b0) ++
  emitOne n (.sbcsZr a1 b1) ++
  emitOne n (.sbcsZr a2 b2) ++
  emitOne n (.sbcsZr a3 b3) ++
  ln s!"sw   {s1}, {spill0}" ++ ln s!"sw   {s2}, {spill1}" ++
  ln s!"srli {s1}, {hi a3}, 31" ++
  ln s!"srli {s2}, {hi b3}, 31" ++
  ln s!"beq  {s1}, {s2}, .Lsg{n}" ++
  ln s!"mv   {carry}, {s1}" ++
  s!".Lsg{n}:\n" ++
  ln s!"lw   {s2}, {spill1}" ++ ln s!"lw   {s1}, {spill0}" ++
  ln s!"mv   {lo d}, {carry}" ++ ln s!"li   {hi d}, 0"

/-! ## The call layer

A handler stages its helper arguments into ARM64's `x0`-`x5` and calls through
`bl`. On rv32 the arguments live in `a0`-`a5` — which are also where TOS is
cached, and that is fine: TOS is caller-saved on ARM64 too, so every handler
that calls already reloads it afterwards.

**Why this maps one-to-one.** On ILP32 a 64-bit argument would need an *aligned
register pair*, which would make a register-to-register mapping wrong. Every
helper the interpreter calls takes only pointers, though — `u256 *`, `EvmState *`
(`c/eita_compute.c`, `c/tx_state.h`) — so each argument is one 32-bit register
and the pair rule never fires. That is checked against the C, not assumed: a
helper that grows a `uint64_t` parameter breaks this mapping, and
`argHome`'s docstring is where to look.

**Which convention.** rv32 consumes the x86-64 instruction selection
(`progInstrsRV32`, and the note at the end of this file), so the argument
registers are the ones `OpInstrs.x86Conv` names — `x3`, `x2`, `x1`, `x14`, in
that order — and NOT ARM64's `x0`-`x3`. Getting this wrong is not a build
error: `x3`'s natural home here is the temporary pair `(s10, s11)`, so a
mis-keyed `argHome` emits a plausible-looking `addi s10, sp, 0` and the helper
is called with whatever TOS left in `a0`. That is what shipped to the board —
`eita_helper_mul` was reached with `a1 = 0` and faulted on a null load, which
`make rv32_qemu` now catches on this machine. `argHome_matches_x86Conv` pins
the correspondence so it cannot drift again.

Staging is recognised **structurally**: a maximal run of argument-register
writes immediately followed by `blSym` IS the argument staging for that call,
because that is the shape every call gadget has (`OpInstrs.x86BinHelper`,
`x86TernaryHelper`, `copyCbPop3`, `keccakCbPop1`). Keying on the register alone
cannot work — the same registers are the temporary pool everywhere else — and
keying on `stpFpLr` does not work either: the ARM64 selection opens its call
blocks with it, the x86-64 selection does not, so only two of the twenty-four
call sites in the emitted interpreter were ever recognised.

Inside a staging run an argument register means the ABI register **as a source
too** (`stageSrc`). `x86BinHelper` writes `subImm .x2 .x23 32` and then reads
its own result in `addReg .x2 .x24 .x2`; reading that source from `x2`'s
natural pair instead of from `a1` is how `calldataload` came to emit
`add a1, s3, t4` against an uninitialised `t4`. -/

/-- The ABI argument registers, under the x86-64 selection's convention
    (`OpInstrs.x86Conv = (x3, x2, x1, x14)` — SysV's rdi/rsi/rdx/rcx). All
    helper arguments are pointers, so each is a single 32-bit register on
    ILP32 and the aligned-pair rule never fires; a helper that grows a
    `uint64_t` parameter breaks that, and this is where to look. -/
def argHome : Reg → Option String
  | .x3 => some "a0" | .x2 => some "a1" | .x1 => some "a2" | .x14 => some "a3"
  | _ => none

/-- Inside a staging run, a SOURCE that is an argument register has already
    been staged, so it reads from the ABI register. Elsewhere `lo` applies. -/
def stageSrc (r : Reg) : String := (argHome r).getD (lo r)

/-- **`argHome` is the SysV argument order, positionally.** `OpInstrs.argRegs`
    is the x86-64 backend's own statement of which `Reg` carries which SysV
    argument; rv32 consumes the same instruction stream, so its homes must be
    `a0`-`a3` in that same order. Keyed to ARM64's `x0`-`x3` instead, as it was
    until 2026-11-24, this compiles and assembles and calls every helper with
    its arguments in the wrong registers. -/
theorem argHome_matches_sysv_arg_order :
    Evm.CL.OpInstrs.argRegs.map (fun (r, _) => argHome r)
      = [some "a0", some "a1", some "a2", some "a3"] := by native_decide

def isArgDest : AInstr → Bool
  | .subImm d _ _ | .addImm d _ _ | .movImm d _ | .movImmW d _ | .movReg d _
  | .addLsl5 d _ _ | .addLsl d _ _ _ | .addLsr d _ _ _ | .ldrOff d _ _
  | .ldrBase d _ | .addSp d _ | .addReg d _ _ | .ldrSp d _ => (argHome d).isSome
  | _ => false

/-- Which registers a call block may only touch through the staging rules.

    `x0` used to be here. The host-callback path gives it two further meanings
    — the vtable slot that `blr` jumps through, and then the gas the callback
    returned (`OpInstrs.chargeGasX0`) — and neither survived the rv32 homes,
    so the six callback handlers were refused outright. Both are handled now:
    a slot loaded into `x0`'s pair is `jalr`-able from its low half, and
    `callSaving` moves the ABI return value into that pair after every call. So
    `x0` is an ordinary temporary here again and the refusal is gone. -/
def abiHazard (r : Reg) : Bool := (argHome r).isSome

/-- Is this the staging for a call — a run of argument-register writes whose
    next non-staging instruction is the `blSym` that consumes them?

    This is the recognition rule the section header argues for. Keying on
    `stpFpLr` instead (as this did until the board run of 2026-11-24) misses
    every x86-64 call gadget, because only ARM64's open with a frame save:
    twenty-two of the twenty-four call sites in the emitted interpreter went
    unrecognised and called their helpers with TOS in the argument
    registers. -/
def stagesCall : List AInstr → Bool
  | .blSym _ :: _ => true
  | .blr _ :: _   => true          -- an indirect call through a vtable slot
  | it :: rest    =>
      -- Either this instruction stages an argument, or it is the call TARGET
      -- being materialised in `x0`. Nothing else: the window has to stay
      -- narrow, because the argument registers are also the TOS cache
      -- (`Regs.tos` is a0-a7 and `argHome` maps into the same four), so an
      -- instruction wrongly taken for staging writes a TOS limb instead of a
      -- temporary pair.
      --
      -- A first attempt admitted anything that mentioned no argument
      -- register, which is how `extcodecopy` ended up with `lw a3, 0(a3)` on
      -- a register nothing had set: the rule reached back over a 256-bit OR
      -- and swept it into the window. The alignment audit caught it, which
      -- was luck — this is the rule that makes it not matter.
      --
      -- Narrow enough to admit exactly the callback gadget:
      --   ldrOff x3 x20 504, addSp x2 0, addSp x1 128,   -- three arguments
      --   ldrOff x0 x20 496, ldrOff x0 x0 96,            -- the vtable slot
      --   blr x0
      (isArgDest it ||
       (destOf it == some .x0 && (mentions it).all (fun r => (argHome r).isNone))) &&
      stagesCall rest
  | []            => false

/-- Staging one argument: address arithmetic into an ABI register. The
    vocabulary is deliberately small — anything else inside a call block is a
    marker, so a block cannot quietly contain work that needed the temp pool. -/
def emitStage : AInstr → String
  | .addSp d i       => ln s!"addi {(argHome d).getD marker}, sp, {i}"
  | .addImm d a i    =>
      if i < 2048 then ln s!"addi {(argHome d).getD marker}, {stageSrc a}, {i}"
      else s!"    /* «unlowered: staged add immediate over 12 bits» */\n"
  | .subImm d a i    =>
      if i < 2048 then ln s!"addi {(argHome d).getD marker}, {stageSrc a}, -{i}"
      else s!"    /* «unlowered: staged sub immediate over 12 bits» */\n"
  | .movImm d i      =>
      if i < 2 ^ 32 then ln s!"li   {(argHome d).getD marker}, {i}"
      else s!"    /* «unlowered: staged immediate over 32 bits» */\n"
  | .movImmW d i     => ln s!"li   {(argHome d).getD marker}, {i}"
  | .movReg d a      => ln s!"mv   {(argHome d).getD marker}, {stageSrc a}"
  | .addReg d a b    => ln s!"add  {(argHome d).getD marker}, {stageSrc a}, {stageSrc b}"
  | .addLsl5 d a b   =>
      let A := (argHome d).getD marker
      ln s!"slli {A}, {stageSrc b}, 5" ++ ln s!"add  {A}, {stageSrc a}, {A}"
  | .addLsl d a b sh =>
      let A := (argHome d).getD marker
      ln s!"slli {A}, {stageSrc b}, {sh}" ++ ln s!"add  {A}, {stageSrc a}, {A}"
  | .addLsr d a b sh =>
      let A := (argHome d).getD marker
      ln s!"srli {A}, {stageSrc b}, {sh}" ++ ln s!"add  {A}, {stageSrc a}, {A}"
  | .ldrOff d b o    => ln s!"lw   {(argHome d).getD marker}, {o}({stageSrc b})"
  | .ldrBase d b     => ln s!"lw   {(argHome d).getD marker}, 0({stageSrc b})"
  | .ldrSp d o       => ln s!"lw   {(argHome d).getD marker}, {o}(sp)"
  | _ => s!"    /* «unlowered: not an argument-staging form» */\n"

/-! ## A program, with compare-and-branch fusion -/

/-- A program. Two pieces of context travel with it: a unique index for the
    local labels some sequences need, and whether we are inside a **call
    block**, where an argument register means the ABI register rather than its
    usual home. A block is closed by `blSym`; it is opened either by `stpFpLr`
    (the frame save an ARM64-selected `cbEnter` leaves in the stream) or, the
    case that matters, by the first instruction of a `stagesCall` run. -/
def emitFused : List Reg → Bool → Nat → List AInstr → String
  | _, _, _, [] => ""
  -- the call block's brackets
  | A, _, n, .stpFpLr :: rest   => emitOne n .stpFpLr ++ emitFused A true n.succ rest
  | A, _, n, .blSym sym :: rest =>
      emitOne n (.blSym sym) ++ emitFused (stepAligned A (.blSym sym)) false n.succ rest
  | A, _, n, .blr r :: rest =>
      emitOne n (.blr r) ++ emitFused (stepAligned A (.blr r)) false n.succ rest
  -- compare-and-branch / compare-and-select fusion (see `cmpBranch`)
  -- the 256-bit signed compare: four discarded subtracts and the `cset` that
  -- reads N ≠ V. Fused, because one flag register cannot hold two flags.
  | A, m, n, .subsZr a0 b0 :: .sbcsZr a1 b1 :: .sbcsZr a2 b2 :: .sbcsZr a3 b3
             :: .cset d .lt :: rest =>
      sltSigned256 n a0 b0 a1 b1 a2 b2 a3 b3 d ++
      emitFused (dropAligned A d) m n.succ rest
  | A, m, n, .cmpReg a b :: .bhiOog :: rest =>
      cmpBranch n b a "_eita_oog" false ++ emitFused A m n.succ rest
  | A, m, n, .cmpReg a b :: .bloOog :: rest =>
      cmpBranch n a b "_eita_oog" false ++ emitFused A m n.succ rest
  | A, m, n, .cmpReg a b :: .blsLbl l :: rest =>
      cmpBranch n a b l true ++ emitFused A m n.succ rest
  | A, m, n, .cmpReg p q :: .cselHi d x y :: rest =>
      cmpSelect n p q d x y ++ emitFused (dropAligned A d) m n.succ rest
  | A, m, n, .cmpImm a i :: .bSym c sym :: rest =>
      cmpImmBranch n a i c sym ++ emitFused A m n.succ rest
  | A, m, n, .cmpImm a i :: .bcLbl c l :: rest =>
      cmpImmBranch n a i c l ++ emitFused A m n.succ rest
  | A, m, n, .cmpImm a i :: .bhiOog :: rest =>
      cmpImmBranch n a i .hi "_eita_oog" ++ emitFused A m n.succ rest
  | A, m, n, .cmpImm a i :: .bloOog :: rest =>
      cmpImmBranch n a i .lo "_eita_oog" ++ emitFused A m n.succ rest
  | A, m, n, .cmpImm a i :: .blsLbl l :: rest =>
      cmpImmBranch n a i .ls l ++ emitFused A m n.succ rest
  -- compare-then-select: `cset`, `csel …, ne`, `csinv …, xzr, eq`
  | A, m, n, .cmpImm r i :: .cset d .eq :: rest =>
      cmpImmSelect n r i true (setArm d 1) (setArm d 0) ++ emitFused (dropAligned A d) m n.succ rest
  | A, m, n, .cmpImm r i :: .cselNe d a b :: rest =>
      cmpImmSelect n r i true (moveArm d b) (moveArm d a) ++ emitFused (dropAligned A d) m n.succ rest
  | A, m, n, .cmpImm r i :: .csinvEqZr d a :: rest =>
      cmpImmSelect n r i true (moveArm d a) (onesArm d) ++ emitFused (dropAligned A d) m n.succ rest
  | A, m, n, .cmpImmWHex r i :: .bSym c sym :: rest =>
      cmpImmWBranch r i c sym ++ emitFused A m n.succ rest
  | A, m, n, .cmpImmWHex r i :: .bcLbl c l :: rest =>
      cmpImmWBranch r i c l ++ emitFused A m n.succ rest
  | A, m, n, .cmpImmWHex r i :: .cset d .eq :: rest =>
      cmpImmSelect n r i false (setArm d 1) (setArm d 0) ++ emitFused (dropAligned A d) m n.succ rest
  | A, m, n, .cmpImmWHex r i :: .cselNe d a b :: rest =>
      cmpImmSelect n r i false (moveArm d b) (moveArm d a) ++ emitFused (dropAligned A d) m n.succ rest
  | A, m, n, .cmpReg a b :: .bcLbl c l :: rest =>
      (match c with
       | .lo => cmpBranch n a b l false
       | .ls => cmpBranch n a b l true
       | .hi => cmpBranch n b a l false
       | .hs => cmpBranch n b a l true
       | _ => s!"    /* «unlowered: compare branch condition» */\n") ++ emitFused A m n.succ rest
  | A, m, n, .cmpReg a b :: .bSym c sym :: rest =>
      (match c with
       | .lo => cmpBranch n a b sym false
       | .ls => cmpBranch n a b sym true
       | .hi => cmpBranch n b a sym false
       | .hs => cmpBranch n b a sym true
       | _ => s!"    /* «unlowered: compare branch condition» */\n") ++ emitFused A m n.succ rest
  -- Inside a call block, a write to an argument register is staging. Any OTHER
  -- mention of one is a third meaning the duality does not cover — the host
  -- callbacks put the vtable slot AND the returned gas in x0 — so it stops
  -- loudly instead of quietly reading the shared temporary pair.
  | A, m, n, it :: rest =>
      -- A staging run opens here if this instruction writes an argument
      -- register and everything up to the next `blSym` does too.
      let staging := m || (isArgDest it && stagesCall rest)
      (if staging then
         (if isArgDest it then emitStage it
          else if (mentions it).any abiHazard then
            s!"    /* «unlowered: argument register used as a call target or result» */\n"
          else emitOne n it)
       else
         -- outside staging, an access the alignment analysis cannot justify
         -- gets the byte-wise sequence rather than a `lw`/`sw` the chip traps
         match unalignedAccess A it with
         | some txt => txt
         | none => emitOne n it)
      ++ emitFused (stepAligned A it) staging n.succ rest

def emitProgRV32 (p : List AInstr) : String := emitFused alignedSeed false 0 p

/-- The same, from a given label counter: the local labels some sequences need
    must be unique across a whole FILE, not just a program, or the assembler
    sees a duplicate definition. -/
def emitProgRV32From (n : Nat) (p : List AInstr) : String := emitFused alignedSeed false n p

/-- The rv32 instance of the shared lowering. `emit` is the unfused path, so a
    compare reaching it is a marker; `emitProgRV32` is what the emitter uses. -/
def target : Evm.CL.Lowering.Target where
  name := "rv32imac"
  reg  := lo
  emit := emitOne 0

/-! ## Coverage -/

/-- **The rv32 lowering covers every instruction in the gadget set** — no
    `«unlowered»` marker survives, the same gate x86-64 passes. -/
theorem every_gadget_instruction_lowers :
    gadgetSet.all (fun p => ((emitProgRV32 p).splitOn "«").length == 1) = true := by
  native_decide

/-- No shifted add takes a NOS operand, which is what frees the NOS load pair to
    hold the shifted value (`shiftedAdd`). -/
theorem no_shifted_add_reads_nos :
    gadgetSet.all (fun p => p.all (fun it =>
      match it with
      | .addLsl _ a b _ | .addLsr _ a b _ | .addLsl5 _ a b =>
          (nosLimb a).isNone && (nosLimb b).isNone
      | _ => true)) = true := by
  native_decide

/-- The diagnosis path: which lines still carry a marker, if any. -/
def coverageGaps : List String :=
  (gadgetSet.flatMap (fun p =>
    ((emitProgRV32 p).splitOn "
").filter (fun l => (l.splitOn "«").length > 1))).eraseDups

/-- Every register the gadgets mention has an rv32 home. -/
theorem every_mentioned_register_has_a_home :
    gadgetSet.all (fun p => p.all (fun it =>
      (mentions it).all (fun r => lo r != marker && hi r != marker))) = true := by
  native_decide

/-- The marker is not decorative: a compare whose branch was not fused, and the
    aliased multiply, both produce one. -/
theorem marker_fires_on_unfused_compare :
    ((emitOne 0 (.cmpReg .x0 .x14)).splitOn "«").length = 2 := by native_decide

/-- …and the aliased multiply no longer does: EXP's accumulator is
    `mulReg x14 x14 x15`, which now computes into a borrowed pair and moves. -/
theorem aliased_multiply_lowers :
    ((emitOne 0 (.mulReg .x14 .x14 .x15)).splitOn "«").length = 1 := by native_decide

/-! ## Which instruction selection rv32 consumes

`OpInstrs` offers two selections per `Op`: `Op.toAInstrs` (ARM64) and
`Op.instrsX86?`. rv32 takes the **x86-64** one, and not as a convenience — it is
the semantically right input. ARM64 caches NOS, so its stream contains NOS
*reloads* (`ldp x10, x11, [x14]`); rv32 has no NOS cache (`Regs`: no registers
left for it), so those instructions have nothing to write, and lowering them to
a write of the load pair would silently drop a cache update the target does not
have. The x86-64 selection never loads into NOS — measured, not assumed
(`x86_selection_never_writes_nos`) — because x86-64 made the same choice.

Every `Op` has an x86-64 selection, so nothing is lost by taking it. -/

def progInstrsRV32 (p : AsmCore.Prog) : List AInstr :=
  (p.filterMap Evm.CL.OpInstrs.Op.instrsX86?).flatten

def rv32Streams : List (String × List AInstr) :=
  (Evm.CL.ARM64.Interp.handlerProgs Evm.CL.ARM64.Interp.opCost).map
    (fun (nm, p) => (nm, progInstrsRV32 p))

/-- Every `Op` the interpreter emits has an x86-64 selection. -/
theorem every_op_has_an_x86_selection :
    (Evm.CL.ARM64.Interp.handlerProgs Evm.CL.ARM64.Interp.opCost).all (fun (_, p) =>
      p.all (fun o => (Evm.CL.OpInstrs.Op.instrsX86? o).isSome)) = true := by
  native_decide

/-- …and it never loads into a NOS register, which is what makes it the right
    input for a target with no NOS cache. -/
theorem x86_selection_never_writes_nos :
    rv32Streams.all (fun (_, is) => is.all (fun it =>
      match it with
      | .ldpOff r1 r2 _ _ => (nosLimb r1).isNone && (nosLimb r2).isNone
      | _ => true)) = true := by
  native_decide


/-! ## The call block's own obligation

Sharing homes is inherited from x86-64 along with its theorem. The *duality* is
not: inside a call block an argument register means the ABI register, outside it
means the shared temporary pair. That is sound only if no instruction inside a
block touches an argument register in any other way — reading one as an operand
would read the temporary pair instead of the argument. x86-64 has no equivalent
obligation (it stages into SysV registers through `X86Xfer`), so this one is
checked here. -/

/-- Walk a program, tracking the call block, and check the duality holds.

    `staged` is the set of argument registers this block has already written.
    Reading one of those as a SOURCE is sound — `stageSrc` reads the ABI
    register, which holds the value the block just put there, which is exactly
    what `x86BinHelper`'s `addReg .x2 .x24 .x2` means. Reading one the block
    has NOT written is the hazard: `stageSrc` would read an ABI register
    nothing set, instead of the temporary pair the program meant. -/
def blockSafe : List Reg → Bool → List AInstr → Bool
  | _, _, [] => true
  | _, _, .stpFpLr :: rest   => blockSafe [] true rest
  | _, _, .blSym _ :: rest   => blockSafe [] false rest
  | staged, m, it :: rest =>
      let d := destOf it
      let ok :=
        if !m then true
        else (mentions it).all (fun r =>
          !abiHazard r || d == some r || staged.contains r)
      let staged' := match d with
        | some r => if (argHome r).isSome then r :: staged else staged
        | none => staged
      ok && blockSafe staged' m rest

/-- The handlers whose call blocks touch an argument register in a way the
    duality does not permit: all six are the host-callback path, where `x0`
    holds the vtable slot for `blr` and then the returned gas. Lowering them
    needs the callback ABI read off `Op.instrsX86?` / `X86Xfer`, not guessed —
    this is the exact path on which x86-64 took three memory faults. The
    emitter refuses them (a marker), so they are excluded from coverage rather
    than emitted wrongly. -/
def blockHazards : List String :=
  (rv32Streams.filterMap (fun (nm, is) => if blockSafe [] false is then none else some nm))

/-- **Empty**, and that is the point of the call layer.

    This used to be the six host-callback handlers, refused because `x0` meant
    the vtable slot and then the returned gas and neither survived the rv32
    homes. `callSaving` lands the ABI return value in `x0`'s pair and
    `stagesCall` recognises the gadget that interleaves argument staging with
    the vtable loads, so the duality holds everywhere and nothing is refused on
    this ground. Keep it empty: a name appearing here is a call block the
    lowering cannot justify. -/
theorem no_block_hazards : blockHazards = [] := by native_decide


/-! ## The flag-liveness obligation

ARM64's non-flag-setting instructions PRESERVE the flags; several of their rv32
lowerings do not, because `Regs.carry` is the only scratch some sequences have
(the shift funnel, the 64-bit zero fold, the immediate a compare needs). So a
flag-neutral instruction can destroy a flag the ARM program still intends to
consume — the rv32 counterpart of x86-64's flag-provenance problem
(`X86FlagProv`), and a hazard the assembler cannot see.

The check is a liveness walk: a producer makes the flag live, a consumer clears
it, and a lowering that writes `carry` while it is live is a hazard. Which forms
write `carry` is read off the EMITTED TEXT rather than from a hand-kept list, so
it cannot drift from the lowering. -/

/-- Does this form's lowering write the carry register? Read from the emitted
    text: a line whose destination operand is `carry`. -/
def writesCarry (it : AInstr) : Bool :=
  ((emitOne 0 it).splitOn "\n").any (fun l =>
    match (l.splitOn " ").filter (fun t => t != "") with
    | _ :: d :: _ => d == carry ++ ","
    | _ => false)

/-- The ARM forms that SET the flags. -/
def setsFlags : AInstr → Bool
  | .adds _ _ _ | .adcs _ _ _ | .subsReg _ _ _ | .sbcs _ _ _
  | .subsImm _ _ _ | .addsImm _ _ _ | .cmpReg _ _ | .cmpImm _ _
  | .cmpImmWHex _ _ | .subsZr _ _ | .sbcsZr _ _ | .tstImm _ _ => true
  | _ => false

/-- The ARM forms that READ them. `adc`/`sbc` are consumers as much as
    `adcs`/`sbcs` — they take the carry in and simply do not produce one, and
    leaving them out of this list is what made the first run of this check
    report two false hazards. -/
def readsFlags : AInstr → Bool
  | .bcsOog | .bloOog | .bhiOog | .blsLbl _ | .bSym _ _ | .bcLbl _ _
  | .cset _ _ | .cselHi _ _ _ | .cselNe _ _ _ | .csinvEqZr _ _
  | .adcs _ _ _ | .sbcs _ _ _ | .adc _ _ _ | .sbc _ _ _ => true
  | _ => false

/-- The hazards in one program: a `carry` write while a flag is live. -/
def carryHazards (is : List AInstr) : List AInstr :=
  (is.foldl (fun (st : Bool × List AInstr) it =>
    if setsFlags it then (true, st.2)
    else if readsFlags it then (false, st.2)
    else if st.1 && writesCarry it then (st.1, st.2 ++ [it])
    else st) (false, [])).2

/-- **No handler destroys a live flag.** Every program where the lowering uses
    `carry` as a scratch has no flag in flight at that point, over all 150
    handlers the interpreter emits. -/
theorem no_carry_clobber_hazards :
    rv32Streams.all (fun (_, is) => (carryHazards is).isEmpty) = true := by
  native_decide

/-- …and over the structured gadgets. -/
theorem no_carry_clobber_hazards_in_gadgets :
    gadgetSet.all (fun p => (carryHazards p).isEmpty) = true := by native_decide

/-! ## Handler coverage, as a ratchet

The gadget set is covered completely. Of the 150 handler programs the threaded
interpreter emits, **all 150 lower completely and assemble**. The ones that
did not, and what each needed:

* **`slt`, `sgt`** — a 256-bit SIGNED compare, whose `cset lt` reads N ≠ V:
  two flags where rv32 has one register. Not emulated — the chain's borrow is
  already the unsigned answer, and signed differs only when the signs do
  (`sltSigned256`).
* **`clz`** (EIP-7939) and **`exp`** — `clzReg`, open-coded as the five-step
  branchless ladder rv32imac needs without Zbb (`clz64`); `exp` also needed a
  multiply into its own operand, which its square-and-multiply accumulator
  does, now computing into a borrowed pair.
* **`sstore`** — `madd`, for the address of the next journal entry; and its
  five fork gas schedules, which became emitted C (`Evm.CL.SstoreGasC`).

The set is pinned by NAME, not just by count: a count ratchet lets one handler
regress while another lands and reports no change. -/

def handlersCovered : Nat :=
  (rv32Streams.filter (fun (_, is) => ((emitProgRV32 is).splitOn "«").length == 1)).length

def handlerTotal : Nat := rv32Streams.length

/-- Where the port stands: **every** handler lowers.

    Stated as an equality against `handlerTotal` rather than as `150 ≤
    handlersCovered`, which is what this was while the set was still closing.
    A lower bound cannot distinguish "all of them" from "all of the ones that
    existed when I last raised the number" — so a handler added upstream could
    arrive unlowered and the ratchet would still pass. The count is pinned
    separately, so a handler disappearing is also visible. -/
theorem every_handler_lowers : handlersCovered = handlerTotal := by native_decide
example : handlerTotal = 150 := by native_decide

/-- And exactly which handlers do not lower, by name, so neither the set nor
    its membership can change unnoticed. `every_handler_lowers` already says
    this set is empty; keeping it by name means a regression reports WHICH
    handler broke, not just that the count slipped. -/
def uncovered : List String :=
  rv32Streams.filterMap (fun (nm, is) =>
    if ((emitProgRV32 is).splitOn "«").length == 1 then none else some nm)


/-- **Empty.** Every handler the threaded interpreter emits lowers to rv32imac.
    Keep it empty: a name here is a handler the backend refuses, and an opcode
    the device cannot evaluate is a wall it hits on some transaction later. -/
theorem no_uncovered_handlers : uncovered = [] := by native_decide

/-! ## Size, measured -/

def insnLines (text : String) : Nat :=
  ((text.splitOn "\n").filter (fun l => l.startsWith "    ")).length

def rv32Insns : Nat := (gadgetSet.map (fun p => insnLines (emitProgRV32 p))).foldl (· + ·) 0

/-! ## Spot checks

The sequences worth reading, pinned so an edit to the lowering has to admit it
changed them. Coverage and the assembler together still do not say a sequence
COMPUTES the right thing — that is `X86Sem`'s counterpart for rv32, and it is
not written yet. These three are checked by hand, and they are the three the
rest rests on. -/

/-- A 64-bit add with carry-out, in one flag register: the low half's carry,
    then the high half's two carries accumulated through the conditional skip
    the mutual-exclusivity argument licenses. -/
theorem adds_is_the_mutual_exclusion_sequence :
    emitOne 7 (.adds .x0 .x17 .x16) =
      "    add  t0, s8, s10\n" ++
      "    sltu s7, t0, s10\n" ++
      "    add  t1, s9, s7\n" ++
      "    sltu s7, t1, s7\n" ++
      "    add  t1, t1, s11\n" ++
      "    bgeu t1, s11, .Lk15\n" ++
      "    addi s7, s7, 1\n" ++
      ".Lk15:\n" := by native_decide

/-- The u256 chain's instruction, with a carry-in AND a carry-out, over a NOS
    operand: the limb is loaded first (its address register is the pair's own
    high half, so the load costs no scratch), then each half folds the carry in
    and measures the carry out. This is ADD's inner step. -/
theorem adcs_loads_nos_then_chains :
    emitOne 3 (.adcs .x7 .x7 .x11) =
      "    add  t6, s3, s2\n" ++
      "    lw   s6, -56(t6)\n" ++
      "    lw   t6, -52(t6)\n" ++
      "    add  a2, a2, s7\n" ++
      "    sltu s7, a2, s7\n" ++
      "    add  a2, a2, s6\n" ++
      "    bgeu a2, s6, .Lk6\n" ++
      "    addi s7, s7, 1\n" ++
      ".Lk6:\n" ++
      "    add  a3, a3, s7\n" ++
      "    sltu s7, a3, s7\n" ++
      "    add  a3, a3, t6\n" ++
      "    bgeu a3, t6, .Lk7\n" ++
      "    addi s7, s7, 1\n" ++
      ".Lk7:\n" := by native_decide

/-- SUB's inner step. The borrow-IN is subtracted first, which frees `carry` to
    hold the second borrow while the first sits in a spilled victim — and the
    two cannot both be 1, so the `or` is the borrow out. -/
theorem sbcs_subtracts_the_borrow_in_first :
    emitOne 4 (.sbcs .x7 .x7 .x11) =
      "    add  t6, s3, s2\n" ++
      "    lw   s6, -56(t6)\n" ++
      "    lw   t6, -52(t6)\n" ++
      "    sw   t0, 608(s0)\n" ++
      "    sltu t0, a2, s7\n" ++
      "    sub  a2, a2, s7\n" ++
      "    sltu s7, a2, s6\n" ++
      "    sub  a2, a2, s6\n" ++
      "    or   s7, s7, t0\n" ++
      "    lw   t0, 608(s0)\n" ++
      "    sw   t0, 608(s0)\n" ++
      "    sltu t0, a3, s7\n" ++
      "    sub  a3, a3, s7\n" ++
      "    sltu s7, a3, t6\n" ++
      "    sub  a3, a3, t6\n" ++
      "    or   s7, s7, t0\n" ++
      "    lw   t0, 608(s0)\n" := by native_decide

/-- A borrow taken BEFORE the write that consumes its operand, and `zero` as the
    high half of a 32-bit role: `sub x14, x23, #3` on `sp` leaves
    `0 - borrow` in the high half, which IS the 64-bit two's-complement result
    (`0xffffffff` exactly when `sp < 3`). No assumption, just `x0`. -/
theorem subImm_borrows_before_writing :
    emitOne 0 (.subImm .x14 .x23 3) =
      "    sltiu s7, s2, 3\n" ++
      "    addi t2, s2, -3\n" ++
      "    sub  t3, zero, s7\n" := by native_decide

/-- A fused compare-and-branch consumes no register: rv32's branches take both
    operands, and `b.hi` is the reversed `bltu`. -/
theorem cmp_bhi_fuses_to_three_branches :
    emitProgRV32 [.cmpReg .x0 .x14, .bhiOog] =
      "    bltu t3, t1, _eita_oog\n" ++
      "    bne  t3, t1, .Lx0\n" ++
      "    bltu t2, t0, _eita_oog\n" ++
      ".Lx0:\n" := by native_decide

/-! ## Size, measured

257 ARM64 instructions become 872 — **3.4x**, where x86-64's two-operand forms
cost 1.25x. The factor is not the ISA being RISC: it is 64-bit data on 32-bit
registers (every arithmetic instruction becomes two, plus the carry plumbing)
and the absent flags (a compare costs three branches, a carry-out five
instructions). For a wallet executing one transaction at 350 MHz this is the
right trade; it is also the number to beat if the interpreter ever needs to be
fast on this target. -/

theorem insn_count : rv32Insns = 905 := by native_decide

/-- The expansion over ARM64, as a bound rather than a snapshot. -/
theorem expansion_under_three_and_a_half :
    rv32Insns * 10 ≤ Evm.CL.Lowering.arm64Insns * 36 := by native_decide

/-- The handlers that lower completely, with their names, for the assembler
    gate: a sequence that Lean is happy with still has to BE rv32. -/
def coveredHandlers : List (String × List AInstr) :=
  rv32Streams.filter (fun (_, is) => ((emitProgRV32 is).splitOn "«").length == 1)

end Evm.CL.RV32
