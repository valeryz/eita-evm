/-
  Evm.CL.ARM64.SstoreGas — emit the per-fork SSTORE gas/refund plans and
  the per-fork access-cost data table, both evaluated out of the Lean
  spec (Stage C-2 of the native-tier fork lane).

  ## SSTORE plan functions

  One symbol per gas schedule; the host's cb-sstore dispatches on
  `*fork-ord*`:

    _eita_sstore_gas_legacy    Frontier..Byzantium and Petersburg
                               (ord < 6 or ord = 7)
    _eita_sstore_gas_eip1283   Constantinople (ord = 6)
    _eita_sstore_gas_eip2200   Istanbul/MuirGlacier (ord 8, 9)
    _eita_sstore_gas_berlin    Berlin (ord 10)
    _eita_sstore_gas_london    London+ (ord ≥ 11)

  Every constant below is *probed out of the corresponding spec-side
  `sstoreGas` function* (Stage B pattern) — a schedule change in the
  spec re-emits here without hand edits. Each plan's REFUND CLAMP
  DISCIPLINE is reproduced exactly:

    legacy    unconditional add (never negative)
    eip1283   one signed sum, clamped at 0 once
    eip2200   sequential adjustments, each clamped at 0
    berlin    add first, then one subtraction clamped at 0
    london    same shape as berlin, EIP-3529 constants

  C ABI (AAPCS64), uniform across all five:

    void eita_sstore_gas_*(uint64_t out[2],      // x0: {cost, newRefund}
                           uint64_t refund,      // x1: refund counter in
                           const uint64_t *orig, // x2: 4 LE limbs
                           const uint64_t *cur,  // x3: 4 LE limbs
                           const uint64_t *neu,  // x4: 4 LE limbs
                           uint64_t cold);       // x5: bit0 (berlin/london)

  `orig` is ignored by `legacy`; `cold` is ignored by all pre-Berlin
  plans. Precondition: `refund + 65536 < 2^63` (the eip1283 clamp reads
  the sign bit of `refund + delta`, so the counter needs headroom for
  the largest delta; it is bounded by gas spent, so this always holds —
  `SstoreGasSem` proves the routines under exactly this bound).

  ## Access-cost table

  `_eita_access_costs[ord][kind] = {cold, warm}` (uint64 pairs), kinds
  0 = sload, 1 = balance, 2 = extcodesize/copy, 3 = extcodehash. Warm
  entries are `(Op.metadata fork op).staticCost` — the same ladder the
  IR compiler charges from — and cold entries are the Berlin spec
  constants (pre-Berlin cold = warm: no access lists). An op that does
  not exist on a fork (EXTCODEHASH pre-Constantinople) gets {0, 0};
  the dispatch table faults on the opcode before any cb runs.

  The differential gate `tests/audit-call-gas.lisp` (extended in
  Stage C-6) compares these symbols against Lean-oracle vectors.
-/

import Evm.CL.ARM64
import Evm.CL.Frame
import Evm.CL.ARM64.SstoreGasDenote
import Evm.IR.Types
import Evm.Frontier.Vm.Instructions
import Evm.Constantinople.Vm.Instructions.Storage
import Evm.Istanbul.Vm.Instructions.Storage
import Evm.Berlin.Vm.Instructions.Storage
import Evm.London.Vm.Effect

namespace Evm.CL.ARM64.SstoreGas

/-! ## Spec probes

    Constants are extracted by evaluating the spec functions at
    distinguished `(original, current, new)` points. 0/1/2 are
    arbitrary distinct nonzero/zero markers. -/

private def frontierP (cur new_ : Evm.U256) : Nat × Nat :=
  Evm.Frontier.Vm.Instructions.sstoreGas 0 cur new_

private def eip1283P (refund : Nat) (o c n : Evm.U256) : Nat × Nat :=
  Evm.Constantinople.Vm.Instructions.sstoreGas refund o c n

private def eip2200P (refund : Nat) (o c n : Evm.U256) : Nat × Nat :=
  Evm.Istanbul.Vm.Instructions.sstoreGas refund o c n

private def berlinP (refund : Nat) (cold : Bool) (o c n : Evm.U256) :
    Nat × Nat :=
  Evm.Berlin.Vm.Instructions.Storage.sstoreGas refund cold o c n

private def londonP (refund : Nat) (cold : Bool) (o c n : Evm.U256) :
    Nat × Nat :=
  Evm.London.Vm.Effect.sstoreGas refund cold o c n

/-! ## Asm helpers

    Scratch discipline: x6-x9, x16, x17 are helper scratch; predicate
    results live in x10-x15 (computed by the prologue BEFORE x16/x17
    are reused for cost/refund accumulation). -/

/-- OR-fold the four limbs at `[p]`; `dst := 1` iff the u256 is zero. -/
private def isZero (p dst : String) : String :=
  s!"    ldp   x6, x7, [{p}]\n" ++
  s!"    ldp   x8, x9, [{p}, #16]\n" ++
  "    orr   x6, x6, x7\n" ++
  "    orr   x8, x8, x9\n" ++
  "    orr   x6, x6, x8\n" ++
  "    cmp   x6, #0\n" ++
  s!"    cset  {dst}, eq\n"

/-- XOR/OR-fold limb pairs; `dst := 1` iff the u256s at `[p]`/`[q]`
    are equal. -/
private def isEq (p q dst : String) : String :=
  s!"    ldp   x6, x7, [{p}]\n" ++
  s!"    ldp   x8, x9, [{q}]\n" ++
  "    eor   x6, x6, x8\n" ++
  "    eor   x7, x7, x9\n" ++
  "    orr   x6, x6, x7\n" ++
  s!"    ldp   x8, x9, [{p}, #16]\n" ++
  s!"    ldp   x16, x17, [{q}, #16]\n" ++
  "    eor   x8, x8, x16\n" ++
  "    eor   x9, x9, x17\n" ++
  "    orr   x8, x8, x9\n" ++
  "    orr   x6, x6, x8\n" ++
  "    cmp   x6, #0\n" ++
  s!"    cset  {dst}, eq\n"

/-- Full predicate prologue: x10 origZero, x11 curZero, x12 newZero,
    x13 origEqCur, x14 curEqNew, x15 origEqNew. -/
private def prologue : String :=
  isZero "x2" "x10" ++ isZero "x3" "x11" ++ isZero "x4" "x12" ++
  isEq "x2" "x3" "x13" ++ isEq "x3" "x4" "x14" ++ isEq "x2" "x4" "x15"

/-- Pre-EIP-1283 plan (Frontier..Byzantium, Petersburg): cost depends
    only on `(current = 0, new ≠ 0)`; refund is an unconditional add. -/
private def legacyCodeSpec : String :=
  let setCost     := (frontierP 0 1).1
  let resetCost   := (frontierP 1 2).1
  let clearRefund := (frontierP 1 0).2
  "\n.global _eita_sstore_gas_legacy\n" ++
  ".p2align 2\n" ++
  "_eita_sstore_gas_legacy:\n" ++
  isZero "x3" "x11" ++
  isZero "x4" "x12" ++
  -- cost = (curZero ∧ ¬newZero) ? set : reset
  movImm "x16" resetCost ++
  movImm "x17" setCost ++
  "    eor   x9, x12, #1\n" ++
  "    and   x9, x9, x11\n" ++
  "    cmp   x9, #0\n" ++
  "    csel  x16, x16, x17, eq\n" ++
  -- refund' = refund + ((¬curZero ∧ newZero) ? clear : 0)
  "    eor   x9, x11, #1\n" ++
  "    and   x9, x9, x12\n" ++
  movImm "x8" clearRefund ++
  "    cmp   x9, #0\n" ++
  "    csel  x8, xzr, x8, eq\n" ++
  "    add   x17, x1, x8\n" ++
  "    stp   x16, x17, [x0]\n" ++
  "    ret\n"

/-- EIP-1283 (Constantinople): signed delta summed across both refund
    rules, clamped at 0 ONCE — `sstoreGas`'s `(refund + Δ).toNat`. -/
private def eip1283CodeSpec : String :=
  let noopCost   := (eip1283P 0 1 1 1).1
  let setCost    := (eip1283P 0 0 0 1).1
  let resetCost  := (eip1283P 0 1 1 2).1
  let dirtyCost  := (eip1283P 0 1 2 3).1
  let clearRef   := (eip1283P 0 1 1 0).2
  let resetZeroR := (eip1283P 0 0 1 0).2
  let resetNzR   := (eip1283P 0 1 2 1).2
  "\n.global _eita_sstore_gas_eip1283\n" ++
  ".p2align 2\n" ++
  "_eita_sstore_gas_eip1283:\n" ++
  prologue ++
  "    cbz   x14, 1f\n" ++              -- ¬curEqNew → 1
  movImm "x16" noopCost ++
  "    mov   x17, x1\n" ++
  "    b     9f\n" ++
  "1:\n" ++
  "    cbz   x13, 2f\n" ++              -- ¬origEqCur → dirty
  "    cbz   x10, 3f\n" ++              -- ¬origZero → 3
  movImm "x16" setCost ++
  "    mov   x17, x1\n" ++
  "    b     9f\n" ++
  "3:\n" ++                              -- fresh, orig ≠ 0
  movImm "x16" resetCost ++
  movImm "x8" clearRef ++
  "    cmp   x12, #0\n" ++
  "    csel  x8, xzr, x8, eq\n" ++       -- + clear iff newZero
  "    add   x17, x1, x8\n" ++
  "    b     9f\n" ++
  "2:\n" ++                              -- dirty
  movImm "x16" dirtyCost ++
  "    mov   x9, #0\n" ++                -- signed Δ
  "    cbnz  x10, 4f\n" ++               -- origZero → skip clear rules
  "    cbz   x11, 5f\n" ++
  movImm "x8" clearRef ++
  "    sub   x9, x9, x8\n" ++            -- current = 0: Δ -= clear
  "5:\n" ++
  "    cbz   x12, 4f\n" ++
  movImm "x8" clearRef ++
  "    add   x9, x9, x8\n" ++            -- new = 0: Δ += clear
  "4:\n" ++
  "    cbz   x15, 6f\n" ++               -- origEqNew?
  movImm "x8" resetNzR ++
  movImm "x7" resetZeroR ++
  "    cmp   x10, #0\n" ++
  "    csel  x8, x7, x8, ne\n" ++        -- origZero picks the 19800 row
  "    add   x9, x9, x8\n" ++
  "6:\n" ++
  "    add   x17, x1, x9\n" ++           -- refund + Δ (two's complement)
  "    cmp   x17, #0\n" ++
  "    csel  x17, xzr, x17, lt\n" ++     -- single signed clamp
  "9:\n" ++
  "    stp   x16, x17, [x0]\n" ++
  "    ret\n"

/-- EIP-2200 (Istanbul/MuirGlacier): SEQUENTIAL refund adjustments,
    each clamped at 0 — Istanbul `sstoreGas`'s `adjustRefund` chain.
    The EIP-1706 gasLeft ≤ 2300 trip-wire stays host/handler-side. -/
private def eip2200CodeSpec : String :=
  let sloadCost  := (eip2200P 0 1 1 1).1
  let setCost    := (eip2200P 0 0 0 1).1
  let resetCost  := (eip2200P 0 1 1 2).1
  let clearRef   := (eip2200P 0 1 1 0).2
  let resetZeroR := (eip2200P 0 0 1 0).2
  let resetNzR   := (eip2200P 0 1 2 1).2
  "\n.global _eita_sstore_gas_eip2200\n" ++
  ".p2align 2\n" ++
  "_eita_sstore_gas_eip2200:\n" ++
  prologue ++
  movImm "x16" sloadCost ++              -- default cost (no-op + dirty)
  "    mov   x17, x1\n" ++               -- refund counter r
  "    cbnz  x14, 9f\n" ++               -- curEqNew → done
  "    cbz   x13, 1f\n" ++               -- ¬origEqCur → dirty (cost stays)
  movImm "x8" setCost ++
  movImm "x9" resetCost ++
  "    cmp   x10, #0\n" ++
  "    csel  x16, x8, x9, ne\n" ++       -- clean: origZero ? set : reset
  "1:\n" ++
  -- r1: ¬origZero ∧ ¬curZero ∧ newZero → r += clear
  "    cbnz  x10, 2f\n" ++
  "    cbnz  x11, 2f\n" ++
  "    cbz   x12, 2f\n" ++
  movImm "x8" clearRef ++
  "    add   x17, x17, x8\n" ++
  "2:\n" ++
  -- r2: ¬origZero ∧ curZero → r = r ∸ clear (clamped)
  "    cbnz  x10, 3f\n" ++
  "    cbz   x11, 3f\n" ++
  movImm "x8" clearRef ++
  "    subs  x9, x17, x8\n" ++
  "    csel  x17, xzr, x9, lo\n" ++
  "3:\n" ++
  -- r3: origEqNew → r += origZero ? (set - sload) : (reset - sload)
  "    cbz   x15, 9f\n" ++
  movImm "x8" resetZeroR ++
  movImm "x9" resetNzR ++
  "    cmp   x10, #0\n" ++
  "    csel  x8, x8, x9, ne\n" ++
  "    add   x17, x17, x8\n" ++
  "9:\n" ++
  "    stp   x16, x17, [x0]\n" ++
  "    ret\n"

/-- Berlin / London shared shape: EIP-2200 tree with warm/cold split,
    accumulating `refundAdd`/`refundSub`, then `r1 = refund + add`,
    `result = r1 < sub ? 0 : r1 - sub` — exactly the spec `sstoreGas`
    add-then-single-clamped-sub discipline. Constants are probed from
    the given plan function. -/
private def eip2929CodeSpec (nm : String) (k : SstoreGasDenote.Consts2929) : String :=
  -- The constants come from `SstoreGasDenote`, which is also what
  -- `berlin_eq_spec` / `london_eq_spec` prove this routine equal to, so the
  -- numbers emitted and the numbers proved are the same numbers.
  let warmCost    := k.warm
  let setCost     := k.set
  let resetCost   := k.reset
  let coldSurch   := k.coldSurch
  let clearRef    := k.clearRef
  let resetZeroA  := k.resetZeroA
  let resetNzA    := k.resetNzA
  -- The subtracted clear refund used to be probed indirectly (`big − result`,
  -- because a subtraction is only observable through the clamp);
  -- `berlin_subClear_eq` / `london_subClear_eq` prove that probe recovers
  -- exactly `clearRef`, so the routine can just use it.
  let subClear    := k.clearRef
  s!"\n.global _eita_sstore_gas_{nm}\n" ++
  ".p2align 2\n" ++
  s!"_eita_sstore_gas_{nm}:\n" ++
  prologue ++
  movImm "x16" warmCost ++               -- default cost (no-op + dirty)
  "    mov   x7, #0\n" ++                -- refundAdd
  "    mov   x9, #0\n" ++                -- refundSub
  "    cbnz  x14, 8f\n" ++               -- curEqNew → no-op
  "    cbz   x13, 1f\n" ++               -- ¬origEqCur → dirty
  -- clean slot
  movImm "x8" setCost ++
  movImm "x6" resetCost ++
  "    cmp   x10, #0\n" ++
  "    csel  x16, x8, x6, ne\n" ++       -- origZero ? set : reset
  "    cbnz  x10, 8f\n" ++               -- refundAdd = clear iff
  "    cbz   x12, 8f\n" ++               --   ¬origZero ∧ newZero
  movImm "x7" clearRef ++
  "    b     8f\n" ++
  "1:\n" ++                              -- dirty (cost = warm already)
  "    cbnz  x10, 2f\n" ++               -- origZero → skip clear rules
  "    cbz   x11, 3f\n" ++
  movImm "x9" subClear ++                -- curZero → sub = clear
  "    b     2f\n" ++
  "3:\n" ++
  "    cbz   x12, 2f\n" ++
  movImm "x7" clearRef ++                -- new = 0 → add += clear
  "2:\n" ++
  "    cbz   x15, 8f\n" ++               -- origEqNew?
  movImm "x8" resetNzA ++
  movImm "x6" resetZeroA ++
  "    cmp   x10, #0\n" ++
  "    csel  x8, x6, x8, ne\n" ++
  "    add   x7, x7, x8\n" ++
  "8:\n" ++
  "    cbz   x5, 4f\n" ++                -- cold surcharge
  movImm "x8" coldSurch ++
  "    add   x16, x16, x8\n" ++
  "4:\n" ++
  "    add   x17, x1, x7\n" ++           -- r1 = refund + add
  "    subs  x8, x17, x9\n" ++
  "    csel  x17, xzr, x8, lo\n" ++      -- r1 < sub ? 0 : r1 - sub
  "    stp   x16, x17, [x0]\n" ++
  "    ret\n"

/-! ## Access-cost table -/

def tableForks : List (Evm.Fork × String) :=
  [(.frontier, "frontier"), (.homestead, "homestead"),
   (.daoFork, "dao_fork"), (.tangerineWhistle, "tangerine_whistle"),
   (.spuriousDragon, "spurious_dragon"), (.byzantium, "byzantium"),
   (.constantinople, "constantinople"), (.petersburg, "petersburg"),
   (.istanbul, "istanbul"), (.muirGlacier, "muir_glacier"),
   (.berlin, "berlin"), (.london, "london"),
   (.arrowGlacier, "arrow_glacier"), (.grayGlacier, "gray_glacier"),
   (.paris, "paris"), (.shanghai, "shanghai"),
   (.cancun, "cancun"), (.prague, "prague"),
   (.osaka, "osaka"), (.bpo1, "bpo1"), (.bpo2, "bpo2"), (.amsterdam, "amsterdam")]

/-- kind 0 sload, 1 balance, 2 extcodesize/copy, 3 extcodehash. -/
def accessKinds : List (String × Evm.IR.Op) :=
  [("sload", .sload), ("balance", .balance),
   ("extcode", .extcodesize), ("extcodehash", .extcodehash)]

/-- Warm cost = the IR ladder's staticCost — the same value the chunk
    compiler reads; 0 when the op does not exist on the fork. -/
def warmCost (f : Evm.Fork) (op : Evm.IR.Op) : Nat :=
  match Evm.IR.Op.metadata f op with
  | some m => m.staticCost
  | none   => 0

/-- Cold cost: Berlin+ uses the EIP-2929 spec constants (cold REPLACES
    warm — EELS charges 2100|2600 OR 100, never the sum); pre-Berlin
    cold = warm (no access lists). -/
def coldCost (f : Evm.Fork) (op : Evm.IR.Op) : Nat :=
  if (Evm.IR.Op.metadata f op).isNone then 0
  else if f.atLeast .berlin then
    match op with
    | .sload => Evm.Berlin.Vm.Gas.coldSload
    | _      => Evm.Berlin.Vm.Gas.coldAccountAccess
  else warmCost f op

/-- `_eita_access_costs`: 20 ords × 4 kinds × {cold, warm} u64 pairs.
    Byte index = ord*64 + kind*16 (+8 for warm). -/
private def accessTableSpec : String :=
  ".data\n" ++
  ".global _eita_access_costs\n" ++
  ".p2align 3\n" ++
  "_eita_access_costs:\n" ++
  String.join (tableForks.map fun (f, nm) =>
    s!"    // {nm}\n" ++
    String.join (accessKinds.map fun (knm, op) =>
      s!"    .quad {coldCost f op}, {warmCost f op}    // {knm}\n"))

/-- All Stage C-2 emission: five plan symbols + the access table. -/
def codeSpec : String :=
  ".section __TEXT,__text,regular,pure_instructions\n" ++
  legacyCodeSpec ++
  eip1283CodeSpec ++
  eip2200CodeSpec ++
  eip2929CodeSpec "berlin" SstoreGasDenote.berlinConsts ++
  eip2929CodeSpec "london" SstoreGasDenote.londonConsts ++
  accessTableSpec

/-! ## The routines as instructions (stage 4t)

The strings above are the specification; the programs below are what is
emitted. `code_derived` is the character identity. -/

section Instrs
open Evm.CL.AsmCore Evm.CL.Frame

def isZeroA (p dst : Reg) : List AInstr :=
  [ .ldpOff .x6 .x7 p 0, .ldpOff .x8 .x9 p 16, .orr3 .x6 .x6 .x7, .orr3 .x8 .x8 .x9,
    .orr3 .x6 .x6 .x8, .cmpImm .x6 0, .cset dst .eq ]

def isEqA (p q dst : Reg) : List AInstr :=
  [ .ldpOff .x6 .x7 p 0, .ldpOff .x8 .x9 q 0, .eor3 .x6 .x6 .x8, .eor3 .x7 .x7 .x9, .orr3 .x6 .x6 .x7,
    .ldpOff .x8 .x9 p 16, .ldpOff .x16 .x17 q 16, .eor3 .x8 .x8 .x16, .eor3 .x9 .x9 .x17,
    .orr3 .x8 .x8 .x9, .orr3 .x6 .x6 .x8, .cmpImm .x6 0, .cset dst .eq ]

/-- x10 origZero, x11 curZero, x12 newZero, x13 origEqCur, x14 curEqNew, x15 origEqNew. -/
def prologueA : List AInstr :=
  isZeroA .x2 .x10 ++ isZeroA .x3 .x11 ++ isZeroA .x4 .x12 ++
  isEqA .x2 .x3 .x13 ++ isEqA .x3 .x4 .x14 ++ isEqA .x2 .x4 .x15

def legacyA : List AInstr :=
  -- the constants are `SstoreGasDenote`'s probes, so the numbers in the program
  -- and the numbers in the plan theorems are the same definitions
  let setCost     := SstoreGasDenote.setCost
  let resetCost   := SstoreGasDenote.resetCost
  let clearRefund := SstoreGasDenote.clearRefund
  [.blank] ++ header "_eita_sstore_gas_legacy" ++
  isZeroA .x3 .x11 ++ isZeroA .x4 .x12 ++
  movImmInstrs .x16 resetCost ++ movImmInstrs .x17 setCost ++
  [ .eorImm1 .x9 .x12, .and3 .x9 .x9 .x11, .cmpImm .x9 0, .csel .x16 .x16 .x17 .eq,
    .eorImm1 .x9 .x11, .and3 .x9 .x9 .x12 ] ++
  movImmInstrs .x8 clearRefund ++
  [ .cmpImm .x9 0, .cselZrA .x8 .x8 .eq, .addReg .x17 .x1 .x8, .stpOff .x16 .x17 .x0 0, .ret ]

def eip1283A : List AInstr :=
  let noopCost   := SstoreGasDenote.noopCost1283
  let setCost    := SstoreGasDenote.setCost1283
  let resetCost  := SstoreGasDenote.resetCost1283
  let dirtyCost  := SstoreGasDenote.dirtyCost1283
  let clearRef   := SstoreGasDenote.clearRef1283
  let resetZeroR := SstoreGasDenote.resetZeroR1283
  let resetNzR   := SstoreGasDenote.resetNzR1283
  [.blank] ++ header "_eita_sstore_gas_eip1283" ++ prologueA ++
  [ .cbzLbl .x14 "1f" ] ++ movImmInstrs .x16 noopCost ++ [ .movReg .x17 .x1, .bLbl "9f", .label "1",
    .cbzLbl .x13 "2f", .cbzLbl .x10 "3f" ] ++ movImmInstrs .x16 setCost ++
  [ .movReg .x17 .x1, .bLbl "9f", .label "3" ] ++
  movImmInstrs .x16 resetCost ++ movImmInstrs .x8 clearRef ++
  [ .cmpImm .x12 0, .cselZrA .x8 .x8 .eq, .addReg .x17 .x1 .x8, .bLbl "9f", .label "2" ] ++
  movImmInstrs .x16 dirtyCost ++
  [ .movImm .x9 0, .cbnzLbl .x10 "4f", .cbzLbl .x11 "5f" ] ++ movImmInstrs .x8 clearRef ++
  [ .subReg .x9 .x9 .x8, .label "5", .cbzLbl .x12 "4f" ] ++ movImmInstrs .x8 clearRef ++
  [ .addReg .x9 .x9 .x8, .label "4", .cbzLbl .x15 "6f" ] ++
  movImmInstrs .x8 resetNzR ++ movImmInstrs .x7 resetZeroR ++
  [ .cmpImm .x10 0, .csel .x8 .x7 .x8 .ne, .addReg .x9 .x9 .x8, .label "6",
    .addReg .x17 .x1 .x9, .cmpImm .x17 0, .cselZrA .x17 .x17 .lt, .label "9",
    .stpOff .x16 .x17 .x0 0, .ret ]

def eip2200A : List AInstr :=
  let sloadCost  := SstoreGasDenote.sloadCost2200
  let setCost    := SstoreGasDenote.setCost2200
  let resetCost  := SstoreGasDenote.resetCost2200
  let clearRef   := SstoreGasDenote.clearRef2200
  let resetZeroR := SstoreGasDenote.resetZeroR2200
  let resetNzR   := SstoreGasDenote.resetNzR2200
  [.blank] ++ header "_eita_sstore_gas_eip2200" ++ prologueA ++
  movImmInstrs .x16 sloadCost ++
  [ .movReg .x17 .x1, .cbnzLbl .x14 "9f", .cbzLbl .x13 "1f" ] ++
  movImmInstrs .x8 setCost ++ movImmInstrs .x9 resetCost ++
  [ .cmpImm .x10 0, .csel .x16 .x8 .x9 .ne, .label "1",
    .cbnzLbl .x10 "2f", .cbnzLbl .x11 "2f", .cbzLbl .x12 "2f" ] ++ movImmInstrs .x8 clearRef ++
  [ .addReg .x17 .x17 .x8, .label "2", .cbnzLbl .x10 "3f", .cbzLbl .x11 "3f" ] ++ movImmInstrs .x8 clearRef ++
  [ .subsReg .x9 .x17 .x8, .cselZrA .x17 .x9 .lo, .label "3", .cbzLbl .x15 "9f" ] ++
  movImmInstrs .x8 resetZeroR ++ movImmInstrs .x9 resetNzR ++
  [ .cmpImm .x10 0, .csel .x8 .x8 .x9 .ne, .addReg .x17 .x17 .x8, .label "9",
    .stpOff .x16 .x17 .x0 0, .ret ]

def eip2929A (nm : String) (k : SstoreGasDenote.Consts2929) : List AInstr :=
  [.blank] ++ header ("_eita_sstore_gas_" ++ nm) ++ prologueA ++
  movImmInstrs .x16 k.warm ++
  [ .movImm .x7 0, .movImm .x9 0, .cbnzLbl .x14 "8f", .cbzLbl .x13 "1f" ] ++
  movImmInstrs .x8 k.set ++ movImmInstrs .x6 k.reset ++
  [ .cmpImm .x10 0, .csel .x16 .x8 .x6 .ne, .cbnzLbl .x10 "8f", .cbzLbl .x12 "8f" ] ++
  movImmInstrs .x7 k.clearRef ++
  [ .bLbl "8f", .label "1", .cbnzLbl .x10 "2f", .cbzLbl .x11 "3f" ] ++ movImmInstrs .x9 k.clearRef ++
  [ .bLbl "2f", .label "3", .cbzLbl .x12 "2f" ] ++ movImmInstrs .x7 k.clearRef ++
  [ .label "2", .cbzLbl .x15 "8f" ] ++ movImmInstrs .x8 k.resetNzA ++ movImmInstrs .x6 k.resetZeroA ++
  [ .cmpImm .x10 0, .csel .x8 .x6 .x8 .ne, .addReg .x7 .x7 .x8, .label "8", .cbzLbl .x5 "4f" ] ++
  movImmInstrs .x8 k.coldSurch ++
  [ .addReg .x16 .x16 .x8, .label "4", .addReg .x17 .x1 .x7, .subsReg .x8 .x17 .x9,
    .cselZrA .x17 .x8 .lo, .stpOff .x16 .x17 .x0 0, .ret ]

def accessTableA : List AInstr :=
  [ .dataSection, .global "_eita_access_costs", .p2align3, .symLabel "_eita_access_costs" ] ++
  tableForks.flatMap (fun (f, nm) =>
    .commentLine nm :: accessKinds.map (fun (knm, op) => .quadPair (coldCost f op) (warmCost f op) knm))

/-- All Stage C-2 emission as instructions: five plan symbols + the access table. -/
def instrs : List AInstr :=
  [.textSection] ++ legacyA ++ eip1283A ++ eip2200A ++
  eip2929A "berlin" SstoreGasDenote.berlinConsts ++
  eip2929A "london" SstoreGasDenote.londonConsts ++ accessTableA

end Instrs

/-- What is emitted. -/
def code : String := Evm.CL.Frame.text instrs

theorem code_derived : code = codeSpec := by native_decide

end Evm.CL.ARM64.SstoreGas
