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

/-! ## The routines as instructions (stage 4t)

The programs are the only source: `code` is their printing, and
`SstoreGasSem` proves what they compute. -/

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

/-- `_eita_access_costs`: 20 ords × 4 kinds × {cold, warm} u64 pairs.
    Byte index = ord*64 + kind*16 (+8 for warm). -/
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

end Evm.CL.ARM64.SstoreGas
