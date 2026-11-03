/-
  Evm.CL.X86SstoreGas — `_eita_sstore_gas_*` for x86-64.

  Stage 4w of #238. The ARM64 routines keep the six predicates in x10–x15
  and the three pointers, the counter, the cold flag and the out pointer
  besides — thirteen registers. x86-64 has nine caller-saved ones under the
  SysV convention (the six argument registers and rax, r10, r11), so the
  prologue PACKS the predicates into one register as bits:

      x9 = origZero·1 | curZero·2 | newZero·4 | origEqCur·8 | curEqNew·16
         | origEqNew·32 | cold·64

  and the trees test bits (`tst x9, #bit`) where ARM64 tests registers. The
  trees are otherwise the ARM64 trees (`ARM64.SstoreGas`) instruction for
  instruction, with the same plans (`SstoreGasDenote`) — `X86SstoreGasSem`
  runs them under `AsmSem` and proves it.

  Registers (x86-64 homes): out x3 (rdi), refund x2 (rsi), orig x1 (rdx),
  cur x14 (rcx), new x6 (r8), cold x7 (r9) — the SysV argument order — and
  x8 (r10), x9 (r11), x0 (rax) as scratch. The cold bit is packed first, which
  frees x7; after the prologue the pointers are dead, x14 is held at ZERO for
  the selects (`cmov` takes no immediate) and x1/x6/x0/x7 are temporaries.
  Every subtract writes its left operand (x86-64's two-operand form).
-/

import Evm.CL.AsmCore
import Evm.CL.Frame
import Evm.CL.ARM64.SstoreGasDenote

namespace Evm.CL.X86SstoreGas

open Evm.CL.AsmCore Evm.CL.Frame Evm.CL.ARM64

/-- `x8 := 1` iff the u256 at `[p]` is zero (OR-fold, two registers). -/
def isZeroX (p : Reg) : List AInstr :=
  [ .ldrOff .x8 p 0, .ldrOff .x0 p 8, .orr3 .x8 .x8 .x0,
    .ldrOff .x0 p 16, .orr3 .x8 .x8 .x0, .ldrOff .x0 p 24, .orr3 .x8 .x8 .x0,
    .cmpImm .x8 0, .cset .x8 .eq ]

/-- `x8 := 1` iff the u256s at `[p]` and `[q]` are equal (XOR/OR-fold, three
    registers; x7 is free once cold is packed). -/
def isEqX (p q : Reg) : List AInstr :=
  [ .ldrOff .x8 p 0, .ldrOff .x0 q 0, .eor3 .x8 .x8 .x0,
    .ldrOff .x0 p 8, .ldrOff .x7 q 8, .eor3 .x0 .x0 .x7, .orr3 .x8 .x8 .x0,
    .ldrOff .x0 p 16, .ldrOff .x7 q 16, .eor3 .x0 .x0 .x7, .orr3 .x8 .x8 .x0,
    .ldrOff .x0 p 24, .ldrOff .x7 q 24, .eor3 .x0 .x0 .x7, .orr3 .x8 .x8 .x0,
    .cmpImm .x8 0, .cset .x8 .eq ]

/-- `x9 |= x8 << k`. -/
def packBit (k : Nat) : List AInstr :=
  (if k = 0 then [] else [AInstr.lslImm .x8 .x8 k]) ++ [ .orr3 .x9 .x9 .x8 ]

/-- The cold flag (any non-zero = cold) as bit 6, first, then the six
    predicates; x14 := 0 for the selects. -/
def prologueX : List AInstr :=
  [ .cmpImm .x7 0, .cset .x9 .eq, .eorImm1 .x9 .x9, .lslImm .x9 .x9 6 ] ++
  isZeroX .x1 ++ packBit 0 ++ isZeroX .x14 ++ packBit 1 ++ isZeroX .x6 ++ packBit 2 ++
  isEqX .x1 .x14 ++ packBit 3 ++ isEqX .x14 .x6 ++ packBit 4 ++ isEqX .x1 .x6 ++ packBit 5 ++
  [ .movImm .x14 0 ]

/-- The bit of each predicate. -/
def bOrigZero : Nat := 1
def bCurZero : Nat := 2
def bNewZero : Nat := 4
def bOrigEqCur : Nat := 8
def bCurEqNew : Nat := 16
def bOrigEqNew : Nat := 32
def bCold : Nat := 64

/-- Legacy: only cur/new; bits 1 and 2 of x9 (orig and cold are ignored). -/
def legacyBody : List AInstr :=
  [ .movImm .x9 0 ] ++ isZeroX .x14 ++ packBit 1 ++ isZeroX .x6 ++ packBit 2 ++
  movImmInstrs .x8 SstoreGasDenote.resetCost ++
  [ .tstImm .x9 bCurZero, .bcLbl .eq "1f", .tstImm .x9 bNewZero, .bcLbl .ne "1f" ] ++
  movImmInstrs .x8 SstoreGasDenote.setCost ++
  [ .label "1", .movImm .x0 0, .tstImm .x9 bCurZero, .bcLbl .ne "2f",
    .tstImm .x9 bNewZero, .bcLbl .eq "2f" ] ++
  movImmInstrs .x0 SstoreGasDenote.clearRefund ++
  [ .label "2", .addReg .x7 .x2 .x0, .stpOff .x8 .x7 .x3 0, .ret ]

/-- EIP-1283: one signed delta in x1, clamped once by the sign bit. -/
def eip1283Body : List AInstr :=
  prologueX ++
  [ .tstImm .x9 bCurEqNew, .bcLbl .eq "1f" ] ++
  movImmInstrs .x8 SstoreGasDenote.noopCost1283 ++ [ .movReg .x7 .x2, .bLbl "9f", .label "1",
    .tstImm .x9 bOrigEqCur, .bcLbl .eq "2f", .tstImm .x9 bOrigZero, .bcLbl .eq "3f" ] ++
  movImmInstrs .x8 SstoreGasDenote.setCost1283 ++ [ .movReg .x7 .x2, .bLbl "9f", .label "3" ] ++
  movImmInstrs .x8 SstoreGasDenote.resetCost1283 ++ movImmInstrs .x0 SstoreGasDenote.clearRef1283 ++
  [ .tstImm .x9 bNewZero, .csel .x0 .x0 .x14 .ne, .addReg .x7 .x2 .x0, .bLbl "9f", .label "2" ] ++
  movImmInstrs .x8 SstoreGasDenote.dirtyCost1283 ++
  [ .movImm .x1 0, .tstImm .x9 bOrigZero, .bcLbl .ne "4f", .tstImm .x9 bCurZero, .bcLbl .eq "5f" ] ++
  movImmInstrs .x0 SstoreGasDenote.clearRef1283 ++
  [ .subReg .x1 .x1 .x0, .label "5", .tstImm .x9 bNewZero, .bcLbl .eq "4f" ] ++
  movImmInstrs .x0 SstoreGasDenote.clearRef1283 ++
  [ .addReg .x1 .x1 .x0, .label "4", .tstImm .x9 bOrigEqNew, .bcLbl .eq "6f" ] ++
  movImmInstrs .x0 SstoreGasDenote.resetNzR1283 ++ movImmInstrs .x6 SstoreGasDenote.resetZeroR1283 ++
  [ .tstImm .x9 bOrigZero, .csel .x0 .x6 .x0 .ne, .addReg .x1 .x1 .x0, .label "6",
    .addReg .x7 .x2 .x1, .cmpImm .x7 0, .csel .x7 .x14 .x7 .lt, .label "9",
    .stpOff .x8 .x7 .x3 0, .ret ]

/-- EIP-2200: the sequential discipline — add, saturating subtract, add. -/
def eip2200Body : List AInstr :=
  prologueX ++
  movImmInstrs .x8 SstoreGasDenote.sloadCost2200 ++
  [ .movReg .x7 .x2, .tstImm .x9 bCurEqNew, .bcLbl .ne "9f", .tstImm .x9 bOrigEqCur, .bcLbl .eq "1f" ] ++
  movImmInstrs .x0 SstoreGasDenote.setCost2200 ++ movImmInstrs .x1 SstoreGasDenote.resetCost2200 ++
  [ .tstImm .x9 bOrigZero, .csel .x8 .x0 .x1 .ne, .label "1",
    .tstImm .x9 bOrigZero, .bcLbl .ne "2f", .tstImm .x9 bCurZero, .bcLbl .ne "2f",
    .tstImm .x9 bNewZero, .bcLbl .eq "2f" ] ++
  movImmInstrs .x0 SstoreGasDenote.clearRef2200 ++
  [ .addReg .x7 .x7 .x0, .label "2", .tstImm .x9 bOrigZero, .bcLbl .ne "3f",
    .tstImm .x9 bCurZero, .bcLbl .eq "3f" ] ++
  movImmInstrs .x0 SstoreGasDenote.clearRef2200 ++
  [ .subsReg .x1 .x7 .x0, .csel .x7 .x14 .x1 .lo, .label "3", .tstImm .x9 bOrigEqNew, .bcLbl .eq "9f" ] ++
  movImmInstrs .x0 SstoreGasDenote.resetZeroR2200 ++ movImmInstrs .x1 SstoreGasDenote.resetNzR2200 ++
  [ .tstImm .x9 bOrigZero, .csel .x0 .x0 .x1 .ne, .addReg .x7 .x7 .x0, .label "9",
    .stpOff .x8 .x7 .x3 0, .ret ]

/-- EIP-2929/3529: add first (x1), then one clamped subtract (x6); the cold
    surcharge on the cost. -/
def eip2929Body (k : SstoreGasDenote.Consts2929) : List AInstr :=
  prologueX ++
  movImmInstrs .x8 k.warm ++
  [ .movImm .x1 0, .movImm .x6 0, .tstImm .x9 bCurEqNew, .bcLbl .ne "8f",
    .tstImm .x9 bOrigEqCur, .bcLbl .eq "1f" ] ++
  movImmInstrs .x0 k.set ++ movImmInstrs .x7 k.reset ++
  [ .tstImm .x9 bOrigZero, .csel .x8 .x0 .x7 .ne, .tstImm .x9 bOrigZero, .bcLbl .ne "8f",
    .tstImm .x9 bNewZero, .bcLbl .eq "8f" ] ++
  movImmInstrs .x1 k.clearRef ++
  [ .bLbl "8f", .label "1", .tstImm .x9 bOrigZero, .bcLbl .ne "2f",
    .tstImm .x9 bCurZero, .bcLbl .eq "3f" ] ++
  movImmInstrs .x6 k.clearRef ++
  [ .bLbl "2f", .label "3", .tstImm .x9 bNewZero, .bcLbl .eq "2f" ] ++
  movImmInstrs .x1 k.clearRef ++
  [ .label "2", .tstImm .x9 bOrigEqNew, .bcLbl .eq "8f" ] ++
  movImmInstrs .x0 k.resetNzA ++ movImmInstrs .x7 k.resetZeroA ++
  [ .tstImm .x9 bOrigZero, .csel .x0 .x7 .x0 .ne, .addReg .x1 .x1 .x0, .label "8",
    .tstImm .x9 bCold, .bcLbl .eq "4f" ] ++
  movImmInstrs .x0 k.coldSurch ++
  [ .addReg .x8 .x8 .x0, .label "4", .addReg .x7 .x2 .x1, .subsReg .x0 .x7 .x6,
    .csel .x7 .x14 .x0 .lo, .stpOff .x8 .x7 .x3 0, .ret ]

/-- (symbol, body). -/
def routines : List (String × List AInstr) :=
  [ ("_eita_sstore_gas_legacy", legacyBody),
    ("_eita_sstore_gas_eip1283", eip1283Body),
    ("_eita_sstore_gas_eip2200", eip2200Body),
    ("_eita_sstore_gas_berlin", eip2929Body SstoreGasDenote.berlinConsts),
    ("_eita_sstore_gas_london", eip2929Body SstoreGasDenote.londonConsts) ]

/-- The five as one program with headers, for `AsmSem.entry`. -/
def instrs : List AInstr := routines.flatMap (fun (s, b) => header s ++ b)

end Evm.CL.X86SstoreGas
