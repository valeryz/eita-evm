/-
  Evm.CL.X86CallGas — `_eita_call_gas{,_frontier,_tangerine}` for x86-64.

  Stage 4w of #238. The ARM64 routines (`ARM64.CallGas`) are AAPCS64 programs
  over x0–x4; the x86-64 ones are the SAME plan (`CallGasDenote.plan*`) as
  `AInstr` programs over the registers whose x86-64 homes are the SysV
  argument registers:

      out        x3  → rdi        gasArg   x14 → rcx
      flags      x2  → rsi        avail    x6  → r8
      delegated  x1  → rdx

  and three scratch registers with caller-saved homes — x8 (r10), x7 (r9),
  x9 (r11) — plus x0 (rax) held at ZERO for the selects: x86-64's `cmov`
  takes no immediate, so where ARM64 writes `csel d, xzr, …` these programs
  write `mov x0, 0` once and `csel … x0`, which the `AsmSem` semantics sees
  exactly (no hidden temporary). `X86CallGasSem` runs them under `AsmSem`
  and proves they store the plans, as `CallGasSem` does for ARM64.

  C ABI (SysV): void eita_call_gas(uint64_t out[3], uint64_t flags,
                                   uint64_t delegated, uint64_t gasArg,
                                   uint64_t avail).
-/

import Evm.CL.AsmCore
import Evm.CL.Frame
import Evm.CL.ARM64.CallGasDenote

namespace Evm.CL.X86CallGas

open Evm.CL.AsmCore Evm.CL.Frame Evm.CL.ARM64

/-- `x7 := fee if flag bit set else 0; x8 += x7`. `x0` is zero. -/
def feeIf (bit fee : Nat) : List AInstr :=
  movImmInstrs .x7 fee ++ [ .tstImm .x2 bit, .csel .x7 .x7 .x0 .ne, .addReg .x8 .x8 .x7 ]

/-- pool (x9) = avail ∸ charge; forward (x9) = min(gasArg, pool − pool/64).
    Every subtract writes its LEFT operand (x86-64's two-operand form). -/
def capForward : List AInstr :=
  [ .subsReg .x9 .x6 .x8, .csel .x9 .x0 .x9 .lo,
    .lsrImm .x7 .x9 6, .subReg .x9 .x9 .x7,
    .cmpReg .x14 .x9, .csel .x9 .x14 .x9 .lo ]

/-- stipend (x7) iff chargesValue; store (charge, forward), stipend; return. -/
def finish (stipend : Nat) : List AInstr :=
  movImmInstrs .x7 stipend ++
  [ .tstImm .x2 2, .csel .x7 .x7 .x0 .ne, .stpOff .x8 .x9 .x3 0, .strOff .x7 .x3 16, .ret ]

def berlinBody : List AInstr :=
  [ .movImm .x0 0 ] ++
  movImmInstrs .x8 CallGasDenote.baseWarm ++ movImmInstrs .x7 CallGasDenote.baseCold ++
  [ .tstImm .x2 1, .csel .x8 .x7 .x8 .ne ] ++
  feeIf 2 CallGasDenote.valueFee ++ feeIf 4 CallGasDenote.newAcctFee ++
  [ .addReg .x8 .x8 .x1 ] ++ capForward ++ finish CallGasDenote.stipendC

def frontierBody : List AInstr :=
  [ .movImm .x0 0 ] ++
  movImmInstrs .x8 CallGasDenote.fBase ++
  feeIf 2 CallGasDenote.fValueFee ++ feeIf 4 CallGasDenote.fNewAcctFee ++
  [ .movReg .x9 .x14 ] ++ finish CallGasDenote.fStipend

def tangerineBody : List AInstr :=
  [ .movImm .x0 0 ] ++
  movImmInstrs .x8 CallGasDenote.tBase ++
  feeIf 2 CallGasDenote.tValueFee ++ feeIf 4 CallGasDenote.tNewAcctFee ++
  capForward ++ finish CallGasDenote.tStipend

/-- (symbol, body), for the file and the gates. -/
def routines : List (String × List AInstr) :=
  [ ("_eita_call_gas", berlinBody), ("_eita_call_gas_frontier", frontierBody),
    ("_eita_call_gas_tangerine", tangerineBody) ]

/-- The three as one program with headers, for `AsmSem.entry`. -/
def instrs : List AInstr :=
  routines.flatMap (fun (s, b) => header s ++ b)

end Evm.CL.X86CallGas
