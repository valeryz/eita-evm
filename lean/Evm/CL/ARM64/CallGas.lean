/-
  Evm.CL.ARM64.CallGas — emit `_eita_call_gas`, the native binding of
  the pure CALL-family gas plan `Evm.Berlin.Vm.Effect.callGasPlan`.

  Every constant in the emitted code is *evaluated out of the Lean
  definition* (below, `chargeConst` / `stipendConst` call `callGasPlan`
  itself), so a schedule change in the spec re-emits here without any
  hand edit. The runtime control structure mirrors `callGasPlan`
  line-for-line:

    charge  = const(flags) + delegatedCost      -- charge is affine in
                                                -- delegatedCost by defn
    pool    = avail ∸ charge                    -- Nat subtraction: clamp 0
    forward = min gasArg (pool - pool / 64)     -- capForward (EIP-150)
    stipend = const(flags)

  C ABI (AAPCS64):

    void eita_call_gas(uint64_t out[3],   // x0: {charge, forward, stipend}
                       uint64_t flags,    // x1: bit0 isCold, bit1 chargesValue,
                                          //     bit2 chargesNewAccount
                       uint64_t delegated_cost,  // x2 (EIP-7702; 0 pre-Prague)
                       uint64_t gas_arg,  // x3: CALL gas argument, clamped by
                                          //     the caller to 2^64-1 (sound:
                                          //     forward ≤ pool < 2^64)
                       uint64_t avail);   // x4: parent gas AFTER memexp,
                                          //     BEFORE the base charge

  The differential gate `tests/audit-call-gas.lisp` compares this
  symbol against Lean-oracle vectors from `lake exe callGasVectors`.
-/

import Evm.CL.ARM64
import Evm.CL.Frame
import Evm.CL.ARM64.CallGasDenote
import Evm.Frontier.Vm.Effect
import Evm.TangerineWhistle.Vm.Effect
import Evm.Berlin.Vm.Effect

namespace Evm.CL.ARM64.CallGas

open Evm.Berlin.Vm.Effect (callGasPlan)

/-! ## The routines as instructions (stage 4t) -/

section Instrs
open Evm.CL.AsmCore Evm.CL.Frame

/-- `(flagBit, fee)` → charge += flag ? fee : 0. -/
def feeIf (bit fee : Nat) : List AInstr :=
  movImmInstrs .x10 fee ++ [ .tstImm .x1 bit, .cselZrB .x10 .x10 .ne, .addReg .x9 .x9 .x10 ]

/-- pool = avail ∸ charge; forward = min(gasArg, pool − pool/64). -/
def capForward : List AInstr :=
  [ .subsReg .x11 .x4 .x9, .cselZrA .x11 .x11 .lo, .lsrImm .x12 .x11 6, .subReg .x12 .x11 .x12,
    .cmpReg .x3 .x12, .csel .x12 .x3 .x12 .lo ]

/-- stipend iff chargesValue; store (charge, forward), stipend; return. -/
def finish (stipend : Nat) : List AInstr :=
  movImmInstrs .x13 stipend ++
  [ .tstImm .x1 2, .cselZrB .x13 .x13 .ne, .stpOff .x9 .x12 .x0 0, .strOff .x13 .x0 16, .ret ]

def berlinA : List AInstr :=
  [.textSection] ++ header "_eita_call_gas" ++
  movImmInstrs .x9 CallGasDenote.baseWarm ++ movImmInstrs .x10 CallGasDenote.baseCold ++
  [ .tstImm .x1 1, .csel .x9 .x10 .x9 .ne ] ++
  feeIf 2 CallGasDenote.valueFee ++ feeIf 4 CallGasDenote.newAcctFee ++
  [ .addReg .x9 .x9 .x2 ] ++ capForward ++ finish CallGasDenote.stipendC

def frontierA : List AInstr :=
  [.blank] ++ header "_eita_call_gas_frontier" ++
  movImmInstrs .x9 CallGasDenote.fBase ++
  feeIf 2 CallGasDenote.fValueFee ++ feeIf 4 CallGasDenote.fNewAcctFee ++
  [ .movReg .x12 .x3 ] ++ finish CallGasDenote.fStipend

def tangerineA : List AInstr :=
  [.blank] ++ header "_eita_call_gas_tangerine" ++
  movImmInstrs .x9 CallGasDenote.tBase ++
  feeIf 2 CallGasDenote.tValueFee ++ feeIf 4 CallGasDenote.tNewAcctFee ++
  capForward ++ finish CallGasDenote.tStipend

def instrs : List AInstr := berlinA ++ frontierA ++ tangerineA

end Instrs

def code : String := Evm.CL.Frame.text instrs

end Evm.CL.ARM64.CallGas
