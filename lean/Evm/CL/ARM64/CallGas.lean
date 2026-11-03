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

def codeSpec : String :=
  -- The constants come from `CallGasDenote`, which is also what
  -- `plan_eq_spec` proves this routine's arithmetic equal to — so the numbers
  -- the emitter materialises and the numbers the theorem is about cannot drift.
  let baseWarm   := CallGasDenote.baseWarm
  let baseCold   := CallGasDenote.baseCold
  let valueFee   := CallGasDenote.valueFee
  let newAcctFee := CallGasDenote.newAcctFee
  let stipend    := CallGasDenote.stipendC
  ".section __TEXT,__text,regular,pure_instructions\n" ++
  ".global _eita_call_gas\n" ++
  ".p2align 2\n" ++
  "_eita_call_gas:\n" ++
  movImm "x9"  baseWarm ++
  movImm "x10" baseCold ++
  "    tst   x1, #1\n" ++
  "    csel  x9, x10, x9, ne\n" ++           -- base = isCold ? cold : warm
  movImm "x10" valueFee ++
  "    tst   x1, #2\n" ++
  "    csel  x10, x10, xzr, ne\n" ++
  "    add   x9, x9, x10\n" ++               -- + (chargesValue ? callValue : 0)
  movImm "x10" newAcctFee ++
  "    tst   x1, #4\n" ++
  "    csel  x10, x10, xzr, ne\n" ++
  "    add   x9, x9, x10\n" ++               -- + (chargesNewAccount ? newAccount : 0)
  "    add   x9, x9, x2\n" ++                -- + delegatedCost  ⇒ charge
  "    subs  x11, x4, x9\n" ++
  "    csel  x11, xzr, x11, lo\n" ++         -- pool = avail ∸ charge
  "    lsr   x12, x11, #6\n" ++
  "    sub   x12, x11, x12\n" ++             -- pool - pool/64
  "    cmp   x3, x12\n" ++
  "    csel  x12, x3, x12, lo\n" ++          -- forward = min gasArg capped
  movImm "x13" stipend ++
  "    tst   x1, #2\n" ++
  "    csel  x13, x13, xzr, ne\n" ++         -- stipend iff chargesValue
  "    stp   x9, x12, [x0]\n" ++
  "    str   x13, [x0, #16]\n" ++
  "    ret\n" ++
  -- _eita_call_gas_frontier — Frontier/Homestead (pre-EIP-150) plan,
  -- evaluated from `Evm.Frontier.Vm.Effect.callGasPlan`. Same ABI;
  -- bit0 (isCold) and x2 (delegatedCost) don't exist pre-Berlin and
  -- are ignored, x4 (avail) is unused because there is NO forwarding
  -- cap: forward = gasArg verbatim, and the HOST must OOG-check
  -- charge + forward against the parent's gas.
  frontierCode ++
  -- _eita_call_gas_tangerine — TangerineWhistle..MuirGlacier (EIP-150)
  -- plan, evaluated from `Evm.TangerineWhistle.Vm.Effect.callGasPlan`:
  -- base 700, 63/64 cap, no cold/delegated terms.
  tangerineCode
where
  frontierCode : String :=
    let base       := CallGasDenote.fBase
    let valueFee   := CallGasDenote.fValueFee
    let newAcctFee := CallGasDenote.fNewAcctFee
    let stipend    := CallGasDenote.fStipend
    "\n.global _eita_call_gas_frontier\n" ++
    ".p2align 2\n" ++
    "_eita_call_gas_frontier:\n" ++
    movImm "x9"  base ++
    movImm "x10" valueFee ++
    "    tst   x1, #2\n" ++
    "    csel  x10, x10, xzr, ne\n" ++
    "    add   x9, x9, x10\n" ++             -- + (chargesValue ? callValue : 0)
    movImm "x10" newAcctFee ++
    "    tst   x1, #4\n" ++
    "    csel  x10, x10, xzr, ne\n" ++
    "    add   x9, x9, x10\n" ++             -- + (chargesNewAccount ? newAccount : 0)
    "    mov   x12, x3\n" ++                 -- forward = gasArg, uncapped
    movImm "x13" stipend ++
    "    tst   x1, #2\n" ++
    "    csel  x13, x13, xzr, ne\n" ++       -- stipend iff chargesValue
    "    stp   x9, x12, [x0]\n" ++
    "    str   x13, [x0, #16]\n" ++
    "    ret\n"
  tangerineCode : String :=
    let base       := CallGasDenote.tBase
    let valueFee   := CallGasDenote.tValueFee
    let newAcctFee := CallGasDenote.tNewAcctFee
    let stipend    := CallGasDenote.tStipend
    "\n.global _eita_call_gas_tangerine\n" ++
    ".p2align 2\n" ++
    "_eita_call_gas_tangerine:\n" ++
    movImm "x9"  base ++
    movImm "x10" valueFee ++
    "    tst   x1, #2\n" ++
    "    csel  x10, x10, xzr, ne\n" ++
    "    add   x9, x9, x10\n" ++             -- + (chargesValue ? callValue : 0)
    movImm "x10" newAcctFee ++
    "    tst   x1, #4\n" ++
    "    csel  x10, x10, xzr, ne\n" ++
    "    add   x9, x9, x10\n" ++             -- + (chargesNewAccount ? newAccount : 0)  ⇒ charge
    "    subs  x11, x4, x9\n" ++
    "    csel  x11, xzr, x11, lo\n" ++       -- pool = avail ∸ charge
    "    lsr   x12, x11, #6\n" ++
    "    sub   x12, x11, x12\n" ++           -- pool - pool/64
    "    cmp   x3, x12\n" ++
    "    csel  x12, x3, x12, lo\n" ++        -- forward = min gasArg capped
    movImm "x13" stipend ++
    "    tst   x1, #2\n" ++
    "    csel  x13, x13, xzr, ne\n" ++       -- stipend iff chargesValue
    "    stp   x9, x12, [x0]\n" ++
    "    str   x13, [x0, #16]\n" ++
    "    ret\n"

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

theorem code_derived : code = codeSpec := by native_decide

end Evm.CL.ARM64.CallGas
