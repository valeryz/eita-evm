/-
  Evm.CL.X86CallGasSem — the x86-64 `_eita_call_gas*` PROGRAMS run under
  `AsmSem` store exactly the `CallGasDenote` plans: the same theorems as
  `ARM64.CallGasSem`, over the SysV register homes (`X86CallGas`). One
  semantics, two register conventions, one plan.
-/

import Evm.CL.AsmSem
import Evm.CL.X86CallGas
import Evm.CL.ARM64.CallGasSem

namespace Evm.CL.X86CallGasSem

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.ARM64
open Evm.CL.ARM64.CallGasSem (flagsWord)

/-- The three words the routine leaves at `out` (x3 = rdi). -/
def outWords (m : RM) (m' : RM) : BitVec 64 × BitVec 64 × BitVec 64 :=
  (m'.mem (m.regs .x3), m'.mem (m.regs .x3 + 8#64), m'.mem (m.regs .x3 + 16#64))

syntax "callgasx_unfold" : tactic
macro_rules
  | `(tactic| callgasx_unfold) => `(tactic| (
      simp only [X86CallGas.instrs, X86CallGas.routines, X86CallGas.berlinBody,
        X86CallGas.frontierBody, X86CallGas.tangerineBody, Evm.CL.Frame.header,
        X86CallGas.feeIf, X86CallGas.capForward, X86CallGas.finish,
        List.flatMap_cons, List.flatMap_nil,
        CallGasDenote.fBase_eq, CallGasDenote.fValueFee_eq, CallGasDenote.fNewAcctFee_eq,
        CallGasDenote.fStipend_eq, CallGasDenote.tBase_eq, CallGasDenote.tValueFee_eq,
        CallGasDenote.tNewAcctFee_eq, CallGasDenote.tStipend_eq,
        CallGasDenote.baseWarm_eq, CallGasDenote.baseCold_eq, CallGasDenote.valueFee_eq,
        CallGasDenote.newAcctFee_eq, CallGasDenote.stipendC_eq,
        Evm.Frontier.Vm.Gas.call, Evm.Frontier.Vm.Gas.callValue, Evm.Frontier.Vm.Gas.newAccount,
        Evm.Frontier.Vm.Gas.callStipend, Evm.TangerineWhistle.Vm.Gas.call,
        Evm.Berlin.Vm.Gas.warmAccess, Evm.Berlin.Vm.Gas.coldAccountAccess]
      simp (disch := decide) only [movImmInstrs_small, List.cons_append, List.nil_append,
        List.append_assoc]
      simp only [entry, BEq.beq, String.reduceEq, decide_true, decide_false, ite_true, ite_false,
        reduceCtorEq]))

set_option maxHeartbeats 8000000 in
/-- `_eita_call_gas_frontier` stores `planFrontier`. -/
theorem frontier_sem (m : RM) (isCold cv cn : Bool) (gasArg : Nat)
    (h2 : m.regs .x2 = flagsWord isCold cv cn) (h14 : m.regs .x14 = BitVec.ofNat 64 gasArg) :
    (exec (entry "_eita_call_gas_frontier" X86CallGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 (CallGasDenote.planFrontier cv cn gasArg).charge,
              BitVec.ofNat 64 (CallGasDenote.planFrontier cv cn gasArg).forward,
              BitVec.ofNat 64 (CallGasDenote.planFrontier cv cn gasArg).stipend) := by
  callgasx_unfold
  simp [exec, step, h2, h14, bcHolds, logicFlags, outWords, CallGasDenote.planFrontier,
        CallGasDenote.selIf, CallGasDenote.fBase_eq, CallGasDenote.fValueFee_eq,
        CallGasDenote.fNewAcctFee_eq, CallGasDenote.fStipend_eq, Evm.Frontier.Vm.Gas.call,
        Evm.Frontier.Vm.Gas.callValue, Evm.Frontier.Vm.Gas.newAccount,
        Evm.Frontier.Vm.Gas.callStipend]
  cases cv <;> cases cn <;> simp

set_option maxHeartbeats 8000000 in
/-- `_eita_call_gas_tangerine` stores `planTangerine`. -/
theorem tangerine_sem (m : RM) (isCold cv cn : Bool) (gasArg avail : Nat)
    (h2 : m.regs .x2 = flagsWord isCold cv cn) (h14 : m.regs .x14 = BitVec.ofNat 64 gasArg)
    (h6 : m.regs .x6 = BitVec.ofNat 64 avail) (hg : gasArg < 2^64) (ha : avail < 2^64) :
    (exec (entry "_eita_call_gas_tangerine" X86CallGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 (CallGasDenote.planTangerine cv cn gasArg avail).charge,
              BitVec.ofNat 64 (CallGasDenote.planTangerine cv cn gasArg avail).forward,
              BitVec.ofNat 64 (CallGasDenote.planTangerine cv cn gasArg avail).stipend) := by
  callgasx_unfold
  simp [exec, step, h2, h14, h6, bcHolds, logicFlags, subFlags, outWords,
        CallGasDenote.planTangerine, CallGasDenote.selIf, CallGasDenote.satSub,
        CallGasDenote.retain6364, CallGasDenote.minLo,
        CallGasDenote.tBase_eq, CallGasDenote.tValueFee_eq,
        CallGasDenote.tNewAcctFee_eq, CallGasDenote.tStipend_eq, Evm.TangerineWhistle.Vm.Gas.call,
        Evm.Frontier.Vm.Gas.callValue, Evm.Frontier.Vm.Gas.newAccount,
        Evm.Frontier.Vm.Gas.callStipend]
  cases cv <;> cases cn <;> simp [ushiftRight_six] <;> (repeat' split) <;> bv_omega

set_option maxHeartbeats 8000000 in
/-- `_eita_call_gas` (Berlin+) stores `plan`. -/
theorem berlin_sem (m : RM) (isCold cv cn : Bool) (delegated gasArg avail : Nat)
    (h2 : m.regs .x2 = flagsWord isCold cv cn) (h1 : m.regs .x1 = BitVec.ofNat 64 delegated)
    (h14 : m.regs .x14 = BitVec.ofNat 64 gasArg) (h6 : m.regs .x6 = BitVec.ofNat 64 avail)
    (hd : delegated + 2600 + 9000 + 25000 < 2^64) (hg : gasArg < 2^64) (ha : avail < 2^64) :
    (exec (entry "_eita_call_gas" X86CallGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 (CallGasDenote.plan isCold cv cn delegated gasArg avail).charge,
              BitVec.ofNat 64 (CallGasDenote.plan isCold cv cn delegated gasArg avail).forward,
              BitVec.ofNat 64 (CallGasDenote.plan isCold cv cn delegated gasArg avail).stipend) := by
  callgasx_unfold
  simp [exec, step, h2, h1, h14, h6, bcHolds, logicFlags, subFlags, outWords,
        CallGasDenote.plan, CallGasDenote.selIf, CallGasDenote.satSub,
        CallGasDenote.retain6364, CallGasDenote.minLo,
        CallGasDenote.baseWarm_eq, CallGasDenote.baseCold_eq, CallGasDenote.valueFee_eq,
        CallGasDenote.newAcctFee_eq, CallGasDenote.stipendC_eq,
        Evm.Berlin.Vm.Gas.warmAccess, Evm.Berlin.Vm.Gas.coldAccountAccess,
        Evm.Frontier.Vm.Gas.callValue, Evm.Frontier.Vm.Gas.newAccount,
        Evm.Frontier.Vm.Gas.callStipend]
  cases isCold <;> cases cv <;> cases cn <;> simp [ushiftRight_six] <;> (repeat' split) <;>
    (repeat' apply And.intro) <;> bv_omega

/-! ## Program → spec -/

theorem berlin_is_callGasPlan (m : RM) (isCold cv cn : Bool) (delegated gasArg avail : Nat)
    (h2 : m.regs .x2 = flagsWord isCold cv cn) (h1 : m.regs .x1 = BitVec.ofNat 64 delegated)
    (h14 : m.regs .x14 = BitVec.ofNat 64 gasArg) (h6 : m.regs .x6 = BitVec.ofNat 64 avail)
    (hd : delegated + 2600 + 9000 + 25000 < 2^64) (hg : gasArg < 2^64) (ha : avail < 2^64) :
    let p := Evm.Berlin.Vm.Effect.callGasPlan isCold cv cn delegated gasArg avail
    (exec (entry "_eita_call_gas" X86CallGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 p.charge, BitVec.ofNat 64 p.forward, BitVec.ofNat 64 p.stipend) := by
  intro p
  rw [berlin_sem m isCold cv cn delegated gasArg avail h2 h1 h14 h6 hd hg ha,
      CallGasDenote.plan_eq_spec]

theorem tangerine_is_callGasPlan (m : RM) (isCold cv cn : Bool) (gasArg avail : Nat)
    (h2 : m.regs .x2 = flagsWord isCold cv cn) (h14 : m.regs .x14 = BitVec.ofNat 64 gasArg)
    (h6 : m.regs .x6 = BitVec.ofNat 64 avail) (hg : gasArg < 2^64) (ha : avail < 2^64) :
    let p := Evm.TangerineWhistle.Vm.Effect.callGasPlan cv cn gasArg avail
    (exec (entry "_eita_call_gas_tangerine" X86CallGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 p.charge, BitVec.ofNat 64 p.forward, BitVec.ofNat 64 p.stipend) := by
  intro p
  rw [tangerine_sem m isCold cv cn gasArg avail h2 h14 h6 hg ha, CallGasDenote.planTangerine_eq_spec]

theorem frontier_is_callGasPlan (m : RM) (isCold cv cn : Bool) (gasArg : Nat)
    (h2 : m.regs .x2 = flagsWord isCold cv cn) (h14 : m.regs .x14 = BitVec.ofNat 64 gasArg) :
    let p := Evm.Frontier.Vm.Effect.callGasPlan cv cn gasArg
    (exec (entry "_eita_call_gas_frontier" X86CallGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 p.charge, BitVec.ofNat 64 p.forward, BitVec.ofNat 64 p.stipend) := by
  intro p
  rw [frontier_sem m isCold cv cn gasArg h2 h14, CallGasDenote.planFrontier_eq_spec]

end Evm.CL.X86CallGasSem
