/-
  Evm.CL.ARM64.CallGasSem — the `_eita_call_gas*` PROGRAMS run under `AsmSem`
  store exactly the `CallGasDenote` plans.
-/

import Evm.CL.AsmSem
import Evm.CL.ARM64.CallGas
import Evm.CL.ARM64.CallGasDenote

namespace Evm.CL.ARM64.CallGasSem

open Evm.CL.AsmCore Evm.CL.AsmSem Evm.CL.ARM64

set_option maxHeartbeats 8000000 in
/-- x1 as the C caller packs it: bit0 isCold, bit1 chargesValue, bit2 chargesNewAccount. -/
def flagsWord (isCold cv cn : Bool) : BitVec 64 :=
  (if isCold then 1 else 0) ||| (if cv then 2 else 0) ||| (if cn then 4 else 0)

@[simp] theorem flagsWord_bit1 (a b c : Bool) : (flagsWord a b c &&& 1#64 = 0#64) ↔ a = false := by
  cases a <;> cases b <;> cases c <;> simp [flagsWord]
@[simp] theorem flagsWord_bit2 (a b c : Bool) : (flagsWord a b c &&& 2#64 = 0#64) ↔ b = false := by
  cases a <;> cases b <;> cases c <;> simp [flagsWord]
@[simp] theorem flagsWord_bit4 (a b c : Bool) : (flagsWord a b c &&& 4#64 = 0#64) ↔ c = false := by
  cases a <;> cases b <;> cases c <;> simp [flagsWord]

/-- The three words the routine leaves at `out`. -/
def outWords (m : RM) (m' : RM) : BitVec 64 × BitVec 64 × BitVec 64 :=
  (m'.mem (m.regs .x0), m'.mem (m.regs .x0 + 8#64), m'.mem (m.regs .x0 + 16#64))


/-- Everything the three proofs unfold: the program, the probed constants as
    numbers, the machine. -/
syntax "callgas_unfold" : tactic
macro_rules
  | `(tactic| callgas_unfold) => `(tactic| (
      simp only [CallGas.instrs, CallGas.berlinA, CallGas.frontierA, CallGas.tangerineA,
        Evm.CL.Frame.header, CallGas.feeIf, CallGas.capForward, CallGas.finish,
        CallGasDenote.fBase_eq, CallGasDenote.fValueFee_eq, CallGasDenote.fNewAcctFee_eq,
        CallGasDenote.fStipend_eq, CallGasDenote.tBase_eq, CallGasDenote.tValueFee_eq,
        CallGasDenote.tNewAcctFee_eq, CallGasDenote.tStipend_eq,
        CallGasDenote.baseWarm_eq, CallGasDenote.baseCold_eq, CallGasDenote.valueFee_eq,
        CallGasDenote.newAcctFee_eq, CallGasDenote.stipendC_eq,
        Evm.Frontier.Vm.Gas.call, Evm.Frontier.Vm.Gas.callValue, Evm.Frontier.Vm.Gas.newAccount,
        Evm.Frontier.Vm.Gas.callStipend, Evm.TangerineWhistle.Vm.Gas.call,
        Evm.Berlin.Vm.Gas.warmAccess, Evm.Berlin.Vm.Gas.coldAccountAccess]
      simp (disch := decide) only [movImmInstrs_small, List.cons_append, List.nil_append]
      simp only [entry, BEq.beq, String.reduceEq, decide_true, decide_false, ite_true, ite_false,
        reduceCtorEq]))

/-- `_eita_call_gas_frontier` stores `planFrontier` — no cap, `avail` unread. -/
theorem frontier_sem (m : RM) (isCold cv cn : Bool) (gasArg : Nat)
    (h1 : m.regs .x1 = flagsWord isCold cv cn) (h3 : m.regs .x3 = BitVec.ofNat 64 gasArg) :
    (exec (entry "_eita_call_gas_frontier" CallGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 (CallGasDenote.planFrontier cv cn gasArg).charge,
              BitVec.ofNat 64 (CallGasDenote.planFrontier cv cn gasArg).forward,
              BitVec.ofNat 64 (CallGasDenote.planFrontier cv cn gasArg).stipend) := by
  callgas_unfold
  simp [exec, step, h1, h3, bcHolds, logicFlags, outWords, CallGasDenote.planFrontier,
        CallGasDenote.selIf, CallGasDenote.fBase_eq, CallGasDenote.fValueFee_eq,
        CallGasDenote.fNewAcctFee_eq, CallGasDenote.fStipend_eq, Evm.Frontier.Vm.Gas.call,
        Evm.Frontier.Vm.Gas.callValue, Evm.Frontier.Vm.Gas.newAccount,
        Evm.Frontier.Vm.Gas.callStipend]
  cases cv <;> cases cn <;> simp

set_option maxHeartbeats 8000000 in
/-- `_eita_call_gas_tangerine` stores `planTangerine`: the saturating pool and
    the 63/64 cap, for every `gasArg` and `avail` that fit the registers. -/
theorem tangerine_sem (m : RM) (isCold cv cn : Bool) (gasArg avail : Nat)
    (h1 : m.regs .x1 = flagsWord isCold cv cn) (h3 : m.regs .x3 = BitVec.ofNat 64 gasArg)
    (h4 : m.regs .x4 = BitVec.ofNat 64 avail) (hg : gasArg < 2^64) (ha : avail < 2^64) :
    (exec (entry "_eita_call_gas_tangerine" CallGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 (CallGasDenote.planTangerine cv cn gasArg avail).charge,
              BitVec.ofNat 64 (CallGasDenote.planTangerine cv cn gasArg avail).forward,
              BitVec.ofNat 64 (CallGasDenote.planTangerine cv cn gasArg avail).stipend) := by
  callgas_unfold
  simp [exec, step, h1, h3, h4, bcHolds, logicFlags, subFlags, outWords,
        CallGasDenote.planTangerine, CallGasDenote.selIf, CallGasDenote.satSub,
        CallGasDenote.retain6364, CallGasDenote.minLo,
        CallGasDenote.tBase_eq, CallGasDenote.tValueFee_eq,
        CallGasDenote.tNewAcctFee_eq, CallGasDenote.tStipend_eq, Evm.TangerineWhistle.Vm.Gas.call,
        Evm.Frontier.Vm.Gas.callValue, Evm.Frontier.Vm.Gas.newAccount,
        Evm.Frontier.Vm.Gas.callStipend]
  cases cv <;> cases cn <;> simp [ushiftRight_six] <;> (repeat' split) <;> bv_omega

set_option maxHeartbeats 8000000 in
/-- `_eita_call_gas` (Berlin+) stores `plan`: cold/warm base, the fee deltas,
    the delegated cost, pool, cap and stipend. -/
theorem berlin_sem (m : RM) (isCold cv cn : Bool) (delegated gasArg avail : Nat)
    (h1 : m.regs .x1 = flagsWord isCold cv cn) (h2 : m.regs .x2 = BitVec.ofNat 64 delegated)
    (h3 : m.regs .x3 = BitVec.ofNat 64 gasArg) (h4 : m.regs .x4 = BitVec.ofNat 64 avail)
    (hd : delegated + 2600 + 9000 + 25000 < 2^64) (hg : gasArg < 2^64) (ha : avail < 2^64) :
    (exec (entry "_eita_call_gas" CallGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 (CallGasDenote.plan isCold cv cn delegated gasArg avail).charge,
              BitVec.ofNat 64 (CallGasDenote.plan isCold cv cn delegated gasArg avail).forward,
              BitVec.ofNat 64 (CallGasDenote.plan isCold cv cn delegated gasArg avail).stipend) := by
  callgas_unfold
  simp [exec, step, h1, h2, h3, h4, bcHolds, logicFlags, subFlags, outWords,
        CallGasDenote.plan, CallGasDenote.selIf, CallGasDenote.satSub,
        CallGasDenote.retain6364, CallGasDenote.minLo,
        CallGasDenote.baseWarm_eq, CallGasDenote.baseCold_eq, CallGasDenote.valueFee_eq,
        CallGasDenote.newAcctFee_eq, CallGasDenote.stipendC_eq,
        Evm.Berlin.Vm.Gas.warmAccess, Evm.Berlin.Vm.Gas.coldAccountAccess,
        Evm.Frontier.Vm.Gas.callValue, Evm.Frontier.Vm.Gas.newAccount,
        Evm.Frontier.Vm.Gas.callStipend]
  cases isCold <;> cases cv <;> cases cn <;> simp [ushiftRight_six] <;> (repeat' split) <;> (repeat' apply And.intro) <;> bv_omega

/-! ## Program → spec

With `CallGasDenote.plan_eq_spec` (plan = `callGasPlan`), the emitted program
is the fork's plan: no inspection step remains between the asm and the spec. -/

theorem berlin_is_callGasPlan (m : RM) (isCold cv cn : Bool) (delegated gasArg avail : Nat)
    (h1 : m.regs .x1 = flagsWord isCold cv cn) (h2 : m.regs .x2 = BitVec.ofNat 64 delegated)
    (h3 : m.regs .x3 = BitVec.ofNat 64 gasArg) (h4 : m.regs .x4 = BitVec.ofNat 64 avail)
    (hd : delegated + 2600 + 9000 + 25000 < 2^64) (hg : gasArg < 2^64) (ha : avail < 2^64) :
    let p := Evm.Berlin.Vm.Effect.callGasPlan isCold cv cn delegated gasArg avail
    (exec (entry "_eita_call_gas" CallGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 p.charge, BitVec.ofNat 64 p.forward, BitVec.ofNat 64 p.stipend) := by
  intro p
  rw [berlin_sem m isCold cv cn delegated gasArg avail h1 h2 h3 h4 hd hg ha,
      CallGasDenote.plan_eq_spec]

theorem tangerine_is_callGasPlan (m : RM) (isCold cv cn : Bool) (gasArg avail : Nat)
    (h1 : m.regs .x1 = flagsWord isCold cv cn) (h3 : m.regs .x3 = BitVec.ofNat 64 gasArg)
    (h4 : m.regs .x4 = BitVec.ofNat 64 avail) (hg : gasArg < 2^64) (ha : avail < 2^64) :
    let p := Evm.TangerineWhistle.Vm.Effect.callGasPlan cv cn gasArg avail
    (exec (entry "_eita_call_gas_tangerine" CallGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 p.charge, BitVec.ofNat 64 p.forward, BitVec.ofNat 64 p.stipend) := by
  intro p
  rw [tangerine_sem m isCold cv cn gasArg avail h1 h3 h4 hg ha, CallGasDenote.planTangerine_eq_spec]

theorem frontier_is_callGasPlan (m : RM) (isCold cv cn : Bool) (gasArg : Nat)
    (h1 : m.regs .x1 = flagsWord isCold cv cn) (h3 : m.regs .x3 = BitVec.ofNat 64 gasArg) :
    let p := Evm.Frontier.Vm.Effect.callGasPlan cv cn gasArg
    (exec (entry "_eita_call_gas_frontier" CallGas.instrs) m).map (outWords m)
      = some (BitVec.ofNat 64 p.charge, BitVec.ofNat 64 p.forward, BitVec.ofNat 64 p.stipend) := by
  intro p
  rw [frontier_sem m isCold cv cn gasArg h1 h3, CallGasDenote.planFrontier_eq_spec]

end Evm.CL.ARM64.CallGasSem
