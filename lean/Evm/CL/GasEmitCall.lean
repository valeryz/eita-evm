import Evm.CL.GasEmit
import Evm.Frontier.Vm.Call

/-! # Evm.CL.GasEmitCall — the emitted message-call gas IS the fork-typed spec's

`Evm.CL.GasEmit.callExtraGas` and `callStipendGas` are what a host charges and
forwards for CALL, CALLCODE, DELEGATECALL and STATICCALL: the emitted
`spec-call-extra-gas` and `spec-call-stipend-gas` (`Evm.CL.GasEmitC`). A host
has to own that arithmetic — the interpreter's call gadget fills `CallParams`
and charges whatever `CallResult.gas_used` says — so without this file those
two formulas would be a hand-transcription of EELS `calculate_message_call_gas`
sitting in the TRUSTED surface, with example vectors for evidence.

The spec side is `Evm.Berlin.Vm.Effect.callGasPlan` (EELS
`forks/berlin/vm/gas.py`), whose `charge` and `stipend` fields are exactly
these two quantities. This file proves them equal, for every fork from Berlin
on, over every combination of the three predicates. So the formulas are
DERIVED, not asserted, and the trusted surface does not grow to accommodate
them. Same pattern as `GasEmitParis` / `GasEmitCancun` / `GasEmitPrague`.

What this does NOT cover, and is stated so it is not mistaken for covered:

* **the pre-Berlin eras.** `callExtraGas` also encodes EIP-150's flat 700
  (Tangerine Whistle) and Frontier's 40, against
  `Evm.TangerineWhistle.Vm.Effect.callGasPlan` and Frontier's. Those are not
  proved here, and the wallet host refuses any fork below Berlin
  (`wit_host.h`), so nothing executes them.
* **EIP-7702 delegation.** `delegatedCost` is taken as 0; a host that supports
  delegated EOAs has to add `spec-delegate-access-gas` itself, and that
  addition would be a new trusted step.
* **the forwarded amount.** `callGasPlan.forward` is `capForward`, which is
  `GasEmit.retain63of64` applied to `avail - charge`; the equality of those
  two is not proved here either.
-/

namespace Evm.CL.GasEmitCall

open Evm.CL.GasEmit

/-- The three predicates reach the formula as 0/1. -/
private def b (p : Bool) : Nat := if p then 1 else 0

/-- **The emitted extra-gas formula is the Berlin+ spec's `charge`.**

    Holds for every fork from Berlin on and every combination of cold, value
    and new-account, with no EIP-7702 delegation. `charge` does not depend on
    the requested or available gas, so those are arbitrary. -/
theorem callExtraGas_is_berlin_charge
    (ρ : Env) (f : Evm.Fork) (hf : ρ "fork-ord" = f.ord)
    (hb : Evm.Fork.berlin.ord ≤ f.ord)
    (cold cv cna : Bool)
    (hc : ρ "cold" = b cold) (hv : ρ "value-nonzero" = b cv) (hn : ρ "new-acct" = b cna)
    (gasArg avail : Nat) :
    callExtraGas.eval ρ
      = (Evm.Berlin.Vm.Effect.callGasPlan cold cv cna 0 gasArg avail).charge := by
  have hbo : Evm.Fork.berlin.ord = 10 := rfl
  rw [hbo] at hb
  have h3 : ¬ (f.ord < 3) := by omega
  have h10 : ¬ (f.ord < 10) := by omega
  simp [callExtraGas, fork, Expr.eval, hf, hc, hv, hn, b, h3, h10,
        Evm.Berlin.Vm.Effect.callGasPlan, Evm.Berlin.Vm.Effect.callBaseCost,
        Evm.Berlin.Vm.Gas.coldAccountAccess, Evm.Berlin.Vm.Gas.warmAccess,
        Evm.Frontier.Vm.Gas.callValue, Evm.Frontier.Vm.Gas.newAccount]
  cases cold <;> cases cv <;> cases cna <;> simp

/-- **…and the emitted stipend is the spec's `stipend`.** Fork-independent:
    `callStipend` has been 2300 since Frontier. -/
theorem callStipendGas_is_spec_stipend
    (ρ : Env) (cv : Bool) (hv : ρ "value-nonzero" = b cv)
    (cold cna : Bool) (gasArg avail : Nat) :
    callStipendGas.eval ρ
      = (Evm.Berlin.Vm.Effect.callGasPlan cold cv cna 0 gasArg avail).stipend := by
  simp [callStipendGas, Expr.eval, hv, b,
        Evm.Berlin.Vm.Effect.callGasPlan, Evm.Frontier.Vm.Gas.callStipend]
  cases cv <;> simp

end Evm.CL.GasEmitCall
