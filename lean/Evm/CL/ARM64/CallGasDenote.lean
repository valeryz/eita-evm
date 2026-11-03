/-
  Evm.CL.ARM64.CallGasDenote — what `_eita_call_gas` computes, and the proof
  that it is `callGasPlan`.

  Stage 1 of #238 (docs/x86-64-backend.md), second piece. `ARM64.CallGas`
  evaluates its CONSTANTS out of the Lean plan, which is why a schedule change
  re-emits without a hand edit — but the arithmetic AROUND those constants is
  hand-written asm with no denotation:

      base    = tst x1,#1 ; csel            -- isCold ? cold : warm
      charge  = base + csel(value) + csel(newAcct) + x2
      pool    = subs x11,x4,x9 ; csel x11,xzr,x11,lo
      forward = lsr x12,x11,#6 ; sub ; cmp x3,x12 ; csel x12,x3,x12,lo
      stipend = tst x1,#2 ; csel

  Two things in there are only justified by comment today, and both are the kind
  of thing a hand-port to a second ISA gets wrong silently:

  1. **The affine decomposition.** The emitter does not emit four base costs; it
     emits one base plus DELTAS measured at one flag combination
     (`valueFee = chargeConst false true false - baseWarm`) and adds them
     conditionally. That is only equal to the spec for every OTHER flag
     combination if the plan really is affine in the flags. The header says
     "charge is affine in delegatedCost by defn"; nothing said the same about
     `chargesValue` and `chargesNewAccount`, which is where the deltas come from.

  2. **The saturating subtraction.** The spec writes `avail - charge` in ℕ,
     which truncates at zero. The asm implements that with `subs` + `csel …,
     xzr, …, lo` on a u64, where an unchecked `sub` would wrap to ~2^64 and the
     63/64 cap would then forward an astronomical pool. Same shape as the
     chunk-gas bug in `ChunkGas`, in a different gadget.

  `plan_eq_spec` below discharges both, for all three fork variants the emitter
  produces, by building the plan out of the asm's OWN step functions — and
  `CallGasSem` runs the emitted `AInstr` programs under `AsmSem` and shows they
  store exactly these plans, so the step functions are no longer a reading of
  the asm but a theorem about it.
-/

import Evm.Frontier.Vm.Effect
import Evm.TangerineWhistle.Vm.Effect
import Evm.Berlin.Vm.Effect

namespace Evm.CL.ARM64.CallGasDenote

open Evm.Frontier.Vm.Effect (CallGasPlan)

/-- Berlin has its own `CallGasPlan` (with the same three fields). -/
abbrev BPlan := Evm.Berlin.Vm.Effect.CallGasPlan

/-! ## The machine steps, one function each

Each of these is what a single asm pair does — no more, so that a step whose
denotation is wrong cannot hide inside a bigger definition. -/

/-- `tst x1, #bit ; csel d, a, b, ne` — select on a flag bit. -/
def selIf (c : Bool) (a b : Nat) : Nat := if c then a else b

/-- `subs d, a, b ; csel d, xzr, d, lo` — saturating subtract, i.e. exactly ℕ's
    truncating `-`. The `csel` is the whole content of this lemma: without it
    the u64 wraps. -/
def satSub (a b : Nat) : Nat := if b ≤ a then a - b else 0

theorem satSub_eq_natSub (a b : Nat) : satSub a b = a - b := by
  unfold satSub; by_cases h : b ≤ a
  · simp [h]
  · simp [h]; omega

/-- `lsr d, a, #6 ; sub d, a, d` — keep all but a 64th. -/
def retain6364 (pool : Nat) : Nat := pool - pool / 64

/-- `cmp a, b ; csel d, a, b, lo` — unsigned minimum. -/
def minLo (a b : Nat) : Nat := if a < b then a else b

theorem minLo_eq_min (a b : Nat) : minLo a b = min a b := by
  unfold minLo; by_cases h : a < b
  · simp [h, Nat.min_def]; omega
  · simp [h, Nat.min_def]; omega

/-! ## Berlin+ (the live path) -/

/-- The constants the emitter materialises, named as it names them. -/
def baseWarm   : Nat := (Evm.Berlin.Vm.Effect.callGasPlan false false false 0 0 0).charge
def baseCold   : Nat := (Evm.Berlin.Vm.Effect.callGasPlan true  false false 0 0 0).charge
def valueFee   : Nat := (Evm.Berlin.Vm.Effect.callGasPlan false true false 0 0 0).charge - baseWarm
def newAcctFee : Nat :=
  (Evm.Berlin.Vm.Effect.callGasPlan false true true 0 0 0).charge
  - (Evm.Berlin.Vm.Effect.callGasPlan false true false 0 0 0).charge
def stipendC   : Nat := (Evm.Berlin.Vm.Effect.callGasPlan false true false 0 0 0).stipend

/-- `_eita_call_gas`, as a function: the same steps in the same order. -/
def plan (isCold chargesValue chargesNewAccount : Bool)
    (delegated gasArg avail : Nat) : BPlan :=
  let base   := selIf isCold baseCold baseWarm              -- tst #1 ; csel
  let withV  := base + selIf chargesValue valueFee 0        -- tst #2 ; csel ; add
  let charge := withV + selIf chargesNewAccount newAcctFee 0 + delegated
  let pool   := satSub avail charge                          -- subs ; csel lo
  { charge  := charge
    forward := minLo gasArg (retain6364 pool)                -- lsr/sub ; cmp ; csel lo
    stipend := selIf chargesValue stipendC 0 }

/-- The deltas the emitter measures at ONE flag combination really are the
    schedule's fees, which is what makes the conditional adds sound at every
    other combination. -/
theorem valueFee_eq : valueFee = Evm.Frontier.Vm.Gas.callValue := by native_decide
theorem newAcctFee_eq : newAcctFee = Evm.Frontier.Vm.Gas.newAccount := by native_decide
theorem stipendC_eq : stipendC = Evm.Frontier.Vm.Gas.callStipend := by native_decide
theorem baseWarm_eq : baseWarm = Evm.Berlin.Vm.Gas.warmAccess := by native_decide
theorem baseCold_eq : baseCold = Evm.Berlin.Vm.Gas.coldAccountAccess := by native_decide

/-- **The routine is the plan**, for every flag combination and every
    `delegated`, `gasArg`, `avail`. -/
theorem plan_eq_spec (isCold chargesValue chargesNewAccount : Bool)
    (delegated gasArg avail : Nat) :
    plan isCold chargesValue chargesNewAccount delegated gasArg avail
      = Evm.Berlin.Vm.Effect.callGasPlan isCold chargesValue chargesNewAccount
          delegated gasArg avail := by
  simp only [plan, Evm.Berlin.Vm.Effect.callGasPlan, Evm.Berlin.Vm.Effect.capForward,
             Evm.Berlin.Vm.Effect.callBaseCost, selIf, satSub_eq_natSub, minLo_eq_min,
             retain6364]
  cases isCold <;> cases chargesValue <;> cases chargesNewAccount <;>
    simp [baseWarm_eq, baseCold_eq, valueFee_eq, newAcctFee_eq, stipendC_eq]

/-! ## Frontier/Homestead — no forwarding cap at all -/

def fBase       : Nat := (Evm.Frontier.Vm.Effect.callGasPlan false false 0).charge
def fValueFee   : Nat := (Evm.Frontier.Vm.Effect.callGasPlan true false 0).charge - fBase
def fNewAcctFee : Nat :=
  (Evm.Frontier.Vm.Effect.callGasPlan true true 0).charge
  - (Evm.Frontier.Vm.Effect.callGasPlan true false 0).charge
def fStipend    : Nat := (Evm.Frontier.Vm.Effect.callGasPlan true false 0).stipend

/-- `_eita_call_gas_frontier`: `mov x12, x3` — forward is the gas argument
    verbatim, and the HOST must OOG-check charge + forward. -/
theorem fBase_eq : fBase = Evm.Frontier.Vm.Gas.call := by native_decide
theorem fValueFee_eq : fValueFee = Evm.Frontier.Vm.Gas.callValue := by native_decide
theorem fNewAcctFee_eq : fNewAcctFee = Evm.Frontier.Vm.Gas.newAccount := by native_decide
theorem fStipend_eq : fStipend = Evm.Frontier.Vm.Gas.callStipend := by native_decide

def planFrontier (chargesValue chargesNewAccount : Bool) (gasArg : Nat) : CallGasPlan :=
  { charge  := fBase + selIf chargesValue fValueFee 0
                     + selIf chargesNewAccount fNewAcctFee 0
    forward := gasArg
    stipend := selIf chargesValue fStipend 0 }

theorem planFrontier_eq_spec (chargesValue chargesNewAccount : Bool) (gasArg : Nat) :
    planFrontier chargesValue chargesNewAccount gasArg
      = Evm.Frontier.Vm.Effect.callGasPlan chargesValue chargesNewAccount gasArg := by
  simp only [planFrontier, Evm.Frontier.Vm.Effect.callGasPlan, selIf]
  cases chargesValue <;> cases chargesNewAccount <;>
    simp [fBase_eq, fValueFee_eq, fNewAcctFee_eq, fStipend_eq]

/-! ## TangerineWhistle..MuirGlacier — EIP-150 cap, no cold/delegated terms -/

def tBase       : Nat := (Evm.TangerineWhistle.Vm.Effect.callGasPlan false false 0 0).charge
def tValueFee   : Nat := (Evm.TangerineWhistle.Vm.Effect.callGasPlan true false 0 0).charge - tBase
def tNewAcctFee : Nat :=
  (Evm.TangerineWhistle.Vm.Effect.callGasPlan true true 0 0).charge
  - (Evm.TangerineWhistle.Vm.Effect.callGasPlan true false 0 0).charge
def tStipend    : Nat := (Evm.TangerineWhistle.Vm.Effect.callGasPlan true false 0 0).stipend

theorem tBase_eq : tBase = Evm.TangerineWhistle.Vm.Gas.call := by native_decide
theorem tValueFee_eq : tValueFee = Evm.Frontier.Vm.Gas.callValue := by native_decide
theorem tNewAcctFee_eq : tNewAcctFee = Evm.Frontier.Vm.Gas.newAccount := by native_decide
theorem tStipend_eq : tStipend = Evm.Frontier.Vm.Gas.callStipend := by native_decide

def planTangerine (chargesValue chargesNewAccount : Bool) (gasArg avail : Nat) : CallGasPlan :=
  let charge := tBase + selIf chargesValue tValueFee 0
                      + selIf chargesNewAccount tNewAcctFee 0
  { charge  := charge
    forward := minLo gasArg (retain6364 (satSub avail charge))
    stipend := selIf chargesValue tStipend 0 }

theorem planTangerine_eq_spec (chargesValue chargesNewAccount : Bool) (gasArg avail : Nat) :
    planTangerine chargesValue chargesNewAccount gasArg avail
      = Evm.TangerineWhistle.Vm.Effect.callGasPlan chargesValue chargesNewAccount gasArg avail := by
  simp only [planTangerine, Evm.TangerineWhistle.Vm.Effect.callGasPlan,
             Evm.TangerineWhistle.Vm.Effect.capForward, selIf,
             satSub_eq_natSub, minLo_eq_min, retain6364]
  cases chargesValue <;> cases chargesNewAccount <;>
    simp [tBase_eq, tValueFee_eq, tNewAcctFee_eq, tStipend_eq]

/-! ## And the wrap that the `csel` prevents

With an unchecked `sub` the pool for an under-funded call wraps instead of
saturating, and the 63/64 cap then forwards essentially the whole u64 range —
the sub-frame runs with unbounded gas. Stated as a counterexample so the `csel`
cannot be dropped as redundant. -/

def W : Nat := 18446744073709551616

/-- `sub` without the `csel`: wrap, as the register really would. -/
def wrapSub (a b : Nat) : Nat := (a + W - b % W) % W

/-- A call whose parent cannot even pay the base charge: saturating gives a zero
    forward, wrapping gives more than 2^63. -/
example : retain6364 (satSub 100 2600) = 0 := by native_decide
example : 9223372036854775808 ≤ retain6364 (wrapSub 100 2600) := by native_decide

theorem unchecked_pool_is_wrong :
    ∃ avail charge : Nat, retain6364 (wrapSub avail charge) ≠ retain6364 (satSub avail charge) := by
  refine ⟨100, 2600, ?_⟩
  native_decide

end Evm.CL.ARM64.CallGasDenote
