import Evm.CL.EffectSload
import Evm.CL.EffectSstoreProof
import Evm.IR.Dispatch

/-! # CL/EffectSloadProof — `EffectSload.term` IS each fork's SLOAD

`sload_refines`: for every fork, the SLOAD handler the IR binds (`Op.handler f .sload`,
`sload_binding`) and the derived callback agree — the state is unchanged, the accessed slots
and (Berlin+, where the spec keeps one) the original-value cache are the term's, the word the
handler pushes is the term's result — and the opcode's gas is what the callback returns, with
out-of-gas exactly when the gas left is below it. Assumptions, stated: the key is on the
stack, and the stack below it has room for the result (always: the key was popped). -/

set_option linter.unusedSimpArgs false

namespace Evm.CL.EffectSload

open Evm.CL.EffectIR
open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Environment Evm Stack Exception)
open Evm.CL.EffectSettle (SAgree)
open Evm.CL.EffectSstore (Agree charge_cases)

/-- Each fork's SLOAD as the IR binds it (`sload_binding`). -/
def specSload : Evm.Fork → Evm → Except Exception Evm
  | .frontier | .homestead | .daoFork => Evm.Frontier.Vm.Instructions.sload
  | .tangerineWhistle | .spuriousDragon | .byzantium | .constantinople | .petersburg =>
      Evm.TangerineWhistle.Vm.Instructions.sload
  | .istanbul | .muirGlacier => Evm.Istanbul.Vm.Instructions.sload
  | _ => Evm.Berlin.Vm.Effect.doSloadPure

theorem sload_binding (f : Evm.Fork) :
    Evm.IR.Dispatch.Op.handler f .sload = some (specSload f) := by
  cases f <;> rfl

/-! ## The term's meaning in closed form -/

def ctxOf (k : Nat) (self : Evm.Address) (key : Evm.U256) : Ctx :=
  { fork := k, addr := fun _ => self, word := fun _ => key }

/-- Whether the callback finds the slot cold (Berlin+). -/
def coldOf (k : Nat) (e : Environment) (self : Evm.Address) (key : Evm.U256) : Bool :=
  decide (k ≥ 10) && !e.accessedStorageKeys.contains (self, key)

/-- The fork's price, as the spec's constants. -/
def priceOf (k : Nat) (cold : Bool) : Nat :=
  if k ≥ 10 then (if cold then Evm.Berlin.Vm.Gas.coldSload else Evm.Berlin.Vm.Gas.warmAccess)
  else if k ≥ 8 then Evm.Istanbul.Vm.Gas.sLoad
  else if k ≥ 3 then Evm.TangerineWhistle.Vm.Gas.sLoad
  else Evm.Frontier.Vm.Gas.sLoad

/-- The term's result in closed form. -/
def closed (k : Nat) (e : Environment) (self : Evm.Address) (key : Evm.U256) : HState :=
  let v := e.state.getStorage self key
  { HState.ofEnv e with
    slots := if k ≥ 10 ∧ ¬ e.accessedStorageKeys.contains (self, key)
             then e.accessedStorageKeys ++ [(self, key)] else e.accessedStorageKeys
    origs := putOrig e.storageOriginals self key v
    out := v
    gas := priceOf k (coldOf k e self key) }

theorem run_term (k : Nat) (e : Environment) (self : Evm.Address) (key : Evm.U256) :
    term.run (ctxOf k self key) (HState.ofEnv e) = closed k e self key := by
  simp only [term, gas, Stmt.run, BExp.eval, WExp.eval, AExp.eval, GExp.eval, ctxOf, HState.ofEnv,
    String.reduceEq, ite_true, ite_false, coldOf, closed, priceOf]
  by_cases hk : k ≥ 10 <;> by_cases hc : e.accessedStorageKeys.contains (self, key) = true <;>
    simp [hk, hc]

/-! ## Agreement and the theorem -/

/-- The handler pushes the term's result on the rest of the stack, leaves an environment
    that agrees with the term's state, and charges the term's gas; it fails only out of gas,
    exactly when the gas left is below that. -/
def Refines (k : Nat) (spec : Except Exception Evm) (g : Nat) (rest : List Evm.U256)
    (R : HState) : Prop :=
  (∀ evm', spec = .ok evm' → Agree k evm'.env R ∧ g = evm'.gasLeft + R.gas ∧
      evm'.stack = R.out :: rest) ∧
  (∀ e, spec = .error e → e = .outOfGas ∧ g < R.gas)

/-- The pre-Berlin shape: charge a constant, pop, read, push; the environment unchanged. -/
theorem refines_const (k : Nat) (hk : k < 10) (evm : Evm) (key : Evm.U256) (rest : List Evm.U256)
    (hstack : evm.stack = key :: rest) (hlen : rest.length < Evm.Frontier.Vm.stackLimit) :
    Refines k (do
        let gasLeft ← Evm.Frontier.Vm.Gas.charge evm.gasLeft (priceOf k false)
        let (key, s) ← Stack.pop evm.stack
        let value := evm.env.state.getStorage evm.message.currentTarget key
        let s ← Stack.push s value
        return { evm with gasLeft := gasLeft, stack := s, pc := evm.pc + 1 })
      evm.gasLeft rest (closed k evm.env evm.message.currentTarget key) := by
  have hcold : coldOf k evm.env evm.message.currentTarget key = false := by
    simp [coldOf]; omega
  have hpush : Stack.push rest (evm.env.state.getStorage evm.message.currentTarget key) =
      .ok (evm.env.state.getStorage evm.message.currentTarget key :: rest) := by
    unfold Stack.push; simp; omega
  rcases charge_cases evm.gasLeft (priceOf k false) with ⟨hle, hc⟩ | ⟨hlt, hc⟩
  · refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · simp only [hc, hstack, Stack.pop, hpush, bind, Except.bind, pure, Except.pure,
        Except.ok.injEq] at h
      subst h
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · simp only [closed]; exact SAgree.refl _
      · simp [closed, HState.ofEnv]
      · simp [closed, HState.ofEnv]; omega
      · intro h10; omega
      · simp [closed, HState.ofEnv]
      · simp [closed, hcold]; omega
      · simp [closed]
    · simp [hc, hstack, Stack.pop, hpush, bind, Except.bind, pure, Except.pure] at h
  · refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · simp [hc, bind, Except.bind] at h
    · simp only [hc, bind, Except.bind, Except.error.injEq] at h
      exact ⟨h.symm, by simp [closed, hcold]; omega⟩

set_option maxHeartbeats 4000000 in
theorem refines_berlin (k : Nat) (hk : k ≥ 10) (evm : Evm) (key : Evm.U256) (rest : List Evm.U256)
    (hstack : evm.stack = key :: rest) (hlen : rest.length < Evm.Frontier.Vm.stackLimit) :
    Refines k (Evm.Berlin.Vm.Effect.doSloadPure evm) evm.gasLeft rest
      (closed k evm.env evm.message.currentTarget key) := by
  have hpush : Stack.push rest (evm.env.state.getStorage evm.message.currentTarget key) =
      .ok (evm.env.state.getStorage evm.message.currentTarget key :: rest) := by
    unfold Stack.push; simp; omega
  have hp : priceOf k (coldOf k evm.env evm.message.currentTarget key) =
      (if ¬ Evm.Berlin.Vm.Effect.isSlotWarm evm.env evm.message.currentTarget key = true
       then Evm.Berlin.Vm.Gas.coldSload else Evm.Berlin.Vm.Gas.warmAccess) := by
    simp [priceOf, coldOf, hk, Evm.Berlin.Vm.Effect.isSlotWarm]
  unfold Evm.Berlin.Vm.Effect.doSloadPure
  simp only [hstack, Stack.pop, bind, Except.bind, pure, Except.pure]
  rw [← hp]
  rcases charge_cases evm.gasLeft (priceOf k (coldOf k evm.env evm.message.currentTarget key))
    with ⟨hle, hc⟩ | ⟨hlt, hc⟩
  · rw [hc]
    refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · simp only [hpush, Except.ok.injEq] at h; subst h
      refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
      · simp only [Evm.CL.EffectSstore.ws_state, Evm.CL.EffectSstore.co_state, closed]
        exact SAgree.refl _
      · simp [closed, HState.ofEnv]
      · simp [closed, HState.ofEnv, hk]
      · intro _; simp [closed, HState.ofEnv]
      · simp [closed, HState.ofEnv]
      · simp [closed]; omega
      · simp [closed]
    · simp [hpush] at h
  · rw [hc]
    refine ⟨fun evm' h => ?_, fun e h => ?_⟩
    · cases h
    · simp only [Except.error.injEq] at h
      exact ⟨h.symm, by simp [closed]; omega⟩

set_option maxHeartbeats 4000000 in
/-- **The derived SLOAD callback is every fork's SLOAD.** -/
theorem sload_refines (f : Evm.Fork) (evm : Evm) (key : Evm.U256) (rest : List Evm.U256)
    (hstack : evm.stack = key :: rest) (hlen : rest.length < Evm.Frontier.Vm.stackLimit) :
    Refines f.ord (specSload f evm) evm.gasLeft rest
      (term.run (ctxOf f.ord evm.message.currentTarget key) (HState.ofEnv evm.env)) := by
  rw [run_term]
  cases f <;> simp only [specSload, Evm.Fork.ord]
  all_goals first
    | exact refines_berlin _ (by decide) evm key rest hstack hlen
    | exact refines_const _ (by decide) evm key rest hstack hlen

end Evm.CL.EffectSload
