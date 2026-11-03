import Evm.CL.EffectSystem
import Evm.CL.EffectTxProof
import Evm.Arc.Spec.BlockSystem

/-! # CL/EffectSystemProof — `EffectSystem.term` IS every fork's system call

`system_refines`: for every fork ordinal `k`, block environment, world, **rule** (the warm-up
and the gas price a chain's system call starts with), target and data, ANY precompile table
`pre` and ANY frame run `runSub`, the derived system-call effect run from the world (no per-tx
sets yet) and the spec's message (`Evm.Frontier.Vm.System.message`, EELS
`process_unchecked_system_transaction`'s `process_message_call`) agree: the term's world,
accounts_to_delete, touched set and refund counter are the message's (EQUAL), the gas it
charged plus the gas the message left is `SYSTEM_TRANSACTION_GAS`, its flag is the message's
success, and it rejects nothing.

* `system_refines_eels` — Ethereum's rule (`System.eels`: nothing warm, GASPRICE the base fee);
  the world after the call is the message's (EELS drops the accounts_to_delete and the touched
  set: the wrapper runs no end of tx).
* `checked_refines` — `process_checked_system_transaction` (EIP-7002, EIP-7251): the term
  rejects a target without code, the wrapper refuses a failed call, and otherwise the world is
  the spec's: the replay refuses exactly the blocks EELS invalidates.
* `system_refines_arc` — Arc's rule (`Evm.Arc.Spec.BlockSystem.systemRule`, arc-node's revm
  `run_system_call`: the target, NativeCoinControl from Zero7 and, after a block's
  transactions, the precompiles warm; GASPRICE 0), and the end revm's commit runs (the
  derived `spec-destroy-effect`, `spec-sweep-effect`): the wrapper's sequence leaves
  `systemEnd` (extensionally).

Assumptions, stated: a frame never ends with more gas than it was given (`hmono`); a precompile
never returns more gas than it got (`hpmono`); for `system_refines`, a checked call's target
has code (the other case is `checked_refines`'); for Arc's end, only existing accounts carry
storage after the message (`WF`). The seams: `warm-system-seed!` warms `*system-seed*` in order
(= `Rule.seed`); `run-tx-frame!` / `precompile-run-bytes!` as for the tx (the frame's GASPRICE
is the block context's `:effective-gas-price` = `Rule.gasPrice`, its ORIGIN the sender). -/

set_option linter.unusedSimpArgs false

namespace Evm.CL.EffectSystem

open Evm.CL.EffectIR
open Evm.Frontier (State)
open Evm.Frontier.Vm (Environment Evm Exception)
open Evm.Frontier.Vm.Tx (Tx Out callTail)
open Evm.Frontier.Vm.System
open Evm.CL.EffectTx (h0 MBound callPath_run callOracle delegS_run cDel cDel_bool ins_eq)

section sys
variable (k : Nat) (benv : Environment) (st : State) (r : Rule) (tgt : Evm.Address) (data : Evm.Bytes)
  (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
  (runSub : Evm → Except Exception Evm)

/-- The spec's delegation along the system message (`Tx.call`'s `d`; no authorizations, so its
    `e1` is `env0`). -/
def dS : Option Evm.Address :=
  if k ≥ 17 then Evm.Prague.State.parseDelegation ((env0 k benv st r).state.getAccount tgt).code else none

/-- `Tx.call`'s `e2`: the delegate warmed. -/
def e2S : Environment :=
  match dS k benv st r tgt with
  | some a => Evm.Frontier.Vm.Call.warm (env0 k benv st r) a
  | none => env0 k benv st r

/-- The term's inputs as `system-call` passes them (and the defun binds its constants), with
    the precompile table and the frame oracle the theorem gives it: the spec's, on the system
    message's frame. -/
def ctxSys (checked : Bool) : Ctx :=
  { fork := k
    addr := fun x => if x = "sender" then systemAddress else if x = "target" then tgt else 0
    bool := fun x => if x = "prague" then decide (k ≥ 17) else if x = "checked" then checked else false
    nat := fun x => if x = "gas-limit" then systemGas else 0
    input := data
    pre := pre (e2S k benv st r tgt)
    child := callOracle (e2S k benv st r tgt) systemAddress tgt (sysTx tgt data) (dS k benv st r tgt) runSub
    sysSeed := r.seed }

end sys

/-- The warm-up leaves the environment the system message starts in. -/
theorem warmSys_run (c : Ctx) (k : Nat) (benv : Environment) (st : State) (r : Rule)
    (hs : c.sysSeed = r.seed) :
    Stmt.warmSys.run c (h0 st) = HState.ofEnv (env0 k benv st r) := by
  simp [Stmt.run, h0, HState.ofEnv, env0, hs, ins_eq]

set_option maxHeartbeats 4000000 in
/-- **The derived system call is every fork's system message, under any rule.** -/
theorem system_refines (k : Nat) (benv : Environment) (st : State) (r : Rule) (tgt : Evm.Address)
    (data : Evm.Bytes)
    (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm) (checked : Bool)
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hpmono : ∀ a p i g o g', pre (e2S k benv st r tgt) a = some p → p i g = .ok (o, g') → g' ≤ g)
    (hcode : checked = true → (st.getAccount tgt).code.size ≠ 0) :
    let R := term.run (ctxSys k benv st r tgt data pre runSub checked) (h0 st)
    let o := message k benv st r tgt data pre runSub
    R.rej = 0 ∧ R.state = o.env.state ∧ R.destroyed = o.env.selfDestructSet ∧ R.touched = o.env.touched ∧
      R.refund = o.env.refundCounter ∧ R.gas + o.gasLeft = systemGas ∧
      R.out = (if o.success then Evm.U256.ofNat 1 else 0) := by
  intro R o
  let c := ctxSys k benv st r tgt data pre runSub checked
  -- the code rule passes, the warm-up gives `env0`
  have hce : (BExp.and (.var "checked") (.codeEmpty EffectTx.target)).eval c (h0 st) = false := by
    cases hck : checked
    · simp [BExp.eval, c, ctxSys, hck]
    · simp [BExp.eval, c, ctxSys, hck, AExp.eval, h0, EffectTx.target, hcode hck]
  have hR : R = (EffectTx.delegS term.message).run c (HState.ofEnv (env0 k benv st r)) := by
    have h1 : R = (EffectTx.delegS term.message).run c (Stmt.warmSys.run c (h0 st)) := by
      simp only [R, term, Stmt.run]
      rw [if_neg (by rw [hce]; exact Bool.false_ne_true)]
    rw [h1, warmSys_run c k benv st r rfl]
  obtain ⟨dc, hdel⟩ := delegS_run c term.message (env0 k benv st r) tgt (decide (k ≥ 17))
    (by simp [c, ctxSys]) (by simp [c, ctxSys])
  rw [hdel] at hR
  have hdS : (if decide (k ≥ 17) = true then Evm.Prague.State.parseDelegation
      ((env0 k benv st r).state.getAccount tgt).code else none) = dS k benv st r tgt := by
    simp [dS]
  rw [hdS] at hR
  let c4 := { cDel c (dS k benv st r tgt) dc with
    snaps := fun y => if y = "snap" then HState.ofEnv (e2S k benv st r tgt)
                      else (cDel c (dS k benv st r tgt) dc).snaps y }
  have hcreate : (cDel c (dS k benv st r tgt) dc).bool "create" = false := by
    rw [cDel_bool _ _ _ _ (by decide) (by decide)]
    simp [c, ctxSys]
  have hR2 : R = EffectTx.callPath.run c4 (HState.ofEnv (e2S k benv st r tgt)) := by
    rw [hR]; rfl
  have hB : MBound c4 k systemAddress tgt (sysTx tgt data) systemGas (dS k benv st r tgt).isSome
      ((dS k benv st r tgt).getD 0) := by
    constructor <;> simp [c4, cDel, c, ctxSys, sysTx]
  have hch : c4.child = callOracle (e2S k benv st r tgt) systemAddress tgt (sysTx tgt data)
      (dS k benv st r tgt) runSub := by
    simp [c4, cDel, c, ctxSys]
  have hpr : c4.pre = pre (e2S k benv st r tgt) := by
    simp [c4, cDel, c, ctxSys]
  have key := callPath_run c4 k (e2S k benv st r tgt) systemAddress tgt (sysTx tgt data) systemGas
    (dS k benv st r tgt) pre runSub hB (by simp [c4]) hpr hch
    (fun sub hs => by
      have := hmono _ sub hs
      simpa [Evm.fresh, Evm.Frontier.Vm.Tx.callMsg, sysTx] using this)
    (fun p o' g' hp hpo => hpmono _ _ _ _ _ _ hp hpo)
  have ho : o = callTail k (e2S k benv st r tgt) systemAddress tgt (sysTx tgt data) systemGas
      (dS k benv st r tgt) pre runSub := by
    simp only [o, message]
    unfold Evm.Frontier.Vm.Tx.call e2S dS
    simp only [sysTx, List.foldl_nil, ite_self]
    rfl
  rw [hR2, ho]
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := key
  exact ⟨k7, k1, k2, k3, k4, k5, k6⟩

/-- A checked call to a target without code: the term rejects it and changes nothing. -/
theorem system_reject (k : Nat) (benv : Environment) (st : State) (r : Rule) (tgt : Evm.Address)
    (data : Evm.Bytes)
    (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm) (hc : (st.getAccount tgt).code.size = 0) :
    term.run (ctxSys k benv st r tgt data pre runSub true) (h0 st) = { h0 st with rej := 1 } := by
  simp [term, Stmt.run, BExp.eval, ctxSys, AExp.eval, EffectTx.target, h0, hc]

/-- **EELS's checked rule** (`process_checked_system_transaction`, EIP-7002 and EIP-7251): the
    wrapper (`system-call :checked t`: a rejection or a failed call is an invalid block) refuses
    exactly what EELS invalidates; otherwise the world is the spec's. -/
theorem checked_refines (k : Nat) (benv : Environment) (st : State) (r : Rule) (tgt : Evm.Address)
    (data : Evm.Bytes)
    (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm)
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hpmono : ∀ a p i g o g', pre (e2S k benv st r tgt) a = some p → p i g = .ok (o, g') → g' ≤ g) :
    let R := term.run (ctxSys k benv st r tgt data pre runSub true) (h0 st)
    match Evm.Frontier.Vm.System.checked k benv st r tgt data pre runSub with
    | .error _ => R.rej ≠ 0 ∨ R.out ≠ Evm.U256.ofNat 1
    | .ok (s, _) => R.rej = 0 ∧ R.out = Evm.U256.ofNat 1 ∧ R.state = s := by
  intro R
  unfold Evm.Frontier.Vm.System.checked
  by_cases hc : (st.getAccount tgt).code.size = 0
  · simp only [hc, if_true]
    left
    simp [R, system_reject k benv st r tgt data pre runSub hc]
  · simp only [hc, if_false]
    obtain ⟨hrej, hst, -, -, -, -, hout⟩ :=
      system_refines k benv st r tgt data pre runSub true hmono hpmono (fun _ => hc)
    cases hs : (message k benv st r tgt data pre runSub).success
    · simp only [Bool.false_eq_true, if_false]
      right
      have : R.out = 0 := by simp only [R] at hout ⊢; rw [hout, hs]; rfl
      rw [this]; decide
    · simp only [if_true]
      refine ⟨hrej, ?_, hst⟩
      simp only [R] at hout ⊢; rw [hout, hs]; rfl

/-- **Ethereum** (EELS `process_unchecked_system_transaction`: EIP-4788, EIP-2935, and the
    message of EIP-7002/7251): under the EELS rule the wrapper's world after the call is the
    spec's, with no end of tx. -/
theorem system_refines_eels (k : Nat) (benv : Environment) (st : State) (tgt : Evm.Address)
    (data : Evm.Bytes)
    (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm)
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hpmono : ∀ a p i g o g', pre (e2S k benv st (eels benv) tgt) a = some p → p i g = .ok (o, g') → g' ≤ g) :
    let R := term.run (ctxSys k benv st (eels benv) tgt data pre runSub false) (h0 st)
    R.rej = 0 ∧ R.state = (unchecked k benv st (eels benv) tgt data pre runSub).1 ∧
      (R.out = Evm.U256.ofNat 1 ↔ (unchecked k benv st (eels benv) tgt data pre runSub).2.1 = true) := by
  intro R
  obtain ⟨hrej, hst, -, -, -, -, hout⟩ :=
    system_refines k benv st (eels benv) tgt data pre runSub false hmono hpmono (fun h => by cases h)
  refine ⟨hrej, hst, ?_⟩
  simp only [R] at hout ⊢
  rw [hout]
  simp only [unchecked]
  cases (message k benv st (eels benv) tgt data pre runSub).success
  · simp only [Bool.false_eq_true, if_false, iff_false]; decide
  · simp

open Evm.CL.EffectSettle (SAgree WF)
open Evm.Arc.Spec.BlockSystem (systemRule systemEnd)

/-- **Arc** (arc-node: revm's `run_system_call`, then the commit): under Arc's rule, the
    wrapper's sequence — the term, `spec-destroy-effect`, `spec-sweep-effect` — leaves the
    world `systemEnd` describes (extensionally: existence, accounts, storage). -/
theorem system_refines_arc (k : Nat) (benv : Environment) (st : State) (tgt : Evm.Address)
    (data : Evm.Bytes) (zero7 precompilesWarm : Bool)
    (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm)
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hpmono : ∀ a p i g o g', pre (e2S k benv st (systemRule k tgt zero7 precompilesWarm) tgt) a = some p →
      p i g = .ok (o, g') → g' ≤ g)
    (hwf : WF (message k benv st (systemRule k tgt zero7 precompilesWarm) tgt data pre runSub).env.state) :
    let R := term.run (ctxSys k benv st (systemRule k tgt zero7 precompilesWarm) tgt data pre runSub false) (h0 st)
    let E := EffectEndTx.endTx.run (EffectEndTx.ctxOf k) R
    R.rej = 0 ∧
      SAgree (systemEnd k (message k benv st (systemRule k tgt zero7 precompilesWarm) tgt data pre runSub)) E.state := by
  intro R E
  obtain ⟨hrej, hst, hdes, htou, -, -, -⟩ :=
    system_refines k benv st (systemRule k tgt zero7 precompilesWarm) tgt data pre runSub false hmono hpmono
      (fun h => by cases h)
  refine ⟨hrej, ?_⟩
  have hwfR : WF R.state := by simp only [R] at hst ⊢; rw [hst]; exact hwf
  obtain ⟨hB, -⟩ := EffectEndTx.endTx_refines k R hwfR
  have : systemEnd k (message k benv st (systemRule k tgt zero7 precompilesWarm) tgt data pre runSub)
      = EffectEndTx.specEndTx k R.state R.destroyed R.touched := by
    simp only [R] at hst hdes htou ⊢
    rw [hst, hdes, htou]; rfl
  rw [this]; exact hB

end Evm.CL.EffectSystem
