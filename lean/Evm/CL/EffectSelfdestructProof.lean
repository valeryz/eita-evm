import Lean
import Evm.CL.EffectSelfdestruct
import Evm.IR.Trampoline

/-! # CL/EffectSelfdestructProof — `EffectSelfdestruct.term` IS each fork's SELFDESTRUCT

`selfdestruct_refines`: for every fork, the opcode as the IR trampoline binds it
(`selfdestruct_binding_*`) and the derived callback agree — state, per-tx sets, refund —
and the opcode's gas is the native base plus what the callback returns, with out-of-gas
exactly when the gas left is below that. Assumption, stated: the executing account exists
(`hself`; a frame only runs code at an existing account). -/

set_option linter.unusedSimpArgs false   -- one shared hypothesis list per fork group

namespace Evm.CL.EffectSelfdestruct

open Evm.CL.EffectIR
open Evm.Frontier.Vm (Environment Evm)

/-! ## Proof: the term is each fork's SELFDESTRUCT -/

open Lean Elab Term in
/-- `priv% Module Name` — the private declaration `Name` of `Module`, so a proof here can
    unfold the fork handlers' private helpers (`u256ToAddr`, `isDead`) by their equations. -/
elab "priv%" mod:ident n:ident : term => do
  mkConstWithLevelParams ((Name.mkNum (`_private ++ mod.getId) 0) ++ n.getId)

open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Stack Exception)

section lemmas
variable (env : Environment) (a x : Evm.Address)
open Evm.SpuriousDragon.Vm (touchAddr)
open Evm.Berlin.Vm.Effect (warmAddr)

theorem getAccount_setAccount (s : State) (acc : Account) :
    (s.setAccount a acc).getAccount x = if x = a then acc else s.getAccount x := by
  unfold State.setAccount State.getAccount
  by_cases h : x = a
  · subst h; simp
  · have hp : (fun p : Evm.Address × Account => !decide (p.1 = a) && decide (p.1 = x))
        = fun p => decide (p.1 = x) := by
      funext p; by_cases hx : p.1 = x
      · simp [hx, h]
      · simp [hx]
    simp [List.find?_filter, h, Ne.symm h, hp]

theorem accountExists_setAccount (s : State) (acc : Account) :
    (s.setAccount a acc).accountExists x = (decide (x = a) || s.accountExists x) := by
  unfold State.setAccount State.accountExists
  by_cases h : x = a
  · subst h; simp
  · have hp : (fun p : Evm.Address × Account => !decide (p.1 = a) && decide (p.1 = x))
        = fun p => decide (p.1 = x) := by
      funext p; by_cases hx : p.1 = x
      · simp [hx, h]
      · simp [hx]
    simp [List.find?_filter, h, Ne.symm h, hp]

theorem getStorage_setAccount (s : State) (acc : Account) (k : Evm.U256) :
    (s.setAccount a acc).getStorage x k = s.getStorage x k := rfl

@[simp] theorem touch_state : (touchAddr env a).state = env.state := by unfold touchAddr; split <;> rfl
@[simp] theorem touch_sd : (touchAddr env a).selfDestructSet = env.selfDestructSet := by unfold touchAddr; split <;> rfl
@[simp] theorem touch_refund : (touchAddr env a).refundCounter = env.refundCounter := by unfold touchAddr; split <;> rfl
@[simp] theorem touch_accessed : (touchAddr env a).accessedAddresses = env.accessedAddresses := by unfold touchAddr; split <;> rfl
@[simp] theorem touch_created : (touchAddr env a).createdAccounts = env.createdAccounts := by unfold touchAddr; split <;> rfl
@[simp] theorem touch_touched : (touchAddr env a).touched = insertSet env.touched a := by unfold touchAddr insertSet; split <;> rfl
@[simp] theorem warm_state : (warmAddr env a).1.state = env.state := by unfold warmAddr; split <;> rfl
@[simp] theorem warm_sd : (warmAddr env a).1.selfDestructSet = env.selfDestructSet := by unfold warmAddr; split <;> rfl
@[simp] theorem warm_refund : (warmAddr env a).1.refundCounter = env.refundCounter := by unfold warmAddr; split <;> rfl
@[simp] theorem warm_touched : (warmAddr env a).1.touched = env.touched := by unfold warmAddr; split <;> rfl
@[simp] theorem warm_created : (warmAddr env a).1.createdAccounts = env.createdAccounts := by unfold warmAddr; split <;> rfl
@[simp] theorem warm_accessed : (warmAddr env a).1.accessedAddresses = insertSet env.accessedAddresses a := by unfold warmAddr insertSet; split <;> rfl
@[simp] theorem warm_cold : (warmAddr env a).2 = !env.accessedAddresses.contains a := by unfold warmAddr; split <;> simp_all
@[simp] theorem mem_insertSet (l : List Evm.Address) : x ∈ insertSet l a ↔ (x = a ∨ x ∈ l) := by
  unfold insertSet; split <;> simp_all; constructor <;> intro h <;> (try rcases h with h | h) <;> simp_all

theorem getAccount_absent (s : State) (x : Evm.Address) (h : ¬ s.accountExists x = true) :
    s.getAccount x = Account.empty := by
  unfold State.accountExists at h; unfold State.getAccount
  split
  · rename_i p hp; simp_all
  · rfl

theorem acc_eta (A : Account) (v : Evm.U256) (h : A.balance = v) :
    ({ nonce := A.nonce, balance := v, code := A.code } : Account) = A := by
  cases A; simp_all

theorem charge_ok (g c v : Nat) : Evm.Frontier.Vm.Gas.charge g c = .ok v ↔ (c ≤ g ∧ v = g - c) := by
  unfold Evm.Frontier.Vm.Gas.charge
  by_cases h : g < c
  · simp only [h, ite_true]
    constructor
    · intro hc; cases hc
    · intro ⟨h1, _⟩; exact absurd h (Nat.not_lt.mpr h1)
  · simp only [h, ite_false, Except.ok.injEq]
    exact ⟨fun hv => ⟨Nat.not_lt.mp h, hv.symm⟩, fun ⟨_, hv⟩ => hv.symm⟩
theorem charge_err (g c : Nat) (e : Exception) :
    Evm.Frontier.Vm.Gas.charge g c = .error e ↔ (g < c ∧ e = .outOfGas) := by
  unfold Evm.Frontier.Vm.Gas.charge
  by_cases h : g < c
  · simp only [h, ite_true, Except.error.injEq, true_and]; exact eq_comm
  · simp only [h, ite_false, false_and, iff_false]; intro hc; cases hc

theorem gas_close (g c s : Nat) (h : c ≤ g) (hs : s = c) : g = g - c + s := by omega
theorem gas_eq (g c d : Nat) (h : c + d ≤ g) : g = g - (c + d) + c + d := by omega
theorem gas_eq0 (g c : Nat) (h : c ≤ g) : g = g - c + c := by omega
theorem gas_eq3 (g c d e : Nat) (h : c + d + e ≤ g) : g = g - (c + d + e) + c + (e + d) := by omega
end lemmas

/-- The spec environment after the opcode and the term's state agree on everything an
    effect can change: existence, every account, every storage slot (extensionally — the
    spec's association lists differ only in order), the destroyed/touched/warm sets as
    sets, the created set, the refund counter. The rest of the environment the term does
    not touch and the handlers do not change. -/
structure Agree (e : Environment) (h : HState) : Prop where
  exists_   : ∀ x, e.state.accountExists x = h.state.accountExists x
  account   : ∀ x, e.state.getAccount x = h.state.getAccount x
  storage   : ∀ x k, e.state.getStorage x k = h.state.getStorage x k
  destroyed : ∀ x, e.selfDestructSet.contains x = h.destroyed.contains x
  touched   : ∀ x, e.touched.contains x = h.touched.contains x
  accessed  : ∀ x, e.accessedAddresses.contains x = h.accessed.contains x
  created   : e.createdAccounts = h.created
  refund    : e.refundCounter = h.refund

/-- The callback's inputs: the fork ordinal (`*fork-ord*`), the executing account, the
    beneficiary. -/
def ctxOf (k : Nat) (self b : Evm.Address) : Ctx :=
  { fork := k, addr := fun x => if x = "self" then self else b }

/-- The native SELFDESTRUCT handler's own charge: GAS_ZERO to Homestead, 5000 from
    Tangerine Whistle (EIP-150). -/
def baseGas (k : Nat) : Nat := if 3 ≤ k then 5000 else 0

/-- `spec` refines to the term at fork ordinal `k`: when the opcode succeeds, its
    environment agrees with the term's state and the gas it charged is the native base
    plus what the term returns; when it fails it is out of gas, exactly when the gas left
    is below that sum. -/
def Refines (spec : Except Exception Evm) (g k : Nat) (R : HState) : Prop :=
  (∀ evm', spec = .ok evm' → Agree evm'.env R ∧ g = evm'.gasLeft + baseGas k + R.gas) ∧
  (∀ e, spec = .error e → e = .outOfGas ∧ g < baseGas k + R.gas)

/-- The term run on the frame's environment at fork ordinal `k`. -/
def runOn (k : Nat) (evm : Evm) (b : Evm.Address) : HState :=
  term.run (ctxOf k evm.message.currentTarget b) (HState.ofEnv evm.env)

/-- The Cancun-family spec: `Cancun.Vm.Effect.doSelfdestruct` (gas, warm-up, the
    beneficiary popped) yields, and the fork's yield discharge runs the effect. -/
def yieldSpec (run : Evm → Evm.Byzantium.Vm.Effect.YieldEffect →
                (Evm → Except Exception Evm) → Except Exception Evm) (evm : Evm) :
    Except Exception Evm :=
  match Evm.Cancun.Vm.Effect.doSelfdestruct evm with
  | .yield fr eff => run fr eff (fun _ => .error .outOfGas)
  | .error _ e    => .error e
  | .continue fr  => .ok fr
  | .halt fr _    => .ok fr

/-- Each fork's SELFDESTRUCT as the IR trampoline binds it (`selfdestruct_binding_*`). -/
def specSelfdestruct : Evm.Fork → Evm → Except Exception Evm
  | .frontier | .homestead | .daoFork => Evm.Frontier.Vm.selfdestruct
  | .tangerineWhistle => Evm.TangerineWhistle.Vm.selfdestruct
  | .spuriousDragon | .byzantium | .constantinople | .petersburg | .istanbul
  | .muirGlacier => Evm.SpuriousDragon.Vm.selfdestruct
  | .berlin => Evm.Berlin.Vm.Effect.doSelfdestructPure
  | .london | .arrowGlacier | .grayGlacier | .paris | .shanghai =>
      Evm.London.Vm.Effect.doSelfdestructLondon
  | .cancun    => yieldSpec (_root_.Evm.IR.Trampoline.runYieldOf .cancun)
  | .prague    => yieldSpec (_root_.Evm.IR.Trampoline.runYieldOf .prague)
  | .osaka     => yieldSpec (_root_.Evm.IR.Trampoline.runYieldOf .osaka)
  | .bpo1      => yieldSpec (_root_.Evm.IR.Trampoline.runYieldOf .bpo1)
  | .bpo2      => yieldSpec (_root_.Evm.IR.Trampoline.runYieldOf .bpo2)
  | .amsterdam => yieldSpec (_root_.Evm.IR.Trampoline.runYieldOf .amsterdam)

/-- Before Cancun `specSelfdestruct` IS the handler the IR trampoline lifts. -/
theorem selfdestruct_binding_pre (f : Evm.Fork) (h : f.atLeast .cancun = false) :
    _root_.Evm.IR.Trampoline.Terminator.handler f .selfdestruct = some (specSelfdestruct f) := by
  cases f <;> first | rfl | (simp [Evm.Fork.atLeast, Evm.Fork.ord] at h)

/-- From Cancun the IR trampoline steps SELFDESTRUCT with Cancun's `doSelfdestruct` and
    discharges its yield with the fork's `runYieldOf` — `specSelfdestruct`'s two halves. -/
theorem selfdestruct_binding_cancun :
    _root_.Evm.IR.Trampoline.Terminator.stepHandler .cancun .selfdestruct = some Evm.Cancun.Vm.Effect.doSelfdestruct := rfl
theorem selfdestruct_binding_prague :
    _root_.Evm.IR.Trampoline.Terminator.stepHandler .prague .selfdestruct = some Evm.Cancun.Vm.Effect.doSelfdestruct := rfl
theorem selfdestruct_binding_osaka :
    _root_.Evm.IR.Trampoline.Terminator.stepHandler .osaka .selfdestruct = some Evm.Cancun.Vm.Effect.doSelfdestruct := rfl
theorem selfdestruct_binding_bpo1 :
    _root_.Evm.IR.Trampoline.Terminator.stepHandler .bpo1 .selfdestruct = some Evm.Cancun.Vm.Effect.doSelfdestruct := rfl
theorem selfdestruct_binding_bpo2 :
    _root_.Evm.IR.Trampoline.Terminator.stepHandler .bpo2 .selfdestruct = some Evm.Cancun.Vm.Effect.doSelfdestruct := rfl
theorem selfdestruct_binding_amsterdam :
    _root_.Evm.IR.Trampoline.Terminator.stepHandler .amsterdam .selfdestruct = some Evm.Cancun.Vm.Effect.doSelfdestruct := rfl

/-! ### Proof automation (shared by every fork group) -/

attribute [local simp] Stmt.run BExp.eval WExp.eval AExp.eval GExp.eval ctxOf isDead baseGas
  getAccount_setAccount accountExists_setAccount getStorage_setAccount State.addBalance
  State.touchAccount Evm.CL.GasEmit.Expr.eval Evm.CL.GasEmit.selfdestructColdGas
  Evm.CL.GasEmit.newAccountFee Evm.CL.GasEmit.selfdestructRefund Evm.CL.GasEmit.fork
  Evm.TangerineWhistle.Vm.Gas.selfDestruct Evm.Frontier.Vm.Gas.newAccount
  Evm.Frontier.Vm.Gas.selfDestructRefund Evm.Berlin.Vm.Gas.coldAccountAccess
  Evm.Berlin.Vm.Effect.isAddrWarm Evm.London.Vm.Gas.selfDestructRefund
  Evm.Cancun.State.wasCreatedThisTx

set_option hygiene false in
/-- Name the inputs after the handler is unfolded: `a` (executing account), `b` (beneficiary),
    `g` (gas left), `env`; the term is unfolded on the right. -/
macro "sd_inputs" : tactic => `(tactic| (
  simp only [runOn, term, newAccount, HState.ofEnv]
  generalize evm.message.currentTarget = a at *
  generalize Evm.Address.ofNat bW.toNat = b at *
  generalize evm.gasLeft = g at *
  generalize evm.env = env at *))

set_option hygiene false in
/-- Close one simplified `Agree` field: set-membership commutation, the executing account's
    existence (`hself`), or a split on the address `x` against `a` (self) and `b`
    (beneficiary). Unhygienic: it names the proof's own hypotheses. -/
macro "sd_field" : tactic => `(tactic| first
  | (rw [Bool.or_comm]; done)
  | (intro hx; subst hx; exact hself)
  | (((repeat' split) <;> subst_vars <;> simp_all [State.getBalance, acc_eta, getAccount_absent]) <;> done)
  | ((by_cases hxa : x = a <;> by_cases hxb : x = b <;> subst_vars <;> simp_all) <;> done))

set_option hygiene false in
/-- Close a gas equation `g = g - cost + base + termGas` from `hg : cost ≤ g`. -/
macro "sd_gas" : tactic => `(tactic| first
  | ((try simp only [Nat.add_assoc] at hg ⊢)
     exact gas_close _ _ _ hg (by first | rfl | ac_rfl | omega))
  | exact hg)

set_option maxHeartbeats 4000000 in
theorem refines_frontier_ok (k : Nat) (hlo : 0 ≤ k) (hhi : k < 3) (evm : Evm) (bW : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = bW :: rest) (hstatic : evm.message.isStatic = false)
    (hself : evm.env.state.accountExists evm.message.currentTarget = true) (evm' : Evm)
    (hspec : Evm.Frontier.Vm.selfdestruct evm = .ok evm') :
    Agree evm'.env (runOn k evm (Evm.Address.ofNat bW.toNat)) ∧
      evm.gasLeft = evm'.gasLeft + baseGas k + (runOn k evm (Evm.Address.ofNat bW.toNat)).gas := by
  have hu : ∀ x, (priv% Evm.Frontier.Vm.Interpreter Evm.Frontier.Vm.u256ToAddr) x = Evm.Address.ofNat x.toNat := fun _ => rfl
  obtain ⟨hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16⟩ :
      ¬ (3 ≤ k) ∧ (k < 3) ∧ ¬ (4 ≤ k) ∧ (k < 4) ∧ ¬ (10 ≤ k) ∧ (k < 10) ∧ ¬ (11 ≤ k) ∧ (k < 11) ∧ ¬ (16 ≤ k) ∧ (k < 16) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  unfold Evm.Frontier.Vm.selfdestruct at hspec
  simp only [hu, hstack, hstatic, Stack.pop, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
    ite_false] at hspec
  sd_inputs
  simp only [Except.ok.injEq] at hspec
  subst hspec
  by_cases heq : a = b
  · subst heq
    by_cases hb0 : env.state.getBalance a = 0#256 <;>
    by_cases hds : a ∈ env.selfDestructSet <;>
    refine ⟨?_, ?_⟩
    all_goals first
      | (refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro x) <;> (try intro kk) <;> simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds] <;> sd_field)
      | (simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds])
  · skip
    by_cases hb0 : env.state.getBalance a = 0#256 <;>
    by_cases hds : a ∈ env.selfDestructSet <;>
    by_cases hex : env.state.accountExists b = true <;>
    refine ⟨?_, ?_⟩
    all_goals first
      | (refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro x) <;> (try intro kk) <;> simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, heq, Ne.symm heq] <;> sd_field)
      | (simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, heq, Ne.symm heq])

set_option maxHeartbeats 4000000 in
theorem refines_frontier_err (k : Nat) (hlo : 0 ≤ k) (hhi : k < 3) (evm : Evm) (bW : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = bW :: rest) (hstatic : evm.message.isStatic = false)
    (e : Exception) (hspec : Evm.Frontier.Vm.selfdestruct evm = .error e) :
    e = .outOfGas ∧ evm.gasLeft < baseGas k + (runOn k evm (Evm.Address.ofNat bW.toNat)).gas := by
  have hu : ∀ x, (priv% Evm.Frontier.Vm.Interpreter Evm.Frontier.Vm.u256ToAddr) x = Evm.Address.ofNat x.toNat := fun _ => rfl
  obtain ⟨hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16⟩ :
      ¬ (3 ≤ k) ∧ (k < 3) ∧ ¬ (4 ≤ k) ∧ (k < 4) ∧ ¬ (10 ≤ k) ∧ (k < 10) ∧ ¬ (11 ≤ k) ∧ (k < 11) ∧ ¬ (16 ≤ k) ∧ (k < 16) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  unfold Evm.Frontier.Vm.selfdestruct at hspec
  simp only [hu, hstack, hstatic, Stack.pop, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
    ite_false] at hspec
  simp at hspec

set_option maxHeartbeats 4000000 in
theorem refines_tangerine_ok (k : Nat) (hlo : 3 ≤ k) (hhi : k < 4) (evm : Evm) (bW : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = bW :: rest) (hstatic : evm.message.isStatic = false)
    (hself : evm.env.state.accountExists evm.message.currentTarget = true) (evm' : Evm)
    (hspec : Evm.TangerineWhistle.Vm.selfdestruct evm = .ok evm') :
    Agree evm'.env (runOn k evm (Evm.Address.ofNat bW.toNat)) ∧
      evm.gasLeft = evm'.gasLeft + baseGas k + (runOn k evm (Evm.Address.ofNat bW.toNat)).gas := by
  have hu : ∀ x, (priv% Evm.TangerineWhistle.Vm.Interpreter Evm.TangerineWhistle.Vm.u256ToAddr) x = Evm.Address.ofNat x.toNat := fun _ => rfl
  obtain ⟨hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16⟩ :
      (3 ≤ k) ∧ ¬ (k < 3) ∧ ¬ (4 ≤ k) ∧ (k < 4) ∧ ¬ (10 ≤ k) ∧ (k < 10) ∧ ¬ (11 ≤ k) ∧ (k < 11) ∧ ¬ (16 ≤ k) ∧ (k < 16) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  unfold Evm.TangerineWhistle.Vm.selfdestruct at hspec
  simp only [hu, hstack, hstatic, Stack.pop, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
    ite_false] at hspec
  sd_inputs
  split at hspec
  · simp at hspec
  · rename_i _ v hc
    simp only [Except.ok.injEq] at hspec
    subst hspec
    obtain ⟨hg, rfl⟩ := (charge_ok _ _ _).mp hc
    by_cases heq : a = b
    · subst heq
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      refine ⟨?_, ?_⟩
      all_goals first
        | (refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro x) <;> (try intro kk) <;> simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds] <;> sd_field)
        | (simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds] at hg ⊢ <;> sd_gas)
    · skip
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      by_cases hex : env.state.accountExists b = true <;>
      refine ⟨?_, ?_⟩
      all_goals first
        | (refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro x) <;> (try intro kk) <;> simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, heq, Ne.symm heq] <;> sd_field)
        | (simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, heq, Ne.symm heq] at hg ⊢ <;> sd_gas)

set_option maxHeartbeats 4000000 in
theorem refines_tangerine_err (k : Nat) (hlo : 3 ≤ k) (hhi : k < 4) (evm : Evm) (bW : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = bW :: rest) (hstatic : evm.message.isStatic = false)
    (e : Exception) (hspec : Evm.TangerineWhistle.Vm.selfdestruct evm = .error e) :
    e = .outOfGas ∧ evm.gasLeft < baseGas k + (runOn k evm (Evm.Address.ofNat bW.toNat)).gas := by
  have hu : ∀ x, (priv% Evm.TangerineWhistle.Vm.Interpreter Evm.TangerineWhistle.Vm.u256ToAddr) x = Evm.Address.ofNat x.toNat := fun _ => rfl
  obtain ⟨hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16⟩ :
      (3 ≤ k) ∧ ¬ (k < 3) ∧ ¬ (4 ≤ k) ∧ (k < 4) ∧ ¬ (10 ≤ k) ∧ (k < 10) ∧ ¬ (11 ≤ k) ∧ (k < 11) ∧ ¬ (16 ≤ k) ∧ (k < 16) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  unfold Evm.TangerineWhistle.Vm.selfdestruct at hspec
  simp only [hu, hstack, hstatic, Stack.pop, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
    ite_false] at hspec
  sd_inputs
  split at hspec
  · rename_i _ e' hc
    obtain ⟨hg, rfl⟩ := (charge_err _ _ _).mp hc
    simp only [Except.error.injEq] at hspec
    subst hspec
    refine ⟨rfl, ?_⟩
    by_cases heq : a = b
    · subst heq
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      by_cases hex : env.state.accountExists a = true <;>
      simp [hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex] at hg ⊢ <;> first | exact hg | omega
    · skip
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      by_cases hex : env.state.accountExists b = true <;>
      simp [hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, heq, Ne.symm heq] at hg ⊢ <;> first | exact hg | omega
  · simp at hspec

set_option maxHeartbeats 4000000 in
theorem refines_spurious_ok (k : Nat) (hlo : 4 ≤ k) (hhi : k < 10) (evm : Evm) (bW : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = bW :: rest) (hstatic : evm.message.isStatic = false)
    (hself : evm.env.state.accountExists evm.message.currentTarget = true) (evm' : Evm)
    (hspec : Evm.SpuriousDragon.Vm.selfdestruct evm = .ok evm') :
    Agree evm'.env (runOn k evm (Evm.Address.ofNat bW.toNat)) ∧
      evm.gasLeft = evm'.gasLeft + baseGas k + (runOn k evm (Evm.Address.ofNat bW.toNat)).gas := by
  have hu : ∀ x, (priv% Evm.SpuriousDragon.Vm.Interpreter Evm.SpuriousDragon.Vm.u256ToAddr) x = Evm.Address.ofNat x.toNat := fun _ => rfl
  have hd : ∀ s y, (priv% Evm.SpuriousDragon.Vm.Interpreter Evm.SpuriousDragon.Vm.isDead) s y = Evm.CL.EffectIR.isDead s y := fun _ _ => rfl
  obtain ⟨hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16⟩ :
      (3 ≤ k) ∧ ¬ (k < 3) ∧ (4 ≤ k) ∧ ¬ (k < 4) ∧ ¬ (10 ≤ k) ∧ (k < 10) ∧ ¬ (11 ≤ k) ∧ (k < 11) ∧ ¬ (16 ≤ k) ∧ (k < 16) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  unfold Evm.SpuriousDragon.Vm.selfdestruct at hspec
  simp only [hu, hd, hstack, hstatic, Stack.pop, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
    ite_false] at hspec
  sd_inputs
  split at hspec
  · simp at hspec
  · rename_i _ v hc
    simp only [Except.ok.injEq] at hspec
    subst hspec
    obtain ⟨hg, rfl⟩ := (charge_ok _ _ _).mp hc
    by_cases heq : a = b
    · subst heq
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      refine ⟨?_, ?_⟩
      all_goals first
        | (refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro x) <;> (try intro kk) <;> simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds] <;> sd_field)
        | (simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds] at hg ⊢ <;> sd_gas)
    · skip
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      by_cases hex : env.state.accountExists b = true <;>
      by_cases hem : (env.state.getAccount b).isEmpty = true <;>
      refine ⟨?_, ?_⟩
      all_goals first
        | (refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro x) <;> (try intro kk) <;> simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, hem, heq, Ne.symm heq] <;> sd_field)
        | (simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, hem, heq, Ne.symm heq] at hg ⊢ <;> sd_gas)

set_option maxHeartbeats 4000000 in
theorem refines_spurious_err (k : Nat) (hlo : 4 ≤ k) (hhi : k < 10) (evm : Evm) (bW : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = bW :: rest) (hstatic : evm.message.isStatic = false)
    (e : Exception) (hspec : Evm.SpuriousDragon.Vm.selfdestruct evm = .error e) :
    e = .outOfGas ∧ evm.gasLeft < baseGas k + (runOn k evm (Evm.Address.ofNat bW.toNat)).gas := by
  have hu : ∀ x, (priv% Evm.SpuriousDragon.Vm.Interpreter Evm.SpuriousDragon.Vm.u256ToAddr) x = Evm.Address.ofNat x.toNat := fun _ => rfl
  have hd : ∀ s y, (priv% Evm.SpuriousDragon.Vm.Interpreter Evm.SpuriousDragon.Vm.isDead) s y = Evm.CL.EffectIR.isDead s y := fun _ _ => rfl
  obtain ⟨hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16⟩ :
      (3 ≤ k) ∧ ¬ (k < 3) ∧ (4 ≤ k) ∧ ¬ (k < 4) ∧ ¬ (10 ≤ k) ∧ (k < 10) ∧ ¬ (11 ≤ k) ∧ (k < 11) ∧ ¬ (16 ≤ k) ∧ (k < 16) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  unfold Evm.SpuriousDragon.Vm.selfdestruct at hspec
  simp only [hu, hd, hstack, hstatic, Stack.pop, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
    ite_false] at hspec
  sd_inputs
  split at hspec
  · rename_i _ e' hc
    obtain ⟨hg, rfl⟩ := (charge_err _ _ _).mp hc
    simp only [Except.error.injEq] at hspec
    subst hspec
    refine ⟨rfl, ?_⟩
    by_cases heq : a = b
    · subst heq
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      by_cases hex : env.state.accountExists a = true <;>
      by_cases hem : (env.state.getAccount a).isEmpty = true <;>
      simp [hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, hem] at hg ⊢ <;> first | exact hg | omega
    · skip
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      by_cases hex : env.state.accountExists b = true <;>
      by_cases hem : (env.state.getAccount b).isEmpty = true <;>
      simp [hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, hem, heq, Ne.symm heq] at hg ⊢ <;> first | exact hg | omega
  · simp at hspec

set_option maxHeartbeats 4000000 in
theorem refines_berlin_ok (k : Nat) (hlo : 10 ≤ k) (hhi : k < 11) (evm : Evm) (bW : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = bW :: rest) (hstatic : evm.message.isStatic = false)
    (hself : evm.env.state.accountExists evm.message.currentTarget = true) (evm' : Evm)
    (hspec : Evm.Berlin.Vm.Effect.doSelfdestructPure evm = .ok evm') :
    Agree evm'.env (runOn k evm (Evm.Address.ofNat bW.toNat)) ∧
      evm.gasLeft = evm'.gasLeft + baseGas k + (runOn k evm (Evm.Address.ofNat bW.toNat)).gas := by
  have hd : ∀ s y, (priv% Evm.Berlin.Vm.Effect Evm.Berlin.Vm.Effect.isDead) s y = Evm.CL.EffectIR.isDead s y := fun _ _ => rfl
  have hu : ∀ x, Evm.Byzantium.Vm.Effect.u256ToAddr x = Evm.Address.ofNat x.toNat := fun _ => rfl
  obtain ⟨hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16⟩ :
      (3 ≤ k) ∧ ¬ (k < 3) ∧ (4 ≤ k) ∧ ¬ (k < 4) ∧ (10 ≤ k) ∧ ¬ (k < 10) ∧ ¬ (11 ≤ k) ∧ (k < 11) ∧ ¬ (16 ≤ k) ∧ (k < 16) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  unfold Evm.Berlin.Vm.Effect.doSelfdestructPure at hspec
  simp only [hd, hu, hstack, hstatic, Stack.pop, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
    ite_false] at hspec
  sd_inputs
  split at hspec
  · simp at hspec
  · rename_i _ v hc
    simp only [Except.ok.injEq] at hspec
    subst hspec
    obtain ⟨hg, rfl⟩ := (charge_ok _ _ _).mp hc
    by_cases heq : a = b
    · subst heq
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      by_cases hwa : a ∈ env.accessedAddresses <;>
      refine ⟨?_, ?_⟩
      all_goals first
        | (refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro x) <;> (try intro kk) <;> simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hwa] <;> sd_field)
        | (simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hwa] at hg ⊢ <;> sd_gas)
    · skip
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      by_cases hex : env.state.accountExists b = true <;>
      by_cases hem : (env.state.getAccount b).isEmpty = true <;>
      by_cases hwa : b ∈ env.accessedAddresses <;>
      refine ⟨?_, ?_⟩
      all_goals first
        | (refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro x) <;> (try intro kk) <;> simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, hem, hwa, heq, Ne.symm heq] <;> sd_field)
        | (simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, hem, hwa, heq, Ne.symm heq] at hg ⊢ <;> sd_gas)

set_option maxHeartbeats 4000000 in
theorem refines_berlin_err (k : Nat) (hlo : 10 ≤ k) (hhi : k < 11) (evm : Evm) (bW : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = bW :: rest) (hstatic : evm.message.isStatic = false)
    (e : Exception) (hspec : Evm.Berlin.Vm.Effect.doSelfdestructPure evm = .error e) :
    e = .outOfGas ∧ evm.gasLeft < baseGas k + (runOn k evm (Evm.Address.ofNat bW.toNat)).gas := by
  have hd : ∀ s y, (priv% Evm.Berlin.Vm.Effect Evm.Berlin.Vm.Effect.isDead) s y = Evm.CL.EffectIR.isDead s y := fun _ _ => rfl
  have hu : ∀ x, Evm.Byzantium.Vm.Effect.u256ToAddr x = Evm.Address.ofNat x.toNat := fun _ => rfl
  obtain ⟨hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16⟩ :
      (3 ≤ k) ∧ ¬ (k < 3) ∧ (4 ≤ k) ∧ ¬ (k < 4) ∧ (10 ≤ k) ∧ ¬ (k < 10) ∧ ¬ (11 ≤ k) ∧ (k < 11) ∧ ¬ (16 ≤ k) ∧ (k < 16) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  unfold Evm.Berlin.Vm.Effect.doSelfdestructPure at hspec
  simp only [hd, hu, hstack, hstatic, Stack.pop, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
    ite_false] at hspec
  sd_inputs
  split at hspec
  · rename_i _ e' hc
    obtain ⟨hg, rfl⟩ := (charge_err _ _ _).mp hc
    simp only [Except.error.injEq] at hspec
    subst hspec
    refine ⟨rfl, ?_⟩
    by_cases heq : a = b
    · subst heq
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      by_cases hex : env.state.accountExists a = true <;>
      by_cases hem : (env.state.getAccount a).isEmpty = true <;>
      by_cases hwa : a ∈ env.accessedAddresses <;>
      simp [hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, hem, hwa] at hg ⊢ <;> first | exact hg | omega
    · skip
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      by_cases hex : env.state.accountExists b = true <;>
      by_cases hem : (env.state.getAccount b).isEmpty = true <;>
      by_cases hwa : b ∈ env.accessedAddresses <;>
      simp [hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, hem, hwa, heq, Ne.symm heq] at hg ⊢ <;> first | exact hg | omega
  · simp at hspec

set_option maxHeartbeats 4000000 in
theorem refines_london_ok (k : Nat) (hlo : 11 ≤ k) (hhi : k < 16) (evm : Evm) (bW : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = bW :: rest) (hstatic : evm.message.isStatic = false)
    (hself : evm.env.state.accountExists evm.message.currentTarget = true) (evm' : Evm)
    (hspec : Evm.London.Vm.Effect.doSelfdestructLondon evm = .ok evm') :
    Agree evm'.env (runOn k evm (Evm.Address.ofNat bW.toNat)) ∧
      evm.gasLeft = evm'.gasLeft + baseGas k + (runOn k evm (Evm.Address.ofNat bW.toNat)).gas := by
  have hd : ∀ s y, (priv% Evm.London.Vm.Effect Evm.London.Vm.Effect.isDead) s y = Evm.CL.EffectIR.isDead s y := fun _ _ => rfl
  have hu : ∀ x, Evm.Byzantium.Vm.Effect.u256ToAddr x = Evm.Address.ofNat x.toNat := fun _ => rfl
  obtain ⟨hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16⟩ :
      (3 ≤ k) ∧ ¬ (k < 3) ∧ (4 ≤ k) ∧ ¬ (k < 4) ∧ (10 ≤ k) ∧ ¬ (k < 10) ∧ (11 ≤ k) ∧ ¬ (k < 11) ∧ ¬ (16 ≤ k) ∧ (k < 16) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  unfold Evm.London.Vm.Effect.doSelfdestructLondon at hspec
  simp only [hd, hu, hstack, hstatic, Stack.pop, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
    ite_false] at hspec
  sd_inputs
  split at hspec
  · simp at hspec
  · rename_i _ v hc
    simp only [Except.ok.injEq] at hspec
    subst hspec
    obtain ⟨hg, rfl⟩ := (charge_ok _ _ _).mp hc
    by_cases heq : a = b
    · subst heq
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      by_cases hwa : a ∈ env.accessedAddresses <;>
      refine ⟨?_, ?_⟩
      all_goals first
        | (refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro x) <;> (try intro kk) <;> simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hwa] <;> sd_field)
        | (simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hwa] at hg ⊢ <;> sd_gas)
    · skip
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      by_cases hex : env.state.accountExists b = true <;>
      by_cases hem : (env.state.getAccount b).isEmpty = true <;>
      by_cases hwa : b ∈ env.accessedAddresses <;>
      refine ⟨?_, ?_⟩
      all_goals first
        | (refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro x) <;> (try intro kk) <;> simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, hem, hwa, heq, Ne.symm heq] <;> sd_field)
        | (simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, hem, hwa, heq, Ne.symm heq] at hg ⊢ <;> sd_gas)

set_option maxHeartbeats 4000000 in
theorem refines_london_err (k : Nat) (hlo : 11 ≤ k) (hhi : k < 16) (evm : Evm) (bW : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = bW :: rest) (hstatic : evm.message.isStatic = false)
    (e : Exception) (hspec : Evm.London.Vm.Effect.doSelfdestructLondon evm = .error e) :
    e = .outOfGas ∧ evm.gasLeft < baseGas k + (runOn k evm (Evm.Address.ofNat bW.toNat)).gas := by
  have hd : ∀ s y, (priv% Evm.London.Vm.Effect Evm.London.Vm.Effect.isDead) s y = Evm.CL.EffectIR.isDead s y := fun _ _ => rfl
  have hu : ∀ x, Evm.Byzantium.Vm.Effect.u256ToAddr x = Evm.Address.ofNat x.toNat := fun _ => rfl
  obtain ⟨hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16⟩ :
      (3 ≤ k) ∧ ¬ (k < 3) ∧ (4 ≤ k) ∧ ¬ (k < 4) ∧ (10 ≤ k) ∧ ¬ (k < 10) ∧ (11 ≤ k) ∧ ¬ (k < 11) ∧ ¬ (16 ≤ k) ∧ (k < 16) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  unfold Evm.London.Vm.Effect.doSelfdestructLondon at hspec
  simp only [hd, hu, hstack, hstatic, Stack.pop, bind, Except.bind, pure, Except.pure, Bool.false_eq_true,
    ite_false] at hspec
  sd_inputs
  split at hspec
  · rename_i _ e' hc
    obtain ⟨hg, rfl⟩ := (charge_err _ _ _).mp hc
    simp only [Except.error.injEq] at hspec
    subst hspec
    refine ⟨rfl, ?_⟩
    by_cases heq : a = b
    · subst heq
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      by_cases hex : env.state.accountExists a = true <;>
      by_cases hem : (env.state.getAccount a).isEmpty = true <;>
      by_cases hwa : a ∈ env.accessedAddresses <;>
      simp [hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, hem, hwa] at hg ⊢ <;> first | exact hg | omega
    · skip
      by_cases hb0 : env.state.getBalance a = 0#256 <;>
      by_cases hds : a ∈ env.selfDestructSet <;>
      by_cases hex : env.state.accountExists b = true <;>
      by_cases hem : (env.state.getAccount b).isEmpty = true <;>
      by_cases hwa : b ∈ env.accessedAddresses <;>
      simp [hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hex, hem, hwa, heq, Ne.symm heq] at hg ⊢ <;> first | exact hg | omega
  · simp at hspec

/-- What the Cancun-family yield discharge does with a SELFDESTRUCT yield. -/
def DischargesEIP6780 (run : Evm → Evm.Byzantium.Vm.Effect.YieldEffect →
    (Evm → Except Exception Evm) → Except Exception Evm) : Prop :=
  ∀ fr b rs, run fr (.selfdestruct b) rs = Evm.Cancun.Vm.Effect.selfdestructEIP6780 fr b

set_option maxHeartbeats 4000000 in
theorem refines_cancun_ok (k : Nat) (hlo : 16 ≤ k) (evm : Evm) (bW : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = bW :: rest) (hstatic : evm.message.isStatic = false)
    (hself : evm.env.state.accountExists evm.message.currentTarget = true) (evm' : Evm)
    (run : Evm → Evm.Byzantium.Vm.Effect.YieldEffect → (Evm → Except Exception Evm) → Except Exception Evm)
    (hrun : DischargesEIP6780 run) (hspec : yieldSpec run evm = .ok evm') :
    Agree evm'.env (runOn k evm (Evm.Address.ofNat bW.toNat)) ∧
      evm.gasLeft = evm'.gasLeft + baseGas k + (runOn k evm (Evm.Address.ofNat bW.toNat)).gas := by
  have hu : ∀ x, Evm.Cancun.Vm.Effect.u256ToAddrL x = Evm.Address.ofNat x.toNat := fun _ => rfl
  obtain ⟨hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16⟩ :
      3 ≤ k ∧ ¬ k < 3 ∧ 4 ≤ k ∧ ¬ k < 4 ∧ 10 ≤ k ∧ ¬ k < 10 ∧ 11 ≤ k ∧ ¬ k < 11 ∧ 16 ≤ k ∧ ¬ k < 16 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  unfold yieldSpec Evm.Cancun.Vm.Effect.doSelfdestruct at hspec
  simp only [hu, hstack, hstatic, Stack.pop, Bool.false_eq_true, ite_false] at hspec
  split at hspec
  · rename_i fr eff hy
    split at hy
    · simp at hy
    · rename_i gl hc
      simp only [Evm.Byzantium.Vm.Effect.StepResult.yield.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      rw [hrun] at hspec
      obtain ⟨hg, rfl⟩ := (charge_ok _ _ _).mp hc
      unfold Evm.Cancun.Vm.Effect.selfdestructEIP6780 at hspec
      simp only [hstatic, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, ite_false,
        Except.ok.injEq] at hspec
      subst hspec
      sd_inputs
      by_cases heq : a = b
      · subst heq
        by_cases hb0 : env.state.getBalance a = 0#256 <;>
        by_cases hds : a ∈ env.selfDestructSet <;>
        by_cases hcr : a ∈ env.createdAccounts <;>
        by_cases hwa : a ∈ env.accessedAddresses <;>
        refine ⟨?_, ?_⟩
        all_goals first
          | (refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro x) <;> (try intro kk) <;> simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hcr, hwa] <;> sd_field)
          | (simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hcr, hwa] at hg ⊢ <;> sd_gas)
      · skip
        by_cases hb0 : env.state.getBalance a = 0#256 <;>
        by_cases hds : a ∈ env.selfDestructSet <;>
        by_cases hcr : a ∈ env.createdAccounts <;>
        by_cases hex : env.state.accountExists b = true <;>
        by_cases hem : (env.state.getAccount b).isEmpty = true <;>
        by_cases hwa : b ∈ env.accessedAddresses <;>
        refine ⟨?_, ?_⟩
        all_goals first
          | (refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> (try intro x) <;> (try intro kk) <;> simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hcr, hex, hem, hwa, heq, Ne.symm heq] <;> sd_field)
          | (simp [hself, hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hcr, hex, hem, hwa, heq, Ne.symm heq] at hg ⊢ <;> sd_gas)
  all_goals first
    | (simp at hspec; done)
    | (rename_i hy; split at hy <;> simp at hy)

set_option maxHeartbeats 4000000 in
theorem refines_cancun_err (k : Nat) (hlo : 16 ≤ k) (evm : Evm) (bW : Evm.U256)
    (rest : List Evm.U256) (hstack : evm.stack = bW :: rest) (hstatic : evm.message.isStatic = false)
    (run : Evm → Evm.Byzantium.Vm.Effect.YieldEffect → (Evm → Except Exception Evm) → Except Exception Evm)
    (hrun : DischargesEIP6780 run) (e : Exception) (hspec : yieldSpec run evm = .error e) :
    e = .outOfGas ∧ evm.gasLeft < baseGas k + (runOn k evm (Evm.Address.ofNat bW.toNat)).gas := by
  have hu : ∀ x, Evm.Cancun.Vm.Effect.u256ToAddrL x = Evm.Address.ofNat x.toNat := fun _ => rfl
  obtain ⟨hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16⟩ :
      3 ≤ k ∧ ¬ k < 3 ∧ 4 ≤ k ∧ ¬ k < 4 ∧ 10 ≤ k ∧ ¬ k < 10 ∧ 11 ≤ k ∧ ¬ k < 11 ∧ 16 ≤ k ∧ ¬ k < 16 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  unfold yieldSpec Evm.Cancun.Vm.Effect.doSelfdestruct at hspec
  simp only [hu, hstack, hstatic, Stack.pop, Bool.false_eq_true, ite_false] at hspec
  sd_inputs
  split at hspec
  · rename_i fr eff hy
    split at hy
    · simp at hy
    · rename_i gl hc
      simp only [Evm.Byzantium.Vm.Effect.StepResult.yield.injEq] at hy
      obtain ⟨rfl, rfl⟩ := hy
      rw [hrun] at hspec
      unfold Evm.Cancun.Vm.Effect.selfdestructEIP6780 at hspec
      simp [hstatic, bind, Except.bind, pure, Except.pure] at hspec
  · rename_i fr e' hy
    split at hy
    · rename_i e'' hc
      simp only [Evm.Byzantium.Vm.Effect.StepResult.error.injEq] at hy
      obtain ⟨-, rfl⟩ := hy
      obtain ⟨hg, rfl⟩ := (charge_err _ _ _).mp hc
      simp only [Except.error.injEq] at hspec
      subst hspec
      refine ⟨rfl, ?_⟩
      by_cases heq : a = b
      · subst heq
        by_cases hb0 : env.state.getBalance a = 0#256 <;>
        by_cases hds : a ∈ env.selfDestructSet <;>
        by_cases hcr : a ∈ env.createdAccounts <;>
        by_cases hex : env.state.accountExists a = true <;>
        by_cases hem : (env.state.getAccount a).isEmpty = true <;>
        by_cases hwa : a ∈ env.accessedAddresses <;>
        simp [hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hcr, hex, hem, hwa] at hg ⊢ <;> first | exact hg | omega
      · skip
        by_cases hb0 : env.state.getBalance a = 0#256 <;>
        by_cases hds : a ∈ env.selfDestructSet <;>
        by_cases hcr : a ∈ env.createdAccounts <;>
        by_cases hex : env.state.accountExists b = true <;>
        by_cases hem : (env.state.getAccount b).isEmpty = true <;>
        by_cases hwa : b ∈ env.accessedAddresses <;>
        simp [hk3, hl3, hk4, hl4, hk10, hl10, hk11, hl11, hk16, hl16, hb0, hds, hcr, hex, hem, hwa, heq, Ne.symm heq] at hg ⊢ <;> first | exact hg | omega
    · simp at hy
  · rename_i _ hy; split at hy <;> simp at hy
  · rename_i _ _ hy; split at hy <;> simp at hy

/-- The derived `cb-selfdestruct` IS each fork's SELFDESTRUCT. For every fork `f` and every
    frame with the beneficiary word on its stack, outside a static context (EIP-214 is the
    native handler's), executing at an existing account: the spec's SELFDESTRUCT as the IR
    trampoline binds it (`specSelfdestruct f`, `selfdestruct_binding_*`) succeeds exactly
    when the gas left covers the native base plus the gas the term returns, and then its
    environment agrees with the term's state; otherwise it runs out of gas. -/
theorem selfdestruct_refines (f : Evm.Fork) (evm : Evm) (bW : Evm.U256) (rest : List Evm.U256)
    (hstack : evm.stack = bW :: rest) (hstatic : evm.message.isStatic = false)
    (hself : evm.env.state.accountExists evm.message.currentTarget = true) :
    Refines (specSelfdestruct f evm) evm.gasLeft f.ord (runOn f.ord evm (Evm.Address.ofNat bW.toNat)) := by
  cases f with
  | frontier =>
    exact ⟨fun evm' h => refines_frontier_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_frontier_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | homestead =>
    exact ⟨fun evm' h => refines_frontier_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_frontier_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | daoFork =>
    exact ⟨fun evm' h => refines_frontier_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_frontier_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | tangerineWhistle =>
    exact ⟨fun evm' h => refines_tangerine_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_tangerine_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | spuriousDragon =>
    exact ⟨fun evm' h => refines_spurious_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_spurious_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | byzantium =>
    exact ⟨fun evm' h => refines_spurious_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_spurious_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | constantinople =>
    exact ⟨fun evm' h => refines_spurious_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_spurious_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | petersburg =>
    exact ⟨fun evm' h => refines_spurious_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_spurious_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | istanbul =>
    exact ⟨fun evm' h => refines_spurious_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_spurious_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | muirGlacier =>
    exact ⟨fun evm' h => refines_spurious_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_spurious_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | berlin =>
    exact ⟨fun evm' h => refines_berlin_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_berlin_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | london =>
    exact ⟨fun evm' h => refines_london_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_london_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | arrowGlacier =>
    exact ⟨fun evm' h => refines_london_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_london_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | grayGlacier =>
    exact ⟨fun evm' h => refines_london_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_london_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | paris =>
    exact ⟨fun evm' h => refines_london_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_london_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | shanghai =>
    exact ⟨fun evm' h => refines_london_ok _ (by decide) (by decide) evm bW rest hstack hstatic hself evm' h,
           fun e h => refines_london_err _ (by decide) (by decide) evm bW rest hstack hstatic e h⟩
  | cancun =>
    exact ⟨fun evm' h => refines_cancun_ok _ (by decide) evm bW rest hstack hstatic hself evm' _ (fun _ _ _ => rfl) h,
           fun e h => refines_cancun_err _ (by decide) evm bW rest hstack hstatic _ (fun _ _ _ => rfl) e h⟩
  | prague =>
    exact ⟨fun evm' h => refines_cancun_ok _ (by decide) evm bW rest hstack hstatic hself evm' _ (fun _ _ _ => rfl) h,
           fun e h => refines_cancun_err _ (by decide) evm bW rest hstack hstatic _ (fun _ _ _ => rfl) e h⟩
  | osaka =>
    exact ⟨fun evm' h => refines_cancun_ok _ (by decide) evm bW rest hstack hstatic hself evm' _ (fun _ _ _ => rfl) h,
           fun e h => refines_cancun_err _ (by decide) evm bW rest hstack hstatic _ (fun _ _ _ => rfl) e h⟩
  | bpo1 =>
    exact ⟨fun evm' h => refines_cancun_ok _ (by decide) evm bW rest hstack hstatic hself evm' _ (fun _ _ _ => rfl) h,
           fun e h => refines_cancun_err _ (by decide) evm bW rest hstack hstatic _ (fun _ _ _ => rfl) e h⟩
  | bpo2 =>
    exact ⟨fun evm' h => refines_cancun_ok _ (by decide) evm bW rest hstack hstatic hself evm' _ (fun _ _ _ => rfl) h,
           fun e h => refines_cancun_err _ (by decide) evm bW rest hstack hstatic _ (fun _ _ _ => rfl) e h⟩
  | amsterdam =>
    exact ⟨fun evm' h => refines_cancun_ok _ (by decide) evm bW rest hstack hstatic hself evm' _ (fun _ _ _ => rfl) h,
           fun e h => refines_cancun_err _ (by decide) evm bW rest hstack hstatic _ (fun _ _ _ => rfl) e h⟩

end Evm.CL.EffectSelfdestruct
