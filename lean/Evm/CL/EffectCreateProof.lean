import Evm.CL.EffectCreate
import Evm.IR.Trampoline

/-! # CL/EffectCreateProof — `EffectCreate.term` IS every fork's CREATE

`create_refines`: for every fork ordinal `k`, the derived callback and the spec's CREATE
after the memory charge (`Evm.Frontier.Vm.Create.run`, which every fork's
`doCreate`/`doCreate2` and `.createLike` arm are — `create_binding`) agree, for ANY child
run `runSub` (the init code's execution — the spec's trampoline, the replay's native
interpreter): the callback runs the child on exactly the frame the spec builds (same
message, same environment), and given the same child result

* if the spec's CREATE succeeds, its environment agrees with the term's state — the world
  state, the destroyed / touched / accessed / created sets, the refund counter, the
  accessed slots and the original-value cache, all EQUAL (not just extensionally) —, the
  gas it charged is the term's, it pushed the term's word and its return data is the
  term's;
* if it fails, it is out of gas, exactly when the gas left is below the term's charge.

Assumptions, stated: the child never ends with more gas than it was given (`hmono`); the
creator's stack has room for the result (`hlen`; the operands were just popped). Arc's chain
veto is outside the theorem (its meaning is "no veto"). -/

set_option linter.unusedSimpArgs false

namespace Evm.CL.EffectCreate

open Evm.CL.EffectIR
open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Environment Evm Stack Exception Message)
open Evm.Frontier.Vm.Create

/-- The environment the term's state stands for, over the creator's `e`. -/
def envOf (e : Environment) (h : HState) : Environment :=
  { e with state := h.state, selfDestructSet := h.destroyed, touched := h.touched,
           accessedAddresses := h.accessed, createdAccounts := h.created,
           refundCounter := h.refund, accessedStorageKeys := h.slots, storageOriginals := h.origs }

/-- The child run as the spec does it: `runSub` on the fresh frame of message `m` (with the
    forwarded gas) over the environment the term's state stands for. -/
def oracle (runSub : Evm → Except Exception Evm) (e : Environment) (m : Message) :
    HState → Nat → ChildRes := fun h fwd =>
  match runSub (Evm.fresh { m with gas := fwd }
      { envOf e h with originalState := e.originalState.destroyStorage m.currentTarget }) with
  | .error _ => .err
  | .ok sub  => .ok (HState.ofEnv sub.env) sub.gasLeft sub.output sub.reverted

/-- The init message (its gas is the forwarded gas, supplied at the run). -/
def msgOf (evm : Evm) (value : Evm.U256) (initCode : Evm.Bytes) (newAddr : Evm.Address) : Message :=
  { caller := evm.message.currentTarget, target := none, currentTarget := newAddr, value := value,
    data := Evm.Bytes.empty, code := initCode, gas := 0, depth := evm.message.depth + 1 }

/-- The callback's inputs as the wrapper computes them. -/
def ctxOf (k : Nat) (evm : Evm) (value : Evm.U256) (initCode : Evm.Bytes) (newAddr : Evm.Address)
    (base : Nat) (runSub : Evm → Except Exception Evm) : Ctx :=
  { fork := k
    addr := fun x => if x = "new" then newAddr else evm.message.currentTarget
    word := fun _ => value
    bool := fun x => if x = "deep" then decide (evm.message.depth ≥ maxDepth)
                     else if x = "oversize" then decide (k ≥ 15 ∧ initCode.size > maxInitCodeSize)
                     else false
    nat  := fun x => if x = "gas" then evm.gasLeft else base
    child := oracle runSub evm.env (msgOf evm value initCode newAddr) }

/-- The spec environment and the term's state agree on everything an effect can change. -/
structure Agree (e : Environment) (h : HState) : Prop where
  state     : e.state = h.state
  destroyed : e.selfDestructSet = h.destroyed
  touched   : e.touched = h.touched
  accessed  : e.accessedAddresses = h.accessed
  created   : e.createdAccounts = h.created
  refund    : e.refundCounter = h.refund
  slots     : e.accessedStorageKeys = h.slots
  origs     : e.storageOriginals = h.origs

theorem agree_ofEnv (e : Environment) (h : HState) (hh : HState.ofEnv e = h) : Agree e h := by
  subst hh; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def Refines (evm : Evm) (spec : Except Exception Evm) (R : HState) : Prop :=
  (∀ evm', spec = .ok evm' → Agree evm'.env R ∧ evm.gasLeft = evm'.gasLeft + R.gas ∧
      evm'.stack = R.out :: evm.stack ∧ evm'.returnData = R.rdata) ∧
  (∀ e, spec = .error e → e = .outOfGas ∧ evm.gasLeft < R.gas)

/-! ## Arithmetic of the gas formulas -/

theorem retain_eval (k g : Nat) :
    GasEmit.retain63of64.eval (fun y => if y = "gas" then g else if y = "fork-ord" then k else 0)
      = if k ≥ 3 then g - g / 64 else g := by
  simp only [GasEmit.retain63of64, GasEmit.fork, GasEmit.Expr.eval]
  by_cases h : k < 3
  · simp [h]; (try omega)
  · simp [h]; (try omega)

theorem deposit_eval (n : Nat) :
    GasEmit.codeDepositGas.eval (fun y => if y = "nbytes" then n else 0) = Evm.Frontier.Vm.Gas.codeDeposit * n := by
  simp [GasEmit.codeDepositGas, GasEmit.Expr.eval, Evm.Frontier.Vm.Gas.codeDeposit]

theorem push_ok (e : Evm) (w : Evm.U256) (h : e.stack.length < Evm.Frontier.Vm.stackLimit) :
    Evm.Frontier.Vm.Create.push e w = .ok { e with stack := w :: e.stack, pc := e.pc + 1 } := by
  unfold Evm.Frontier.Vm.Create.push Stack.push
  simp [Nat.not_le.mpr h, bind, Except.bind, pure, Except.pure]

end Evm.CL.EffectCreate

open Evm.CL.EffectIR Evm.Frontier.Vm.Create
open Evm.Frontier.Vm (Environment Evm Stack Exception Message)

namespace Evm.CL.EffectCreate

/-- The forwarded gas the term computes in context `c`. -/
def fwdv (c : Ctx) : Nat :=
  let g := c.nat "gas" - c.nat "base"
  if c.fork ≥ 3 then g - g / 64 else g

theorem fwd_eval (c : Ctx) (h : HState) : fwd.eval c h = fwdv c := by
  simp only [fwd, GExp.eval, fwdv]
  exact retain_eval c.fork (c.nat "gas" - c.nat "base")

theorem fail_run (c : Ctx) (h : HState) :
    fail.run c h = { (c.snaps "snap") with gas := h.gas + (c.nat "base" + fwdv c), out := 0, rdata := h.rdata } := by
  simp [fail, Stmt.run, GExp.eval, WExp.eval, fwd_eval]

theorem succeed_run (c : Ctx) (h : HState) :
    succeed.run c h =
      { h with state := h.state.setAccount (c.addr "new") { (h.state.getAccount (c.addr "new")) with code := (c.res "r").out },
               gas := h.gas + (c.nat "base" + ((fwdv c - (c.res "r").gas) + Evm.Frontier.Vm.Gas.codeDeposit * (c.res "r").out.size)),
               out := Evm.U256.ofNat (c.addr "new").toNat } := by
  simp [succeed, Stmt.run, GExp.eval, WExp.eval, AExp.eval, fwd_eval, deposit, deposit_eval]

def failSt (c : Ctx) (h : HState) : HState :=
  { (c.snaps "snap") with gas := h.gas + (c.nat "base" + fwdv c), out := 0, rdata := h.rdata }

def finishClosed (c : Ctx) (h : HState) : HState :=
  match c.res "r" with
  | .err => failSt c h
  | .ok _ g o true => { (c.snaps "snap") with gas := h.gas + (c.nat "base" + (fwdv c - g)), out := 0, rdata := o }
  | .ok _ g o false =>
    if c.fork ≥ 11 ∧ 0 < o.size ∧ o.get! 0 = (0xEF : UInt8) then failSt c h
    else if g < Evm.Frontier.Vm.Gas.codeDeposit * o.size then
      (if c.fork ≥ 1 then failSt c h
       else { h with gas := h.gas + (c.nat "base" + (fwdv c - g)), out := Evm.U256.ofNat (c.addr "new").toNat })
    else if c.fork ≥ 4 ∧ Evm.SpuriousDragon.Vm.Gas.maxCodeSize < o.size then failSt c h
    else { h with state := h.state.setAccount (c.addr "new") { (h.state.getAccount (c.addr "new")) with code := o },
                     gas := h.gas + (c.nat "base" + ((fwdv c - g) + Evm.Frontier.Vm.Gas.codeDeposit * o.size)),
                  out := Evm.U256.ofNat (c.addr "new").toNat }

set_option maxHeartbeats 4000000 in
theorem finish_run (c : Ctx) (h : HState) : finish.run c h = finishClosed c h := by
  unfold finish finishClosed
  cases hr : c.res "r" with
  | err =>
    simp [Stmt.run, BExp.eval, hr, ChildRes.isErr, fail_run, failSt]
  | ok h' g o rv =>
    cases rv
    · simp only [Stmt.run, BExp.eval, hr, ChildRes.isErr, ChildRes.isRev, ChildRes.out, ChildRes.gas,
        GExp.eval, deposit, deposit_eval, Bool.false_eq_true, ite_false]
      by_cases hef : c.fork ≥ 11 ∧ 0 < o.size ∧ o.get! 0 = (0xEF : UInt8)
      · simp [hef, fail_run, failSt]
      · simp only [hef, ite_false]
        by_cases hd : g < Evm.Frontier.Vm.Gas.codeDeposit * o.size
        · by_cases hk1 : c.fork ≥ 1
          · simp [hd, hk1, Stmt.run, BExp.eval, GExp.eval, fail_run, failSt] <;> (try (intro a b d; exact absurd ⟨a, b, d⟩ hef))
          · simp [hd, hk1, Stmt.run, BExp.eval, GExp.eval, WExp.eval, AExp.eval, fwd_eval, hr, ChildRes.gas] <;> (try (intro a b d; exact absurd ⟨a, b, d⟩ hef))
        · by_cases hs : c.fork ≥ 4 ∧ Evm.SpuriousDragon.Vm.Gas.maxCodeSize < o.size
          · simp [hd, hs, Stmt.run, BExp.eval, GExp.eval, fail_run, failSt, hr, ChildRes.out] <;> (try (intro a b d; exact absurd ⟨a, b, d⟩ hef))
          · by_cases hk4 : c.fork ≥ 4
            · have : ¬ Evm.SpuriousDragon.Vm.Gas.maxCodeSize < o.size := fun h => hs ⟨hk4, h⟩
              simp [hd, hk4, this, Stmt.run, BExp.eval, GExp.eval, succeed_run, hr, ChildRes.out, ChildRes.gas] <;> (try (intro a b d; exact absurd ⟨a, b, d⟩ hef))
            · simp [hd, hk4, hs, Stmt.run, BExp.eval, GExp.eval, succeed_run, hr, ChildRes.out, ChildRes.gas] <;> (try (intro a b d; exact absurd ⟨a, b, d⟩ hef))
    · simp [Stmt.run, BExp.eval, hr, ChildRes.isErr, ChildRes.isRev, ChildRes.out, ChildRes.gas, GExp.eval,
        WExp.eval, fwd_eval]

end Evm.CL.EffectCreate

namespace Evm.CL.EffectCreate

/-- What the term's state is after the child run `res` from `h`. -/
def afterChild (h : HState) : ChildRes → HState
  | .err => h
  | .ok h' _ _ _ => { h' with gas := h.gas, out := h.out, rdata := h.rdata, facts := h.facts }

theorem runInit_run (c : Ctx) (h : HState) :
    runInit.run c h =
      finishClosed { c with res := fun y => if y = "r" then c.child h (fwdv c) else c.res y }
        (afterChild h (c.child h (fwdv c))) := by
  simp only [runInit, Stmt.run, fwd_eval]
  rw [finish_run]
  cases c.child h (fwdv c) <;> rfl

/-- The child's world in the term's state (from the snapshot `h`). -/
def childH (c : Ctx) (h : HState) : HState :=
  let a := c.addr "new"
  let s := c.addr "self"
  let v := c.word "value"
  let st := h.state.destroyStorage a
  let st := if c.fork ≥ 4 then st.setAccount a
              { (st.getAccount a) with nonce := (st.getAccount a).nonce + 1 } else st
  let st := st.touchAccount a
  let st := if v = 0 then st else (st.subBalance s v).addBalance a v
  { h with state := st,
           created := if h.created.contains a then h.created else a :: h.created,
           facts := if v = 0 then h.facts else h.facts ++ [(2, s, a, v)] }

set_option maxHeartbeats 4000000 in
theorem proceed_run (c : Ctx) (h : HState) :
    proceed.run c h = runInit.run c (childH c h) := by
  simp only [proceed, Stmt.run, BExp.eval, Bool.and_false, Bool.false_eq_true, ite_false]
  unfold childH
  by_cases hk : c.fork ≥ 4 <;> by_cases hv : c.word "value" = 0#256 <;>
    simp [hk, hv, transfer, Stmt.run, BExp.eval, WExp.eval, AExp.eval, Evm.Frontier.State.subBalance,
      Evm.Frontier.State.getBalance]

end Evm.CL.EffectCreate

namespace Evm.CL.EffectCreate

/-- The state after the warm-up and the creator's nonce bump. -/
def hbOf (c : Ctx) (h : HState) : HState :=
  let h1 := if c.fork ≥ 10 then { h with accessed := insertSet h.accessed (c.addr "new") } else h
  let acc := h1.state.getAccount (c.addr "self")
  { h1 with state := h1.state.setAccount (c.addr "self") { acc with nonce := acc.nonce + 1 } }

/-- The context after the warm-up and the collision test bind `cold` and `coll`. -/
def c1Of (c : Ctx) (h : HState) : Ctx :=
  { c with bool := fun y =>
      if y = "coll" then Evm.Frontier.Vm.Create.collides h.state (c.addr "new")
      else if y = "cold" then (decide (c.fork ≥ 10) && !h.accessed.contains (c.addr "new"))
      else c.bool y }

set_option maxHeartbeats 4000000 in
theorem afterWarm_run (c : Ctx) (h : HState) :
    (Stmt.warm (.forkGe 10) new "cold" (.letB "coll" (.collides new) (.seq (.bumpNonce self) afterBump))).run c h
      = afterBump.run (c1Of c h) (hbOf c h) := by
  unfold c1Of hbOf
  by_cases hk : c.fork ≥ 10
  · simp only [Stmt.run, BExp.eval, AExp.eval, hk, decide_true, ite_true, Bool.true_and]
  · simp only [Stmt.run, BExp.eval, AExp.eval, hk, decide_false, ite_false, Bool.false_eq_true, Bool.false_and]

theorem afterBump_coll (c : Ctx) (h : HState) (hc : c.bool "coll" = true) :
    afterBump.run c h = { h with gas := h.gas + (c.nat "base" + fwdv c), out := 0 } := by
  simp [afterBump, Stmt.run, BExp.eval, hc, GExp.eval, WExp.eval, fwd_eval, fwdv]

theorem afterBump_proceed (c : Ctx) (h : HState) (hc : c.bool "coll" = false) :
    afterBump.run c h = proceed.run { c with snaps := fun y => if y = "snap" then h else c.snaps y } h := by
  simp [afterBump, Stmt.run, BExp.eval, hc]

end Evm.CL.EffectCreate

namespace Evm.CL.EffectCreate

section prelude
variable (k : Nat) (evm : Evm) (value : Evm.U256) (initCode : Evm.Bytes) (newAddr : Evm.Address)
  (base : Nat) (runSub : Evm → Except Exception Evm)

theorem term_halt (hG : evm.gasLeft < base) :
    term.run (ctxOf k evm value initCode newAddr base runSub) (HState.ofEnv evm.env)
      = { HState.ofEnv evm.env with gas := base, out := 0 } := by
  simp [term, Stmt.run, GExp.eval, WExp.eval, ctxOf, hG, HState.ofEnv]

theorem term_oversize (hG : ¬ evm.gasLeft < base) (hov : k ≥ 15 ∧ initCode.size > maxInitCodeSize) :
    term.run (ctxOf k evm value initCode newAddr base runSub) (HState.ofEnv evm.env)
      = { HState.ofEnv evm.env with gas := evm.gasLeft + 1, out := 0 } := by
  simp [term, Stmt.run, GExp.eval, BExp.eval, WExp.eval, ctxOf, hG, hov, HState.ofEnv]

theorem term_failfast (hG : ¬ evm.gasLeft < base) (hov : ¬ (k ≥ 15 ∧ initCode.size > maxInitCodeSize))
    (hff : evm.message.depth ≥ maxDepth ∨
      (evm.env.state.getAccount evm.message.currentTarget).balance.toNat < value.toNat ∨
      (evm.env.state.getAccount evm.message.currentTarget).nonce = maxNonce) :
    term.run (ctxOf k evm value initCode newAddr base runSub) (HState.ofEnv evm.env)
      = { HState.ofEnv evm.env with gas := base, out := 0 } := by
  have hov' : ¬ (15 ≤ k ∧ maxInitCodeSize < initCode.size) := hov
  rcases hff with h | h | h <;>
    simp [term, Stmt.run, GExp.eval, BExp.eval, WExp.eval, AExp.eval, ctxOf, hG, hov', h, HState.ofEnv,
      Evm.Frontier.State.getBalance]

theorem term_rest (hG : ¬ evm.gasLeft < base) (hov : ¬ (k ≥ 15 ∧ initCode.size > maxInitCodeSize))
    (hff : ¬ (evm.message.depth ≥ maxDepth ∨
      (evm.env.state.getAccount evm.message.currentTarget).balance.toNat < value.toNat ∨
      (evm.env.state.getAccount evm.message.currentTarget).nonce = maxNonce)) :
    term.run (ctxOf k evm value initCode newAddr base runSub) (HState.ofEnv evm.env)
      = afterFailFast.run (ctxOf k evm value initCode newAddr base runSub) (HState.ofEnv evm.env) := by
  have hov' : ¬ (15 ≤ k ∧ maxInitCodeSize < initCode.size) := hov
  simp only [not_or] at hff
  obtain ⟨h1, h2, h3⟩ := hff
  simp [term, Stmt.run, GExp.eval, BExp.eval, WExp.eval, AExp.eval, ctxOf, hG, hov', HState.ofEnv,
    Evm.Frontier.State.getBalance, h1, h2, h3]

end prelude

end Evm.CL.EffectCreate

namespace Evm.CL.EffectCreate

section spec
variable (k : Nat) (evm : Evm) (value : Evm.U256) (initCode : Evm.Bytes) (newAddr : Evm.Address)
  (base : Nat)

/-- The spec's forwarded gas. -/
def fwdOf : Nat := let g := evm.gasLeft - base; if k ≥ 3 then g - g / 64 else g

/-- The creator's environment once the address is warm and its nonce bumped. -/
def env2Of : Environment :=
  let env1 := if k ≥ 10 then Evm.Frontier.Vm.Create.warm evm.env newAddr else evm.env
  let acc := evm.env.state.getAccount evm.message.currentTarget
  { env1 with state := env1.state.setAccount evm.message.currentTarget { acc with nonce := acc.nonce + 1 } }

/-- The creator as it waits for the child. -/
def e2Of : Evm :=
  { evm with gasLeft := (evm.gasLeft - base) - fwdOf k evm base, returnData := Evm.Bytes.empty,
             env := env2Of k evm newAddr }

theorem start_halt (hG : evm.gasLeft < base) :
    start (Rules.ofOrd k) evm value initCode newAddr base = .halt := by
  simp [start, hG]

theorem start_oversize (hG : ¬ evm.gasLeft < base) (hov : k ≥ 15 ∧ initCode.size > maxInitCodeSize) :
    start (Rules.ofOrd k) evm value initCode newAddr base = .halt := by
  simp [start, hG, Rules.ofOrd, hov.1, hov.2]

theorem start_failfast (hG : ¬ evm.gasLeft < base) (hov : ¬ (k ≥ 15 ∧ initCode.size > maxInitCodeSize))
    (hff : evm.message.depth ≥ maxDepth ∨
      (evm.env.state.getAccount evm.message.currentTarget).balance.toNat < value.toNat ∨
      (evm.env.state.getAccount evm.message.currentTarget).nonce = maxNonce) :
    start (Rules.ofOrd k) evm value initCode newAddr base
      = .done { evm with gasLeft := evm.gasLeft - base, returnData := Evm.Bytes.empty } := by
  have hov' : ¬ ((Rules.ofOrd k).eip3860 = true ∧ initCode.size > maxInitCodeSize) := by
    simpa [Rules.ofOrd] using hov
  simp only [start, hG, hov', ite_false, hff, ite_true]

theorem start_coll (hG : ¬ evm.gasLeft < base) (hov : ¬ (k ≥ 15 ∧ initCode.size > maxInitCodeSize))
    (hff : ¬ (evm.message.depth ≥ maxDepth ∨
      (evm.env.state.getAccount evm.message.currentTarget).balance.toNat < value.toNat ∨
      (evm.env.state.getAccount evm.message.currentTarget).nonce = maxNonce))
    (hcol : collides evm.env.state newAddr = true) :
    start (Rules.ofOrd k) evm value initCode newAddr base = .done (e2Of k evm newAddr base) := by
  have hov' : ¬ ((Rules.ofOrd k).eip3860 = true ∧ initCode.size > maxInitCodeSize) := by
    simpa [Rules.ofOrd] using hov
  simp only [start, hG, hov', ite_false, hff, hcol, ite_true, e2Of, env2Of, fwdOf, Rules.ofOrd]
  have hov2 : 15 ≤ k → initCode.size ≤ maxInitCodeSize := fun h => Nat.le_of_not_lt (fun h' => hov ⟨h, h'⟩)
  by_cases h10 : k ≥ 10 <;> by_cases h3 : k ≥ 3 <;> simp [h10, h3] <;> exact hov2

/-- The message the child runs with. -/
def msgFwd : Message := { msgOf evm value initCode newAddr with gas := fwdOf k evm base }

theorem start_run (hG : ¬ evm.gasLeft < base) (hov : ¬ (k ≥ 15 ∧ initCode.size > maxInitCodeSize))
    (hff : ¬ (evm.message.depth ≥ maxDepth ∨
      (evm.env.state.getAccount evm.message.currentTarget).balance.toNat < value.toNat ∨
      (evm.env.state.getAccount evm.message.currentTarget).nonce = maxNonce))
    (hcol : collides evm.env.state newAddr = false) :
    start (Rules.ofOrd k) evm value initCode newAddr base
      = .run (e2Of k evm newAddr base) (msgFwd k evm value initCode newAddr base)
          (childState (Rules.ofOrd k) (env2Of k evm newAddr).state evm.message.currentTarget newAddr value) := by
  have hov' : ¬ ((Rules.ofOrd k).eip3860 = true ∧ initCode.size > maxInitCodeSize) := by
    simpa [Rules.ofOrd] using hov
  simp only [start, hG, hov', ite_false, hff, hcol, e2Of, env2Of, fwdOf, msgFwd, msgOf, Rules.ofOrd,
    Bool.false_eq_true]
  have hov2 : 15 ≤ k → initCode.size ≤ maxInitCodeSize := fun h => Nat.le_of_not_lt (fun h' => hov ⟨h, h'⟩)
  by_cases h10 : k ≥ 10 <;> by_cases h3 : k ≥ 3 <;> simp [h10, h3] <;> exact hov2

end spec

end Evm.CL.EffectCreate

namespace Evm.CL.EffectCreate

theorem warm_eq (e : Environment) (a : Evm.Address) :
    Evm.Frontier.Vm.Create.warm e a = { e with accessedAddresses := insertSet e.accessedAddresses a } := by
  unfold Evm.Frontier.Vm.Create.warm insertSet
  split <;> simp_all

set_option maxHeartbeats 8000000 in
theorem frame_eq (k : Nat) (evm : Evm) (value : Evm.U256) (initCode : Evm.Bytes) (newAddr : Evm.Address)
    (base : Nat) (c c' : Ctx)
    (hk : c.fork = k) (hn : c.addr "new" = newAddr) (hs : c.addr "self" = evm.message.currentTarget)
    (_hv : c.word "value" = value) (_hg : c.nat "gas" = evm.gasLeft) (_hb : c.nat "base" = base)
    (hk' : c'.fork = k) (hn' : c'.addr "new" = newAddr) (hs' : c'.addr "self" = evm.message.currentTarget)
    (hv' : c'.word "value" = value) (hg' : c'.nat "gas" = evm.gasLeft) (hb' : c'.nat "base" = base) :
    Evm.fresh { msgOf evm value initCode newAddr with gas := fwdv c' }
        { envOf evm.env (childH c' (hbOf c (HState.ofEnv evm.env))) with
            originalState := evm.env.originalState.destroyStorage newAddr }
      = Evm.Frontier.Vm.Create.child (e2Of k evm newAddr base) (msgFwd k evm value initCode newAddr base)
          (childState (Rules.ofOrd k) (env2Of k evm newAddr).state evm.message.currentTarget newAddr value) := by
  have hf : fwdv c' = fwdOf k evm base := by simp [fwdv, fwdOf, hk', hg', hb']
  unfold Evm.Frontier.Vm.Create.child
  rw [hf]
  congr 1
  simp only [envOf, childH, hbOf, HState.ofEnv, e2Of, env2Of, msgFwd, msgOf, hk, hn, hs, hk', hn', hs', hv',
    childState, Rules.ofOrd, warm_eq]
  by_cases h10 : k ≥ 10 <;> by_cases h4 : k ≥ 4 <;> by_cases h0 : value = 0 <;> simp [h10, h4, h0]

end Evm.CL.EffectCreate

namespace Evm.CL.EffectCreate

theorem refines_ok (evm evm' : Evm) (R : HState)
    (hA : Agree evm'.env R) (hg : evm.gasLeft = evm'.gasLeft + R.gas) (hs : evm'.stack = R.out :: evm.stack)
    (hr : evm'.returnData = R.rdata) : Refines evm (.ok evm') R :=
  ⟨fun e h => by cases h; exact ⟨hA, hg, hs, hr⟩, fun e h => by cases h⟩

theorem refines_err (evm : Evm) (R : HState) (hg : evm.gasLeft < R.gas) :
    Refines evm (.error .outOfGas) R := by
  refine ⟨fun e h => ?_, fun e h => ?_⟩
  · cases h
  · cases h; exact ⟨rfl, hg⟩

@[simp] theorem hbOf_gas (c : Ctx) (h : HState) : (hbOf c h).gas = h.gas := by
  unfold hbOf; split <;> rfl
@[simp] theorem hbOf_out (c : Ctx) (h : HState) : (hbOf c h).out = h.out := by
  unfold hbOf; split <;> rfl
@[simp] theorem hbOf_rdata (c : Ctx) (h : HState) : (hbOf c h).rdata = h.rdata := by
  unfold hbOf; split <;> rfl
@[simp] theorem ofEnv_gas (e : Environment) : (HState.ofEnv e).gas = 0 := rfl
@[simp] theorem ofEnv_out (e : Environment) : (HState.ofEnv e).out = 0 := rfl
@[simp] theorem ofEnv_rdata (e : Environment) : (HState.ofEnv e).rdata = Evm.Bytes.empty := rfl

theorem fwdOf_le (k : Nat) (evm : Evm) (base : Nat) : fwdOf k evm base ≤ evm.gasLeft - base := by
  unfold fwdOf; simp only; split <;> omega

theorem fwdv_ctx (k : Nat) (evm : Evm) (base : Nat) (c : Ctx) (hk : c.fork = k)
    (hg : c.nat "gas" = evm.gasLeft) (hb : c.nat "base" = base) : fwdv c = fwdOf k evm base := by
  simp [fwdv, fwdOf, hk, hg, hb]

theorem agree_hb (k : Nat) (evm : Evm) (newAddr : Evm.Address) (_base : Nat) (c : Ctx)
    (hk : c.fork = k) (hn : c.addr "new" = newAddr) (hs : c.addr "self" = evm.message.currentTarget)
    (g : Nat) (o : Evm.U256) (rd : Evm.Bytes) :
    Agree (env2Of k evm newAddr) { hbOf c (HState.ofEnv evm.env) with gas := g, out := o, rdata := rd } := by
  unfold env2Of hbOf
  by_cases h10 : k ≥ 10
  · rw [ite_eq_left h10, warm_eq]
    have : c.fork ≥ 10 := hk ▸ h10
    simp only [this, ite_true]
    exact ⟨by simp [HState.ofEnv, hn, hs], rfl, rfl, by simp [HState.ofEnv, hn], rfl, rfl, rfl, rfl⟩
  · rw [ite_eq_right h10]
    have : ¬ c.fork ≥ 10 := hk ▸ h10
    simp only [this, ite_false]
    exact ⟨by simp [HState.ofEnv, hs], rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Evm.CL.EffectCreate

namespace Evm.CL.EffectCreate

/-- The child result as the oracle hands it to the term. -/
def toRes : Except Exception Evm → ChildRes
  | .error _ => .err
  | .ok sub  => .ok (HState.ofEnv sub.env) sub.gasLeft sub.output sub.reverted

theorem oracle_eq (runSub : Evm → Except Exception Evm) (e : Environment) (m : Message) (h : HState) (fwd : Nat) :
    oracle runSub e m h fwd = toRes (runSub (Evm.fresh { m with gas := fwd }
      { envOf e h with originalState := e.originalState.destroyStorage m.currentTarget })) := by
  unfold oracle toRes; cases runSub _ <;> rfl

theorem arith_rev (G B F g : Nat) (h1 : B ≤ G) (h2 : F ≤ G - B) (h3 : g ≤ F) :
    G = G - B - F + g + (0 + (B + (F - g))) := by omega
theorem arith_ok (G B F g d : Nat) (h1 : B ≤ G) (h2 : F ≤ G - B) (h3 : g ≤ F) (h4 : d ≤ g) :
    G = G - B - F + (g - d) + (0 + (B + (F - g + d))) := by omega
theorem arith_err (G B F : Nat) (h1 : B ≤ G) (h2 : F ≤ G - B) :
    G = G - B - F + 0 + (0 + (B + F)) := by omega

theorem push_ite (e : Evm) (w : Evm.U256) :
    Evm.Frontier.Vm.Create.push e w =
      if e.stack.length ≥ Evm.Frontier.Vm.stackLimit then .error .stackOverflow
      else .ok { e with stack := w :: e.stack, pc := e.pc + 1 } := by
  unfold Evm.Frontier.Vm.Create.push Stack.push
  split <;> simp_all [bind, Except.bind, pure, Except.pure]

set_option maxHeartbeats 16000000 in
theorem finish_refines (k : Nat) (evm : Evm) (_value : Evm.U256) (_initCode : Evm.Bytes)
    (newAddr : Evm.Address) (base : Nat) (C c3 : Ctx) (hc : HState) (R : Except Exception Evm)
    (hlen : evm.stack.length < Evm.Frontier.Vm.stackLimit)
    (hG : base ≤ evm.gasLeft)
    (hCk : C.fork = k) (hCn : C.addr "new" = newAddr) (hCs : C.addr "self" = evm.message.currentTarget)
    (hk : c3.fork = k) (hn : c3.addr "new" = newAddr) (hg : c3.nat "gas" = evm.gasLeft)
    (hb : c3.nat "base" = base) (hsnap : c3.snaps "snap" = hbOf C (HState.ofEnv evm.env))
    (hres : c3.res "r" = toRes R)
    (hmonoR : ∀ sub, R = .ok sub → sub.gasLeft ≤ fwdOf k evm base)
    (hcg : hc.gas = 0) (hco : hc.out = 0) (hcr : hc.rdata = Evm.Bytes.empty) :
    Refines evm (resume (Rules.ofOrd k) (e2Of k evm newAddr base) newAddr R)
      (finishClosed c3 (afterChild hc (toRes R))) := by
  have hfwd := fwdOf_le k evm base
  have hF : fwdv c3 = fwdOf k evm base := fwdv_ctx k evm base c3 hk hg hb
  unfold resume finishClosed
  rw [hres]
  cases R with
  | error e =>
    simp only [toRes, afterChild, failSt, hsnap, hF, hb, hcg, hcr]
    have hl : ¬ evm.stack.length ≥ Evm.Frontier.Vm.stackLimit := Nat.not_le.mpr hlen
    simp only [push_ite, e2Of, hl, ite_false]
    refine refines_ok _ _ _ (agree_hb k evm newAddr base C hCk hCn hCs _ _ _) ?_ (by simp [e2Of]) (by simp [e2Of])
    exact arith_err _ _ _ hG hfwd
  | ok sub =>
    have hm := hmonoR sub rfl
    cases hrv : sub.reverted
    · have hl : ¬ evm.stack.length ≥ Evm.Frontier.Vm.stackLimit := Nat.not_le.mpr hlen
      simp only [toRes, hrv, Bool.false_eq_true, ite_false, afterChild, hsnap, hF, hb, hcg, hcr, hco]
      by_cases hef : k ≥ 11 ∧ 0 < sub.output.size ∧ sub.output.get! 0 = (0xEF : UInt8)
      · have hef' : (Rules.ofOrd k).eip3541 = true ∧ 0 < sub.output.size ∧ sub.output.get! 0 = (0xEF : UInt8) := by
          simpa [Rules.ofOrd] using hef
        simp only [hk, hef, hef', ite_true, failSt, hsnap, hF, hb, hcg, hcr, push_ite, e2Of, hl, ite_false]
        refine refines_ok _ _ _ (agree_hb k evm newAddr base C hCk hCn hCs _ _ _) ?_ (by simp) (by simp)
        exact arith_err _ _ _ hG hfwd
      · have hef' : ¬ ((Rules.ofOrd k).eip3541 = true ∧ 0 < sub.output.size ∧ sub.output.get! 0 = (0xEF : UInt8)) := by
          simpa [Rules.ofOrd] using hef
        simp only [hk, hef, hef', ite_false]
        by_cases hd : sub.gasLeft < Evm.Frontier.Vm.Gas.codeDeposit * sub.output.size
        · by_cases h1 : k ≥ 1
          · have h1' : (Rules.ofOrd k).homestead = true := by simp [Rules.ofOrd, h1]
            simp only [hd, h1, h1', ite_true, failSt, hsnap, hF, hb, hcg, hcr, push_ite, e2Of, hl, ite_false]
            refine refines_ok _ _ _ (agree_hb k evm newAddr base C hCk hCn hCs _ _ _) ?_ (by simp) (by simp)
            exact arith_err _ _ _ hG hfwd
          · have h1' : (Rules.ofOrd k).homestead = false := by simp [Rules.ofOrd]; omega
            simp only [hd, h1, h1', ite_true, ite_false, Bool.false_eq_true, push_ite, e2Of, hl, hb, hF, hcg, hco, hn]
            refine refines_ok _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ rfl (by simp [hcr])
            simpa using arith_rev _ _ _ _ hG hfwd hm
        · by_cases hs : k ≥ 4 ∧ Evm.SpuriousDragon.Vm.Gas.maxCodeSize < sub.output.size
          · have hs' : (Rules.ofOrd k).eip161 = true ∧ sub.output.size > Evm.SpuriousDragon.Vm.Gas.maxCodeSize := by
              simpa [Rules.ofOrd] using hs
            simp only [hd, hs, hs', ite_true, ite_false, failSt, hsnap, hF, hb, hcg, hcr, push_ite, e2Of, hl]
            refine refines_ok _ _ _ (agree_hb k evm newAddr base C hCk hCn hCs _ _ _) ?_ (by simp) (by simp)
            exact arith_err _ _ _ hG hfwd
          · have hs' : ¬ ((Rules.ofOrd k).eip161 = true ∧ sub.output.size > Evm.SpuriousDragon.Vm.Gas.maxCodeSize) := by
              simpa [Rules.ofOrd] using hs
            simp only [hd, hs, hs', ite_false, push_ite, e2Of, hl, hb, hF, hcg, hco, hn]
            refine refines_ok _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ rfl (by simp [hcr])
            simpa using arith_ok _ _ _ _ _ hG hfwd hm (Nat.le_of_not_lt hd)
    · simp only [toRes, hrv, ite_true, afterChild, hsnap, hF, hb, hcg, hcr]
      have hl : ¬ evm.stack.length ≥ Evm.Frontier.Vm.stackLimit := Nat.not_le.mpr hlen
      simp only [push_ite, e2Of, hl, ite_false]
      refine refines_ok _ _ _ (agree_hb k evm newAddr base C hCk hCn hCs _ _ _) ?_ (by simp [e2Of]) (by simp [e2Of])
      exact arith_rev _ _ _ _ hG hfwd hm

end Evm.CL.EffectCreate

namespace Evm.CL.EffectCreate

theorem arith_coll (G B F : Nat) (h1 : B ≤ G) (h2 : F ≤ G - B) : G = G - B - F + (0 + (B + F)) := by
  omega

set_option maxHeartbeats 16000000 in
/-- **The derived CREATE callback is every fork's CREATE.** -/
theorem create_refines (k : Nat) (evm : Evm) (value : Evm.U256) (initCode : Evm.Bytes)
    (newAddr : Evm.Address) (base : Nat) (runSub : Evm → Except Exception Evm)
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hlen : evm.stack.length < Evm.Frontier.Vm.stackLimit) :
    Refines evm (Evm.Frontier.Vm.Create.run (Rules.ofOrd k) evm value initCode newAddr base runSub)
      (term.run (ctxOf k evm value initCode newAddr base runSub) (HState.ofEnv evm.env)) := by
  unfold Evm.Frontier.Vm.Create.run
  by_cases hG : evm.gasLeft < base
  · rw [start_halt k evm value initCode newAddr base hG, term_halt k evm value initCode newAddr base runSub hG]
    exact refines_err _ _ hG
  by_cases hov : k ≥ 15 ∧ initCode.size > maxInitCodeSize
  · rw [start_oversize k evm value initCode newAddr base hG hov,
      term_oversize k evm value initCode newAddr base runSub hG hov]
    exact refines_err _ _ (by simp)
  by_cases hff : evm.message.depth ≥ maxDepth ∨
      (evm.env.state.getAccount evm.message.currentTarget).balance.toNat < value.toNat ∨
      (evm.env.state.getAccount evm.message.currentTarget).nonce = maxNonce
  · rw [start_failfast k evm value initCode newAddr base hG hov hff,
      term_failfast k evm value initCode newAddr base runSub hG hov hff]
    simp only
    rw [push_ok { evm with gasLeft := evm.gasLeft - base, returnData := Evm.Bytes.empty } 0 hlen]
    refine refines_ok _ _ _ ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ ?_ rfl rfl
    show evm.gasLeft = (evm.gasLeft - base) + base
    exact (Nat.sub_add_cancel (Nat.le_of_not_lt hG)).symm
  rw [term_rest k evm value initCode newAddr base runSub hG hov hff]
  rw [show afterFailFast.run (ctxOf k evm value initCode newAddr base runSub) (HState.ofEnv evm.env)
      = (Stmt.warm (.forkGe 10) new "cold" (.letB "coll" (.collides new) (.seq (.bumpNonce self) afterBump))).run
          (ctxOf k evm value initCode newAddr base runSub) (HState.ofEnv evm.env) from rfl, afterWarm_run]
  have hfwd := fwdOf_le k evm base
  cases hcol : collides evm.env.state newAddr
  · -- no collision: the child runs
    rw [start_run k evm value initCode newAddr base hG hov hff hcol]
    simp only
    have hc1 : (c1Of (ctxOf k evm value initCode newAddr base runSub) (HState.ofEnv evm.env)).bool "coll" = false := by
      simp [c1Of, ctxOf, HState.ofEnv, hcol]
    rw [afterBump_proceed _ _ hc1, proceed_run, runInit_run]
    have hor : ∀ (c' : Ctx), c'.child = (ctxOf k evm value initCode newAddr base runSub).child →
        c'.fork = k → c'.addr "new" = newAddr → c'.addr "self" = evm.message.currentTarget →
        c'.word "value" = value → c'.nat "gas" = evm.gasLeft → c'.nat "base" = base →
        c'.child (childH c' (hbOf (ctxOf k evm value initCode newAddr base runSub) (HState.ofEnv evm.env))) (fwdv c')
          = toRes (runSub (Evm.Frontier.Vm.Create.child (e2Of k evm newAddr base)
              (msgFwd k evm value initCode newAddr base)
              (childState (Rules.ofOrd k) (env2Of k evm newAddr).state evm.message.currentTarget newAddr value))) := by
      intro c' hch hk hn hs hv hg hb
      rw [hch]
      show oracle runSub evm.env (msgOf evm value initCode newAddr) _ _ = _
      rw [oracle_eq]
      congr 2
      exact frame_eq k evm value initCode newAddr base (ctxOf k evm value initCode newAddr base runSub) c' rfl
        (by simp [ctxOf]) (by simp [ctxOf]) rfl (by simp [ctxOf]) (by simp [ctxOf]) hk hn hs hv hg hb
    rw [hor _ ?h1 ?h2 ?h3 ?h4 ?h5 ?h6 ?h7]
    case h1 => rfl
    case h2 => rfl
    case h3 => simp [c1Of, ctxOf]
    case h4 => simp [c1Of, ctxOf]
    case h5 => rfl
    case h6 => simp [c1Of, ctxOf]
    case h7 => simp [c1Of, ctxOf]
    apply finish_refines k evm value initCode newAddr base (ctxOf k evm value initCode newAddr base runSub)
      _ _ _ hlen (Nat.le_of_not_lt hG) rfl (by simp [ctxOf]) (by simp [ctxOf]) rfl (by simp [c1Of, ctxOf])
      (by simp [c1Of, ctxOf]) (by simp [c1Of, ctxOf]) (by simp) (by simp)
    · intro sub hsub
      have := hmono _ sub hsub
      simpa [Evm.Frontier.Vm.Create.child, Evm.fresh, msgFwd] using this
    · simp [childH]
    · simp [childH]
    · simp [childH]
  · -- collision: the forwarded gas is lost
    rw [start_coll k evm value initCode newAddr base hG hov hff hcol]
    have hc1 : (c1Of (ctxOf k evm value initCode newAddr base runSub) (HState.ofEnv evm.env)).bool "coll" = true := by
      simp [c1Of, ctxOf, HState.ofEnv, hcol]
    rw [afterBump_coll _ _ hc1]
    simp only
    rw [push_ok (e2Of k evm newAddr base) 0 hlen]
    refine refines_ok _ _ _ (agree_hb k evm newAddr base _ rfl (by simp [ctxOf]) (by simp [ctxOf]) _ _ _) ?_ ?_ ?_
    · have : fwdv (c1Of (ctxOf k evm value initCode newAddr base runSub) (HState.ofEnv evm.env)) = fwdOf k evm base :=
        fwdv_ctx k evm base _ rfl (by simp [c1Of, ctxOf]) (by simp [c1Of, ctxOf])
      have hb : (c1Of (ctxOf k evm value initCode newAddr base runSub) (HState.ofEnv evm.env)).nat "base" = base := by
        simp [c1Of, ctxOf]
      simp only [e2Of, hbOf_gas, ofEnv_gas, hb, this]
      exact arith_coll _ _ _ (Nat.le_of_not_lt hG) hfwd
    · simp [e2Of]
    · simp [e2Of]

end Evm.CL.EffectCreate

namespace Evm.CL.EffectCreate

open Evm.IR.Trampoline in
/-- Each fork's CREATE / CREATE2 as the IR binds it, run to its end: the bound step handler
    (`Terminator.stepHandler`), and when it yields, the yield discharged by the fork's own
    `handleYield` (`runYieldOf`) with `runSub` running the child. `none`: not an opcode at
    this fork (CREATE2 before Constantinople). -/
def specCreate (f : Evm.Fork) (c : Evm.IR.CreateKind) (evm : Evm) (runSub : Evm → Except Exception Evm) :
    Option (Except Exception Evm) :=
  (Terminator.stepHandler f (.create c)).map fun h =>
    StepResultOf.cases f (h evm) Except.ok
      (fun st => StepOf.cases f st (fun fr eff => runYieldOf f fr eff runSub) (fun fr _ => .ok fr)
        (fun _ e => .error e))

/-- The opcode run to its end under one rule set: the native part, then `Create.run` — the
    callback's part, `create_refines`. -/
def fullCreate (r : Rules) (static create2 : Bool) (evm : Evm) (runSub : Evm → Except Exception Evm) :
    Except Exception Evm :=
  match native r static create2 evm with
  | .error e => .error e
  | .ok n => Evm.Frontier.Vm.Create.run r n.frame n.value n.initCode n.newAddr n.base runSub

/-- The opcode only reads these rules (`resume` reads the rest). -/
theorem start_congr (r r' : Rules) (h3 : r.eip150 = r'.eip150) (h4 : r.eip161 = r'.eip161)
    (h10 : r.eip2929 = r'.eip2929) (h15 : r.eip3860 = r'.eip3860) :
    start r = start r' := by
  funext evm value initCode newAddr base
  unfold start childState
  rw [h3, h4, h10, h15]

theorem native_congr (r r' : Rules) (h15 : r.eip3860 = r'.eip3860) : native r = native r' := by
  funext static c2 evm; unfold native baseOf; rw [h15]

theorem start_target (r : Rules) (evm : Evm) (v : Evm.U256) (ic : Evm.Bytes) (na : Evm.Address) (b : Nat)
    (p : Evm) (m : Message) (st : Evm.Frontier.State) (h : start r evm v ic na b = .run p m st) :
    m.currentTarget = na := by
  unfold start at h
  simp only at h
  revert h
  split
  · intro h; cases h
  split
  · intro h; cases h
  split
  · intro h; cases h
  split
  · intro h; cases h
  · intro h; cases h; rfl

/-- Running `opcode` with the trampoline's continuations is `fullCreate`, when the step and
    the merge read the same rules. -/
theorem opcode_full (r r' : Rules) (h3 : r.eip150 = r'.eip150) (h4 : r.eip161 = r'.eip161)
    (h10 : r.eip2929 = r'.eip2929) (h15 : r.eip3860 = r'.eip3860)
    (static create2 : Bool) (evm : Evm) (runSub : Evm → Except Exception Evm) :
    opcode r static create2 evm .error .ok
      (fun p m st _ _ _ => resume r' p m.currentTarget (runSub (Evm.Frontier.Vm.Create.child p m st)))
      = fullCreate r' static create2 evm runSub := by
  unfold opcode fullCreate Evm.Frontier.Vm.Create.run
  rw [native_congr r r' h15, start_congr r r' h3 h4 h10 h15]
  cases native r' static create2 evm with
  | error e => rfl
  | ok n =>
    simp only
    cases hs : start r' n.frame n.value n.initCode n.newAddr n.base with
    | halt => rfl
    | done e => simp only; cases h : push e 0 <;> simp [h]
    | run p m st =>
      simp only
      rw [start_target _ _ _ _ _ _ _ _ _ hs]

end Evm.CL.EffectCreate

namespace Evm.CL.EffectCreate

open Evm.IR.Trampoline

/-- One fork's binding: unfold the bound handler to `opcode` (with its rules ordinal `a`),
    move it to the fork's own ordinal `b` (the opcode reads only rules equal on the two),
    and discharge each outcome — the yield by the fork's `.createLike` arm, `resume`. -/
macro "create_bind" a:term:max b:term:max : tactic => `(tactic| (
  simp only [specCreate, Terminator.stepHandler, stepHandlerFrontier, stepHandlerHomestead,
    stepHandlerTangerine, stepHandlerSpurious, stepHandlerByzFamily, Evm.Fork.atLeast, Evm.Fork.ord,
    Option.map_some, Option.some.injEq, reduceCtorEq]
  -- On v4.29 the per-argument equation lemmas no longer rewrite the bare,
  -- not-yet-applied `doCreate` constant under `Option.map` (simp reports no
  -- progress for it), so unfold the bound handler explicitly — before the
  -- opcode-unfolding simp below, or the re-exposed `opcode` stays folded
  -- with `native` trapped inside. Each goal contains exactly one fork's
  -- handler.
  first
    | unfold Evm.Frontier.Vm.Effect.doCreate
    | unfold Evm.Homestead.Vm.Effect.doCreate
    | unfold Evm.TangerineWhistle.Vm.Effect.doCreate
    | unfold Evm.SpuriousDragon.Vm.Effect.doCreate
    | unfold Evm.Byzantium.Vm.Effect.doCreate
    | unfold Evm.Constantinople.Vm.Effect.doCreate2
    | unfold Evm.Berlin.Vm.Effect.doCreate
    | unfold Evm.Berlin.Vm.Effect.doCreate2
    | unfold Evm.Shanghai.Vm.Effect.doCreate
    | unfold Evm.Shanghai.Vm.Effect.doCreate2
  try dsimp only [Option.map]
  simp +decide only [Bool.false_eq_true, ite_false, ite_true, decide_false, decide_true, opcode, fullCreate, Evm.Frontier.Vm.Create.run,
    Evm.Fork.ord, Option.map_some]
  -- v4.29: simp can leave the bound handler folded again (seen at Berlin);
  -- a no-op dsimp would fail, hence the `try`.
  try dsimp only [Evm.Frontier.Vm.Effect.doCreate, Evm.Homestead.Vm.Effect.doCreate,
    Evm.TangerineWhistle.Vm.Effect.doCreate, Evm.SpuriousDragon.Vm.Effect.doCreate,
    Evm.Byzantium.Vm.Effect.doCreate, Evm.Constantinople.Vm.Effect.doCreate2,
    Evm.Berlin.Vm.Effect.doCreate, Evm.Berlin.Vm.Effect.doCreate2,
    Evm.Shanghai.Vm.Effect.doCreate, Evm.Shanghai.Vm.Effect.doCreate2, Option.map,
    Evm.Frontier.Vm.Create.opcode]
  rw [native_congr (Rules.ofOrd $a) (Rules.ofOrd $b) (by decide),
    start_congr (Rules.ofOrd $a) (Rules.ofOrd $b) (by decide) (by decide) (by decide) (by decide)]
  cases native (Rules.ofOrd $b) _ _ _ with
  | error e => rfl
  | ok n =>
    simp only
    cases hs : start (Rules.ofOrd $b) n.frame n.value n.initCode n.newAddr n.base with
    | halt => rfl
    | done e => simp only; cases h : push e 0 <;> rfl
    | run p m st =>
      simp only
      rw [← start_target _ _ _ _ _ _ _ _ _ hs]
      rfl))

set_option maxHeartbeats 16000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Every fork's CREATE and CREATE2, as the IR binds them, are `fullCreate` at the fork's
    rules**: the native part, then `Create.run` (`create_refines`). CREATE2 is no opcode
    before Constantinople. -/
theorem create_binding (f : Evm.Fork) (c : Evm.IR.CreateKind) (evm : Evm)
    (runSub : Evm → Except Exception Evm) :
    specCreate f c evm runSub =
      if c = .create2 ∧ f.ord < 6 then none
      else some (fullCreate (Rules.ofOrd f.ord) (decide (f.ord ≥ 5)) (c = .create2) evm runSub) := by
  cases f <;> cases c
  · create_bind 0 0
  · rfl
  · create_bind 1 1
  · rfl
  · create_bind 1 2
  · rfl
  · create_bind 3 3
  · rfl
  · create_bind 4 4
  · rfl
  · create_bind 5 5
  · rfl
  · create_bind 5 6
  · create_bind 6 6
  · create_bind 5 7
  · create_bind 6 7
  · create_bind 5 8
  · create_bind 6 8
  · create_bind 5 9
  · create_bind 6 9
  · create_bind 10 10
  · create_bind 10 10
  · create_bind 10 11
  · create_bind 10 11
  · create_bind 10 12
  · create_bind 10 12
  · create_bind 10 13
  · create_bind 10 13
  · create_bind 10 14
  · create_bind 10 14
  · create_bind 15 15
  · create_bind 15 15
  · create_bind 15 16
  · create_bind 15 16
  · create_bind 15 17
  · create_bind 15 17
  · create_bind 15 18
  · create_bind 15 18
  · create_bind 15 19
  · create_bind 15 19
  · create_bind 15 20
  · create_bind 15 20
  · create_bind 15 21
  · create_bind 15 21

end Evm.CL.EffectCreate

namespace Evm.CL.EffectCreate

/-! ## The wrapper's inputs: the charge and EIP-3860's cap are the emitted formulas -/

/-- `spec-create-gas` (what `cb-create` passes as `base`) is the opcode's charge `baseOf`. -/
theorem createGas_eq (ρ : GasEmit.Env) (k len : Nat) (c2 : Bool) (hk : ρ "fork-ord" = k)
    (hl : ρ "initcode-len" = len) (hc : ρ "is-create2" = if c2 then 1 else 0) :
    GasEmit.createGas.eval ρ = baseOf (Rules.ofOrd k) c2 len := by
  simp only [GasEmit.createGas, GasEmit.fork, GasEmit.Expr.eval, hk, hl, hc, baseOf, Rules.ofOrd,
    initCodeCost, Evm.Frontier.Vm.Gas.create, Evm.Frontier.Vm.Gas.keccak256Word]
  by_cases h15 : k < 15 <;> cases c2 <;> simp [h15] <;> omega

/-- `spec-create-initcode-oversize` (what `cb-create` passes as `oversize`) is EIP-3860's cap
    as `start` reads it. -/
theorem oversize_eq (ρ : GasEmit.Env) (k len : Nat) (hk : ρ "fork-ord" = k) (hl : ρ "initcode-len" = len) :
    (0 < GasEmit.createInitcodeOversize.eval ρ) = (k ≥ 15 ∧ len > maxInitCodeSize) := by
  simp only [GasEmit.createInitcodeOversize, GasEmit.fork, GasEmit.Expr.eval, hk, hl, maxInitCodeSize,
    Evm.SpuriousDragon.Vm.Gas.maxCodeSize]
  by_cases h15 : k < 15 <;> by_cases hl' : 49152 < len <;> simp [h15, hl'] <;> omega

/-! ## End to end -/

/-- **CREATE at every fork, end to end**: the opcode the IR binds at fork `f` is the native
    part (`native`) and then `Create.run`, and the derived callback refines that, for every
    child run `runSub`. -/
theorem create_spec_refines (f : Evm.Fork) (c : Evm.IR.CreateKind) (evm : Evm) (n : Native)
    (runSub : Evm → Except Exception Evm)
    (hc : ¬ (c = .create2 ∧ f.ord < 6))
    (hn : native (Rules.ofOrd f.ord) (decide (f.ord ≥ 5)) (decide (c = .create2)) evm = .ok n)
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hlen : n.frame.stack.length < Evm.Frontier.Vm.stackLimit) :
    specCreate f c evm runSub
        = some (Evm.Frontier.Vm.Create.run (Rules.ofOrd f.ord) n.frame n.value n.initCode n.newAddr n.base runSub) ∧
      Refines n.frame (Evm.Frontier.Vm.Create.run (Rules.ofOrd f.ord) n.frame n.value n.initCode n.newAddr n.base runSub)
        (term.run (ctxOf f.ord n.frame n.value n.initCode n.newAddr n.base runSub) (HState.ofEnv n.frame.env)) := by
  refine ⟨?_, create_refines _ _ _ _ _ _ _ hmono hlen⟩
  rw [create_binding, ite_eq_right hc]
  simp only [fullCreate, hn]

end Evm.CL.EffectCreate
