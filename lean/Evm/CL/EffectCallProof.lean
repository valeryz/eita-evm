import Evm.CL.EffectCall
import Evm.CL.EffectCreateProof
import Evm.IR.Trampoline

/-! # CL/EffectCallProof — `EffectCall.term` IS every fork's CALL family

`call_refines`: for every fork ordinal `k`, the derived callback and the spec's call after the
opcode's part (`Evm.Frontier.Vm.Call.run`, which every fork's `doCall`/`doCallcode`/
`doDelegatecall`/`doStaticcall` and `.callLike` arm are — `call_binding`) agree, for ANY
precompile table `pre` and ANY child run `runSub`: the callback runs the child on exactly
the frame the spec builds (same message, same environment), runs the same precompile on the
same input and gas, and given the same result

* if the spec's call succeeds, its environment agrees with the term's state — the world
  state, the destroyed / touched / accessed / created sets, the refund counter, the
  accessed slots and the original-value cache, all EQUAL —, the gas it charged is the
  term's, it pushed the term's flag, its return data is the term's and its memory is the
  caller's with (at most `retLen` bytes of) the return data written at `retOff` (the
  native handler's part after the callback);
* if it fails, it is out of gas, exactly when the gas left is below the term's charge.

Assumptions, stated: the child never ends with more gas than it was given (`hmono`); the
caller's stack has room for the flag (`hlen`; the operands were just popped). Arc's chain
precompile, frame-init veto and transfer log are outside the theorem (their meaning is "no
chain rule"). -/

set_option linter.unusedSimpArgs false

namespace Evm.CL.EffectCall

open Evm.CL.EffectIR
open Evm.CL.EffectCreate (envOf Agree toRes agree_ofEnv warm_eq ofEnv_gas ofEnv_out ofEnv_rdata)
open Evm.Frontier (State Account)
open Evm.Frontier.Vm (Environment Evm Stack Exception Message Memory)
open Evm.Frontier.Vm.Call

/-! ## The callback's inputs as the wrapper computes them -/

/-- `kind` as the native handler passes it. -/
def kindNat : Kind → Nat
  | .call => 0 | .callcode => 1 | .delegatecall => 2 | .staticcall => 3

/-- The child run as the spec does it: `runSub` on the fresh frame of message `m` (with the
    child's gas, supplied at the run) over the environment the term's state stands for. -/
def oracle (runSub : Evm → Except Exception Evm) (e : Environment) (m : Message) :
    HState → Nat → ChildRes := fun h g =>
  toRes (runSub (Evm.fresh { m with gas := g } (envOf e h)))

/-- The output written into the caller's memory: at most `retLen` bytes of the return data
    at `retOff` (the native handler's part after the callback). -/
def writeOut (m : Memory) (retOff retLen : Nat) (rd : Evm.Bytes) : Memory :=
  Memory.write m retOff (Evm.Bytes.sliceZeroPad rd 0 (min retLen rd.size))

def Refines (evm : Evm) (retOff retLen : Nat) (spec : Except Exception Evm) (R : HState) : Prop :=
  (∀ evm', spec = .ok evm' → Agree evm'.env R ∧ evm.gasLeft = evm'.gasLeft + R.gas ∧
      evm'.stack = R.out :: evm.stack ∧ evm'.returnData = R.rdata ∧
      evm'.memory = writeOut evm.memory retOff retLen R.rdata) ∧
  (∀ e, spec = .error e → e = .outOfGas ∧ evm.gasLeft < R.gas)

/-! ## The term's pieces in closed form -/

def ripA : Evm.Address := Evm.Address.ofNat 3

/-- Touch `a` when the fork has EIP-161 (the `touch` primitive). -/
def touchH (c : Ctx) (h : HState) (a : Evm.Address) : HState :=
  if c.fork ≥ 4 then { h with touched := insertSet h.touched a } else h

/-- `incorporate_child_on_error`'s second leg, on the state of `h`. -/
def rule2v (ct : Evm.Address) (st : State) : Bool :=
  decide (ct = ripA) && (st.accountExists ripA && EffectIR.isDead st ripA)

def usedv (c : Ctx) (g : Nat) : Nat :=
  (c.nat "charge" + (c.nat "fwd" + c.nat "stip")) - g - c.nat "stip"

/-- A child result without the child's world (what `finish` reads of it). -/
def _root_.Evm.CL.EffectIR.ChildRes.strip : ChildRes → ChildRes
  | .err => .err
  | .ok _ g o r => .ok default g o r

def finishClosed (c : Ctx) (h : HState) : HState :=
  match (c.res "r").strip with
  | .err =>
    let s := c.snaps "snap"
    let s := if rule2v (c.addr "ct") s.state then touchH c s ripA else s
    { s with gas := h.gas + (c.nat "charge" + c.nat "fwd"), out := 0, rdata := h.rdata }
  | .ok _ g o true =>
    let rt := h.touched.contains ripA
    let s := c.snaps "snap"
    let s := if rt || rule2v (c.addr "ct") s.state then touchH c s ripA else s
    { s with gas := h.gas + usedv c g, out := 0, rdata := o }
  | .ok _ g o false =>
    let s := if h.state.accountExists (c.addr "ct") && EffectIR.isDead h.state (c.addr "ct")
             then touchH c h (c.addr "ct") else h
    { s with gas := h.gas + usedv c g, out := Evm.U256.ofNat 1, rdata := o }

theorem rule2_eval (c : Ctx) (h : HState) : rule2.eval c h = rule2v (c.addr "ct") h.state := rfl

theorem touch_run (c : Ctx) (h : HState) (a : AExp) : (Stmt.touch a).run c h = touchH c h (a.eval c) := rfl

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
theorem finish_run (c : Ctx) (h : HState) : finish.run c h = finishClosed c h := by
  unfold finish finishClosed
  cases hr : c.res "r" with
  | err =>
    simp only [Stmt.run, BExp.eval, hr, ChildRes.strip, ChildRes.isErr, ite_true, rule2_eval, touch_run, AExp.eval,
      GExp.eval, WExp.eval]
    cases rule2v (c.addr "ct") (c.snaps "snap").state <;> by_cases h4 : c.fork ≥ 4 <;> simp [h4, touchH, ripA]
  | ok h' g o rv =>
    cases rv
    · simp only [Stmt.run, BExp.eval, hr, ChildRes.strip, ChildRes.isErr, ChildRes.isRev, Bool.false_eq_true, ite_false,
        GExp.eval, WExp.eval, AExp.eval, touch_run, used, fwdAll, ChildRes.gas, ChildRes.out, usedv]
      cases (h.state.accountExists (c.addr "ct") && EffectIR.isDead h.state (c.addr "ct")) <;>
        by_cases h4 : c.fork ≥ 4 <;> simp [h4, touchH]
    · simp only [Stmt.run, BExp.eval, hr, ChildRes.strip, ChildRes.isErr, ChildRes.isRev, Bool.false_eq_true, ite_false,
        ite_true, GExp.eval, WExp.eval, AExp.eval, touch_run, used, fwdAll, ChildRes.gas, ChildRes.out,
        usedv, rule2_eval]
      cases rule2v (c.addr "ct") (c.snaps "snap").state <;> by_cases ht : Evm.Address.ofNat 3 ∈ h.touched <;>
        by_cases h4 : c.fork ≥ 4 <;> simp [h4, ht, touchH, ripA]

/-- The term's state after the child run `res` from `h`. -/
def afterChild (h : HState) : ChildRes → HState
  | .err => h
  | .ok h' _ _ _ => { h' with gas := h.gas, out := h.out, rdata := h.rdata, facts := h.facts }

/-- The precompile's result as `runPre` gives it. -/
def preRes (c : Ctx) (h : HState) (a : Evm.Address) (g : Nat) : ChildRes :=
  match c.pre a with
  | some p => match p c.input g with
    | .ok (out, g') => .ok h g' out false
    | .error _ => .err
  | none => .err

def fwdv (c : Ctx) : Nat := c.nat "fwd" + c.nat "stip"

set_option backward.isDefEq.respectTransparency false in
theorem dispatch_run (c : Ctx) (h : HState) :
    dispatch.run c h =
      if (!c.bool "hasdeleg" && (c.pre (c.addr "to")).isSome) then
        finishClosed { c with res := fun y => if y = "r" then preRes c h (c.addr "to") (fwdv c) else c.res y } h
      else
        finishClosed { c with res := fun y => if y = "r" then c.child h (fwdv c) else c.res y }
          (afterChild h (c.child h (fwdv c))) := by
  simp only [dispatch, Stmt.run, BExp.eval, AExp.eval, GExp.eval, fwdAll, fwdv]
  split
  · rw [finish_run]; rfl
  · rw [finish_run]; cases c.child h (c.nat "fwd" + c.nat "stip") <;> rfl

/-- The child's world in the term's state: before EIP-161 the current target comes into
    existence; a CALL moves its value (and records the transfer fact). -/
def childH (c : Ctx) (h : HState) : HState :=
  let st := if c.fork ≥ 4 then h.state else h.state.touchAccount (c.addr "ct")
  let s := c.addr "self"
  let a := c.addr "to"
  let v := c.word "value"
  if c.nat "kind" = 0 ∧ v ≠ 0 then
    { h with state := (st.subBalance s v).addBalance a v, facts := h.facts ++ [(1, s, a, v)] }
  else { h with state := st }

set_option maxHeartbeats 4000000 in
theorem proceed_run (c : Ctx) (h : HState) : proceed.run c h = dispatch.run c (childH c h) := by
  simp only [proceed, Stmt.run, BExp.eval, AExp.eval, WExp.eval, transfer]
  unfold childH
  by_cases hk : c.fork ≥ 4 <;> by_cases hc : c.nat "kind" = 0 <;> by_cases hv : c.word "value" = 0#256 <;>
    simp [hk, hc, hv, Evm.Frontier.State.subBalance, Evm.Frontier.State.getBalance]

theorem cwarm_eq (e : Environment) (a : Evm.Address) :
    Evm.Frontier.Vm.Call.warm e a = { e with accessedAddresses := insertSet e.accessedAddresses a } := by
  unfold Evm.Frontier.Vm.Call.warm insertSet
  split <;> simp_all

/-! ## The spec's quantities, from the opcode's hand-over `n` -/

section spec
variable (k : Nat) (n : Native)

def dS : Option Evm.Address := delegate n.frame.env (n.frame.env.state.getAccount n.to).code
def coldS : Bool := (Rules.ofOrd k).eip2929 && !n.frame.env.accessedAddresses.contains n.to
def env1S : Environment := if (Rules.ofOrd k).eip2929 then warm n.frame.env n.to else n.frame.env
def dcostS : Nat :=
  match dS n with
  | some a => if (env1S k n).accessedAddresses.contains a then Evm.Berlin.Vm.Gas.warmAccess
              else Evm.Berlin.Vm.Gas.coldAccountAccess
  | none => 0
def env2S : Environment :=
  match dS n with
  | some a => warm (env1S k n) a
  | none => env1S k n
def planS : Evm.Frontier.Vm.Effect.CallGasPlan :=
  plan (Rules.ofOrd k) (coldS k n) (valueFee n.kind n.value)
    (newAcct (Rules.ofOrd k) n.kind n.frame.env.state n.to n.value) (dcostS k n) n.gasArg n.frame.gasLeft
def ctS : Evm.Address := target n.kind n.frame.message.currentTarget n.to
def stS : State :=
  let st := if (Rules.ofOrd k).eip161 then (env2S k n).state else (env2S k n).state.touchAccount (ctS n)
  if n.kind = .call ∧ n.value ≠ 0 then
    (st.subBalance n.frame.message.currentTarget n.value).addBalance n.to n.value
  else st
def e0S : Evm :=
  { n.frame with gasLeft := n.frame.gasLeft - (planS k n).charge - (planS k n).forward,
                 env := env2S k n, returnData := Evm.Bytes.empty }
abbrev ffS : Prop :=
  (valueFee n.kind n.value = true ∧
    (n.frame.env.state.getAccount n.frame.message.currentTarget).balance.toNat < n.value.toNat) ∨
  n.frame.message.depth ≥ maxDepth

theorem start_eq : start (Rules.ofOrd k) n =
    if n.frame.gasLeft < (planS k n).charge + (planS k n).forward then .halt
    else if ffS n then .done { e0S k n with gasLeft := (e0S k n).gasLeft + (planS k n).forward + (planS k n).stipend }
    else .run (e0S k n) { childMsg (Rules.ofOrd k) n with gas := (planS k n).forward + (planS k n).stipend }
      (if (dS n).isSome then none else some n.to) (stS k n) := rfl

end spec

def ctxOf (k : Nat) (n : Native)
    (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm) : Ctx :=
  let d := delegate n.frame.env (n.frame.env.state.getAccount n.to).code
  { fork := k
    addr := fun x => if x = "to" then n.to else if x = "deleg" then d.getD 0
                     else n.frame.message.currentTarget
    word := fun _ => n.value
    bool := fun x => if x = "hasdeleg" then d.isSome
                     else if x = "deep" then decide (n.frame.message.depth ≥ maxDepth)
                     else false
    nat  := fun x => if x = "kind" then kindNat n.kind else if x = "gasarg" then n.gasArg
                     else n.frame.gasLeft
    child := oracle runSub n.frame.env (childMsg (Rules.ofOrd k) n)
    pre := pre (env2S k n)
    input := n.input }


/-- What the context holds once the term has bound its prefix (`ct`, the warm-ups' flags,
    `vf`, `na`, the plan). -/
structure Bound (k : Nat) (n : Native)
    (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm) (c : Ctx) : Prop where
  fork   : c.fork = k
  avail  : c.nat "avail" = n.frame.gasLeft
  charge : c.nat "charge" = (planS k n).charge
  fwd    : c.nat "fwd" = (planS k n).forward
  stip   : c.nat "stip" = (planS k n).stipend
  kind   : c.nat "kind" = kindNat n.kind
  vf     : c.bool "vf" = valueFee n.kind n.value
  deep   : c.bool "deep" = decide (n.frame.message.depth ≥ maxDepth)
  hasd   : c.bool "hasdeleg" = (dS n).isSome
  self   : c.addr "self" = n.frame.message.currentTarget
  to     : c.addr "to" = n.to
  ct     : c.addr "ct" = target n.kind n.frame.message.currentTarget n.to
  value  : c.word "value" = n.value
  child  : c.child = oracle runSub n.frame.env (childMsg (Rules.ofOrd k) n)
  pre    : c.pre = pre (env2S k n)
  input  : c.input = n.input

theorem kindNat_eq (kd : Kind) (m : Nat) : (kindNat kd = m) ↔
    (match kd with | .call => m = 0 | .callcode => m = 1 | .delegatecall => m = 2 | .staticcall => m = 3) := by
  cases kd <;> simp [kindNat] <;> omega

set_option maxHeartbeats 4000000 in
theorem afterPlan_run (c : Ctx) (h : HState) :
    afterPlan.run c h =
      if c.nat "avail" < c.nat "charge" + c.nat "fwd" then
        { h with gas := h.gas + (c.nat "charge" + c.nat "fwd") }
      else if (c.bool "vf" && decide ((h.state.getBalance (c.addr "self")).toNat < (c.word "value").toNat))
              || c.bool "deep" then
        { h with gas := h.gas + (c.nat "charge" - c.nat "stip"), out := 0 }
      else proceed.run { c with snaps := fun y => if y = "snap" then h else c.snaps y } h := by
  simp only [afterPlan, Stmt.run, BExp.eval, GExp.eval, WExp.eval, AExp.eval]
  -- v4.29: simp leaves the two sides printing identically but not
  -- syntactically equal (hidden instance arguments); kernel defeq closes.
  try rfl

/-! ## Helpers -/

theorem writeOut_empty (m : Memory) (o l : Nat) : writeOut m o l Evm.Bytes.empty = m := by
  have h0 : Evm.Bytes.empty.size = 0 := rfl
  simp [writeOut, Memory.write, Evm.Bytes.sliceZeroPad, h0]

theorem plan_stip_le (r : Rules) (cold vf na : Bool) (d g a : Nat) :
    (plan r cold vf na d g a).stipend ≤ (plan r cold vf na d g a).charge := by
  unfold plan Evm.Berlin.Vm.Effect.callGasPlan Evm.TangerineWhistle.Vm.Effect.callGasPlan
    Evm.Frontier.Vm.Effect.callGasPlan
  cases vf <;> split <;> (try split) <;> simp [Evm.Frontier.Vm.Gas.callStipend, Evm.Frontier.Vm.Gas.callValue] <;> omega

theorem env1S_eq (k : Nat) (n : Native) :
    env1S k n = { n.frame.env with accessedAddresses := (env1S k n).accessedAddresses } := by
  unfold env1S; split <;> simp [cwarm_eq]

theorem env2S_eq (k : Nat) (n : Native) :
    env2S k n = { n.frame.env with accessedAddresses := (env2S k n).accessedAddresses } := by
  unfold env2S
  cases dS n with
  | none => exact env1S_eq k n
  | some a => simp only [cwarm_eq]; rw [env1S_eq k n]

theorem push_ite (e : Evm) (w : Evm.U256) :
    Evm.Frontier.Vm.Call.push e w =
      if e.stack.length ≥ Evm.Frontier.Vm.stackLimit then .error .stackOverflow
      else .ok { e with stack := w :: e.stack, pc := e.pc + 1 } := by
  unfold Evm.Frontier.Vm.Call.push Stack.push
  split <;> simp_all [bind, Except.bind, pure, Except.pure]

/-- The transfer fact a CALL with a value records. -/
def factsS (n : Native) : List (Nat × Evm.Address × Evm.Address × Evm.U256) :=
  if n.kind = .call ∧ n.value ≠ 0 then [(1, n.frame.message.currentTarget, n.to, n.value)] else []

theorem childH_bound (k : Nat) (n : Native) pre runSub (c : Ctx) (hB : Bound k n pre runSub c)
    (s : String → HState) :
    childH { c with snaps := s } (HState.ofEnv (env2S k n))
      = { HState.ofEnv (env2S k n) with state := stS k n, facts := factsS n } := by
  unfold childH stS factsS ctS
  simp only [hB.fork, hB.ct, hB.kind, hB.self, hB.to, hB.value, Rules.ofOrd]
  have hk : ∀ kd : Kind, (kindNat kd = 0) ↔ kd = .call := by intro kd; cases kd <;> simp [kindNat]
  by_cases h4 : k ≥ 4 <;> by_cases hc : n.kind = .call <;> by_cases hv : n.value = 0#256 <;>
    simp [h4, hc, hv, hk, HState.ofEnv]

theorem frame_eq (k : Nat) (n : Native) (g : Nat) (st : State) (fs) :
    Evm.fresh { childMsg (Rules.ofOrd k) n with gas := g }
        (envOf n.frame.env { HState.ofEnv (env2S k n) with state := st, facts := fs })
      = child (e0S k n) { childMsg (Rules.ofOrd k) n with gas := g } st := by
  unfold child e0S
  congr 1
  rw [env2S_eq k n]
  simp [envOf, HState.ofEnv]

theorem env2S_state (k : Nat) (n : Native) : (env2S k n).state = n.frame.env.state := by
  have := congrArg Environment.state (env2S_eq k n); simpa using this

theorem ctouch_eq (e : Environment) (a : Evm.Address) :
    Evm.Frontier.Vm.Call.touch e a = { e with touched := insertSet e.touched a } := by
  unfold Evm.Frontier.Vm.Call.touch insertSet
  split <;> simp_all

theorem agree_mod (e : Environment) (h : HState) (g : Nat) (o : Evm.U256) (r : Evm.Bytes)
    (fs : List (Nat × Evm.Address × Evm.Address × Evm.U256)) (hA : Agree e h) :
    Agree e { h with gas := g, out := o, rdata := r, facts := fs } :=
  ⟨hA.state, hA.destroyed, hA.touched, hA.accessed, hA.created, hA.refund, hA.slots, hA.origs⟩

theorem agree_mod3 (e : Environment) (h : HState) (g : Nat) (o : Evm.U256) (r : Evm.Bytes)
    (hA : Agree e h) : Agree e { h with gas := g, out := o, rdata := r } :=
  ⟨hA.state, hA.destroyed, hA.touched, hA.accessed, hA.created, hA.refund, hA.slots, hA.origs⟩

theorem existsDead (s : State) (a : Evm.Address) :
    (s.accountExists a && EffectIR.isDead s a) = (s.accountExists a && (s.getAccount a).isEmpty) := by
  unfold EffectIR.isDead; cases s.accountExists a <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- `incorporate_child_on_error`'s exemption, as the term computes it. -/
theorem ripemd_agree (k : Nat) (c : Ctx) (hk : c.fork = k) (e : Environment) (ct : Evm.Address)
    (T : List Evm.Address) :
    Agree (ripemdKeep (Rules.ofOrd k) e ct T)
      (if T.contains ripA || rule2v ct e.state then touchH c (HState.ofEnv e) ripA else HState.ofEnv e) := by
  have hcond : ((Rules.ofOrd k).eip161 = true ∧ (T.contains ripemd = true ∨
      (ct = ripemd ∧ e.state.accountExists ripemd = true ∧ (e.state.getAccount ripemd).isEmpty = true)))
      ↔ (k ≥ 4 ∧ (T.contains ripA || rule2v ct e.state) = true) := by
    simp only [Rules.ofOrd, rule2v, existsDead, ripA, ripemd, decide_eq_true_eq, Bool.or_eq_true,
      Bool.and_eq_true]
  unfold ripemdKeep
  simp only [hcond]
  generalize (T.contains ripA || rule2v ct e.state) = b
  cases b <;> by_cases h4 : k ≥ 4 <;> simp [h4, touchH, hk, ctouch_eq, HState.ofEnv] <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem arith_ff (G c f s : Nat) (h1 : ¬ G < c + f) (h2 : s ≤ c) :
    G = G - c - f + f + s + (0 + (c - s)) := by omega

/-- The term's state once the child's world is in place. -/
def h4S (k : Nat) (n : Native) : HState :=
  { HState.ofEnv (env2S k n) with state := stS k n, facts := factsS n }

/-- EIP-161's touch of a successful child's target, as the term computes it. -/
theorem success_agree (k : Nat) (c : Ctx) (hk : c.fork = k) (e : Environment) (ct : Evm.Address)
    (h : HState) (hA : Agree e h) :
    Agree (if (Rules.ofOrd k).eip161 = true ∧ e.state.accountExists ct = true ∧ (e.state.getAccount ct).isEmpty = true
           then Evm.Frontier.Vm.Call.touch e ct else e)
      (if (h.state.accountExists ct && EffectIR.isDead h.state ct) then touchH c h ct else h) := by
  rw [← hA.state, existsDead]
  have hcond : ((Rules.ofOrd k).eip161 = true ∧ e.state.accountExists ct = true ∧
      (e.state.getAccount ct).isEmpty = true) ↔
      (k ≥ 4 ∧ (e.state.accountExists ct && (e.state.getAccount ct).isEmpty) = true) := by
    simp [Rules.ofOrd]
  simp only [hcond]
  generalize (e.state.accountExists ct && (e.state.getAccount ct).isEmpty) = b
  cases b <;> by_cases h4 : k ≥ 4 <;> simp [h4, touchH, hk, ctouch_eq] <;>
    first
    | exact hA
    | exact ⟨hA.state, hA.destroyed, by rw [hA.touched], hA.accessed, hA.created, hA.refund, hA.slots, hA.origs⟩

theorem oracle_child (k : Nat) (n : Native) (runSub : Evm → Except Exception Evm) (g : Nat) :
    oracle runSub n.frame.env (childMsg (Rules.ofOrd k) n)
        { HState.ofEnv (env2S k n) with state := stS k n, facts := factsS n } g
      = toRes (runSub (child (e0S k n) { childMsg (Rules.ofOrd k) n with gas := g } (stS k n))) := by
  unfold oracle; rw [frame_eq]

theorem arith_rev (G c f s g : Nat) (h1 : ¬ G < c + f) (h2 : s ≤ c) (h3 : g ≤ f + s) :
    G = G - c - f + g + (0 + ((c + (f + s)) - g - s)) := by omega
theorem arith_err (G c f : Nat) (h1 : ¬ G < c + f) : G = G - c - f + (c + f) := by omega

set_option maxHeartbeats 64000000 in
set_option backward.isDefEq.respectTransparency false in
theorem finish_refines (k : Nat) (n : Native) (c3 : Ctx) (R : Except Exception Evm)
    (hk : c3.fork = k) (hch : c3.nat "charge" = (planS k n).charge)
    (hfw : c3.nat "fwd" = (planS k n).forward) (hsp : c3.nat "stip" = (planS k n).stipend)
    (hct : c3.addr "ct" = ctS n) (hsnap : c3.snaps "snap" = HState.ofEnv (env2S k n))
    (hres : (c3.res "r").strip = (toRes R).strip)
    (hG : ¬ n.frame.gasLeft < (planS k n).charge + (planS k n).forward)
    (hst : (planS k n).stipend ≤ (planS k n).charge)
    (hmonoR : ∀ sub, R = .ok sub → sub.gasLeft ≤ (planS k n).forward + (planS k n).stipend)
    (hlen : n.frame.stack.length < Evm.Frontier.Vm.stackLimit) :
    Refines n.frame n.retOff n.retLen (resume (Rules.ofOrd k) (e0S k n) (ctS n) n.retOff n.retLen R)
      (finishClosed c3 (afterChild (h4S k n) (toRes R))) := by
  have hl : ¬ n.frame.stack.length ≥ Evm.Frontier.Vm.stackLimit := Nat.not_le.mpr hlen
  unfold resume finishClosed
  rw [hres]
  cases R with
  | error e =>
    simp only [toRes, ChildRes.strip, afterChild, hsnap, hct, hch, hfw, push_ite, e0S, hl, ite_false]
    refine ⟨fun e' h => ?_, fun e h => (by cases h)⟩
    cases h
    refine ⟨?_, ?_, rfl, rfl, ?_⟩
    · have := ripemd_agree k c3 hk (env2S k n) (ctS n) []
      simp only [List.contains_nil, Bool.false_or] at this
      exact agree_mod _ _ _ _ _ _ (by simpa [HState.ofEnv] using this)
    · simp [h4S, HState.ofEnv]; exact arith_err _ _ _ hG
    · simp [h4S, HState.ofEnv, writeOut_empty]
  | ok sub =>
    have hm := hmonoR sub rfl
    cases hrv : sub.reverted
    · simp only [toRes, ChildRes.strip, hrv, afterChild, hct, hch, hfw, hsp, Bool.false_eq_true, ite_false, push_ite, e0S, hl,
        usedv]
      refine ⟨fun e' h => ?_, fun e h => (by cases h)⟩
      cases h
      refine ⟨?_, ?_, ?_, rfl, ?_⟩
      · exact agree_mod3 _ _ _ _ _ (success_agree k c3 hk sub.env (ctS n)
          { HState.ofEnv sub.env with gas := (h4S k n).gas, out := (h4S k n).out, rdata := (h4S k n).rdata, facts := (h4S k n).facts }
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)
      · simp only [h4S, HState.ofEnv]; exact arith_rev _ _ _ _ _ hG hst hm
      · rfl
      · rfl
    · simp only [toRes, ChildRes.strip, hrv, afterChild, hct, hch, hfw, hsp, hsnap, ite_true, push_ite, e0S, hl, ite_false,
        usedv]
      refine ⟨fun e' h => ?_, fun e h => (by cases h)⟩
      cases h
      refine ⟨?_, ?_, rfl, rfl, rfl⟩
      · exact agree_mod3 _ _ _ _ _ (ripemd_agree k c3 hk (env2S k n) (ctS n) sub.env.touched)
      · simp only [h4S, HState.ofEnv]; exact arith_rev _ _ _ _ _ hG hst hm

set_option maxHeartbeats 64000000 in
theorem afterPlan_refines (k : Nat) (n : Native) pre runSub (c : Ctx) (h : HState) (hB : Bound k n pre runSub c)
    (hh : h = HState.ofEnv (env2S k n))
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hpmono : ∀ a p i g o g', pre (env2S k n) a = some p → p i g = .ok (o, g') → g' ≤ g)
    (hlen : n.frame.stack.length < Evm.Frontier.Vm.stackLimit) :
    Refines n.frame n.retOff n.retLen (Evm.Frontier.Vm.Call.run (Rules.ofOrd k) pre n runSub)
      (afterPlan.run c h) := by
  subst hh
  have hl : ¬ n.frame.stack.length ≥ Evm.Frontier.Vm.stackLimit := Nat.not_le.mpr hlen
  have hst : (planS k n).stipend ≤ (planS k n).charge := plan_stip_le _ _ _ _ _ _ _
  unfold Evm.Frontier.Vm.Call.run
  rw [start_eq, afterPlan_run]
  simp only [hB.avail, hB.charge, hB.fwd, hB.stip]
  by_cases hG : n.frame.gasLeft < (planS k n).charge + (planS k n).forward
  · simp only [hG, ite_true]
    refine ⟨fun e h => (by cases h), fun e h => ?_⟩
    simp only [Except.error.injEq] at h; subst h
    exact ⟨rfl, by simp [HState.ofEnv]; omega⟩
  · simp only [hG, ite_false]
    have hcond : ((c.bool "vf" && decide (((HState.ofEnv (env2S k n)).state.getBalance (c.addr "self")).toNat
        < (c.word "value").toNat)) || c.bool "deep") = decide (ffS n) := by
      simp only [hB.vf, hB.deep, hB.self, hB.value, HState.ofEnv, env2S_state, ffS,
        Evm.Frontier.State.getBalance]
      cases valueFee n.kind n.value <;> simp
    rw [hcond]
    by_cases hff : ffS n
    · simp only [hff, decide_true, ite_true]
      rw [push_ite]
      simp only [e0S, hl, ite_false]
      refine ⟨fun e' h => ?_, fun e h => (by cases h)⟩
      cases h
      refine ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, rfl, rfl, ?_⟩
      · simp only [HState.ofEnv]; exact arith_ff _ _ _ _ hG hst
      · simp [HState.ofEnv, writeOut_empty]
    · simp only [hff, decide_false, Bool.false_eq_true, ite_false]
      rw [proceed_run, childH_bound k n pre runSub c hB, dispatch_run]
      have hct : ({ childMsg (Rules.ofOrd k) n with gas := (planS k n).forward + (planS k n).stipend }
          : Message).currentTarget = ctS n := rfl
      have hfv : fwdv { c with snaps := fun y => if y = "snap" then HState.ofEnv (env2S k n) else c.snaps y }
          = (planS k n).forward + (planS k n).stipend := by simp [fwdv, hB.fwd, hB.stip]
      rw [hfv]
      simp only [hB.hasd, hB.pre, hB.to]
      unfold runChild
      rw [hB.child]
      have he0 : (e0S k n).env = env2S k n := rfl
      simp only [he0]
      cases hd : dS n
      · cases hp : pre (env2S k n) n.to
        · simp only [hp, hd, Option.isSome_none, Bool.not_false, Bool.true_and, Option.isSome_none,
            Bool.false_eq_true, ite_false, Option.bind_some]
          rw [oracle_child]
          exact finish_refines k n _ _ hB.fork hB.charge hB.fwd hB.stip hB.ct (by simp) (by simp [ChildRes.strip]) hG hst
            (fun sub hs => by have := hmono _ sub hs; simpa [child, Evm.fresh] using this) hlen
        · rename_i p
          have hdata : (childMsg (Rules.ofOrd k) n).data = n.input := rfl
          simp only [hp, hd, Option.isSome_none, Bool.not_false, Bool.true_and, Option.isSome_some,
            ite_true, Option.bind_some, hdata, preRes, hB.pre, hB.to, hB.input]
          cases hpr : p n.input ((planS k n).forward + (planS k n).stipend) with
          | error e =>
            simp only [hpr, hp, Bool.false_eq_true, ↓reduceIte, Option.bind_some]
            exact finish_refines k n _ (.error e) hB.fork hB.charge hB.fwd hB.stip hB.ct (by simp) (by simp [toRes, hpr, ChildRes.strip, child, Evm.fresh])
              hG hst (fun sub hs => by cases hs) hlen
          | ok og =>
            obtain ⟨o, g⟩ := og
            have hg := hpmono _ _ _ _ _ _ hp hpr
            simp only [hpr, hp, Bool.false_eq_true, ↓reduceIte, Option.bind_some]
            exact finish_refines k n _
              (.ok { child (e0S k n) { childMsg (Rules.ofOrd k) n with gas := (planS k n).forward + (planS k n).stipend } (stS k n) with gasLeft := g, output := o, halted := true })
              hB.fork hB.charge hB.fwd hB.stip hB.ct (by simp) (by simp [toRes, hpr, ChildRes.strip, child, Evm.fresh])
              hG hst (fun sub hs => by cases hs; exact hg) hlen
      · simp only [hd, Option.isSome_some, Bool.not_true, Bool.false_and, Bool.false_eq_true, ite_false,
          ite_true, Option.bind_none]
        rw [oracle_child]
        exact finish_refines k n _ _ hB.fork hB.charge hB.fwd hB.stip hB.ct (by simp) (by simp [ChildRes.strip]) hG hst
          (fun sub hs => by have := hmono _ sub hs; simpa [child, Evm.fresh] using this) hlen

theorem vf_eq (kd : Kind) (v : Evm.U256) :
    ((decide (kindNat kd = 0) || decide (kindNat kd = 1)) && decide (v ≠ 0)) = valueFee kd v := by
  cases kd <;> simp [valueFee, kindNat]

theorem na_eq (k : Nat) (kd : Kind) (s : State) (to : Evm.Address) (v : Evm.U256) :
    (decide (kindNat kd = 0) && (decide (k ≥ 4) && (decide (v ≠ 0) && EffectIR.isDead s to) ||
        !decide (k ≥ 4) && !s.accountExists to)) = newAcct (Rules.ofOrd k) kd s to v := by
  cases kd <;> by_cases h4 : k ≥ 4 <;>
    simp [newAcct, kindNat, Rules.ofOrd, h4, Evm.Frontier.Vm.Call.isDead, EffectIR.isDead]

/-- v4.29 normal-form bridges: simp now leaves `!decide (v = 0)` and `decide
    (4 ≤ k)` where it used to produce `decide (v ≠ 0)` / `decide (k ≥ 4)`, so
    `vf_eq` / `na_eq` no longer match as rewrite rules. These restore the
    shapes they are stated in. -/
theorem decide_ne_zero (v : Evm.U256) :
    (!decide (v = 0)) = decide (v ≠ 0) := decide_not.symm

theorem bitvec_zero_lit : (0#256 : Evm.U256) = 0 := rfl

theorem four_le_iff_ge4 (k : Nat) : (4 ≤ k) = (k ≥ 4) := rfl

set_option maxHeartbeats 64000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The derived CALL-family callback is every fork's call.** -/
theorem call_refines (k : Nat) (n : Native)
    (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (runSub : Evm → Except Exception Evm)
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hpmono : ∀ a p i g o g', pre (env2S k n) a = some p → p i g = .ok (o, g') → g' ≤ g)
    (hlen : n.frame.stack.length < Evm.Frontier.Vm.stackLimit) :
    Refines n.frame n.retOff n.retLen (Evm.Frontier.Vm.Call.run (Rules.ofOrd k) pre n runSub)
      (term.run (ctxOf k n pre runSub) (HState.ofEnv n.frame.env)) := by
  unfold term
  simp only [Stmt.run, BExp.eval, AExp.eval, GExp.eval, WExp.eval, ctxOf, String.reduceEq, ↓reduceIte,
    Bool.false_eq_true, ite_false, ite_true]
  have hdS : delegate n.frame.env (n.frame.env.state.getAccount n.to).code = dS n := rfl
  rw [hdS]
  by_cases h10 : k ≥ 10 <;> cases hd : dS n <;>
    simp only [h10, decide_true, decide_false, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
      ite_true, ite_false, Option.getD_some] <;>
    refine afterPlan_refines k n pre runSub _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ ?_
      hmono hpmono hlen
  all_goals (try dsimp only)
  all_goals (try simp only [String.reduceEq, ↓reduceIte, Bool.false_eq_true, ite_false, ite_true])
  all_goals try (first
    | rfl
    | (simp only [planS]; congr 1 <;>
        first
        | rfl
        | (simp [coldS, env1S, dcostS, hd, h10, Rules.ofOrd, cwarm_eq, HState.ofEnv, insertSet,
            Evm.Berlin.Vm.Gas.warmAccess, Evm.Berlin.Vm.Gas.coldAccountAccess]; done)
        | (cases n.kind <;> simp [valueFee, newAcct, kindNat, Rules.ofOrd, HState.ofEnv,
            Evm.Frontier.Vm.Call.isDead, EffectIR.isDead]; done))
    | (cases n.kind <;> simp [kindNat, target, ctS, valueFee]; done)
    | (simp [hd, h10, HState.ofEnv, env2S, env1S, cwarm_eq, ctxOf, oracle]; done))
  all_goals try (simp only [vf_eq, na_eq, HState.ofEnv]; unfold planS coldS dcostS env1S; simp [hd, h10, Rules.ofOrd, cwarm_eq, insertSet, Evm.Berlin.Vm.Gas.warmAccess, Evm.Berlin.Vm.Gas.coldAccountAccess]; try rfl; done)
  all_goals try (unfold env2S env1S; simp [hd, h10, Rules.ofOrd, cwarm_eq, HState.ofEnv]; done)
  -- v4.29: simp's normal forms for decide/≠/≥ diverge from vf_eq/na_eq's
  -- statement shapes; restore the shapes, rewrite via the bridges, close.
  all_goals try (simp only [bitvec_zero_lit, decide_ne_zero, four_le_iff_ge4, vf_eq, na_eq, Rules.ofOrd, HState.ofEnv]; rfl)
  done

end Evm.CL.EffectCall

namespace Evm.CL.EffectCall

open Evm.IR.Trampoline
open Evm.CL.EffectIR
open Evm.Frontier.Vm (Environment Evm Stack Exception Message Memory)
open Evm.Frontier.Vm.Call

/-- The spec's kind for the IR's. -/
def kindOf : Evm.IR.CallKind → Kind
  | .call => .call | .callcode => .callcode | .delegatecall => .delegatecall | .staticcall => .staticcall

/-- Each fork's call as the IR binds it, run to its end: the bound step handler and, when it
    yields, the fork's own `handleYield` (`runYieldOf`) with `runSub` running the child.
    `none`: not an opcode at this fork (DELEGATECALL before Homestead, STATICCALL before
    Byzantium). -/
def specCall (f : Evm.Fork) (c : Evm.IR.CallKind) (evm : Evm) (runSub : Evm → Except Exception Evm) :
    Option (Except Exception Evm) :=
  (Terminator.stepHandler f (.call c)).map fun h =>
    StepResultOf.cases f (h evm) Except.ok
      (fun st => StepOf.cases f st (fun fr eff => runYieldOf f fr eff runSub) (fun fr _ => .ok fr)
        (fun _ e => .error e))

/-- The opcode run to its end under one rule set and precompile table: the native part, then
    `Call.run` — the callback's part, `call_refines`. -/
def fullCall (r : Rules) (pre : Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile)
    (k : Kind) (evm : Evm) (runSub : Evm → Except Exception Evm) : Except Exception Evm :=
  match native r k evm with
  | .error e => .error e
  | .ok n => Evm.Frontier.Vm.Call.run r pre n runSub

/-- The precompile table each fork's trampoline hands `Call.runChild`: the fork's
    (`Call.precompiles`), with the OP-Stack rules on top at Cancun and Prague (off on
    Ethereum: `opP256VerifyGas = none`, `opBn256PairingCap = none`). -/
def tableOf (f : Evm.Fork) :
    Environment → Evm.Address → Option Evm.Frontier.Vm.PrecompiledContracts.Precompile :=
  match f with
  | .cancun => Evm.Cancun.Vm.Effect.opPrecompiles Evm.Cancun.Vm.PrecompiledContracts.lookup
  | .prague => Evm.Cancun.Vm.Effect.opPrecompiles (precompiles 17)
  | _ => fun _ => precompiles f.ord

open Evm.Frontier.Vm.Call in
/-- One fork's binding: unfold the bound handler to `opcode` (rules ordinal `a`) and the
    fork's `.callLike` arm to `resume` (rules ordinal `K`, the fork's table), move both to the
    fork's own ordinal `b` (the call family reads only rules equal on them), and discharge each
    outcome. -/
macro "call_bind" a:term:max K:term:max b:term:max : tactic => `(tactic| (
  simp only [specCall, Terminator.stepHandler, stepHandlerFrontier, stepHandlerHomestead,
    stepHandlerTangerine, stepHandlerSpurious, stepHandlerByzFamily, Evm.Fork.atLeast, Evm.Fork.ord,
    Option.map_some, Option.some.injEq, reduceCtorEq]
  -- v4.29: the per-argument equation lemmas no longer rewrite the bare,
  -- not-yet-applied handler constants under `Option.map`; unfold whichever
  -- handler this goal binds, before the opcode-unfolding simp below.
  first
    | unfold Evm.Frontier.Vm.Effect.doCall
    | unfold Evm.Frontier.Vm.Effect.doCallcode
    | unfold Evm.Homestead.Vm.Effect.doCall
    | unfold Evm.Homestead.Vm.Effect.doCallcode
    | unfold Evm.Homestead.Vm.Effect.doDelegatecall
    | unfold Evm.TangerineWhistle.Vm.Effect.doCall
    | unfold Evm.TangerineWhistle.Vm.Effect.doCallcode
    | unfold Evm.TangerineWhistle.Vm.Effect.doDelegatecall
    | unfold Evm.SpuriousDragon.Vm.Effect.doCall
    | unfold Evm.SpuriousDragon.Vm.Effect.doCallcode
    | unfold Evm.SpuriousDragon.Vm.Effect.doDelegatecall
    | unfold Evm.Byzantium.Vm.Effect.doCall
    | unfold Evm.Byzantium.Vm.Effect.doCallcode
    | unfold Evm.Byzantium.Vm.Effect.doDelegatecall
    | unfold Evm.Byzantium.Vm.Effect.doStaticcall
    | unfold Evm.Berlin.Vm.Effect.doCall
    | unfold Evm.Berlin.Vm.Effect.doCallcode
    | unfold Evm.Berlin.Vm.Effect.doDelegatecall
    | unfold Evm.Berlin.Vm.Effect.doStaticcall
  try dsimp only [Option.map]
  simp +decide only [Bool.false_eq_true, ite_false, ite_true, decide_false, decide_true, opcode, fullCall,
    tableOf, kindOf, Option.map_some, Evm.Frontier.Vm.Call.run]
  -- v4.29: simp can leave the bound handler folded again; a no-op dsimp
  -- would fail, hence the `try`.
  try dsimp only [Evm.Frontier.Vm.Effect.doCall, Evm.Frontier.Vm.Effect.doCallcode,
    Evm.Homestead.Vm.Effect.doCall, Evm.Homestead.Vm.Effect.doCallcode,
    Evm.Homestead.Vm.Effect.doDelegatecall,
    Evm.TangerineWhistle.Vm.Effect.doCall, Evm.TangerineWhistle.Vm.Effect.doCallcode,
    Evm.TangerineWhistle.Vm.Effect.doDelegatecall,
    Evm.SpuriousDragon.Vm.Effect.doCall, Evm.SpuriousDragon.Vm.Effect.doCallcode,
    Evm.SpuriousDragon.Vm.Effect.doDelegatecall,
    Evm.Byzantium.Vm.Effect.doCall, Evm.Byzantium.Vm.Effect.doCallcode,
    Evm.Byzantium.Vm.Effect.doDelegatecall, Evm.Byzantium.Vm.Effect.doStaticcall,
    Evm.Berlin.Vm.Effect.doCall, Evm.Berlin.Vm.Effect.doCallcode,
    Evm.Berlin.Vm.Effect.doDelegatecall, Evm.Berlin.Vm.Effect.doStaticcall,
    Option.map, Evm.Frontier.Vm.Call.opcode]
  rw [show Rules.ofOrd $a = Rules.ofOrd $b from by decide]
  cases native (Rules.ofOrd $b) _ _ with
  | error e => rfl
  | ok n =>
    simp only
    cases hs : start (Rules.ofOrd $b) n with
    | halt => rfl
    | done e => simp only; cases h : push e 0 <;> rfl
    | run p m c st =>
      simp only [runYieldOf, Evm.Frontier.Vm.Effect.handleYield, Evm.Homestead.Vm.Effect.handleYield,
        Evm.TangerineWhistle.Vm.Effect.handleYield, Evm.SpuriousDragon.Vm.Effect.handleYield,
        Evm.Byzantium.Vm.Effect.handleYield, Evm.Constantinople.Vm.Effect.handleYield,
        Evm.Petersburg.Vm.Effect.handleYield, Evm.Istanbul.Vm.Effect.handleYield,
        Evm.Berlin.Vm.Effect.handleYield, Evm.London.Vm.Effect.handleYield, Evm.Paris.Vm.Effect.handleYield,
        Evm.Shanghai.Vm.Effect.handleYield, Evm.Cancun.Vm.Effect.handleYield, Evm.Osaka.Vm.Effect.handleYield,
        Evm.Amsterdam.Vm.Effect.handleYield, StepResultOf.cases, StepOf.cases]
      rw [show Rules.ofOrd $K = Rules.ofOrd $b from by decide]
      rfl))

set_option maxHeartbeats 64000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Every fork's CALL, CALLCODE, DELEGATECALL and STATICCALL, as the IR binds them, are
    `fullCall` at the fork's rules and precompile table**: the native part, then `Call.run`
    (`call_refines`). DELEGATECALL is no opcode before Homestead, STATICCALL before
    Byzantium. -/
theorem call_binding (f : Evm.Fork) (c : Evm.IR.CallKind) (evm : Evm)
    (runSub : Evm → Except Exception Evm) :
    specCall f c evm runSub =
      if (c = .delegatecall ∧ f.ord < 1) ∨ (c = .staticcall ∧ f.ord < 5) then none
      else some (fullCall (Rules.ofOrd f.ord) (tableOf f) (kindOf c) evm runSub) := by
  cases f <;> cases c
  · call_bind 0 0 0
  · call_bind 0 0 0
  · rfl
  · rfl
  · call_bind 1 1 1
  · call_bind 1 1 1
  · call_bind 1 1 1
  · rfl
  · call_bind 1 1 2
  · call_bind 1 1 2
  · call_bind 1 1 2
  · rfl
  · call_bind 3 3 3
  · call_bind 3 3 3
  · call_bind 3 3 3
  · rfl
  · call_bind 4 4 4
  · call_bind 4 4 4
  · call_bind 4 4 4
  · rfl
  · call_bind 5 5 5
  · call_bind 5 5 5
  · call_bind 5 5 5
  · call_bind 5 5 5
  · call_bind 5 6 6
  · call_bind 5 6 6
  · call_bind 5 6 6
  · call_bind 5 6 6
  · call_bind 5 7 7
  · call_bind 5 7 7
  · call_bind 5 7 7
  · call_bind 5 7 7
  · call_bind 5 8 8
  · call_bind 5 8 8
  · call_bind 5 8 8
  · call_bind 5 8 8
  · call_bind 5 8 9
  · call_bind 5 8 9
  · call_bind 5 8 9
  · call_bind 5 8 9
  · call_bind 10 10 10
  · call_bind 10 10 10
  · call_bind 10 10 10
  · call_bind 10 10 10
  · call_bind 10 11 11
  · call_bind 10 11 11
  · call_bind 10 11 11
  · call_bind 10 11 11
  · call_bind 10 11 12
  · call_bind 10 11 12
  · call_bind 10 11 12
  · call_bind 10 11 12
  · call_bind 10 11 13
  · call_bind 10 11 13
  · call_bind 10 11 13
  · call_bind 10 11 13
  · call_bind 10 14 14
  · call_bind 10 14 14
  · call_bind 10 14 14
  · call_bind 10 14 14
  · call_bind 10 15 15
  · call_bind 10 15 15
  · call_bind 10 15 15
  · call_bind 10 15 15
  · call_bind 10 16 16
  · call_bind 10 16 16
  · call_bind 10 16 16
  · call_bind 10 16 16
  · call_bind 10 16 17
  · call_bind 10 16 17
  · call_bind 10 16 17
  · call_bind 10 16 17
  · call_bind 10 18 18
  · call_bind 10 18 18
  · call_bind 10 18 18
  · call_bind 10 18 18
  · call_bind 10 18 19
  · call_bind 10 18 19
  · call_bind 10 18 19
  · call_bind 10 18 19
  · call_bind 10 18 20
  · call_bind 10 18 20
  · call_bind 10 18 20
  · call_bind 10 18 20
  · call_bind 10 21 21
  · call_bind 10 21 21
  · call_bind 10 21 21
  · call_bind 10 21 21

/-- **The CALL family at every fork, end to end**: the opcode the IR binds at fork `f` is the
    native part (`native`) and then `Call.run`, and the derived callback refines that, for every
    child run `runSub`. -/
theorem call_spec_refines (f : Evm.Fork) (c : Evm.IR.CallKind) (evm : Evm) (n : Native)
    (runSub : Evm → Except Exception Evm)
    (hc : ¬ ((c = .delegatecall ∧ f.ord < 1) ∨ (c = .staticcall ∧ f.ord < 5)))
    (hn : native (Rules.ofOrd f.ord) (kindOf c) evm = .ok n)
    (hmono : ∀ e sub, runSub e = .ok sub → sub.gasLeft ≤ e.gasLeft)
    (hpmono : ∀ a p i g o g', tableOf f (env2S f.ord n) a = some p → p i g = .ok (o, g') → g' ≤ g)
    (hlen : n.frame.stack.length < Evm.Frontier.Vm.stackLimit) :
    specCall f c evm runSub = some (Evm.Frontier.Vm.Call.run (Rules.ofOrd f.ord) (tableOf f) n runSub) ∧
      Refines n.frame n.retOff n.retLen (Evm.Frontier.Vm.Call.run (Rules.ofOrd f.ord) (tableOf f) n runSub)
        (term.run (ctxOf f.ord n (tableOf f) runSub) (HState.ofEnv n.frame.env)) := by
  refine ⟨?_, call_refines _ _ _ _ hmono hpmono hlen⟩
  rw [call_binding, ite_eq_right hc]
  simp only [fullCall, hn]

end Evm.CL.EffectCall
