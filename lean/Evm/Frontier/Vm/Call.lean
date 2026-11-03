/-
  Evm.Frontier.Vm.Call — CALL / CALLCODE / DELEGATECALL / STATICCALL for every fork, once.

  EELS `vm/instructions/system.py` `call` / `callcode` / `delegatecall` / `staticcall` /
  `generic_call`, `vm/gas.py` `calculate_message_call_gas`, `vm/interpreter.py`
  `process_message` (the snapshot, `touch_account`, `move_ether`, the precompile dispatch
  of `execute_code`), `vm/__init__.py` `incorporate_child_on_{success,error}`, and from
  Prague `vm/eoa_delegation.py` `access_delegation` — the same clauses at every fork,
  switched by the fork's ordinal (`Rules.ofOrd`):

    * EIP-150 (TW, ord 3): base 700 and the 63/64 cap on the forwarded gas
      (`calculate_message_call_gas`'s `max_message_call_gas`); before it base 40 and the
      whole requested gas is charged and forwarded (out of gas when it does not fit).
    * EIP-161 (SD, ord 4): the new-account charge only for a CALL moving value to a dead
      account (before: a CALL to an absent account, any value); the callee is touched
      when the child succeeds and leaves it existing and empty
      (`incorporate_child_on_success`), and the RIPEMD-160 exemption of
      `incorporate_child_on_error` (mainnet block 2,675,119): a failed child's touch of
      0x03 survives. Before SD, `process_message`'s `touch_account` brings the current
      target into existence (on success; a failed child rolls it back).
    * EIP-214 (Byzantium, ord 5): STATICCALL; a CALL with value in a static frame is an
      exceptional halt; the child of a static frame is static. (EIP-140's REVERT — the
      child's gas and output come back — needs no fork switch: only Byzantium+ children
      can REVERT.)
    * EIP-2929 (Berlin, ord 10): the target joins the accessed set (cold 2600 / warm 100
      instead of the base); the child's warm-ups survive only its success
      (`incorporate_child_on_success` merges them, `..._on_error` does not).
    * EIP-7702 (`env.pragueDelegation`: set by the drivers whose EL fork is Prague+):
      a target whose code is a delegation designator runs the delegate's code, the
      delegate's access is charged with the base (before the 63/64 cap) and joins the
      accessed set, and precompiles are disabled for the frame (`access_delegation`).

  The precompile table is the fork's (`precompiles`), passed in by the fork's trampoline:
  Frontier 0x01–0x04, Byzantium +0x05–0x08 (EIP-196/197/198), Istanbul +0x09 (EIP-152,
  EIP-1108 repricing), Berlin's EIP-2565 MODEXP, Cancun +0x0a, Prague +0x0b–0x11
  (EIP-2537), Osaka EIP-7883 MODEXP and 0x100 (EIP-7951).

  Every fork's `doCall`/`doCallcode`/`doDelegatecall`/`doStaticcall` is `opcode` (the pops,
  the static check, the memory charge for both ranges, then `start`); every fork's
  `.callLike` arm is `resume` on `runChild` (the fork's precompile table, or the child
  `runSub` runs). The derived host callback (`Evm.CL.EffectCall`) is proved against
  `start`/`resume` (`Evm.CL.EffectCallProof.call_refines`).

  Stated choices (each unobservable on the chains we replay, or recorded as a gap):

    * From Spurious Dragon `process_message` also brings an absent current target into
      existence; the spec does not (the world never holds the empty account EELS creates
      and, on success, sweeps at the end of the tx). Every rule from Spurious Dragon asks
      `is_account_dead` (absent or empty), so nothing in between tells the two apart —
      the residual assumption of `EffectEndTxProof.sd_form_closes`.
    * The touch on success and the RIPEMD-160 exemption are kept after Paris, where EELS
      dropped the touched set (EIP-7523: no empty account exists to sweep).
    * The exemption's first leg (0x03 in the failed child's touched set) is applied to a
      REVERTed child only: an exceptionally halting child's environment is not returned
      by the spec's child run (`runSub : Evm → Except Exception Evm`). It matters only
      when 0x03 existed empty before the child — on mainnet, around block 2,675,119.
    * Amsterdam's EELS reservoir/state-gas meter and EIP-7708 transfer logs are not in
      the Lean Amsterdam spec (pre-existing, outside this module).
-/

import Evm.Frontier.Vm
import Evm.Frontier.Vm.Instructions.Memory
import Evm.Frontier.Vm.PrecompiledContracts
import Evm.Byzantium.Vm.PrecompiledContracts
import Evm.Istanbul.Vm.PrecompiledContracts
import Evm.Berlin.Vm.PrecompiledContracts.Modexp
import Evm.Cancun.Vm.PrecompiledContracts
import Evm.Prague.Vm.PrecompiledContracts
import Evm.Osaka.Vm.PrecompiledContracts
import Evm.Prague.State
import Evm.TangerineWhistle.Vm.Gas
import Evm.Berlin.Vm.Gas

/-! ## The three gas plans (EELS `calculate_message_call_gas`)

    Moved here unchanged from the fork Effect modules (which no longer define them) so
    that `Call` can select them by fork; the names are kept: `Evm.CL.ARM64.CallGasSem`
    proves the emitted `_eita_call_gas*` routines equal to them. -/

namespace Evm.Frontier.Vm.Effect

open Evm.Frontier.Vm

/-- `calculate_message_call_gas`'s result as host-visible scalars. -/
structure CallGasPlan where
  /-- Base + per-kind fees, charged to the parent before forwarding. -/
  charge  : Nat
  /-- The forwarded gas, charged to the parent (pre-EIP-150 the whole requested gas). -/
  forward : Nat
  /-- The free 2300 added to the child's gas (never charged to the parent). -/
  stipend : Nat
  deriving Repr, DecidableEq

/-- Frontier (EELS `forks/frontier/vm/gas.py` `calculate_message_call_gas`): base 40, no
    cap — the parent is charged the full `gasArg`. -/
def callGasPlan (chargesValue chargesNewAccount : Bool) (gasArg : Nat) : CallGasPlan :=
  { charge  := Gas.call
      + (if chargesValue then Gas.callValue else 0)
      + (if chargesNewAccount then Gas.newAccount else 0)
    forward := gasArg
    stipend := if chargesValue then Gas.callStipend else 0 }

end Evm.Frontier.Vm.Effect

namespace Evm.TangerineWhistle.Vm.Effect

open Evm.Frontier.Vm

/-- EIP-150 63/64 forwarding cap (EELS `max_message_call_gas`). -/
def capForward (requested available : Nat) : Nat :=
  min requested (available - available / 64)

/-- Tangerine Whistle (EIP-150): base 700 and the 63/64 cap. `avail` is the parent's gas
    after the memory charge, before the base. -/
def callGasPlan (chargesValue chargesNewAccount : Bool) (gasArg avail : Nat) :
    Evm.Frontier.Vm.Effect.CallGasPlan :=
  let charge := Evm.TangerineWhistle.Vm.Gas.call
    + (if chargesValue then Gas.callValue else 0)
    + (if chargesNewAccount then Gas.newAccount else 0)
  { charge  := charge
    forward := capForward gasArg (avail - charge)
    stipend := if chargesValue then Gas.callStipend else 0 }

end Evm.TangerineWhistle.Vm.Effect

namespace Evm.Berlin.Vm.Effect

open Evm.Frontier.Vm

/-- EIP-150 63/64 forwarding cap. -/
def capForward (requested available : Nat) : Nat :=
  min requested (available - available / 64)

/-- EIP-2929: the access replaces TW's flat base. -/
def callBaseCost (isCold : Bool) : Nat :=
  if isCold then Berlin.Vm.Gas.coldAccountAccess else Berlin.Vm.Gas.warmAccess

/-- The Berlin+ plan (same fields as Frontier's). -/
structure CallGasPlan where
  charge  : Nat
  forward : Nat
  stipend : Nat
  deriving Repr, DecidableEq

/-- Berlin+ (EELS `forks/berlin/vm/gas.py` `calculate_message_call_gas`): the access cost,
    the value and new-account fees and EIP-7702's delegate access (`delegatedCost`) are
    charged, the forward capped at 63/64 of what is left. -/
def callGasPlan (isCold chargesValue chargesNewAccount : Bool)
    (delegatedCost gasArg avail : Nat) : CallGasPlan :=
  let charge := callBaseCost isCold
    + (if chargesValue then Gas.callValue else 0)
    + (if chargesNewAccount then Gas.newAccount else 0)
    + delegatedCost
  { charge  := charge
    forward := capForward gasArg (avail - charge)
    stipend := if chargesValue then Gas.callStipend else 0 }

end Evm.Berlin.Vm.Effect

namespace Evm.Frontier.Vm.Call

open Evm.Frontier (State Account)
open Evm.Frontier.Vm
open Evm.Frontier.Vm.Instructions (chargeMemory)
open Evm.Frontier.Vm.PrecompiledContracts (Precompile)

/-- The four opcodes. -/
inductive Kind where
  | call | callcode | delegatecall | staticcall
  deriving DecidableEq, Repr, Inhabited

/-- The fork rules the call family distinguishes. -/
structure Rules where
  eip150  : Bool   -- 63/64 forwarding, base 700
  eip161  : Bool   -- value-gated new-account charge; touched set; RIPEMD-160 exemption
  eip214  : Bool   -- static frames
  eip2929 : Bool   -- warm/cold access
  deriving DecidableEq, Repr

def Rules.ofOrd (k : Nat) : Rules :=
  { eip150 := decide (k ≥ 3), eip161 := decide (k ≥ 4), eip214 := decide (k ≥ 5),
    eip2929 := decide (k ≥ 10) }

/-- EELS `STACK_DEPTH_LIMIT`. -/
def maxDepth : Nat := 1024

/-- EELS `RIPEMD160_ADDRESS`. -/
def ripemd : Evm.Address := Evm.Address.ofNat 3

/-! ## The precompile table of each fork (EELS `precompiled_contracts/mapping.py`) -/

/-- Berlin (EIP-2565): Istanbul's table with MODEXP repriced. -/
def berlinTable (a : Evm.Address) : Option Precompile :=
  if a = Evm.Address.ofNat 0x05 then some Evm.Berlin.Vm.PrecompiledContracts.modexp
  else Evm.Istanbul.Vm.PrecompiledContracts.lookup a

/-- Prague: Cancun's table and EIP-2537's BLS12-381 at 0x0b–0x11. -/
def pragueTable (a : Evm.Address) : Option Precompile :=
  match Evm.Cancun.Vm.PrecompiledContracts.lookup a with
  | some p => some p
  | none => Evm.Prague.Vm.PrecompiledContracts.lookup a

/-- Osaka: Prague's with EIP-7883's MODEXP and EIP-7951's P256VERIFY at 0x100. -/
def osakaTable (a : Evm.Address) : Option Precompile :=
  if a = Evm.Address.ofNat 0x05 then some Evm.Osaka.Vm.PrecompiledContracts.modexp7883
  else if a = Evm.Osaka.Vm.PrecompiledContracts.p256verifyAddress then
    some Evm.Osaka.Vm.PrecompiledContracts.p256verify
  else pragueTable a

/-- The precompile table at fork ordinal `k`. -/
def precompiles (k : Nat) : Evm.Address → Option Precompile :=
  if k ≥ 18 then osakaTable
  else if k ≥ 17 then pragueTable
  else if k ≥ 16 then Evm.Cancun.Vm.PrecompiledContracts.lookup
  else if k ≥ 10 then berlinTable
  else if k ≥ 8 then Evm.Istanbul.Vm.PrecompiledContracts.lookup
  else if k ≥ 5 then Evm.Byzantium.Vm.PrecompiledContracts.lookup
  else Evm.Frontier.Vm.PrecompiledContracts.lookup

/-! ## The pieces -/

/-- The gas plan at the fork's rules. -/
def plan (r : Rules) (cold valueFee newAcct : Bool) (deleg gasArg avail : Nat) :
    Effect.CallGasPlan :=
  if r.eip2929 then
    let p := Evm.Berlin.Vm.Effect.callGasPlan cold valueFee newAcct deleg gasArg avail
    { charge := p.charge, forward := p.forward, stipend := p.stipend }
  else if r.eip150 then Evm.TangerineWhistle.Vm.Effect.callGasPlan valueFee newAcct gasArg avail
  else Effect.callGasPlan valueFee newAcct gasArg

/-- EELS `is_account_dead`: absent, or present and empty. -/
def isDead (s : State) (a : Evm.Address) : Bool :=
  if s.accountExists a then (s.getAccount a).isEmpty else true

/-- EELS `evm.accessed_addresses.add`. -/
def warm (env : Environment) (a : Evm.Address) : Environment :=
  if env.accessedAddresses.contains a then env
  else { env with accessedAddresses := env.accessedAddresses ++ [a] }

/-- EELS `evm.touched_accounts.add`. -/
def touch (env : Environment) (a : Evm.Address) : Environment :=
  if env.touched.contains a then env else { env with touched := env.touched ++ [a] }

/-- EIP-7702 `access_delegation`: the delegate, when delegation is on and `code` is a
    designator. -/
def delegate (env : Environment) (code : Evm.Bytes) : Option Evm.Address :=
  if env.pragueDelegation then Evm.Prague.State.parseDelegation code else none

/-- The current target of the child: the executing account for CALLCODE and
    DELEGATECALL, the popped address otherwise. -/
def target (k : Kind) (self to : Evm.Address) : Evm.Address :=
  match k with
  | .callcode | .delegatecall => self
  | .call | .staticcall => to

/-- `valueFee`: CALL and CALLCODE moving a non-zero value pay CALL_VALUE and give the
    stipend (and must afford the value). -/
def valueFee (k : Kind) (value : Evm.U256) : Bool :=
  decide ((k = .call ∨ k = .callcode) ∧ value ≠ 0)

/-- The new-account charge: a CALL, before EIP-161 to an absent account, from EIP-161
    moving value to a dead one. -/
def newAcct (r : Rules) (k : Kind) (s : State) (to : Evm.Address) (value : Evm.U256) : Bool :=
  decide (k = .call) &&
    (if r.eip161 then decide (value ≠ 0) && isDead s to else !s.accountExists to)

/-- What the opcode hands over after its own part: the frame after the pops and the memory
    charge for both ranges (its gas is what is left after memory), the kind, the popped
    address, value (0 for DELEGATECALL / STATICCALL), requested gas, the input, and the
    output range. -/
structure Native where
  frame  : Evm
  kind   : Kind
  to     : Evm.Address
  value  : Evm.U256
  gasArg : Nat
  input  : Evm.Bytes
  retOff : Nat
  retLen : Nat

def u256ToAddr (x : Evm.U256) : Evm.Address := Evm.Address.ofNat x.toNat

/-- The opcode's part before `start` (the native handler's, in the replay): the pops
    (7 with a value, 6 without), EIP-214's static check (a CALL with value in a static
    frame), the memory charge for the input and output ranges, the input. -/
def native (r : Rules) (k : Kind) (evm : Evm) : Except Exception Native := do
  let (gasArg, addrW, value, argsOff, argsLen, retOff, retLen, s) ←
    if k = .call ∨ k = .callcode then do
      let (a, s) ← Stack.pop evm.stack
      let (b, s) ← Stack.pop s
      let (c, s) ← Stack.pop s
      let (d, s) ← Stack.pop s
      let (e, s) ← Stack.pop s
      let (f, s) ← Stack.pop s
      let (g, s) ← Stack.pop s
      pure (a, b, c, d, e, f, g, s)
    else do
      let (a, s) ← Stack.pop evm.stack
      let (b, s) ← Stack.pop s
      let (d, s) ← Stack.pop s
      let (e, s) ← Stack.pop s
      let (f, s) ← Stack.pop s
      let (g, s) ← Stack.pop s
      pure (a, b, (0 : Evm.U256), d, e, f, g, s)
  if r.eip214 ∧ evm.message.isStatic ∧ k = .call ∧ value ≠ 0 then throw .writeInStaticContext
  let (gasLeft, mem) ← chargeMemory evm.gasLeft evm.memory argsOff.toNat argsLen.toNat
  let (gasLeft, mem) ← chargeMemory gasLeft mem retOff.toNat retLen.toNat
  return { frame := { evm with gasLeft := gasLeft, memory := mem, stack := s }, kind := k,
           to := u256ToAddr addrW, value := value, gasArg := gasArg.toNat,
           input := Evm.Bytes.sliceZeroPad mem argsOff.toNat argsLen.toNat,
           retOff := retOff.toNat, retLen := retLen.toNat }

/-- What happens after the opcode's part. -/
inductive Start where
  /-- An exceptional halt of the caller: the charge (and pre-EIP-150 the forward) does
      not fit. -/
  | halt
  /-- The fail-fast (depth limit, balance below the value): push 0 and continue. -/
  | done (evm : Evm)
  /-- Run the child: the caller as it waits (`parent`), the child's message, the address
      whose precompile (if any) runs — `none` when EIP-7702 disabled precompiles —, and
      the world the child starts in. -/
  | run (parent : Evm) (msg : Message) (pre : Option Evm.Address) (st : State)

/-- The code the child runs and the delegate's access: EELS `access_delegation` (and the
    pre-Prague `get_account(code_address).code`). Read before any write of this call. -/
def codeOf (env : Environment) (to : Evm.Address) : Evm.Bytes :=
  match delegate env (env.state.getAccount to).code with
  | some d => (env.state.getAccount d).code
  | none => (env.state.getAccount to).code

/-- The child's message (its gas is set by `start`): EELS `generic_call`'s `Message` — the
    caller (DELEGATECALL keeps the frame's), the current target, the value (DELEGATECALL
    keeps the frame's, STATICCALL has none), the input, the code (`codeOf`), the depth, the
    static flag (EIP-214). -/
def childMsg (r : Rules) (n : Native) : Message :=
  let evm := n.frame
  let self := evm.message.currentTarget
  let ct := target n.kind self n.to
  { caller := if n.kind = .delegatecall then evm.message.caller else self,
    target := some ct, currentTarget := ct,
    value := match n.kind with
      | .delegatecall => evm.message.value
      | .staticcall => 0
      | _ => n.value,
    data := n.input, code := codeOf evm.env n.to, gas := 0,
    depth := evm.message.depth + 1,
    isStatic := r.eip214 && (decide (n.kind = .staticcall) || evm.message.isStatic) }

/-- `call` / `callcode` / `delegatecall` / `staticcall` from the charge to
    `process_message`: the target's warm-up (EIP-2929), the delegate's (EIP-7702), the
    plan, out of gas, the fail-fast (balance — CALL, CALLCODE —, then the depth in
    `generic_call`), the child's message and world (`touch_account` before EIP-161,
    `move_ether` for a CALL with value). -/
def start (r : Rules) (n : Native) : Start :=
  let evm := n.frame
  let env := evm.env
  let self := evm.message.currentTarget
  let to := n.to
  let cold := r.eip2929 && !env.accessedAddresses.contains to
  let env1 := if r.eip2929 then warm env to else env
  let d := delegate env (env.state.getAccount to).code
  let dcost := match d with
    | some a => if env1.accessedAddresses.contains a then Berlin.Vm.Gas.warmAccess
                else Berlin.Vm.Gas.coldAccountAccess
    | none => 0
  let env2 := match d with
    | some a => warm env1 a
    | none => env1
  let vf := valueFee n.kind n.value
  let p := plan r cold vf (newAcct r n.kind env.state to n.value) dcost n.gasArg evm.gasLeft
  if evm.gasLeft < p.charge + p.forward then .halt
  else
  let g := evm.gasLeft - p.charge - p.forward
  let e0 : Evm := { evm with gasLeft := g, env := env2, returnData := Evm.Bytes.empty }
  if (vf ∧ (env.state.getAccount self).balance.toNat < n.value.toNat) ∨
      evm.message.depth ≥ maxDepth then
    .done { e0 with gasLeft := g + p.forward + p.stipend }
  else
  let ct := target n.kind self to
  let st := if r.eip161 then env2.state else env2.state.touchAccount ct
  let st := if n.kind = .call ∧ n.value ≠ 0 then (st.subBalance self n.value).addBalance to n.value
            else st
  .run e0 { childMsg r n with gas := p.forward + p.stipend } (if d.isSome then none else some to) st

/-- The child frame: the caller's tx environment (with its warm-ups) and the child's
    world. -/
def child (parent : Evm) (msg : Message) (st : State) : Evm :=
  Evm.fresh msg { parent.env with state := st }

/-- `execute_code`: a precompile at the code address (unless delegation disabled them; `pre`
    is the fork's table, read in the caller's environment — the OP-Stack rules are flags there)
    runs on the input with the child's gas — an exceptional halt on failure —, otherwise
    the child frame runs (`runSub`). -/
def runChild (pre : Environment → Evm.Address → Option Precompile) (parent : Evm) (msg : Message)
    (code : Option Evm.Address) (st : State) (runSub : Evm → Except Exception Evm) :
    Except Exception Evm :=
  match code.bind (pre parent.env) with
  | some p =>
    match p msg.data msg.gas with
    | .ok (out, g) => .ok { child parent msg st with gasLeft := g, output := out, halted := true }
    | .error e => .error e
  | none => runSub (child parent msg st)

/-- Push the opcode's result and step past it. -/
def push (evm : Evm) (w : Evm.U256) : Except Exception Evm := do
  let s ← Stack.push evm.stack w
  return { evm with stack := s, pc := evm.pc + 1 }

/-- `incorporate_child_on_error`'s RIPEMD-160 exemption (from EIP-161): 0x03 stays touched
    when the failed child touched it, or when it was the child's target and exists empty. -/
def ripemdKeep (r : Rules) (env : Environment) (ct : Evm.Address) (childTouched : List Evm.Address) :
    Environment :=
  if r.eip161 ∧ (childTouched.contains ripemd ∨
      (ct = ripemd ∧ env.state.accountExists ripemd ∧ (env.state.getAccount ripemd).isEmpty))
  then touch env ripemd else env

/-- `generic_call`'s end: `incorporate_child_on_*`, the return data, the output copied into
    the caller's memory (at most `retLen` bytes), the pushed flag. An exceptional halt keeps
    nothing of the child (its gas is gone); a REVERT keeps nothing but its gas and output;
    a success merges the child's environment and (EIP-161) touches its target when it is
    existing and empty. -/
def resume (r : Rules) (parent : Evm) (ct : Evm.Address) (retOff retLen : Nat)
    (res : Except Exception Evm) : Except Exception Evm :=
  match res with
  | .error _ => push { parent with env := ripemdKeep r parent.env ct [] } 0
  | .ok sub =>
    let mem := Memory.write parent.memory retOff
      (Evm.Bytes.sliceZeroPad sub.output 0 (min retLen sub.output.size))
    if sub.reverted then
      push { parent with env := ripemdKeep r parent.env ct sub.env.touched,
                         gasLeft := parent.gasLeft + sub.gasLeft, memory := mem,
                         returnData := sub.output } 0
    else
      let env := if r.eip161 ∧ sub.env.state.accountExists ct ∧ (sub.env.state.getAccount ct).isEmpty
                 then touch sub.env ct else sub.env
      push { parent with env := env, gasLeft := parent.gasLeft + sub.gasLeft, memory := mem,
                         returnData := sub.output } 1

/-- The whole of the call after the opcode's part, with `pre` the precompile table (in the
    caller's environment) and
    `runSub` the child's run. -/
def run (r : Rules) (pre : Environment → Evm.Address → Option Precompile) (n : Native)
    (runSub : Evm → Except Exception Evm) : Except Exception Evm :=
  match start r n with
  | .halt => .error .outOfGas
  | .done e => push e 0
  | .run p m c st => resume r p m.currentTarget n.retOff n.retLen (runChild pre p m c st runSub)

/-- The opcode, for a fork's step: `native`, then `start`. The continuations build the
    fork's own step result; `yld` gets the waiting caller, the child's message, the
    precompile-eligible address, the child's world and the output range. -/
def opcode {R : Type} (r : Rules) (k : Kind) (evm : Evm)
    (err : Exception → R) (cont : Evm → R)
    (yld : Evm → Message → Option Evm.Address → State → Nat → Nat → R) : R :=
  match native r k evm with
  | .error e => err e
  | .ok n =>
  match start r n with
  | .halt => err .outOfGas
  | .done e =>
    match push e 0 with
    | .error x => err x
    | .ok e' => cont e'
  | .run p m c st => yld p m c st n.retOff n.retLen

end Evm.Frontier.Vm.Call
