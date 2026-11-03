import Evm.CL.EffectIR

/-! # CL/EffectCall — `cb-call`, derived (docs/effect-layer-derivation.md §4.8)

The CALL / CALLCODE / DELEGATECALL / STATICCALL host callback as one `EffectIR` term for
every fork, proved in `Evm.CL.EffectCallProof` (`call_refines`) against every fork's call —
the one definition `Evm.Frontier.Vm.Call.run` that each fork's `doCall`… and `.callLike`
arm are (`call_binding`) — and emitted as `spec-call-effect`.

**What is the callback's part.** The native CALL-family handler pops the operands (7, or 6
without a value — then the value is 0), raises EIP-214's static violation (a CALL with a
value in a static frame), charges the memory expansion of both ranges, and calls the
callback with the target, value, input, requested gas (saturated at 2^64 − 1) and the gas
left (`avail`). After it, the handler installs the callback's return data, copies at most
`retLen` bytes of it into memory, pushes the flag and charges the gas used. The wrapper
(`cb-call`) reads the operands and resolves EIP-7702's designator (`deleg`, when delegation
is on — `*prague-delegation*`, the Lean `env.pragueDelegation`). Everything else is the
term, which returns the gas used, the flag and the return data:

* EIP-2929's warm-up of the target (Berlin+) and of the delegate;
* the plan (`callPlan`: the access, CALL_VALUE, the new-account charge — before EIP-161 a
  CALL to an absent account, from it a CALL moving value to a dead one —, the delegate's
  access, EIP-150's 63/64), out of gas when the charge and the forward do not fit;
* the save point; (Arc's frame-init veto of a value-bearing CALL; outside the theorem);
* the fail-fast — balance below the value (CALL, CALLCODE), depth limit — charging the
  charge net of the stipend;
* the child's world: before EIP-161 the current target comes into existence, a CALL moves
  its value (a transfer fact at the child's depth);
* inside the observed call frame: (a chain precompile, Arc's 0x1800…, outside the
  theorem), the fork's precompile at the target unless EIP-7702 disabled them, or the child
  frame (`runCall`, the seam: the native interpreter);
* its end: an exceptional halt rolls the child back and its gas is lost; a REVERT rolls it
  back and returns its gas and output; a success keeps it and returns its gas and output;
  from EIP-161 a success touches the current target if it is existing and empty, and a
  failure keeps 0x03 (RIPEMD-160) touched when it was the target and exists empty or (a
  REVERT) the child touched it — `incorporate_child_on_*`. -/

namespace Evm.CL.EffectCall

open Evm.CL.EffectIR

abbrev self  : AExp := .var "self"
abbrev to    : AExp := .var "to"
abbrev dlg   : AExp := .var "deleg"
abbrev ct    : AExp := .var "ct"
abbrev rip   : AExp := .lit 3
abbrev value : WExp := .var "value"
abbrev charge : GExp := .var "charge"
abbrev fwd   : GExp := .var "fwd"
abbrev stip  : GExp := .var "stip"

/-- The child's gas: the forward and the stipend. -/
def fwdAll : GExp := .add fwd stip

/-- What the caller pays when the child returns `g` gas: charge + forward − (g − stipend). -/
def used (r : String) : GExp := .sub (.sub (.add charge fwdAll) (.childGas r)) stip

/-- `incorporate_child_on_error`'s second leg: the target was 0x03 and it exists empty. -/
def rule2 : BExp := .and (.addrEq ct rip) (.and (.present rip) (.dead rip))

/-- The end of the child run `r`. -/
def finish : Stmt :=
  .ite (.childErr "r")
    (.seq (.rollback "snap") <| .seq (.ite rule2 (.touch rip) .skip) <|
      .seq (.charge (.add charge fwd)) (.ret .zero)) <|
  .ite (.childRev "r")
    (.letB "rt" (.touchedHas rip) <|
      .seq (.rollback "snap") <| .seq (.ite (.or (.var "rt") rule2) (.touch rip) .skip) <|
      .seq (.charge (used "r")) <| .seq (.retData "r") (.ret .zero)) <|
  .seq (.ite (.and (.present ct) (.dead ct)) (.touch ct) .skip) <|
  .seq (.charge (used "r")) <| .seq (.retData "r") (.ret (.lit 1))

/-- The child: (a chain precompile — Arc —), the fork's precompile at the target unless
    EIP-7702 disabled them, or the child frame. -/
def dispatch : Stmt :=
  .chainCall to fwdAll charge stip "snap" <|
  .ite (.and (.not (.var "hasdeleg")) (.pre to))
    (.runPre to fwdAll "r" finish)
    (.runCall fwdAll "r" finish)

/-- A CALL with a value moves it: the caller's balance down, the target's up, a transfer
    fact at the child's depth (Arc logs it). -/
def transfer : Stmt :=
  .ite (.and (.kindEq 0) (.pos value))
    (.seq (.chainLog self to value) <|
     .seq (.setBalance self (.sub (.balance self) value)) <|
     .seq (.credit to value) (.transferFact 1 self to value true)) .skip

/-- Past the fail-fast: the child's world (`touch_account` before EIP-161, the value), then
    the child inside its observed frame. -/
def proceed : Stmt :=
  .seq (.ite (.forkGe 4) .skip (.markPresent ct)) <|
  .seq transfer (.callRow self to value fwdAll charge stip dispatch)

/-- After the plan: out of gas, the save point, (Arc's veto), the fail-fast, the child. -/
def afterPlan : Stmt :=
  .iteG (.var "avail") (.add charge fwd) (.charge (.add charge fwd)) <|
  .save "snap" <|
  .chainCallVeto (.and (.kindEq 0) (.pos value)) self to value "v"
    (.seq (.charge (.sub charge stip)) <| .seq (.retData "v") (.ret .zero)) <|
  .ite (.or (.and (.var "vf") (.wlt (.balance self) value)) (.var "deep"))
    (.seq (.charge (.sub charge stip)) (.ret .zero))
    proceed

/-- The callback. Inputs: `kind`, `self` (the executing account), `to` (the popped
    address), `deleg`/`hasdeleg` (EIP-7702's delegate), `value`, `gasarg`, `avail`, `deep`
    (depth limit reached), the input (`input-ptr`, `input-len`) and `static` (for a chain
    precompile); returns the gas used, the flag and the return data. -/
def term : Stmt :=
  .seq (.fault to) <|
  .letA "ct" (.or (.kindEq 1) (.kindEq 2)) self to <|
  .warm (.forkGe 10) to "cold" <|
  .seq (.ite (.var "hasdeleg") (.fault dlg) .skip) <|
  .warm (.var "hasdeleg") dlg "dcold" <|
  .letB "vf" (.and (.or (.kindEq 0) (.kindEq 1)) (.pos value)) <|
  .letB "na" (.and (.kindEq 0)
      (.or (.and (.forkGe 4) (.and (.pos value) (.dead to)))
           (.and (.not (.forkGe 4)) (.not (.present to))))) <|
  .callPlan (.var "cold") (.var "vf") (.var "na")
    (.ite (.var "hasdeleg") (.ite (.var "dcold") (.lit 2600) (.lit 100)) (.lit 0))
    (.var "gasarg") (.var "avail") afterPlan

def params : List String :=
  ["kind", "self", "to", "deleg", "hasdeleg", "value", "gasarg", "avail", "deep", "input-ptr",
   "input-len", "static"]

def termCL : String := Stmt.toDefunChild "spec-call-effect" params term

end Evm.CL.EffectCall
