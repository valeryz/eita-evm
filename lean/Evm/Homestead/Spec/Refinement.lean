/-
  Evm.Homestead.Spec.Refinement — proofs that the Homestead executable
  refines the Homestead Spec relations.

  Pattern: per the Frontier/Spec/Refinement.lean template, each
  refinement is a soundness theorem of the shape

    ∀ inputs, executable inputs = .ok post → IsXxxStep inputs post

  Homestead's state-machine delta here is EIP-2's CREATE deposit
  (Spec: `IsCreateDepositRevert`, `IsCreateDepositOk`, `CreateStep.lean`).
  The executable is `Evm.Frontier.Vm.Create` at `Rules.ofOrd 1` — the
  rules `Evm.Homestead.Vm.Effect` runs CREATE with (`opcode` for the
  yield, `resume` for the merge). Both are pure functions, so both
  branches are closed here, not left as `_shape` placeholders.

  (Until 2026-11-02 this module held two `P → P` `_shape` theorems; they
  stopped elaborating when `IsCreateDepositRevert` gained its
  `sender`/`senderAccNonce` arguments, and nothing imported the module.)
-/

import Evm.Homestead.Spec.CreateStep
import Evm.Frontier.Vm.Create

namespace Evm.Homestead.Spec.Refinement

open Evm.Frontier.Vm
open Evm.Homestead.Spec

/-- The CREATE rules the Homestead step runs with (`Homestead.Vm.Effect`). -/
abbrev rules : Create.Rules := Create.Rules.ofOrd 1

/-! ## EIP-2 deposit success

    `resume` on a cleanly halted, non-reverted child with enough gas for
    the deposit is `IsCreateDepositOk`, with the parent-side artefacts
    the trampoline carries (gas, memory, stack, pc) those of the waiting
    parent frame. `halted` is the child run's own postcondition, not
    something `resume` inspects, so it is a hypothesis. -/
theorem createDepositOk_sound (parent subEvm parent' : Evm) (newAddr : Evm.Address)
    (gasLeft : Nat) (mem : Memory) (s : Stack) (pc : Nat)
    (hg : gasLeft = parent.gasLeft) (hm : mem = parent.memory)
    (hs' : s = parent.stack) (hpc : pc = parent.pc)
    (hres : Create.resume rules parent newAddr (.ok subEvm) = .ok parent')
    (hrev : ¬ subEvm.reverted) (hhalt : subEvm.halted)
    (hgas : subEvm.gasLeft ≥ depositCost subEvm.output) :
    IsCreateDepositOk parent subEvm newAddr gasLeft mem s pc parent' := by
  subst hg hm hs' hpc
  have hlt : ¬ subEvm.gasLeft < Gas.codeDeposit * subEvm.output.size := by
    unfold depositCost at hgas; exact Nat.not_lt.mpr hgas
  simp only [Create.resume, rules, Create.Rules.ofOrd, hrev, hlt, Bool.false_eq_true,
    ite_false, decide_eq_true_eq, Create.push, Stack.push] at hres
  by_cases hs : parent.stack.length ≥ stackLimit
  · simp [hs] at hres; cases hres
  · simp only [hs, ite_false] at hres
    refine ⟨hrev, hhalt, hgas, by omega, ?_⟩
    cases hres
    rfl

/-! ## EIP-2 deposit failure

    The revert relation is stated against the frame BEFORE the CREATE's
    nonce bump (`parent`, with `senderAccNonce` the sender's nonce then):
    its post-state is that frame's world with only the bump kept. The
    executable bumps the nonce in `start` and hands `resume` the bumped
    waiting frame, so the theorem runs the two together, as `Create.run`
    does: whatever `start` yields, `resume` on a deposit-short child
    lands on `IsCreateDepositRevert` of the pre-bump frame, its sender and
    nonce, and the gas left after forwarding (the forwarded gas is
    consumed). -/
set_option backward.isDefEq.respectTransparency false in
theorem createDepositRevert_sound (evm subEvm parent' : Evm) (value : Evm.U256)
    (initCode : Evm.Bytes) (newAddr : Evm.Address) (base : Nat)
    (p : Evm) (m : Message) (st : Evm.Frontier.State)
    (hstart : Create.start rules evm value initCode newAddr base = .run p m st)
    (hres : Create.resume rules p newAddr (.ok subEvm) = .ok parent')
    (sender : Evm.Address) (senderAccNonce gasLeft : Nat) (mem : Memory) (s : Stack) (pc : Nat)
    (hsender : sender = evm.message.currentTarget)
    (hnonce : senderAccNonce = (evm.env.state.getAccount sender).nonce)
    (hg : gasLeft = p.gasLeft) (hm : mem = evm.memory) (hs' : s = evm.stack) (hpc : pc = evm.pc)
    (hrev : ¬ subEvm.reverted) (hhalt : subEvm.halted)
    (hgas : subEvm.gasLeft < depositCost subEvm.output) :
    IsCreateDepositRevert evm subEvm sender senderAccNonce gasLeft mem s pc parent' := by
  subst hsender hnonce hg hm hs' hpc
  have hlt : subEvm.gasLeft < Gas.codeDeposit * subEvm.output.size := by
    unfold depositCost at hgas; exact hgas
  simp only [Create.start, rules, Create.Rules.ofOrd] at hstart
  split at hstart
  · cases hstart
  split at hstart
  · simp at *
  split at hstart
  · cases hstart
  split at hstart
  · cases hstart
  cases hstart
  simp only [Create.resume, Create.Rules.ofOrd, hrev, hlt, Bool.false_eq_true,
    ite_false, ite_true, decide_eq_true_eq, Create.push, Stack.push] at hres
  by_cases hs : evm.stack.length ≥ stackLimit
  · simp [hs, Functor.map, Except.map] at hres
  · simp only [hs, ite_false] at hres
    refine ⟨hrev, hhalt, hgas, by omega, ?_⟩
    cases hres
    simp

end Evm.Homestead.Spec.Refinement
