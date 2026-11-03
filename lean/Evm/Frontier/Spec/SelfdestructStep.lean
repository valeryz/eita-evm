/-
  Evm.Frontier.Spec.SelfdestructStep — SELFDESTRUCT (0xff) relations
  for Frontier-era semantics.

  EELS reference: `selfdestruct` in
  `forks/frontier/vm/instructions/system.py` (line 345).

  Unlike CALL/CREATE, SELFDESTRUCT spawns no sub-frame: the yield
  exists only so the trampoline (which owns the shared environment)
  applies the state effects. Two relations:

    1. **entry** (`IsSelfdestructEntry`) — what `doSelfdestruct`
       guarantees at the yield point. It pops the beneficiary word
       (line 351) and charges GAS_ZERO (line 372, a 0-charge no-op),
       so the frame is yielded UNCHANGED — stack still unpopped,
       harmless because the frame halts and never resumes into its
       own code.
    2. **apply** (`IsSelfdestructApply`) — the trampoline-side
       semantics (the `.selfdestruct` arm of `handleYield`), EELS
       lines 363-397:
         * refund GAS_SELF_DESTRUCT_REFUND (24000) only the FIRST
           time this originator self-destructs (lines 363-370; the
           shared-env `selfDestructSet` plays the role of EELS'
           walk up the `accounts_to_delete` chain);
         * move the originator's whole balance to the beneficiary
           (line 383) and zero the originator AFTER (line 391) — the
           order makes beneficiary == originator end at 0, not 2×;
         * append the originator to the destruct set (line 394),
           again only the first time;
         * halt the frame (line 397) — folded in here from
           `resumeSelfdestruct`.

  The `isStatic = false` precondition mirrors `doSelfdestruct`'s
  guard; it belongs to Byzantium (EIP-214) and is vacuous in
  Frontier, where no message is ever static.
-/

import Evm.Frontier.Vm

namespace Evm.Frontier.Spec

open Evm.Frontier.Vm

/-- `doSelfdestruct`'s yield point: beneficiary word on top of the
    stack, not static, frame passed through unchanged. -/
def IsSelfdestructEntry (evm frame : Evm) (beneficiary : Evm.Address) :
    Prop :=
  ∃ (bW : Evm.U256) (rest : Stack),
    evm.stack = bW :: rest ∧
    beneficiary = Evm.Address.ofNat bW.toNat ∧
    evm.message.isStatic = false ∧
    frame = evm

/-- The trampoline's SELFDESTRUCT effect on the yielded frame:
    first-time-gated refund + destruct-set append, balance moved to
    the beneficiary then originator zeroed, frame halted. -/
def IsSelfdestructApply (frame : Evm) (beneficiary : Evm.Address)
    (frame' : Evm) : Prop :=
  let self := frame.message.currentTarget
  let balance := frame.env.state.getBalance self
  let st := frame.env.state.addBalance beneficiary balance
  let st := st.setAccount self { (st.getAccount self) with balance := 0 }
  let firstTime := ¬ frame.env.selfDestructSet.contains self
  let refund := if firstTime then Gas.selfDestructRefund else 0
  frame' = { frame with
    env := { frame.env with
      state := st,
      selfDestructSet :=
        if firstTime then frame.env.selfDestructSet ++ [self]
        else frame.env.selfDestructSet,
      refundCounter := frame.env.refundCounter + refund },
    halted := true }

/-- SELFDESTRUCT as a single spec step: entry ∘ apply fused, the
    semantics of the total `Vm.selfdestruct` handler that `step1`
    wires to 0xff (the frame never resumes, so the two-phase split
    collapses). Like the EELS handler, the stack is NOT popped in
    the result — the beneficiary word is only read; harmless since
    the frame halts. -/
def IsSelfdestructStep (evm evm' : Evm) : Prop :=
  ∃ (bW : Evm.U256) (rest : Stack),
    evm.stack = bW :: rest ∧
    evm.message.isStatic = false ∧
    IsSelfdestructApply evm (Evm.Address.ofNat bW.toNat) evm'

end Evm.Frontier.Spec
