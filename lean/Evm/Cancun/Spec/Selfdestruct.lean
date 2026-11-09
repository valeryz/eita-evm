/-
  Evm.Cancun.Spec.Selfdestruct — EIP-6780 same-tx-only destruction.

  EELS reference: `forks/cancun/vm/instructions/system.py`
  `selfdestruct`. The key delta vs. Shanghai is:

      if originator in evm.created_accounts:
          # full destroy: balance transfer + account deletion
          ...delete...
      else:
          # only balance transfer; account survives
          ...just credit beneficiary, then set self.balance = 0

  Rationale (EIP-6780 abstract): preserves the property that an
  address's code is immutable once committed, even across SELFDESTRUCT,
  EXCEPT for the within-tx CREATE→SELFDESTRUCT pattern (which was
  used to enable runtime-deployed clear-storage tricks).

  Three observable post-state branches, all charged the same gas:

    1. self ∈ createdAccounts (CREATEd in this tx):
        * transfer balance → beneficiary
        * delete self entirely (account + storage)
        * mark self in selfDestructSet (end-of-tx sweep is a no-op
          for already-deleted accounts, but the sweep idempotency
          is what we want).

    2. self ∉ createdAccounts AND beneficiary ≠ self:
        * transfer balance → beneficiary
        * set self.balance = 0
        * do NOT delete self; do NOT mark in selfDestructSet (no
          refund anymore — EIP-3529 removed it at London — so the
          set membership doesn't matter at Cancun).

    3. self ∉ createdAccounts AND beneficiary = self:
        * effectively self-transfer: balance stays put
        * set self.balance = 0 then add it back to self
        * net: no balance change, no deletion.

  In all branches, the call HALTS.

  Inheritance: applies unchanged at Prague.
-/

import Evm.Frontier.Vm

namespace Evm.Cancun.Spec

open Evm.Frontier (State)
open Evm.Frontier.Vm

/-! ## Gas cost (EELS `forks/cancun/vm/instructions/system.py::selfdestruct` 521-536)

        OPCODE_SELFDESTRUCT_BASE (5000)
      + COLD_ACCOUNT_ACCESS (2600)          if the beneficiary is cold (then warmed)
      + OPCODE_SELFDESTRUCT_NEW_ACCOUNT (25000)
                                            if the beneficiary is not alive
                                            (EIP-161: absent or empty) and the
                                            originator's balance is non-zero.

    No refund (EIP-3529, London). -/

def gasSelfdestructBase : Nat := 5000
def gasColdAccountAccess : Nat := 2600
def gasSelfdestructNewAccount : Nat := 25000

/-! ## The relation

    EELS `selfdestruct` 508-564: pop the beneficiary (`to_address_masked`), charge,
    static check, `move_ether(originator → beneficiary, balance)`, and only if the
    originator was created in this tx (EIP-6780): zero its balance (burning it when it
    is its own beneficiary) and add it to `accounts_to_delete` — the deletion itself
    happens at the end of the tx (here `selfDestructSet`, swept by the tx epilogue).
    `move_ether`'s `modify_state` destroys an account it leaves empty; a zero-value
    transfer to an absent beneficiary therefore leaves the world as it was, and the
    beneficiary is touched (`touched`, EIP-161's end-of-tx sweep). The frame halts.

    Restated 2026-11-09: this relation charged only the 5000 base (no cold surcharge,
    no new-account cost, no warming), deleted the account immediately instead of
    queueing it, and moved zero value into absent beneficiaries. -/

/-- The Cancun SELFDESTRUCT step relation. -/
def IsSelfdestructStep (evm evm' : Evm) : Prop :=
  ∃ benWord rest,
    evm.stack = benWord :: rest ∧
    evm.message.isStatic = false ∧
    let beneficiary : Evm.Address := Evm.Address.ofNat benWord.toNat
    let self     := evm.message.currentTarget
    let st       := evm.env.state
    let selfBal  := st.getBalance self
    let createdHere := evm.env.createdAccounts.contains self
    let cold     := ¬ evm.env.accessedAddresses.contains beneficiary
    let alive    := st.accountExists beneficiary ∧ ¬ (st.getAccount beneficiary).isEmpty
    let cost     := gasSelfdestructBase + (if selfBal ≠ 0 ∧ ¬ alive then gasSelfdestructNewAccount else 0)
                    + (if cold then gasColdAccountAccess else 0)
    evm.gasLeft ≥ cost ∧
    -- move_ether, then (created only) zero the originator: the originator ends at
    -- balance 0 except when it is its own beneficiary and survives.
    let stFinal :=
      if ¬ createdHere ∧ beneficiary = self then st
      else
        let moved := if selfBal = 0 ∧ ¬ st.accountExists beneficiary then st
                     else st.addBalance beneficiary selfBal
        moved.setAccount self { (moved.getAccount self) with balance := 0 }
    evm' = { evm with
      stack          := rest,
      gasLeft        := evm.gasLeft - cost,
      halted         := true,
      env            := { evm.env with
        state             := stFinal,
        accessedAddresses :=
          if cold then evm.env.accessedAddresses ++ [beneficiary] else evm.env.accessedAddresses,
        touched           :=
          if evm.env.touched.contains beneficiary then evm.env.touched
          else evm.env.touched ++ [beneficiary],
        selfDestructSet   :=
          if createdHere ∧ ¬ evm.env.selfDestructSet.contains self
          then evm.env.selfDestructSet ++ [self] else evm.env.selfDestructSet } }

/-! ## Invariants -/

/-- EIP-6780: a SELFDESTRUCT of an account not created in this tx never queues it for
    deletion. -/
theorem selfdestruct_not_queued_when_not_created
    (evm evm' : Evm) (h : IsSelfdestructStep evm evm')
    (notCreated : ¬ evm.env.createdAccounts.contains evm.message.currentTarget) :
    evm'.env.selfDestructSet = evm.env.selfDestructSet := by
  obtain ⟨_, _, _, _, _, hEvm⟩ := h
  subst hEvm
  have nc : evm.message.currentTarget ∉ evm.env.createdAccounts := by simpa using notCreated
  simp [nc]

/-- A SELFDESTRUCT of an account created in this tx queues it for the end-of-tx
    deletion (EELS `evm.accounts_to_delete.add(originator)`). -/
theorem selfdestruct_queued_when_created
    (evm evm' : Evm) (h : IsSelfdestructStep evm evm')
    (created : evm.env.createdAccounts.contains evm.message.currentTarget) :
    evm.message.currentTarget ∈ evm'.env.selfDestructSet := by
  obtain ⟨_, _, _, _, _, hEvm⟩ := h
  subst hEvm
  have c : evm.message.currentTarget ∈ evm.env.createdAccounts := by simpa using created
  by_cases hm : evm.message.currentTarget ∈ evm.env.selfDestructSet
  · simp [c, hm]
  · simp [c, hm]

end Evm.Cancun.Spec
