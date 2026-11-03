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

/-! ## Gas cost

    Cancun SELFDESTRUCT cost is unchanged from Berlin:
        5000 + cold-access (2600 if beneficiary is cold) +
        new-account-cost (25000 if beneficiary doesn't exist and
        self has non-zero balance).
    The EIP-3529 (London) refund-removal still applies — no refund.

    We don't re-state the full gas formula here; the predicate just
    pins `gas ≥ gasMin` for the static minimum and lets the impl
    add the cold-access / new-account dynamics.

    EELS: `forks/cancun/vm/gas.py::GAS_SELF_DESTRUCT = 5000`. -/
def gasSelfdestructBase : Nat := 5000

/-! ## The relation

    SELFDESTRUCT pops the beneficiary address from the stack and
    halts the frame. We spec the four observable effects (balance
    transfer, optional account deletion, selfDestructSet update,
    halt flag) directly. -/

/-- The Cancun SELFDESTRUCT step relation. `evm.message.isStatic = false`
    is a precondition (write-in-static-context check happens first). -/
def IsSelfdestructStep (evm evm' : Evm) : Prop :=
  ∃ benWord rest,
    evm.stack = benWord :: rest ∧
    evm.message.isStatic = false ∧
    evm.gasLeft ≥ gasSelfdestructBase ∧
    let beneficiary : Evm.Address := Evm.Address.ofNat benWord.toNat
    let self     := evm.message.currentTarget
    let selfBal  := evm.env.state.getBalance self
    let createdHere := evm.env.createdAccounts.contains self
    -- Effect-1: balance transfer.
    --
    -- Three sub-cases:
    --   (a) createdHere → standard "add to beneficiary, zero self"
    --       (self might be the beneficiary; balance is then BURNT because
    --       the account is deleted in Effect-2).
    --   (b) ¬createdHere ∧ self = beneficiary → NO-OP. EIP-6780
    --       preserves self.balance because EELS effectively does
    --       "set originator 0 then add to beneficiary"; when those
    --       are the same account, the addition follows the zeroing
    --       so balance is preserved. Reentrant SELFDESTRUCT-to-self
    --       (`reentrencySuicide`) relies on this.
    --   (c) ¬createdHere ∧ self ≠ beneficiary → "add to beneficiary,
    --       zero self".
    let stCleared :=
      if ¬ createdHere ∧ beneficiary = self then
        evm.env.state
      else
        let stAfterTransfer := evm.env.state.addBalance beneficiary selfBal
        stAfterTransfer.setAccount self
          { (stAfterTransfer.getAccount self) with balance := 0 }
    -- Effect-2: EIP-6780 branch — full delete only if CREATEd this tx.
    let stFinal :=
      if createdHere then stCleared.deleteAccount self
      else stCleared
    -- Effect-3: track in selfDestructSet (idempotent; first-time only).
    let firstTime := ¬ evm.env.selfDestructSet.contains self
    let sdSet :=
      if firstTime then evm.env.selfDestructSet ++ [self]
      else evm.env.selfDestructSet
    evm' = { evm with
      stack          := rest,
      gasLeft        := evm.gasLeft - gasSelfdestructBase,
      halted         := true,
      env            := { evm.env with
        state           := stFinal,
        selfDestructSet := sdSet },
      pc             := evm.pc }

/-! ## Invariants

    The most important EIP-6780 property: an address that was NOT
    CREATEd in this transaction RETAINS its code and storage after
    SELFDESTRUCT — only the balance moves. -/

/-- EIP-6780 core property: if self was not CREATEd this tx, its
    account is not deleted from state. -/
theorem selfdestruct_preserves_account_when_not_created
    (evm evm' : Evm) (h : IsSelfdestructStep evm evm')
    (notCreated : ¬ evm.env.createdAccounts.contains evm.message.currentTarget) :
    evm'.env.state.accountExists evm.message.currentTarget = true ∨
    -- The case where the account was already absent (so accountExists
    -- was false to begin with) — we don't *create* anything either.
    evm.env.state.accountExists evm.message.currentTarget = false := by
  obtain ⟨_, _, _, _, _, hEvm⟩ := h
  -- With `notCreated`, `stFinal = stCleared` (no deleteAccount), and
  -- `stCleared` is either `evm.env.state` (the self=beneficiary
  -- no-op branch) or `(state.addBalance ben _).setAccount self {..}`
  -- (every other case). In every branch, the resulting state's
  -- accountExists on self is `true` iff it was `true` before — the
  -- only operations are addBalance (preserves accountExists) and
  -- setAccount self (FORCES accountExists self = true by prepending
  -- self to the accounts list). So:
  --   * if pre-state had self, post-state has self  → left disjunct
  --   * if pre-state lacked self:
  --       - same-beneficiary branch: post-state also lacks self → right
  --       - other branch: setAccount inserts self → left
  -- The two-disjunct form lets us avoid casing further.
  by_cases hExists : evm.env.state.accountExists evm.message.currentTarget = true
  · left
    -- Pre-state has self. Show post-state has self too.
    rw [hEvm]
    have hNot : evm.env.createdAccounts.contains evm.message.currentTarget = false := by
      simpa using notCreated
    simp only [hNot, Bool.false_eq_true, if_false]
    -- Inside stCleared: split on the inner branch.
    split
    · -- Branch where stCleared = evm.env.state (the same-beneficiary
      -- self-no-op case). Accounts list unchanged → existence preserved.
      exact hExists
    · -- Branch where stCleared = (addBalance _).setAccount self {…}.
      -- `setAccount self _` prepends `(self, _)` to the accounts list,
      -- forcing `accountExists self = true`.
      unfold Evm.Frontier.State.accountExists Evm.Frontier.State.setAccount
      simp
  · right
    -- accountExists was already false.
    simpa using hExists

/-- Pre-Cancun behaviour (full destroy on every SELFDESTRUCT) is
    recovered when `evm.env.createdAccounts` happens to contain
    `self`. This means: importing Pre-Cancun's `IsSelfdestructStep`
    is a STRICT specialisation of this one. -/
theorem selfdestruct_full_destroy_when_created
    (evm evm' : Evm) (h : IsSelfdestructStep evm evm')
    (created : evm.env.createdAccounts.contains evm.message.currentTarget) :
    evm'.env.state.accountExists evm.message.currentTarget = false := by
  obtain ⟨_, _, _, _, _, hEvm⟩ := h
  rw [hEvm]
  -- `stFinal` is built by the `if createdHere then stCleared.deleteAccount
  -- self else stCleared`. With `created : createdAccounts.contains self`,
  -- we're in the `then` branch ⇒ `stFinal = _ .deleteAccount self`.
  simp only [created, if_true]
  -- Now goal: (something.deleteAccount self).accountExists self = false.
  -- After deleteAccount, accounts has been filtered (≠ self), so the
  -- find? for self returns none, and isSome → false.
  unfold Evm.Frontier.State.accountExists Evm.Frontier.State.deleteAccount
  simp [List.find?_filter]

end Evm.Cancun.Spec
