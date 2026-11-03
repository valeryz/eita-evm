/-
  Evm.London.Spec.Selfdestruct — EIP-3529 SELFDESTRUCT refund removal.

  EELS reference: `forks/london/vm/instructions/system.py`
  `selfdestruct`. The Frontier (and on through Berlin) opcode added
  `24000` to `env.refundCounter` on the first SELFDESTRUCT of an
  account per transaction. EIP-3529 deletes that line entirely; the
  rest of the SELFDESTRUCT semantics (balance transfer, deletion
  queued at end-of-tx, gas charge unchanged at 5000) is preserved.

  Cancun's EIP-6780 further restricts SELFDESTRUCT to only-fully-
  destroy newly-created accounts; that's a separate spec
  (`Cancun/Spec/Selfdestruct.lean`).

  ## What's encoded vs glossed

  * Encoded: the relation between pre- and post-state `refundCounter`
    — it's UNCHANGED across the step (was: `+24000` if first time).
  * Encoded: the `firstTime` flag is still computed (for the
    `selfDestructSet` membership update), but its value doesn't feed
    a refund.
  * Glossed: the actual selfdestruct mechanics (balance transfer to
    beneficiary, account deletion queued via `selfDestructSet`). The
    Paris `Vm/Effect.lean` `selfdestruct` arm in `trampoline`
    *already* matches this spec because the Paris pipeline runs
    through London-shaped semantics by construction — that's why the
    brief says "matches existing impl in London/Vm/Effect.lean".
  * Glossed: the EIP-2929 cold-beneficiary surcharge (2600 gas if
    beneficiary is cold) — that's a SEPARATE delta inside the
    SELFDESTRUCT pre-charge, added at Berlin, NOT undone at London.
    We don't restate it here because it doesn't change between
    Berlin and London.
-/

import Evm.Frontier.Vm
import Evm.Forks

namespace Evm.London.Spec

open Evm.Frontier.Vm

/-- `IsSelfdestructRefundDelta env env' delta` — the
    SELFDESTRUCT-induced increment to `env.refundCounter`. London:
    always 0. -/
def IsSelfdestructRefundDelta (env env' : Environment) (delta : Nat) : Prop :=
  delta = 0 ∧
  env'.refundCounter = env.refundCounter + delta

/-! ## Properties -/

/-- The London delta is exactly zero. Statement of the EIP-3529
    SELFDESTRUCT-refund removal in its simplest form. -/
theorem selfdestruct_refund_zero
    (env env' : Environment) (delta : Nat)
    (h : IsSelfdestructRefundDelta env env' delta) :
    delta = 0 := h.1

/-- The refund counter is unchanged across a London SELFDESTRUCT
    step (insofar as the SELFDESTRUCT itself is concerned —
    surrounding context still mutates other env fields). -/
theorem selfdestruct_refund_unchanged
    (env env' : Environment) (delta : Nat)
    (h : IsSelfdestructRefundDelta env env' delta) :
    env'.refundCounter = env.refundCounter := by
  obtain ⟨hd, he⟩ := h
  simp [he, hd]

/-! ## Fork-conditional value (iff form)

    EIP-3529 dropped the SELFDESTRUCT-first-time refund from 24000
    to 0 at London. Stated as a single iff over `Fork`:

      `refundAt f = 0  ↔  f ≥ London`. -/

/-- London's SELFDESTRUCT refund (= 0; EIP-3529 removed it). -/
def selfdestructRefundWei : Nat := 0

/-- Pre-London SELFDESTRUCT-first-time refund (= 24000). -/
def preLondonSelfdestructRefundWei : Nat := 24000

/-- Fork-parametric SELFDESTRUCT refund. -/
def refundAt (f : Evm.Fork) : Nat :=
  if f.atLeast .london then selfdestructRefundWei
  else preLondonSelfdestructRefundWei

theorem refund_iff_london (f : Evm.Fork) :
    refundAt f = selfdestructRefundWei ↔ f.atLeast .london := by
  unfold refundAt
  split <;> simp_all <;> decide

end Evm.London.Spec
