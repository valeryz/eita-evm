/-
  Evm.Frontier.Spec.Invariants — high-value properties any correct
  EVM implementation must satisfy.

  These are the *bug-catcher* clauses of the spec. They're stated as
  `∀` theorems against the step relation, not against any particular
  executable. An implementation can satisfy the per-opcode spec but
  miss one of these invariants — for instance, accidentally letting
  gas go negative in some edge case — and these theorems would
  catch it the moment refinement is attempted.

  Three invariants in this drop:
    1. Gas monotonicity — every step decreases gasLeft (or halts).
    2. Static-context exclusion — state-mutating opcodes in a
       static frame raise an exception.
    3. Ether conservation — total ether is preserved by every
       sub-frame's transition (modulo block reward / refunds, which
       only happen at the tx/block level).

  All theorems here are stubbed with `sorry` initially. The point
  is to nail down the *statement* — the proof obligation. As the
  spec relations and refinement proofs are filled in, these
  invariants get discharged.
-/

import Evm.Frontier.Vm
import Evm.Frontier.Spec.Step

namespace Evm.Frontier.Spec

open Evm.Frontier.Vm

/-! ## Auxiliary: total ether held by an account / state

    Total ether = sum of all account balances. SELFDESTRUCT
    deletions move balance to the beneficiary, so total is
    preserved. Tx-level operations (block reward, miner gas
    payout) add to total. -/

end Evm.Frontier.Spec

namespace Evm.Frontier.Account
def ether (a : Evm.Frontier.Account) : Nat := a.balance.toNat
end Evm.Frontier.Account

namespace Evm.Frontier.State
def totalEther (s : Evm.Frontier.State) : Nat :=
  s.accounts.foldl (fun acc (_, a) => acc + a.ether) 0
end Evm.Frontier.State

namespace Evm.Frontier.Spec

open Evm.Frontier.Vm

/-! ## Invariant 1: Gas monotonicity

    Every step either halts the frame or strictly decreases
    `gasLeft`. No step adds gas (refunds are tx-level only).

    Phrased as a theorem on `IsAddStep`; in the full spec, the
    universally-quantified version is over any step relation. -/

theorem add_step_gas_strict_decrease
    (evm evm' : Evm) (h : IsAddStep evm evm') :
    evm'.gasLeft < evm.gasLeft := by
  obtain ⟨_, _, _, _, _, hGas, hEvm⟩ := h
  -- hGas : evm.gasLeft ≥ Gas.veryLow, hEvm : evm' = {evm with ...}
  -- Translate both into Nat-arithmetic for omega.
  have hg' : evm'.gasLeft = evm.gasLeft - Gas.veryLow := by
    rw [hEvm]
  -- veryLow = 3, definitionally.
  have hpos : Gas.veryLow > 0 := by decide
  -- evm.gasLeft - veryLow < evm.gasLeft, given gasLeft ≥ veryLow > 0.
  rw [hg']
  exact Nat.sub_lt (Nat.lt_of_lt_of_le hpos hGas) hpos

/-- General form (over an abstract step relation `Step`). Once the
    full opcode-by-opcode spec exists, this is the umbrella theorem
    that every per-opcode step must satisfy. -/
theorem step_decreases_gas_or_halts
    (Step : Evm → Evm → Prop)
    (perOpDecrease : ∀ evm evm', Step evm evm' →
                     evm'.halted ∨ evm'.gasLeft < evm.gasLeft) :
    ∀ evm evm', Step evm evm' →
    evm'.halted ∨ evm'.gasLeft < evm.gasLeft := by
  intro evm evm' h
  exact perOpDecrease evm evm' h

/-! ## Invariant 2: Static-context exclusion

    A frame whose `message.isStatic = true` cannot produce a step
    that mutates the world state (anything in `env.state`,
    `env.logs`, `env.selfDestructSet`).

    This is the spec form of EIP-214: any opcode that *can* mutate
    state must either be inert in static context or raise
    `writeInStaticContext`. The spec doesn't enumerate which
    opcodes — it states the invariant on outcomes.

    Pre-Byzantium forks have `isStatic = false` everywhere, so this
    invariant is vacuous there. Stated here so the same theorem
    text applies across all forks. -/

theorem static_frames_dont_mutate_state
    (Step : Evm → Evm → Prop)
    (perOpStatic : ∀ evm evm', Step evm evm' →
                   evm.message.isStatic →
                   evm'.env.state = evm.env.state ∧
                   evm'.env.logs = evm.env.logs ∧
                   evm'.env.selfDestructSet = evm.env.selfDestructSet) :
    ∀ evm evm', Step evm evm' →
    evm.message.isStatic →
    evm'.env.state = evm.env.state ∧
    evm'.env.logs = evm.env.logs ∧
    evm'.env.selfDestructSet = evm.env.selfDestructSet := by
  intro evm evm' h hStatic
  exact perOpStatic evm evm' h hStatic

/-! ## Invariant 3: Ether conservation at the frame level

    A successful single-frame step preserves total ether.

    Caveats:
    - SELFDESTRUCT *within a frame* moves balance from self to
      beneficiary; total unchanged.
    - CALL with `value > 0` moves balance from caller to callee
      WITHIN the same state; total unchanged.
    - CREATE pre-funding moves balance from sender to new contract;
      total unchanged.
    - Tx-level operations (miner payout, gas refund to sender,
      block reward) DO change total ether — but those happen
      OUTSIDE the per-frame step. The frame-level invariant
      doesn't include them.

    No state-touching opcode at the frame level should mint or burn
    ether. This is the canonical conservation theorem. -/

theorem step_preserves_ether
    (Step : Evm → Evm → Prop)
    (perOpEther : ∀ evm evm', Step evm evm' →
                  evm'.env.state.totalEther = evm.env.state.totalEther) :
    ∀ evm evm', Step evm evm' →
    evm'.env.state.totalEther = evm.env.state.totalEther := by
  intro evm evm' h
  exact perOpEther evm evm' h

/-! ## Notes

    The three theorems above are all *abstract* over `Step`. They
    receive a `perOp*` lemma — one obligation per opcode showing
    the property holds — and conclude the universal statement.

    The catch: discharging `perOpEther` requires per-opcode lemmas.
    Most opcodes don't touch balance (so the lemma is `evm'.env =
    evm.env` and total is trivially preserved). Only the
    balance-touching opcodes (CALL family, CREATE, SELFDESTRUCT)
    need real arithmetic. Those are precisely the opcodes a buggy
    implementation is most likely to get wrong — which is exactly
    why we want this invariant. -/

end Evm.Frontier.Spec
