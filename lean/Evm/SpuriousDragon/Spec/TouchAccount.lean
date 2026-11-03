/-
  Evm.SpuriousDragon.Spec.TouchAccount — EIP-161 touch semantics.

  EELS reference: `forks/spurious_dragon/state_tracker.py::touch_account`
  (and its call sites in `vm/interpreter.py::process_message`,
  `vm/instructions/system.py::call/callcode/delegatecall/selfdestruct`,
  and `fork.py::process_transaction`).

  EIP-161 redefines what "touching" an account means in two ways:

    1. **`is_dead`**: an account is "dead" iff it doesn't exist OR
       it exists but is empty (`nonce = 0 ∧ balance = 0 ∧ code = []`).
       The `NEW_ACCOUNT` (25000) charge on CALL/SELFDESTRUCT now
       triggers iff the target is `is_dead AND value > 0`. (Pre-SD:
       trigger was just `¬ accountExists`.)

    2. **Touched-set tracking**: CALL family, CREATE-target, and
       SELFDESTRUCT-beneficiary now record their target in a
       per-tx `touched` set. After the tx, `SweepEmpty` (see
       `SweepEmpty.lean`) deletes every touched account that is
       still empty.

  This file states the relation for tracking only — i.e., what
  the implementation's `Evm.SpuriousDragon.Vm.Interpreter.touchAddr`
  function (also referenced in the Frontier impl post-mortem of
  2026-05-29 as the omission that caused the divergence at block
  46,383) does on the state.

  The frontier `State.touchAccount` (lines 73-75 of
  `Frontier/State.lean`) adds an *empty account* to state if absent;
  that's a different EELS function and is the one used PRE-EIP-161.
  This SD relation is about the `touched : List Address` field on
  `Environment`, NOT about adding empty accounts to state.
-/

import Evm.Frontier.Vm

namespace Evm.SpuriousDragon.Spec

open Evm.Frontier.Vm

/-! ## IsTouchAccountStep — the EIP-161 set-tracking relation

    Input: an `Evm` frame, an address. Output: a frame whose
    `env.touched` includes the address (once; idempotent if already
    present). Everything else is unchanged.

    Mirrors `Evm.SpuriousDragon.Vm.Interpreter.touchAddr` (lines
    93-95):

        if env.touched.contains a then env
        else { env with touched := env.touched ++ [a] }

    Operating on `Evm` here (rather than `Environment` directly)
    matches the rest of this file's spec idiom. The post-state's
    `env.touched` is the `Set`-style union of the pre-state's
    touched set with `{addr}`. -/
def IsTouchAccountStep (evm : Evm) (addr : Evm.Address) (evm' : Evm) : Prop :=
  evm' = { evm with
    env := { evm.env with
      touched :=
        if evm.env.touched.contains addr then evm.env.touched
        else evm.env.touched ++ [addr] } }

/-! ## Structural lemmas

    Two facts any correct `touchAddr` implementation must satisfy. -/

/-- Touching is idempotent at the set level: once an address is in
    `evm'.env.touched`, applying the relation again with the same
    address leaves the touched list unchanged. -/
theorem touch_idempotent (evm evm' evm'' : Evm) (addr : Evm.Address)
    (h₁ : IsTouchAccountStep evm  addr evm')
    (h₂ : IsTouchAccountStep evm' addr evm'') :
    evm''.env.touched = evm'.env.touched := by
  unfold IsTouchAccountStep at h₁ h₂
  -- After h₁, addr ∈ evm'.env.touched in both branches of the if.
  -- h₂'s if therefore picks the "already contained" branch and
  -- returns evm'.env.touched unchanged.
  have hMem : addr ∈ evm'.env.touched := by
    rw [h₁]
    simp only
    by_cases hCase : addr ∈ evm.env.touched
    · simp [hCase]
    · simp [hCase, List.mem_append]
  rw [h₂]
  simp [hMem]

/-- Touching only ever changes the `touched` field of `env`;
    everything else (state, stack, gas, pc, …) is preserved. -/
theorem touch_preserves_state (evm evm' : Evm) (addr : Evm.Address)
    (h : IsTouchAccountStep evm addr evm') :
    evm'.env.state = evm.env.state ∧
    evm'.stack    = evm.stack    ∧
    evm'.gasLeft  = evm.gasLeft  ∧
    evm'.pc       = evm.pc       := by
  unfold IsTouchAccountStep at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [h]

/-! ## Notes

    - This relation is fork-NEW at SD: pre-SD interpreters never
      populate `env.touched` (it defaults to `[]`). Homestead, TW,
      Frontier all behave AS IF `IsTouchAccountStep evm addr evm =
      evm`, because they never apply it.

    - The relation does NOT add an empty account to state; that's
      `Evm.Frontier.State.touchAccount`, the PRE-EIP-161 behavior
      (which EIP-161 in fact REMOVES — see EELS' switch from
      "process_message calls touch_account unconditionally" to
      "callers populate touched-set, sweep at tx end"). The
      Frontier `IsCallEntrySuccess` clause that says
      `setup.subState = touched` (with `touched` adding the empty
      account) is therefore inherited UNCHANGED by Homestead and TW
      but OVERRIDDEN at SD. The SD CALL relation (not in this file)
      uses `IsTouchAccountStep`-on-env plus the value-gated
      NEW_ACCOUNT predicate, and does NOT pre-populate an empty
      account in state.

    - Composes with `SweepEmpty.lean`: the touched set populated
      here is what `IsSweepEmptyStep` consumes at end of tx.

    - The 2026-05-29 post-mortem of the Frontier mainnet divergence
      at block 46,383 found that the impl had been doing
      `IsTouchAccountStep` on a *frame-local* `touched` list; the
      fix moved it to `Environment.touched` so cross-frame call
      chains accumulate correctly. The relation here is implicitly
      against the cross-frame-shared `env.touched`. -/

end Evm.SpuriousDragon.Spec
