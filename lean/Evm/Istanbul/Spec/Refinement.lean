/-
  Evm.Istanbul.Spec.Refinement — proofs that the Istanbul Effect
  interpreter refines the Istanbul Spec relations.

  Istanbul adds:

    * `Blake2fStep.lean` — EIP-152 BLAKE2F precompile (0x09).
    * `ChainidStep.lean` — EIP-1344 CHAINID (0x46).
    * `GasConstants.lean` — EIP-1884 SLOAD/BALANCE/EXTCODEHASH reprice.
    * `SelfbalanceStep.lean` — EIP-1884 SELFBALANCE (0x47).
    * `SstoreStep.lean` — EIP-2200 net SSTORE.

  CHAINID and SELFBALANCE are nullary-push opcodes; refinement is a
  one-liner via `Frontier.Spec.Refinement.nullaryPush_sound`. SSTORE
  is the heavy state-touching opcode (`sorry`-deferred). Blake2f
  is a precompile whose body is `opaque` in the spec; the gas / size
  obligations are statable but the cryptographic output is axiomatic.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Istanbul.Spec.Blake2fStep
import Evm.Istanbul.Spec.ChainidStep
import Evm.Istanbul.Spec.GasConstants
import Evm.Istanbul.Spec.SelfbalanceStep
import Evm.Istanbul.Spec.SstoreStep
import Evm.Istanbul.Vm.Instructions.Block
import Evm.Istanbul.Vm.Instructions.Environment
import Evm.Istanbul.Vm.Instructions.Storage
import Evm.Istanbul.Vm.Effect

namespace Evm.Istanbul.Spec.Refinement

open Evm.Frontier.Vm
open Evm.Istanbul.Spec

/-! ## EIP-1344 CHAINID (0x46) -/

/-- CHAINID is a NullaryPushStep over `env.chainId`. One-line proof
    via the `nullaryPush_sound` shape lemma in
    `Frontier/Spec/Refinement.lean`. -/
theorem chainid_sound (evm evm' : Evm) :
    Evm.Istanbul.Vm.Instructions.chainid evm = .ok evm' →
    IsChainidStep evm evm' := by
  intro h
  exact Evm.Frontier.Spec.Refinement.nullaryPush_sound
    _ (fun e => e.env.chainId) evm evm' h

/-! ## EIP-1884 SELFBALANCE (0x47) -/

/-- SELFBALANCE is a NullaryPushStep over `state.getBalance
    currentTarget`. State-reading but no mutation; refinement
    reduces to the same shape lemma as CHAINID. -/
theorem selfbalance_sound (evm evm' : Evm) :
    Evm.Istanbul.Vm.Instructions.selfbalance evm = .ok evm' →
    IsSelfbalanceStep evm evm' := by
  intro h
  exact Evm.Frontier.Spec.Refinement.nullaryPush_sound
    _ (fun e => e.env.state.getBalance e.message.currentTarget)
    evm evm' h

/-! ## EIP-2200 SSTORE (0x55) — net-metering, EIP-1706 trip-wire -/

/-- EIP-2200 SSTORE refinement: 9-case decision tree with refunds.
    State-touching, heaviest opcode at this fork. `sorry`-deferred. -/
theorem sstore_sound (evm evm' : Evm) :
    Evm.Istanbul.Vm.Instructions.sstore evm = .ok evm' →
    IsSstoreStep evm evm' := by
  intro _; sorry

/-! ## EIP-152 BLAKE2F precompile (0x09)

    Not a step opcode but a precompile invoked via the trampoline.
    The spec relation `IsBlake2fStep` is `(input, gas, output, gas')`
    -shaped; the impl's `Blake2f` precompile stub returns 64 zero
    bytes pending FFI. Soundness of the gas / size checks is
    statable now; the cryptographic output identity awaits the
    `blake2bCompress` binding. -/

/-- BLAKE2F (0x09): the spec's `IsBlake2fStep` uses an opaque
    `blake2bCompress` for the output; the impl stub returns zeros.
    State the relation; defer the cryptographic equality. -/
theorem blake2f_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gasLeft : Nat) :
    IsBlake2fStep input gas output gasLeft →
    IsBlake2fStep input gas output gasLeft := by
  -- The spec relation is its own statement; refinement against the
  -- impl precompile requires plumbing `Evm.Istanbul.Vm.Precompiled
  -- Contracts.blake2f` through a `(input, gas) → Except Exception
  -- (output, gas')` form.
  intro h; exact h

/-! ## Notes

    - GasConstants.lean defines named constants only; nothing to
      refine here beyond the (already trivial) definitional equality
      with `Evm.Istanbul.Vm.Gas`. No theorem needed.

    - CHAINID / SELFBALANCE now collapse to one-liners via
      `nullaryPush_sound`, analogous to `runBinary_sound` for
      arithmetic ops. -/

end Evm.Istanbul.Spec.Refinement
