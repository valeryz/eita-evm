/-
  Evm.Cancun.Spec.Refinement — proofs that the Cancun Effect
  interpreter refines the Cancun Spec relations.

  Cancun adds:

    * `TransientStorageStep.lean` — EIP-1153 0x5c TLOAD / 0x5d TSTORE.
    * `McopyStep.lean`            — EIP-5656 0x5e MCOPY.
    * `BlobhashStep.lean`         — EIP-4844 0x49 BLOBHASH.
    * `BlobbasefeeStep.lean`      — EIP-7516 0x4a BLOBBASEFEE.
    * `BlobTx.lean`               — EIP-4844 type-3 tx + blob fee mkt.
    * `KzgStep.lean`              — EIP-4844 point-evaluation precompile.
    * `Selfdestruct.lean`         — EIP-6780 same-tx-only destruction.

  Per SPEC-METHODOLOGY: TLOAD/TSTORE/MCOPY/BLOBHASH are state-touching
  or env-reading; BLOBBASEFEE is a one-line nullary-push refinement
  via `Frontier.Spec.Refinement.nullaryPush_sound`. BlobTx and Kzg
  are at the tx / precompile levels (the EIP-4788 system call is
  `Evm.Frontier.Vm.System`, proved in `Evm.CL.EffectSystemProof`); SELFDESTRUCT
  touches state. State-touching obligations are `sorry`-deferred.
  NOTE: theorems suffixed `_shape` are `P → P` placeholders — the spec
  relation is not yet linked to the interpreter (see SPEC-METHODOLOGY).
-/

import Evm.Frontier.Spec.Refinement
import Evm.Cancun.Spec.TransientStorageStep
import Evm.Cancun.Spec.McopyStep
import Evm.Cancun.Spec.BlobhashStep
import Evm.Cancun.Spec.BlobbasefeeStep
import Evm.Cancun.Spec.BlobTx
import Evm.Cancun.Spec.KzgStep
import Evm.Cancun.Spec.Selfdestruct
import Evm.Cancun.Vm.Instructions
import Evm.Cancun.Vm.Effect

namespace Evm.Cancun.Spec.Refinement

open Evm.Frontier (State)
open Evm.Frontier.Vm
open Evm.Cancun.Spec

/-! ## EIP-1153 TLOAD (0x5c) / TSTORE (0x5d) -/

/-- TLOAD reads transient storage. State-touching obligation. -/
theorem tload_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.tload evm = .ok evm' →
    IsTloadStep evm evm' := by
  intro _; sorry

/-- TSTORE writes transient storage. State-touching obligation
    (mutates `env.transientStorage`); static-context check. -/
theorem tstore_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.tstore evm = .ok evm' →
    IsTstoreStep evm evm' := by
  intro _; sorry

/-! ## EIP-5656 MCOPY (0x5e) -/

/-- MCOPY copies bytes within memory, with overlap safety. Memory-
    expansion + multi-word copy obligation. -/
theorem mcopy_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.mcopy evm = .ok evm' →
    IsMcopyStep evm evm' := by
  intro _; sorry

/-! ## EIP-4844 BLOBHASH (0x49) -/

/-- BLOBHASH pops index, pushes `env.blobVersionedHashes[index]` or
    0 OOB. State-reading; refinement needs `runUnary`-shape
    extension to consult `env`. -/
theorem blobhash_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.blobhash evm = .ok evm' →
    IsBlobhashStep evm evm' := by
  intro _; sorry

/-! ## EIP-7516 BLOBBASEFEE (0x4a) -/

/-- BLOBBASEFEE is a NullaryPushStep over `env.blobBaseFee`. One-line
    proof via the `nullaryPush_sound` shape lemma. -/
theorem blobbasefee_sound (evm evm' : Evm) :
    Evm.Cancun.Vm.Instructions.blobbasefee evm = .ok evm' →
    IsBlobbasefeeStep evm evm' := by
  intro h
  exact Evm.Frontier.Spec.Refinement.nullaryPush_sound
    _ (fun e => Evm.U256.ofNat e.env.blobBaseFee) evm evm' h

/-! ## EIP-4844 blob tx / blob fee market (tx-level) -/

/-- `IsBlobCountValid` — per-tx blob count must be in (0, 6]. -/
theorem blobCountValid_sound_shape (numBlobs : Nat) :
    IsBlobCountValid numBlobs →
    IsBlobCountValid numBlobs := by
  intro h; exact h

/-- `IsBlobAffordable` — sender balance covers value + gas-fee +
    blob-fee. -/
theorem blobAffordable_sound_shape
    (senderBalance value gasLimit maxFeePerGas
     maxFeePerBlobGas numBlobs : Nat) :
    IsBlobAffordable senderBalance value gasLimit maxFeePerGas
                     maxFeePerBlobGas numBlobs →
    IsBlobAffordable senderBalance value gasLimit maxFeePerGas
                     maxFeePerBlobGas numBlobs := by
  intro h; exact h

/-- `IsBlobFeeBidSufficient` — tx's max_fee_per_blob_gas ≥ block's
    blob_base_fee. -/
theorem blobFeeBidSufficient_sound_shape (maxFeePerBlobGas blobBaseFee : Nat) :
    IsBlobFeeBidSufficient maxFeePerBlobGas blobBaseFee →
    IsBlobFeeBidSufficient maxFeePerBlobGas blobBaseFee := by
  intro h; exact h

/-! ## EIP-4844 KZG point-evaluation precompile (0x0a) -/

/-- Precompile success branch: well-formed input + valid pairing ⇒
    canonical 64-byte success output. Cryptographic predicates are
    axiomatic in the spec; the impl needs a verified KZG library to
    discharge them. -/
theorem kzg_success_sound_shape
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) :
    IsKzgPrecompileSuccess input gas output gas' →
    IsKzgPrecompileSuccess input gas output gas' := by
  intro h; exact h

/-- Precompile failure branch. -/
theorem kzg_failure_sound_shape (input : Evm.Bytes) (gas : Nat) :
    IsKzgPrecompileFailure input gas →
    IsKzgPrecompileFailure input gas := by
  intro h; exact h

/-! ## EIP-6780 SELFDESTRUCT (same-tx-only destruction) -/

/-- SELFDESTRUCT at Cancun: full delete only if self ∈
    createdAccounts; otherwise only balance moves. State-touching
    obligation. -/
theorem selfdestruct_sound_shape (evm evm' : Evm) :
    IsSelfdestructStep evm evm' →
    IsSelfdestructStep evm evm' := by
  intro h; exact h

/-! ## Notes

    - Most tx- and block-level predicates above are equational; their
      refinement reduces to definitional equality once the impl
      callsite (in `Cancun.Fork` / `Cancun.Vm.Effect`) is extracted.

    - The KZG spec is intentionally minimal: the cryptographic
      semantics are deferred to external libraries.

    - The spec relations match the EIPs Cancun ships (EIP-4788's
      system call is `Evm.Frontier.Vm.System`); every one has a
      soundness obligation here. -/

end Evm.Cancun.Spec.Refinement
