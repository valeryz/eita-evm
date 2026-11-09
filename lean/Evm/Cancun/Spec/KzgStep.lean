/-
  Evm.Cancun.Spec.KzgStep — EIP-4844 point-evaluation precompile (0x0a).

  EELS reference: `forks/cancun/vm/precompiled_contracts/point_evaluation.py`
  `point_evaluation`. Gas constant `POINT_EVALUATION_PRECOMPILE_GAS = 50000`
  in `forks/cancun/vm/gas.py`.

  Behaviour:

    * Input is exactly 192 bytes:
        versioned_hash : 32 bytes
        z              : 32 bytes (field element, big-endian)
        y              : 32 bytes (field element, big-endian)
        commitment     : 48 bytes (G1 element, compressed)
        proof          : 48 bytes (G1 element, compressed)
      Any other input length → out-of-gas / failure.

    * Charge a flat 50000 gas. No memory expansion (precompile
      reads from calldata, not memory).

    * Verify two things:
        1. `kzg_to_versioned_hash(commitment) == versioned_hash`
           (first byte is `VERSIONED_HASH_VERSION_KZG = 0x01`, rest is
           `sha256(commitment)[1:]`).
        2. `kzg_verify_proof(commitment, z, y, proof)`. This is the
           cryptographic check that `commitment` opens at `z` to `y`
           with `proof` as the KZG opening.
      If both succeed, return the 64-byte success constant:
          FIELD_ELEMENTS_PER_BLOB (32 bytes BE) || BLS_MODULUS (32 bytes BE)
      = the canonical "verified" output specified by EIP-4844.

  The versioned-hash binding is computed (over SHA2-256); the KZG
  pairing check is an oracle parameter `verify`. The executable side
  (Evm.Cancun.Vm.PrecompiledContracts.pointEvaluation and the replay's
  run-precompile) calls lean/c/point_evaluation.c over blst, checked
  against the c-kzg-4844 verify_kzg_proof vectors; that FFI is the trust
  boundary, named as the refinement's hypothesis.

  Inheritance: applies unchanged at Prague (which only adds the
  EIP-2537 BLS12-381 precompiles on top).
-/

import Evm.BaseTypes
import Evm.Crypto.Sha256

namespace Evm.Cancun.Spec

/-! ## Constants -/

/-- EELS `POINT_EVALUATION_PRECOMPILE_GAS = 50000`. Flat charge,
    regardless of input. -/
def pointEvaluationGas : Nat := 50000

/-- EELS `VERSIONED_HASH_VERSION_KZG = 0x01`. The version byte
    prepended to `sha256(commitment)[1:]` to form the versioned hash. -/
def versionedHashVersionKzg : UInt8 := 0x01

/-- EELS `FIELD_ELEMENTS_PER_BLOB = 4096`. -/
def fieldElementsPerBlob : Nat := 4096

/-- BLS12-381 scalar field order. EELS:
    `forks/cancun/vm/precompiled_contracts/point_evaluation.py::BLS_MODULUS`. -/
def blsModulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

/-- Required input length: `32 + 32 + 32 + 48 + 48 = 192` bytes. -/
def inputSize : Nat := 192

/-- Output length on success: 64 bytes. -/
def outputSize : Nat := 64

/-! ## The two checks

    `kzg_commitment_to_versioned_hash` (EELS `crypto/kzg.py` 65-74) is computed
    here: `VERSIONED_HASH_VERSION_KZG ‖ sha256(commitment)[1:]`, over the SHA2-256
    primitive `Evm.Crypto.sha256`. The pairing check `verify_kzg_proof`
    (`e(commitment − [y]₁, [1]₂) = e(proof, [s − z]₂)` over BLS12-381) is a trusted
    oracle, the parameter `verify commitment z y proof` of the relations below —
    no uninterpreted axioms (restated 2026-11-09: the two checks used to be
    `axiom … : Prop`s). -/

/-- EELS `kzg_commitment_to_versioned_hash`. -/
def kzgToVersionedHash (commitment : Evm.Bytes) : Evm.Bytes :=
  ByteArray.mk (Array.mk [versionedHashVersionKzg]) ++
    (Evm.Crypto.sha256 commitment).extract 1 32

/-- EELS `point_evaluation`'s acceptance condition (44-65): 192 bytes, the versioned
    hash binds the commitment, and the proof verifies. -/
def pointEvaluationAccepts (verify : Evm.Bytes → Evm.Bytes → Evm.Bytes → Evm.Bytes → Bool)
    (input : Evm.Bytes) : Prop :=
  input.size = inputSize ∧
  kzgToVersionedHash (Evm.Bytes.sliceZeroPad input 96 48) = Evm.Bytes.sliceZeroPad input 0 32 ∧
  verify (Evm.Bytes.sliceZeroPad input 96 48) (Evm.Bytes.sliceZeroPad input 32 32)
    (Evm.Bytes.sliceZeroPad input 64 32) (Evm.Bytes.sliceZeroPad input 144 48) = true

/-! ## The canonical success output

    On a successful verification the precompile returns 64 bytes:
        be32(FIELD_ELEMENTS_PER_BLOB) || be32(BLS_MODULUS) -/

def be32 (n : Nat) : Evm.Bytes :=
  Evm.U256.toBytesBE (Evm.U256.ofNat n)

/-- Canonical success-output: the 32-byte big-endian
    `FIELD_ELEMENTS_PER_BLOB` concatenated with the 32-byte
    `BLS_MODULUS`. EELS:
    `forks/cancun/vm/precompiled_contracts/point_evaluation.py`. -/
def kzgSuccessOutput : Evm.Bytes :=
  be32 fieldElementsPerBlob ++ be32 blsModulus

/-! ## The relation

    The precompile call is wrapped in a sub-frame by the trampoline,
    so the relation here is *not* `Evm → Evm → Prop` like an opcode;
    it's the precompile's "inner" result: given an input and a gas
    budget, did it succeed (with `kzgSuccessOutput` and the remaining
    gas), or did it fail (`outOfGas`).

    The shape matches Frontier's other precompiles:
        `Precompile = Bytes → Nat → Except Exception (Bytes × Nat)`. -/

/-- Success (EELS `point_evaluation` 32-72): the input is accepted, the 50000 gas
    is there, the output is the canonical 64 bytes. -/
def IsKzgPrecompileSuccess (verify : Evm.Bytes → Evm.Bytes → Evm.Bytes → Evm.Bytes → Bool)
    (input : Evm.Bytes) (gas : Nat) (output : Evm.Bytes) (gas' : Nat) : Prop :=
  pointEvaluationAccepts verify input ∧
  gas ≥ pointEvaluationGas ∧
  output = kzgSuccessOutput ∧
  gas' = gas - pointEvaluationGas

/-- Failure: wrong length (44-45), too little gas (54), a versioned-hash mismatch
    (55-56) or a proof that does not verify (59-65) — each `KZGProofError`, the
    exceptional halt. -/
def IsKzgPrecompileFailure (verify : Evm.Bytes → Evm.Bytes → Evm.Bytes → Evm.Bytes → Bool)
    (input : Evm.Bytes) (gas : Nat) : Prop :=
  ¬ pointEvaluationAccepts verify input ∨ gas < pointEvaluationGas

end Evm.Cancun.Spec
