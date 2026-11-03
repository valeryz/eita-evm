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

  Per the methodology, the cryptographic predicate itself is
  *axiomatised*: we introduce `IsValidKzgProof` and
  `IsValidVersionedHash` as opaque `Prop`s and the spec branches on
  them. The executable side (Evm.Cancun.Vm.PrecompiledContracts.pointEvaluation
  and the replay's run-precompile) calls lean/c/point_evaluation.c over blst,
  checked against the c-kzg-4844 verify_kzg_proof vectors; that FFI is the
  trust boundary these axioms name.

  Inheritance: applies unchanged at Prague (which only adds the
  EIP-2537 BLS12-381 precompiles on top).
-/

import Evm.BaseTypes

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

/-! ## Axiomatised cryptographic predicates

    We do not specify KZG math in Lean — the task brief says to
    axiomatise these; the executable precompile runs lean/c/point_evaluation.c.

    `IsValidVersionedHash` checks the simple sha256-based binding
    between the 48-byte commitment and the 32-byte versioned hash.

    `IsValidKzgProof` is the full pairing check
    `e(commitment - [y]_1, [1]_2) == e(proof, [z]_2 - [s]_2)`
    over BLS12-381, where `[s]` is the trusted-setup secret. -/

/-- Versioned-hash check: `versioned_hash == 0x01 || sha256(commitment)[1..32]`. -/
axiom IsValidVersionedHash : Evm.Bytes → Evm.Bytes → Prop

/-- The KZG opening proof check itself. Inputs: commitment (48 bytes,
    compressed G1), z (32 bytes, scalar), y (32 bytes, scalar), proof
    (48 bytes, compressed G1). -/
axiom IsValidKzgProof : Evm.Bytes → Evm.Bytes → Evm.Bytes → Evm.Bytes → Prop

/-! ## The canonical success output

    On a successful verification the precompile returns 64 bytes:
        be32(FIELD_ELEMENTS_PER_BLOB) || be32(BLS_MODULUS) -/

private def be32 (n : Nat) : Evm.Bytes :=
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

/-- Success: input parses as `(vh, z, y, commitment, proof)`, gas is
    sufficient, both crypto checks pass, output equals the canonical
    success bytes. -/
def IsKzgPrecompileSuccess (input : Evm.Bytes) (gas : Nat)
                            (output : Evm.Bytes) (gas' : Nat) : Prop :=
  input.size = inputSize ∧
  gas ≥ pointEvaluationGas ∧
  let vh    := Evm.Bytes.sliceZeroPad input 0   32
  let _z    := Evm.Bytes.sliceZeroPad input 32  32
  let _y    := Evm.Bytes.sliceZeroPad input 64  32
  let c     := Evm.Bytes.sliceZeroPad input 96  48
  let pf    := Evm.Bytes.sliceZeroPad input 144 48
  IsValidVersionedHash vh c ∧
  IsValidKzgProof c (Evm.Bytes.sliceZeroPad input 32 32)
                    (Evm.Bytes.sliceZeroPad input 64 32) pf ∧
  output = kzgSuccessOutput ∧
  gas' = gas - pointEvaluationGas

/-- Failure: any of the input-size, gas, versioned-hash, or KZG
    predicates fails. The precompile signals failure via an EVM
    `Exception` (typically `outOfGas`); the caller frame then
    receives `0` on its stack via the trampoline. -/
def IsKzgPrecompileFailure (input : Evm.Bytes) (gas : Nat) : Prop :=
  input.size ≠ inputSize ∨
  gas < pointEvaluationGas ∨
  (let vh := Evm.Bytes.sliceZeroPad input 0 32
   let c  := Evm.Bytes.sliceZeroPad input 96 48
   ¬ IsValidVersionedHash vh c) ∨
  (let c  := Evm.Bytes.sliceZeroPad input 96 48
   let z  := Evm.Bytes.sliceZeroPad input 32 32
   let y  := Evm.Bytes.sliceZeroPad input 64 32
   let pf := Evm.Bytes.sliceZeroPad input 144 48
   ¬ IsValidKzgProof c z y pf)

end Evm.Cancun.Spec
