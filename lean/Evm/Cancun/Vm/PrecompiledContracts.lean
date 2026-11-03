/-
  Evm.Cancun.Vm.PrecompiledContracts — Cancun precompile registry,
  which extends the existing set with EIP-4844's KZG point-evaluation
  precompile at address 0x0A.

  EELS reference:
    - `forks/cancun/vm/precompiled_contracts/__init__.py`
        (the registry layout)
    - `forks/cancun/vm/precompiled_contracts/point_evaluation.py`
        (the KZG verifier)

  The verification runs in C over vendor/blst (`lean/c/point_evaluation.c`, the
  same object libeita's replay dispatches to), bound below by `@[extern]`. The
  Prop-level relation is `Evm.Cancun.Spec.KzgStep`, whose two crypto predicates
  stay axioms: this FFI is their named trust boundary.

  The Cancun registry inherits Frontier's 0x01..0x04 (ECRECOVER,
  SHA256, RIPEMD160, IDENTITY) and the Byzantium-era 0x05..0x08
  (MODEXP, BN256ADD, BN256MUL, BN256PAIRING) and the Istanbul 0x09
  (BLAKE2F). Those earlier ones are still served by their original
  Frontier precompile lookup (we re-export it).
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Frontier.Vm.PrecompiledContracts
import Evm.Istanbul.Vm.PrecompiledContracts
import Evm.Berlin.Vm.PrecompiledContracts.Modexp
import Evm.Cancun.Vm.Gas

namespace Evm.Cancun.Vm.PrecompiledContracts

open Evm.Frontier.Vm (Exception)

abbrev Precompile :=
  Evm.Bytes → Nat → Except Exception (Evm.Bytes × Nat)

/-- TRUST BOUNDARY: EELS point_evaluation.py:32-72 minus the gas charge — the 192-byte
    length, `kzg_commitment_to_versioned_hash(commitment) == versioned_hash`, and
    `verify_kzg_proof(commitment, z, y, proof)`. Returns the 64-byte
    `FIELD_ELEMENTS_PER_BLOB ‖ BLS_MODULUS` on success and empty on any
    `KZGProofError`. -/
@[extern "lean_point_evaluation"]
opaque pointEvaluationRaw (input : @& ByteArray) : ByteArray

/-- EIP-4844 KZG point-evaluation precompile (0x0A), EELS
    `forks/cancun/vm/precompiled_contracts/point_evaluation.py` (unchanged through Osaka).
    Every failure — wrong length (44-45), too little gas (54), versioned-hash mismatch
    (55-56), a proof that is malformed or does not verify (59-65) — is the exceptional
    halt `KZGProofError`, which consumes the frame's gas like `outOfGas`. -/
def pointEvaluation : Precompile := fun input gasAvailable => do
  if gasAvailable < Evm.Cancun.Vm.Gas.pointEvaluation then
    .error .outOfGas
  let output := pointEvaluationRaw input
  if output.size ≠ 64 then
    .error .outOfGas    -- KZGProofError
  return (output, gasAvailable - Evm.Cancun.Vm.Gas.pointEvaluation)

/-- Cancun precompile registry. Inherits Frontier's 0x01..0x04 and
    adds the KZG verifier at 0x0A. Byzantium 0x05..0x08 + Istanbul
    0x09 aren't in Frontier's registry yet — they live in
    fork-specific code (Frontier-impl only registers four), and we
    do not yet model them at Cancun either. They are stubs in their
    respective forks. -/
def registry : List (Evm.Address × Precompile) :=
  -- Replace Istanbul's modexp (Byzantium gas formula) with Berlin's
  -- EIP-2565 reprice, then add KZG (0x0a). EIP-2565 was Berlin —
  -- between Istanbul and Cancun — and Cancun inherits it, but we
  -- previously slipped through with the old formula because no
  -- mainnet ValidBlocks test exercised modexp prominently. Caught
  -- by Base Isthmus block 0x1d10000 tx 204.
  (Evm.Istanbul.Vm.PrecompiledContracts.registry.filter
      (fun (a, _) => a ≠ Evm.Address.ofNat 0x05)) ++
  [ (Evm.Address.ofNat 0x05, Evm.Berlin.Vm.PrecompiledContracts.modexp)
  , (Evm.Address.ofNat 0x0a, pointEvaluation) ]

/-- Look up the Cancun precompile at `addr`, if any. -/
def lookup (addr : Evm.Address) : Option Precompile :=
  (registry.find? (fun (a, _) => a = addr)).map Prod.snd

end Evm.Cancun.Vm.PrecompiledContracts
