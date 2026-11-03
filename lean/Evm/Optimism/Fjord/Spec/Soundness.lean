/-
  Evm.Optimism.Fjord.Spec.Soundness — known gaps in the Fjord
  executable. See [[no-silent-gaps]].
-/

import Evm.Optimism.Fjord.Spec.P256Verify
import Evm.Optimism.Bedrock.Fork

namespace Evm.Optimism.Fjord.Spec.Soundness

/-! ## RIP-7212 P256VERIFY precompile

    DISCHARGED — partially.

    1. CALL-dispatch wiring (DISCHARGED): the Fjord+ executable
       (`Evm.Optimism.Fjord.Fork.applyBlock` and onwards through
       Granite/Isthmus) sets
       `Environment.opP256VerifyGas := p256VerifyGasAt f` (RIP-7212's
       3450 until Azul, 6900 from Azul).
       Cancun's trampoline `callLike` branch consults this list
       BEFORE treating the target as an EOA, so a CALL to 0x100
       at Fjord+ runs `p256VerifyWith (p256VerifyGas f)` instead.

    2. Verifier correctness (TRUST BOUNDARY at the FFI seam): the
       cryptographic predicate `Evm.Crypto.isValidP256Signature` is
       wired via `@[extern "lean_p256_verify"]` to
       `c/p256verify.c` → OpenSSL's `ECDSA_do_verify` over NIST
       P-256 (NID_X9_62_prime256v1). The trust boundary now sits
       at the C/OpenSSL boundary, not inside Lean. Replacing the
       OpenSSL FFI with a pure-Lean P-256 implementation would
       collapse the chain entirely; see Test.lean for the RFC 6979
       known-good + tampered-s smoke tests. -/

/-- DISCHARGED: the precompile interface exists and has the
    spec-pinned address, per-fork gas (measured on Base: 3450 at
    Isthmus, 6900 at Azul), and input length. -/
theorem p256_precompile_constants :
    p256VerifyAddress = Evm.Address.ofNat 0x0100 ∧
    p256VerifyGas .isthmus = 3450 ∧ p256VerifyGas .azul = 6900 ∧
    p256VerifyInputLen = 160 := by
  refine ⟨rfl, rfl, by decide, rfl⟩

/-- **OPEN (KNOWN GAP)**: a user tx's EIP-2929 precompile warm seed is the
    fork's active precompile set — 0x100 (P256VERIFY) exactly from Fjord,
    0x0a (KZG point evaluation, Cancun rules) exactly from Ecotone — as
    op-geth's `ActivePrecompiles(rules)` pre-warm. The executable
    (`Bedrock.userTxPrecompileWarmSeed`) warms both at every fork, so this is
    FALSE before Fjord; the production Lisp replay gates 0x100 by fork
    (`op-tx-prewarm`). Replaced 2026-11-02 the vacuous
    `p256_is_warm_seeded_post_fjord : hasP256Verify f = true → True`. -/
theorem precompile_warm_seed_per_fork (f : Evm.Optimism.OpFork) :
    (Evm.Address.ofNat 0x100 ∈ Evm.Optimism.Bedrock.userTxPrecompileWarmSeed ↔ hasP256Verify f) ∧
    (Evm.Address.ofNat 0x0a ∈ Evm.Optimism.Bedrock.userTxPrecompileWarmSeed ↔
      f.atLeast .ecotone) := by
  sorry

end Evm.Optimism.Fjord.Spec.Soundness
