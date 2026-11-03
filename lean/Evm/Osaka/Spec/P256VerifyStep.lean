/-
  Evm.Osaka.Spec.P256VerifyStep — EIP-7951 P256VERIFY precompile (0x100).

  EELS reference:
    * `forks/osaka/vm/precompiled_contracts/p256verify.py::p256verify`
      (the entire file).
    * Address: `P256VERIFY_ADDRESS = hex_to_address("0x100")` in
      `forks/osaka/vm/precompiled_contracts/__init__.py` line 56.
    * Gas constant: `PRECOMPILE_P256VERIFY = Uint(6900)` in
      `forks/osaka/vm/gas.py`.

  Per the SPEC-METHODOLOGY: a new precompile gets a relation describing
  the precompile's contract — `(input, gasIn) → (output, gasOut)` —
  written here in spec form. Precompiles aren't dispatched from a
  bytecode step but from `Vm.Effect.trampoline` when a CALL targets a
  precompile address; the relation captures exactly what the
  trampoline gets back from `PrecompiledContracts.lookup` followed by
  invocation.

  EELS semantics, in order:

    1. Charge `PRECOMPILE_P256VERIFY = 6900` gas (out-of-gas otherwise).
    2. If `len(data) ≠ 160`, return with empty output, gas-consumed
       state preserved.
    3. Parse `(msg_hash, r, s, qx, qy)` from the 5×32-byte input.
    4. Bounds-check `0 < r < n`, `0 < s < n`, `qx < p`, `qy < p`,
       `(qx, qy) ≠ (0, 0)`, `(qx, qy)` on the curve. Any failure ⇒
       empty output.
    5. Call `secp256r1_verify`. Failure ⇒ empty output. Success ⇒
       `evm.output := left_pad_zero_bytes(b"\\x01", 32)`.

  The 32-byte success output is `0x00..0001` (big-endian one),
  matching the on-chain convention for "verification succeeded".

  This file states the relation; the implementation in
  `Evm/Osaka/Vm/PrecompiledContracts.lean::p256verify` currently stubs
  the cryptographic verification (always returns empty output), so the
  refinement obligation is open for the success branch. The gas-charge
  and malformed-input branches are correct.
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Osaka.Vm.PrecompiledContracts

namespace Evm.Osaka.Spec

open Evm.Frontier.Vm (Exception)

/-- Address of the P256VERIFY precompile (EELS `P256VERIFY_ADDRESS`). -/
abbrev p256VerifyAddress : Evm.Address :=
  Evm.Osaka.Vm.PrecompiledContracts.p256verifyAddress

/-- Gas charged by P256VERIFY (EELS `PRECOMPILE_P256VERIFY = 6900`). -/
abbrev gasP256Verify : Nat := Evm.Osaka.Vm.PrecompiledContracts.gasP256Verify

/-- The 32-byte success output: big-endian `0x00…0001`. EELS:
    `left_pad_zero_bytes(b"\\x01", 32)`. -/
def p256VerifySuccessOutput : Evm.Bytes := Id.run do
  let mut acc : Evm.Bytes := ByteArray.empty
  for _ in [0:31] do
    acc := acc.push (0 : UInt8)
  acc := acc.push (1 : UInt8)
  return acc

/-- Predicate capturing the abstract result of P256VERIFY on
    `(input, gasIn)`. Existential on the cryptographic verifier
    `verify` — for the spec layer we don't axiomatise SECP256R1
    arithmetic; we just say the precompile's externally observable
    behaviour is parametric in whether the curve verifier accepts the
    signature. EELS makes the same factoring: `secp256r1_verify` is
    an imported black-box. -/
def IsP256VerifyStep
    (verify : Evm.Bytes → Bool)
    (input : Evm.Bytes) (gasIn : Nat)
    (output : Evm.Bytes) (gasOut : Nat) : Prop :=
  gasIn ≥ gasP256Verify ∧
  gasOut = gasIn - gasP256Verify ∧
  (if input.size ≠ 160 then
     output = Evm.Bytes.empty
   else if verify input then
     output = p256VerifySuccessOutput
   else
     output = Evm.Bytes.empty)

end Evm.Osaka.Spec
