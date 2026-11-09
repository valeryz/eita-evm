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

  The checks are stated here from EELS, over the curve constants of
  `Evm.Crypto.P256Verify` (EELS `elliptic_curve.py` 79-90, 134-169); the signature check
  `secp256r1_verify` is the parameter `verify`, as EELS imports it as a black box.
  `Evm.Osaka.Spec.Refinement.p256Verify_sound` proves the precompile refines it for every
  `verify`; the replay's instance is OpenSSL (`Evm.Crypto.isValidP256Signature`).
-/

import Evm.BaseTypes
import Evm.Frontier.Vm.Exceptions
import Evm.Osaka.Vm.PrecompiledContracts
import Evm.Crypto.P256Verify

namespace Evm.Osaka.Spec

open Evm.Frontier.Vm (Exception)

/-- Address of the P256VERIFY precompile (EELS `P256VERIFY_ADDRESS`). -/
abbrev p256VerifyAddress : Evm.Address :=
  Evm.Osaka.Vm.PrecompiledContracts.p256verifyAddress

/-- Gas charged by P256VERIFY (EELS `PRECOMPILE_P256VERIFY = 6900`). -/
abbrev gasP256Verify : Nat := Evm.Osaka.Vm.PrecompiledContracts.gasP256Verify

/-- The 32-byte success output: big-endian `0x00…0001`, EELS 90
    `left_pad_zero_bytes(b"\\x01", 32)` (`Evm.Crypto.p256SuccessOutput`). -/
abbrev p256VerifySuccessOutput : Evm.Bytes := Evm.Crypto.p256SuccessOutput

/-- The 32-byte big-endian word at `off` (EELS 50-59, `U256.from_be_bytes(buffer_read(…))`). -/
def word (input : Evm.Bytes) (off : Nat) : Nat :=
  (Evm.U256.ofBytesBE (Evm.Bytes.sliceZeroPad input off 32)).toNat

/-- EELS 46-88, clause by clause: the input is 160 bytes; 0 < r < n, 0 < s < n (63-66);
    qx, qy < p (71-74); (qx, qy) ≠ (0, 0) (77-78); qy² ≡ qx³ + a·qx + b mod p (82-83);
    `secp256r1_verify` accepts (85-88). -/
def P256Accepts (verify : Nat → Nat → Nat → Nat → Nat → Bool) (input : Evm.Bytes) : Prop :=
  let r := word input 32
  let s := word input 64
  let qx := word input 96
  let qy := word input 128
  input.size = 160 ∧
  0 < r ∧ r < Evm.Crypto.p256N ∧ 0 < s ∧ s < Evm.Crypto.p256N ∧
  qx < Evm.Crypto.p256P ∧ qy < Evm.Crypto.p256P ∧
  ¬ (qx = 0 ∧ qy = 0) ∧
  qy * qy % Evm.Crypto.p256P =
    (qx * qx * qx % Evm.Crypto.p256P + Evm.Crypto.p256A * qx % Evm.Crypto.p256P +
      Evm.Crypto.p256B) % Evm.Crypto.p256P ∧
  verify (word input 0) r s qx qy = true

/-- P256VERIFY on `(input, gasIn)` (EELS `p256verify` 41-90): the 6900 gas is charged (44;
    too little is the out-of-gas halt, which this relation excludes), then the output is
    the 32-byte one exactly when `P256Accepts`, else empty. -/
def IsP256VerifyStep
    (verify : Nat → Nat → Nat → Nat → Nat → Bool)
    (input : Evm.Bytes) (gasIn : Nat)
    (output : Evm.Bytes) (gasOut : Nat) : Prop :=
  gasIn ≥ gasP256Verify ∧
  gasOut = gasIn - gasP256Verify ∧
  (P256Accepts verify input → output = p256VerifySuccessOutput) ∧
  (¬ P256Accepts verify input → output = Evm.Bytes.empty)

/-- P256VERIFY's only exceptional halt: too little gas (44). -/
def IsP256VerifyFailure (gasIn : Nat) : Prop := gasIn < gasP256Verify

end Evm.Osaka.Spec
