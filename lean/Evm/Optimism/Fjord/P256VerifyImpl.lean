/-
  Evm.Optimism.Fjord.P256VerifyImpl — re-export for the Optimism
  tree.

  The actual cryptographic primitive lives in `Evm.Crypto.P256Verify`
  (so the Cancun trampoline can call it without a cycle through
  Optimism). This module just re-exports the relevant names under
  the Fjord namespace for caller ergonomics. Once a real secp256r1
  verifier (FFI or pure Lean) replaces the `opaque` body of
  `Evm.Crypto.isValidP256Signature`, both names see the impl.
-/

import Evm.Crypto.P256Verify

namespace Evm.Optimism.Fjord

/-- Re-export from `Evm.Crypto.p256VerifyWith` (the gas is the fork's). -/
abbrev p256VerifyWith : Nat → Evm.Bytes → Nat →
    Except Evm.Frontier.Vm.Exception (Evm.Bytes × Nat) :=
  Evm.Crypto.p256VerifyWith

/-- Re-export from `Evm.Crypto.isValidP256Signature`. -/
abbrev isValidP256Signature : Evm.Crypto.P256Verifier :=
  Evm.Crypto.isValidP256Signature

end Evm.Optimism.Fjord
