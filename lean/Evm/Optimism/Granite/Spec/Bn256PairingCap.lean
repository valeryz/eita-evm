/-
  Evm.Optimism.Granite.Spec.Bn256PairingCap — Granite caps the input
  to the bn256 pairing precompile.

  Source: optimism-specs `specs/protocol/granite/exec-engine.md`.

  Bn256 pairing (precompile 0x08) accepts a sequence of (G1,G2)
  point pairs as input — 192 bytes per pair (64 + 128). Pre-Granite,
  the input length was unbounded; an adversarial tx could submit
  arbitrarily many pairs and consume disproportionate prover time
  in fraud-proof systems (op-succinct, kona). Granite caps the
  acceptable input at:

    MAX_PAIRING_INPUT_SIZE = 1536 bytes  = 8 pairs

  An input longer than 1536 bytes causes the precompile to revert
  (returns empty bytes; consumes all forwarded gas).

  This is OP-only; mainnet Ethereum still allows arbitrarily large
  bn256 pairing input (the gas formula provides natural DoS
  protection there).
-/

import Evm.BaseTypes
import Evm.Optimism.Forks

namespace Evm.Optimism.Granite.Spec

/-- Per-spec cap on `ecPairing` input length, in bytes. -/
def maxPairingInputSize : Nat := 1536

/-- 192 bytes per (G1, G2) pair. -/
def pairBytes : Nat := 192

/-- The cap is 8 pairs exactly (`1536 / 192 = 8`). Non-trivial
    arithmetic check (catches drift on either constant). -/
example : maxPairingInputSize = 8 * pairBytes := by decide

/-- The cap is active iff Granite or later. -/
def hasPairingCap (f : Evm.Optimism.OpFork) : Bool := f.atLeast .granite

theorem cap_iff_granite (f : Evm.Optimism.OpFork) :
    hasPairingCap f = true ↔ f.atLeast .granite := by
  unfold hasPairingCap; rfl

end Evm.Optimism.Granite.Spec
