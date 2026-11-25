/-
  Evm.Optimism.Cobalt.Fork — Base's Cobalt (2026-09-30 18:00 UTC, timestamp 1790791200).

  Source: base/base @ v1.5.6 (a9f6cc9d). Delta on Beryl, all inside the native precompiles
  (the Ethereum spec stays OSAKA, the static table Beryl's: provider.rs:200-206):

    * two more native precompiles, the transaction context (0x8130…aa02) and the nonce
      manager (0x8130…aa01) (provider.rs:240-243): in Beryl.Spec.nativeKind from Cobalt;
    * the second version of the asset, stablecoin and policy logic (versions.rs);
    * the Cobalt storage features — retired dynamic-storage tails cleared, selector-only ABI
      decode errors (precompiles/src/spec.rs:16-25);
    * the activation registry reads its admin from storage, falling back to the configured
      one, and rejects call value (provider.rs:232-235, activation/dispatch.rs).

  The version, storage-feature and admin choices are the linked logic's, made from the
  upgrade the replay passes it (`eita_base_precompile`'s OP fork ordinal).
-/

import Evm.Optimism.Beryl.Fork

namespace Evm.Optimism.Cobalt

open Evm.Optimism (OpFork)

theorem cobalt_precompiles :
    Beryl.Spec.nativeKind .cobalt Beryl.Spec.txContextAddr = 6 ∧
    Beryl.Spec.nativeKind .cobalt Beryl.Spec.nonceAddr = 7 := by
  decide

/-- Every Beryl native precompile stays one. -/
theorem beryl_kinds_kept (addr : Nat) (h : Beryl.Spec.nativeKind .beryl addr ≠ 0) :
    Beryl.Spec.nativeKind .cobalt addr = Beryl.Spec.nativeKind .beryl addr := by
  unfold Beryl.Spec.nativeKind at *
  by_cases h1 : addr = Beryl.Spec.txContextAddr
  · subst h1; simp_all [OpFork.atLeast, OpFork.ord, Beryl.Spec.txContextAddr,
      Beryl.Spec.factoryAddr, Beryl.Spec.policyAddr, Beryl.Spec.activationAddr, Beryl.Spec.b20Prefix]
  · by_cases h2 : addr = Beryl.Spec.nonceAddr
    · subst h2; simp_all [OpFork.atLeast, OpFork.ord, Beryl.Spec.nonceAddr,
        Beryl.Spec.factoryAddr, Beryl.Spec.policyAddr, Beryl.Spec.activationAddr, Beryl.Spec.b20Prefix]
    · simp_all [OpFork.atLeast, OpFork.ord]

end Evm.Optimism.Cobalt
