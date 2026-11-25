/-
  Evm.Optimism.Beryl.Fork — Base's Beryl (2026-06-25 18:00 UTC, timestamp 1782410400):
  the B-20 native precompiles.

  Source: base/base @ v1.5.6 (a9f6cc9d). Delta on Azul, and nothing else in the execution
  layer (crates/common/evm/src/spec.rs: Beryl's Ethereum spec is OSAKA, as Azul's;
  precompiles/src/provider.rs:194-198: its static precompile table is Azul's):

    * the B-20 factory (0xB20F…), the B-20 token addresses (asset and stablecoin), the policy
      registry (0x8453…02) and the activation registry (0x8453…01) are stateful native
      precompiles (provider.rs:214-239): Spec.NativePrecompiles. Each runs its first
      version (`*Versions::from_base_upgrade`, e.g. b20_asset/versions.rs); the activation
      registry's admin is the chain's configured one (chains/src/config.rs:146-148, 325-333).

  The Lean block driver (Replay.Dispatch) does not run Beryl blocks: a native precompile's
  logic is base/base's linked code, outside this interpreter. The replay runs them with the
  rules here (Replay.Emit, src/chains/op.lisp) and that code (rust/base).
-/

import Evm.Optimism.Azul.Fork
import Evm.Optimism.Beryl.Spec.NativePrecompiles

namespace Evm.Optimism.Beryl

open Evm.Optimism (OpFork)

/-- Beryl's static precompile table is Azul's (provider.rs:194-198). -/
abbrev staticPrecompiles := Evm.Optimism.Azul.azulPrecompiles

/-- No native precompile before Beryl. -/
theorem no_native_before (f : OpFork) (h : f.ord < OpFork.beryl.ord) (addr : Nat) :
    Spec.nativeKind f addr = 0 := by
  cases f <;> simp_all [Spec.nativeKind, OpFork.atLeast, OpFork.ord]

/-- The Cobalt precompiles are not Beryl's. -/
theorem no_cobalt_precompiles :
    Spec.nativeKind .beryl Spec.txContextAddr = 0 ∧ Spec.nativeKind .beryl Spec.nonceAddr = 0 := by
  decide

end Evm.Optimism.Beryl
