/-
  Evm.Optimism.Canyon.Spec.ShanghaiInheritance — Canyon = Shanghai
  EL semantics + one OP-only twist.

  Source: optimism-specs `specs/protocol/canyon/overview.md`.

  Canyon inherits the Shanghai EL delta wholesale (PUSH0, EIP-3651
  warm coinbase, EIP-3860 init-code cap+surcharge) AND ships the
  Create2Deployer predeploy at a canonical address. EIP-4895
  withdrawals are *structurally* enabled (the block carries a
  `withdrawalsRoot` field) but the actual list is always empty on
  OP — there are no validator withdrawals on L2.

  This file states the iff:
    * Shanghai EL features are active iff `f ≥ Canyon`.
    * Withdrawals list is EMPTY iff `f ≥ Canyon`  (Bedrock had no
      `withdrawalsRoot` field at all; from Canyon onwards the field
      exists but is always the empty-trie root).
-/

import Evm.BaseTypes
import Evm.Optimism.Forks

namespace Evm.Optimism.Canyon.Spec

/-- Inherits all of Ethereum Shanghai's EL deltas (warm coinbase,
    PUSH0, init-code surcharge, etc.). -/
def inheritsShanghai (f : Evm.Optimism.OpFork) : Bool := f.atLeast .canyon

theorem inherits_shanghai_iff_canyon (f : Evm.Optimism.OpFork) :
    inheritsShanghai f = true ↔ f.atLeast .canyon := by
  unfold inheritsShanghai; rfl

/-- OP-only: even though Canyon adds the `withdrawals` field to the
    block envelope, the list is REQUIRED to be empty on L2 (no
    validator withdrawals on L2). Enforced at block validation. -/
def withdrawalsMustBeEmpty (f : Evm.Optimism.OpFork) : Bool := f.atLeast .canyon

theorem empty_withdrawals_iff_canyon (f : Evm.Optimism.OpFork) :
    withdrawalsMustBeEmpty f = true ↔ f.atLeast .canyon := by
  unfold withdrawalsMustBeEmpty; rfl

/-- Create2Deployer predeploy address — guaranteed present at Canyon+
    (some L2s deploy it later; OP makes it canonical). -/
def create2Deployer : Evm.Address :=
  Evm.Address.ofNat 0x13b0d85ccb8bf860b6b79af3029fca081ae9bf2a

end Evm.Optimism.Canyon.Spec
