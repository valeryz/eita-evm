/-
  Evm.Optimism.Isthmus.Spec.PragueInheritance — Isthmus = Prague EL
  semantics + an operator-fee twist + a withdrawals-root tweak.

  Source: optimism-specs `specs/protocol/isthmus/overview.md`.

  Isthmus inherits the Prague EL package wholesale:
    * EIP-2537  BLS12-381 precompiles (0x0b..0x11)
    * EIP-2935  historical block hashes via predeploy storage
    * EIP-7702  set-code transactions (delegation type 0x04)
    * EIP-7623  calldata cost increase (floor at gasUsed × 16)
    * EIP-7685  general-purpose requests root in header
    * EIP-7691  6→9 max blobs per block (L1-only effect for OP)

  OP-only additions at Isthmus:
    * Operator fee: a new fee component on every user tx, equal to
      `operator_fee_scalar * gas_used / 10^6 + operator_fee_constant`.
      Routed to a new OperatorFeeVault predeploy at
      0x420000000000000000000000000000000000001B.
    * L1Block predeploy gets `setL1BlockValuesIsthmus()` setter
      (selector 0x098999be); the calldata layout grows to carry the
      two new operator-fee scalars.
    * The header `withdrawalsRoot` field, which was the empty-trie
      root at Canyon..Holocene, now becomes the trie root of the
      L2ToL1MessagePasser's storage — i.e. the canonical L2 → L1
      message-queue root, lifted into the header so light clients
      can verify L1 withdrawals against the L1-posted root.
-/

import Evm.BaseTypes
import Evm.Optimism.Forks

namespace Evm.Optimism.Isthmus.Spec

/-- Inherits all of Ethereum Prague's EL deltas. -/
def inheritsPrague (f : Evm.Optimism.OpFork) : Bool := f.atLeast .isthmus

theorem inherits_prague_iff_isthmus (f : Evm.Optimism.OpFork) :
    inheritsPrague f = true ↔ f.atLeast .isthmus := by
  unfold inheritsPrague; rfl

/-- New predeploy: OperatorFeeVault. Receives the operator-fee
    component on every user tx. -/
def operatorFeeVault : Evm.Address :=
  Evm.Address.ofNat 0x420000000000000000000000000000000000001b

/-- Operator fee components are read from L1Block predeploy storage,
    populated by the per-block `setL1BlockValuesIsthmus` system call. -/
structure OperatorFeeParams where
  scalar   : Nat   -- per-gas, scaled by 10^6
  constant : Nat   -- flat per-tx wei
  deriving Repr

/-- Operator fee in wei for a user tx of `gasUsed` gas. -/
def operatorFeeWei (p : OperatorFeeParams) (gasUsed : Nat) : Nat :=
  p.scalar * gasUsed / 1_000_000 + p.constant

/-- The operator-fee component is in effect iff `f ≥ Isthmus`. -/
def hasOperatorFee (f : Evm.Optimism.OpFork) : Bool := f.atLeast .isthmus

theorem operator_fee_iff_isthmus (f : Evm.Optimism.OpFork) :
    hasOperatorFee f = true ↔ f.atLeast .isthmus := by
  unfold hasOperatorFee; rfl

/-- The L2ToL1MessagePasser predeploy: its storage trie root is what
    Isthmus lifts into `header.withdrawalsRoot`. -/
def l2ToL1MessagePasser : Evm.Address :=
  Evm.Address.ofNat 0x4200000000000000000000000000000000000016

/-- Iff: `header.withdrawalsRoot = msgPasser.storageRoot` is the
    invariant iff `f ≥ Isthmus`. Canyon..Holocene leave it as the
    empty-trie root. -/
def withdrawalsRootIsMsgPasserRoot (f : Evm.Optimism.OpFork) : Bool :=
  f.atLeast .isthmus

theorem withdrawals_root_iff_isthmus (f : Evm.Optimism.OpFork) :
    withdrawalsRootIsMsgPasserRoot f = true ↔ f.atLeast .isthmus := by
  unfold withdrawalsRootIsMsgPasserRoot; rfl

end Evm.Optimism.Isthmus.Spec
