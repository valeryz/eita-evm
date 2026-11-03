/-
  Evm.Cancun.Spec.BlobbasefeeStep — EIP-7516 BLOBBASEFEE (0x4a).

  EELS reference: `forks/cancun/vm/instructions/block.py`
  `blob_base_fee` (gas constant `GAS_BASE = 2`).

  BLOBBASEFEE pushes the current block's `blob_base_fee`, computed by
  `fake_exponential(MIN_BASE_FEE_PER_BLOB_GAS, excess_blob_gas,
  BLOB_BASE_FEE_UPDATE_FRACTION)` and plumbed into the EVM via
  `Environment.blobBaseFee`. Gas: 2 (BASE tier).

  This is just the EIP-3198 BASEFEE shape with a different env field.

  Inheritance: applies unchanged at Prague.
-/

import Evm.Frontier.Spec.StepShapes

namespace Evm.Cancun.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Spec (IsNullaryPushStep)

/-- 0x4a BLOBBASEFEE. Pushes `env.blobBaseFee` as a `U256`. Charges
    2 gas (BASE tier). -/
abbrev IsBlobbasefeeStep : Evm → Evm → Prop :=
  IsNullaryPushStep (fun evm => Evm.U256.ofNat evm.env.blobBaseFee) Gas.base

end Evm.Cancun.Spec
