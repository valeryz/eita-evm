/-
  Evm.Cancun.Spec.BlobhashStep — EIP-4844 BLOBHASH (0x49).

  EELS reference: `forks/cancun/vm/instructions/block.py` `blob_hash`
  (gas constant `GAS_BLOBHASH = 3` in `forks/cancun/vm/gas.py`).

  BLOBHASH pops `index`, pushes the `index`-th versioned hash from
  the current transaction's `blob_versioned_hashes` list, or `0` if
  `index ≥ len(blob_versioned_hashes)`. Gas: 3 (VERY_LOW tier).

  The list is per-transaction, plumbed through
  `Environment.blobVersionedHashes`. For non-blob transactions the
  list is empty, so every BLOBHASH returns 0.

  Inheritance: applies unchanged at Prague.
-/

import Evm.Frontier.Spec.StepShapes

namespace Evm.Cancun.Spec

open Evm.Frontier.Vm
open Evm.Frontier.Spec (IsUnaryStep)

/-- Look up `evm.env.blobVersionedHashes[index]`, returning `0` for
    out-of-bounds. The list-getter `getD` does this directly. -/
def blobHashAt (env : Environment) (index : Nat) : Evm.U256 :=
  match env.blobVersionedHashes[index]? with
  | some h => h
  | none   => 0

/-- 0x49 BLOBHASH. Pops `index : U256`, pushes `versioned_hashes[index]`
    or 0 if OOB. Gas: 3 (VERY_LOW tier; named `Gas.veryLow`).

    Implemented as a parameterised `IsUnaryStep` over the lookup
    function — but the value DEPENDS on `evm.env`, which the unary
    shape's `op` doesn't capture. So we hand-roll the predicate. -/
def IsBlobhashStep (evm evm' : Evm) : Prop :=
  ∃ index rest,
    evm.stack = index :: rest ∧
    rest.length < stackLimit ∧
    evm.gasLeft ≥ Gas.veryLow ∧
    evm' = { evm with
      stack   := blobHashAt evm.env index.toNat :: rest,
      gasLeft := evm.gasLeft - Gas.veryLow,
      pc      := evm.pc + 1 }

end Evm.Cancun.Spec
