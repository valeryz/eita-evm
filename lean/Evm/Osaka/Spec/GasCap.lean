/-
  Evm.Osaka.Spec.GasCap — EIP-7825 transaction gas-limit cap and
  EIP-7892 / Osaka blob count cap.

  EELS reference:
    * EIP-7825: `forks/osaka/transactions.py` lines 30-31 +
      `validate_transaction` lines 547-548:

          TX_MAX_GAS_LIMIT = Uint(16_777_216)
          ...
          if tx.gas > TX_MAX_GAS_LIMIT:
              raise TransactionGasLimitExceededError("Gas limit too high")

    * EIP-7892 (blob count): `forks/osaka/fork.py` lines 123 + 515-519:

          BLOB_COUNT_LIMIT = 6
          ...
          if blob_count > BLOB_COUNT_LIMIT:
              raise BlobCountExceededError(...)

  Per the SPEC-METHODOLOGY: these are cross-cutting validity predicates
  on the transaction shape, not opcode-step relations. They go in a
  dedicated module under `Osaka/Spec/` and are referenced by the
  block-validity predicate (when it lands).

  No refinement obligation here per se: `Evm.Osaka.processTransaction`
  threads these checks directly as early errors, so any execution that
  satisfies the spec's `validTx`/`validBlobCount` is one the implementation
  also accepts.
-/

import Evm.BaseTypes
import Evm.Prague.Transactions

namespace Evm.Osaka.Spec

/-- EIP-7825 constant. -/
def txMaxGasLimit : Nat := 16_777_216

/-- EIP-7892 constant. -/
def blobCountLimit : Nat := 6

/-- The declared gas of a Prague-typed transaction. EELS `tx.gas` is
    the typed-tx-equivalent of the legacy `gas_limit` field. -/
def Evm.Prague.Transaction.gasLimit : Evm.Prague.Transaction → Nat
  | .legacy _ _ gl _ _ _ _ _ _                  => gl.toNat
  | .accessList _ _ _ gl _ _ _ _ _ _ _          => gl.toNat
  | .feeMarket _ _ _ _ gl _ _ _ _ _ _ _         => gl.toNat
  | .blob _ _ _ _ gl _ _ _ _ _ _ _ _ _          => gl.toNat
  | .setCode _ _ _ _ gl _ _ _ _ _ _ _ _         => gl.toNat

/-- Number of blob-versioned-hashes carried by a tx; 0 for non-blob
    txs. -/
def Evm.Prague.Transaction.blobCount : Evm.Prague.Transaction → Nat
  | .blob _ _ _ _ _ _ _ _ _ _ bvh _ _ _ => bvh.length
  | _ => 0

/-- EIP-7825 validity predicate on a single transaction. -/
def IsValidTxGasCap (tx : Evm.Prague.Transaction) : Prop :=
  Evm.Prague.Transaction.gasLimit tx ≤ txMaxGasLimit

/-- EIP-7892 / Osaka blob count validity. -/
def IsValidBlobCount (tx : Evm.Prague.Transaction) : Prop :=
  Evm.Prague.Transaction.blobCount tx ≤ blobCountLimit

end Evm.Osaka.Spec
