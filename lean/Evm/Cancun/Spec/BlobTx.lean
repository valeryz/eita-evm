/-
  Evm.Cancun.Spec.BlobTx — EIP-4844 blob-transaction (type-3) and the
  blob gas market.

  EELS reference: `forks/cancun/vm/gas.py` (`fake_exponential`,
  `calculate_excess_blob_gas`, `calculate_blob_gas_price`),
  `forks/cancun/transactions.py` (blob-tx validation), and
  `forks/cancun/fork.py` `process_transaction` (blob-fee burn).

  Two interlinked pieces of state machinery:

    1. **Blob gas accounting.** Each block carries a `blob_gas_used`
       (sum of `GAS_PER_BLOB · #blobs` over all txs in the block) and
       an `excess_blob_gas` (running counter capped at zero). The next
       block's `excess_blob_gas` is `max(0, parent.excess - target) +
       parent.used`. The target is `TARGET_BLOB_GAS_PER_BLOCK =
       3 · GAS_PER_BLOB = 393216`.

    2. **Blob fee market.** Given a block's `excess_blob_gas`, the
       blob base fee is
            `fake_exponential(1, excess, 3338477)`
       with `fake_exponential` an integer Taylor-series approximation
       of `factor · exp(numerator / denominator)`. The minimum is 1
       wei/gas. The blob fee a tx pays is
            `blobs · GAS_PER_BLOB · blob_base_fee`.

    3. **Per-tx limit.** `MAX_BLOB_GAS_PER_TRANSACTION =
       6 · GAS_PER_BLOB = 786432`, i.e. at most 6 blobs per tx.

  This module specs:
    * the `Nat`-valued constants,
    * the `fakeExponential` integer Taylor series,
    * `calculateExcessBlobGas` (parent → child),
    * `calculateBlobGasPrice` (excess → wei/gas),
    * `IsBlobGasValid` (per-tx bound on number of blobs),
    * the per-tx blob-fee formula.

  The KZG verification predicate is in `KzgStep.lean`. The opcode-level
  BLOBHASH / BLOBBASEFEE are in their own files.

  Inheritance: applies unchanged at Prague.
-/

import Evm.BaseTypes

namespace Evm.Cancun.Spec

/-! ## EIP-4844 constants. EELS: `forks/cancun/vm/gas.py` and
    `forks/cancun/transactions.py`. -/

/-- `GAS_PER_BLOB = 2^17 = 131072` (EELS: `vm/gas.py`). Each blob
    contributes this many "blob gas" units, distinct from EVM gas. -/
def gasPerBlob : Nat := 131072  -- 1 <<< 17

/-- `TARGET_BLOB_GAS_PER_BLOCK = 3 · GAS_PER_BLOB = 393216`. The
    blob-fee equilibrium point: when blob usage averages this per
    block, `excess_blob_gas` stays at zero. -/
def targetBlobGasPerBlock : Nat := 3 * gasPerBlob

/-- `MAX_BLOB_GAS_PER_BLOCK = 6 · GAS_PER_BLOB = 786432`. The hard
    cap on per-block blob gas — also the per-tx maximum, since a tx
    cannot exceed a block's worth of blob gas. -/
def maxBlobGasPerBlock : Nat := 6 * gasPerBlob

/-- `MAX_BLOB_COUNT_PER_TRANSACTION = 6`. Equivalent to
    `MAX_BLOB_GAS_PER_BLOCK / GAS_PER_BLOB`. EELS:
    `forks/cancun/transactions.py::MAX_BLOB_GAS_PER_TRANSACTION`. -/
def maxBlobCountPerTransaction : Nat := 6

/-- `MIN_BASE_FEE_PER_BLOB_GAS = 1` wei/gas. EELS:
    `forks/cancun/vm/gas.py::MIN_BASE_FEE_PER_BLOB_GAS`. -/
def minBaseFeePerBlobGas : Nat := 1

/-- `BLOB_BASE_FEE_UPDATE_FRACTION = 3338477`. The denominator of
    the exponential. Chosen so that the price doubles every
    `~5 * TARGET_BLOB_GAS_PER_BLOCK = ~1965 KB` of excess. EELS:
    `forks/cancun/vm/gas.py::BLOB_BASE_FEE_UPDATE_FRACTION`. -/
def blobBaseFeeUpdateFraction : Nat := 3338477

/-! ## `fake_exponential` — integer Taylor series

    EELS source (`forks/cancun/vm/gas.py`):

        def fake_exponential(factor, numerator, denominator):
            i = 1
            output = 0
            numerator_accum = factor * denominator
            while numerator_accum > 0:
                output += numerator_accum
                numerator_accum = (numerator_accum * numerator) // (denominator * i)
                i += 1
            return output // denominator

    Computes `factor · e^(numerator / denominator)` rounded down,
    using a Taylor series that terminates when the accumulator
    underflows to zero. Pure integer arithmetic — no floats. -/

/-- Integer Taylor-series exponential approximation used by the blob
    fee market. The recursion shape is `numerator_accum`-decreasing
    so it terminates; we expose a fuel-bounded variant for Lean
    totality and pick a `fuel` large enough that mainnet excess
    values never starve. -/
def fakeExponential (factor numerator denominator : Nat) : Nat :=
  let rec loop (fuel : Nat) (output : Nat) (numerAccum : Nat) (i : Nat) : Nat :=
    match fuel with
    | 0 => output
    | fuel+1 =>
      if numerAccum = 0 then output
      else
        let output'    := output + numerAccum
        let numerAccum' := (numerAccum * numerator) / (denominator * i)
        loop fuel output' numerAccum' (i + 1)
  loop 1024 0 (factor * denominator) 1 / denominator

/-- The blob base fee a given block charges per blob-gas. EELS:
    `forks/cancun/vm/gas.py::calculate_blob_gas_price`. Always
    `≥ MIN_BASE_FEE_PER_BLOB_GAS = 1`. -/
def calculateBlobGasPrice (excessBlobGas : Nat) : Nat :=
  fakeExponential minBaseFeePerBlobGas excessBlobGas blobBaseFeeUpdateFraction

/-- The next block's `excess_blob_gas` given the parent's. EELS:
    `forks/cancun/vm/gas.py::calculate_excess_blob_gas`:

        if parent_excess + parent_used < TARGET:
            return 0
        else:
            return parent_excess + parent_used - TARGET
    -/
def calculateExcessBlobGas (parentExcess parentUsed : Nat) : Nat :=
  let sum := parentExcess + parentUsed
  if sum < targetBlobGasPerBlock then 0
  else sum - targetBlobGasPerBlock

/-! ## Per-transaction predicates -/

/-- Total blob gas a tx with `#blobs` blobs consumes. -/
def txBlobGas (numBlobs : Nat) : Nat :=
  gasPerBlob * numBlobs

/-- The blob fee (in wei) a tx pays into the block: `blobBaseFee ·
    txBlobGas`. EELS: `forks/cancun/fork.py::process_transaction`
    lines around the blob-fee burn (`blob_gas_fee` variable). -/
def txBlobFee (blobBaseFee numBlobs : Nat) : Nat :=
  blobBaseFee * txBlobGas numBlobs

/-- The per-tx limit predicate: at most 6 blobs. EELS:
    `forks/cancun/transactions.py::validate_transaction` around the
    `MAX_BLOB_GAS_PER_TRANSACTION` check. -/
def IsBlobCountValid (numBlobs : Nat) : Prop :=
  0 < numBlobs ∧ numBlobs ≤ maxBlobCountPerTransaction

/-- The sender-affordability predicate for the blob fee. EELS:
    `forks/cancun/transactions.py::validate_transaction` checks that
    `sender.balance ≥ tx.value + tx.gas · tx.max_fee_per_gas +
    tx.max_fee_per_blob_gas · tx_blob_gas`. Here we factor out the
    blob-fee portion: the sender must be able to afford
    `max_fee_per_blob_gas · txBlobGas`. -/
def IsBlobAffordable (senderBalance value gasLimit maxFeePerGas
                      maxFeePerBlobGas numBlobs : Nat) : Prop :=
  senderBalance ≥ value + gasLimit * maxFeePerGas
                + maxFeePerBlobGas * txBlobGas numBlobs

/-- The blob-base-fee acceptance predicate: a tx is included in a
    block only if its `max_fee_per_blob_gas` is at least the block's
    `blob_base_fee`. EELS: validate_transaction. -/
def IsBlobFeeBidSufficient (maxFeePerBlobGas blobBaseFee : Nat) : Prop :=
  maxFeePerBlobGas ≥ blobBaseFee

/-! ## What we encoded vs. axiomatised

    Fully encoded:
      * The two constants of the EIP (target / max).
      * `fake_exponential` as a closed-form integer Taylor series
        (fuel-bounded for Lean termination).
      * `calculate_excess_blob_gas` and `calculate_blob_gas_price`
        as direct ports of the EELS one-liners.
      * Per-tx predicates: blob count, affordability, fee-bid.

    Not encoded (intentional gaps):
      * The blob-data side channel itself (the actual 4096 field-
        elements per blob) — they're not visible to the EVM, only
        their KZG commitments and versioned hashes are. `KzgStep`
        handles the precompile that proves a blob-evaluation;
        BLOBHASH exposes the versioned hash.
      * Block-level aggregation (the verifier's
        `total_blob_gas == sum_over_txs`). That's a one-line equation
        but lives in the block-validity spec, not here.

    Per the task brief the per-block bound and `BLOB_BASE_FEE_UPDATE_FRACTION`
    constant are the "trickiest" parts of EIP-4844; both are inline
    above with their EELS line refs. -/

end Evm.Cancun.Spec
