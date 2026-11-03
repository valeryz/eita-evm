/-
  Evm.Cancun.Vm.Gas — gas constants and helpers added at Cancun.

  EELS references (all in `forks/cancun/`):
    - `vm/gas.py:GAS_TLOAD = 100`               (EIP-1153)
    - `vm/gas.py:GAS_TSTORE = 100`              (EIP-1153)
    - `vm/gas.py:GAS_MCOPY = 3` (per word)      (EIP-5656; base = GAS_VERY_LOW)
    - `vm/gas.py:GAS_BLOBHASH_OPCODE = 3`       (EIP-4844)
    - `vm/gas.py:GAS_BLOBBASEFEE = 2`           (EIP-7516)
    - `vm/gas.py:POINT_EVALUATION_PRECOMPILE_GAS = 50000` (EIP-4844)

  Blob-gas market constants (EIP-4844, `forks/cancun/vm/gas.py` and
  `forks/cancun/fork.py`):
    - GAS_PER_BLOB                  = 2^17  = 131_072
    - TARGET_BLOB_GAS_PER_BLOCK     = 3 * GAS_PER_BLOB = 393_216
    - MAX_BLOB_GAS_PER_BLOCK        = 6 * GAS_PER_BLOB = 786_432
    - MIN_BASE_FEE_PER_BLOB_GAS     = 1
    - BLOB_BASE_FEE_UPDATE_FRACTION = 3_338_477
-/

import Evm.BaseTypes

namespace Evm.Cancun.Vm.Gas

/-! ## Opcode constants -/

/-- EIP-1153 TLOAD: warm-storage-equivalent. -/
def tLoad     : Nat := 100

/-- EIP-1153 TSTORE: warm-storage-equivalent. No refund (transient
    storage already vanishes at end of tx). -/
def tStore    : Nat := 100

/-- EIP-5656 MCOPY base: same tier as MLOAD/MSTORE. -/
def mcopyBase : Nat := 3

/-- EIP-5656 MCOPY per-word: `3 · ⌈len/32⌉` (plus memory expansion). -/
def mcopyWord : Nat := 3

/-- EIP-4844 BLOBHASH opcode (0x49). -/
def blobHash  : Nat := 3

/-- EIP-7516 BLOBBASEFEE opcode (0x4a). -/
def blobBaseFee : Nat := 2

/-! ## EIP-4844 blob gas market -/

/-- Blob gas consumed by one blob: 2^17 = 131072. -/
def gasPerBlob : Nat := 131072

/-- Blocks aim for this much per-block blob gas on average. -/
def targetBlobGasPerBlock : Nat := 3 * gasPerBlob   -- 393_216

/-- Hard cap on per-block blob gas: 6 blobs. -/
def maxBlobGasPerBlock    : Nat := 6 * gasPerBlob   -- 786_432

/-- Floor for the per-unit blob gas price. -/
def minBaseFeePerBlobGas  : Nat := 1

/-- Update-fraction `d` in the AIMD controller for the blob base fee
    (EIP-4844). The 3_338_477 value targets ≈ 1.125× per-block max
    growth when blocks run at the 6-blob cap. -/
def blobBaseFeeUpdateFraction : Nat := 3338477

/-- Point-evaluation precompile (KZG) gas. -/
def pointEvaluation : Nat := 50000

/-! ## fake_exponential and friends

    `fake_exponential(factor, numerator, denominator)` is EELS's
    Taylor-series approximation of `factor · e^(numerator/denominator)`
    used to derive the blob base fee from `excess_blob_gas`. EELS
    (`forks/cancun/vm/gas.py:fake_exponential`):

    ```
    i = 1
    output = 0
    numerator_accumulator = factor * denominator
    while numerator_accumulator > 0:
        output += numerator_accumulator
        numerator_accumulator = (numerator_accumulator * numerator)
                                // (denominator * i)
        i += 1
    return output // denominator
    ```

    We give it a fuel parameter for total-function obligations; the
    loop terminates in O(log) iterations for any realistic input
    (numerator ≤ a few million, denominator = 3_338_477).
-/

/-- Cancun's Taylor-series approximation of `factor·e^(num/den)`.
    `fuel` bounds iterations; realistic call sites are well under 100.

    EELS `forks/cancun/vm/gas.py:fake_exponential`. -/
def fakeExponential (fuel factor numerator denominator : Nat) : Nat :=
  let rec go (fuel acc accumulator i : Nat) : Nat :=
    match fuel with
    | 0 => acc
    | fuel'+1 =>
      if accumulator = 0 then acc
      else
        let acc' := acc + accumulator
        let accumulator' := (accumulator * numerator) / (denominator * i)
        go fuel' acc' accumulator' (i + 1)
  if denominator = 0 then 0
  else (go fuel 0 (factor * denominator) 1) / denominator

/-- Default fuel for `fakeExponential`. Realistic inputs converge in
    fewer than 50 iterations; we give 256 as a safety margin. -/
def fakeExponentialFuel : Nat := 256

/-- Blob base fee derived from the block's `excess_blob_gas`. EELS
    `calculate_blob_gas_price` in `forks/cancun/fork.py`. -/
def calculateBlobGasPrice (excessBlobGas : Nat) : Nat :=
  fakeExponential fakeExponentialFuel minBaseFeePerBlobGas excessBlobGas
                  blobBaseFeeUpdateFraction

/-- New `excess_blob_gas` for a child block, given the parent's
    excess and the parent's blob-gas-used. EELS
    `calculate_excess_blob_gas`. -/
def calculateExcessBlobGas (parentExcessBlobGas parentBlobGasUsed : Nat) : Nat :=
  if parentExcessBlobGas + parentBlobGasUsed < targetBlobGasPerBlock then 0
  else parentExcessBlobGas + parentBlobGasUsed - targetBlobGasPerBlock

end Evm.Cancun.Vm.Gas
