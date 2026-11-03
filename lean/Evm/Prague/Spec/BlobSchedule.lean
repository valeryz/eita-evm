/-
  Evm.Prague.Spec.BlobSchedule — EIP-7691 blob throughput increase: the blob fee
  market's constants at Prague, and the blob base fee as a function of the fork.

  EELS reference (execution-specs, `src/ethereum/forks/prague/vm/gas.py`):
    TARGET_BLOB_GAS_PER_BLOCK = U64(786432)       (6 blobs; was 3 at Cancun)
    MAX_BLOB_GAS_PER_BLOCK    = U64(1179648)      (9 blobs; was 6)
    BLOB_BASE_FEE_UPDATE_FRACTION = Uint(5007716) (was 3338477)
  and `calculate_blob_gas_price` / `calculate_excess_blob_gas` unchanged in shape:
    fake_exponential(MIN_BASE_FEE_PER_BLOB_GAS, excess_blob_gas, BLOB_BASE_FEE_UPDATE_FRACTION)
  (`forks/prague/vm/gas.py`, the same two functions as Cancun's with the new constants).

  Only the constants differ from `Evm.Cancun.Spec.BlobTx`; this file states them and the
  fork-typed price `calculateBlobGasPriceAt`, which is what the emitted host formula
  (`Evm.CL.GasEmit.blobBaseFee`, proved equal in `Evm.CL.GasEmitCancun`) must compute:
  the host prices every type-3 tx and every BLOBBASEFEE with it, so a Prague block
  priced with Cancun's fraction (as the hand-written host formula did until 2026-10-25)
  burns the wrong blob fee from the first Prague blob tx on.

  Inheritance: Osaka keeps these constants (`forks/osaka/vm/gas.py`). The BPO forks
  (EIP-7892, after Osaka) change the target, the max and the fraction per schedule; they
  are not in `Evm.Fork` and not modelled here.
-/

import Evm.Cancun.Spec.BlobTx
import Evm.Forks

namespace Evm.Prague.Spec

/-- `TARGET_BLOB_GAS_PER_BLOCK = 6 · GAS_PER_BLOB = 786432` (EIP-7691). -/
def targetBlobGasPerBlock : Nat := 6 * Evm.Cancun.Spec.gasPerBlob

/-- `MAX_BLOB_GAS_PER_BLOCK = 9 · GAS_PER_BLOB = 1179648` (EIP-7691). -/
def maxBlobGasPerBlock : Nat := 9 * Evm.Cancun.Spec.gasPerBlob

/-- `BLOB_BASE_FEE_UPDATE_FRACTION = 5007716` (EIP-7691). -/
def blobBaseFeeUpdateFraction : Nat := 5007716

/-- The fork's update fraction: Cancun's before Prague, Prague's from Prague on. -/
def blobBaseFeeUpdateFractionAt (f : Evm.Fork) : Nat :=
  if f.atLeast .prague then blobBaseFeeUpdateFraction
  else Evm.Cancun.Spec.blobBaseFeeUpdateFraction

/-- The fork's target blob gas per block: 3 blobs before Prague, 6 from Prague on. -/
def targetBlobGasPerBlockAt (f : Evm.Fork) : Nat :=
  if f.atLeast .prague then targetBlobGasPerBlock
  else Evm.Cancun.Spec.targetBlobGasPerBlock

/-- `calculate_blob_gas_price` at fork `f`: `fake_exponential(1, excess, fraction(f))`.
    At Cancun this is `Evm.Cancun.Spec.calculateBlobGasPrice`. -/
def calculateBlobGasPriceAt (f : Evm.Fork) (excessBlobGas : Nat) : Nat :=
  Evm.Cancun.Spec.fakeExponential Evm.Cancun.Spec.minBaseFeePerBlobGas excessBlobGas
    (blobBaseFeeUpdateFractionAt f)

theorem calculateBlobGasPriceAt_cancun (e : Nat) :
    calculateBlobGasPriceAt .cancun e = Evm.Cancun.Spec.calculateBlobGasPrice e := by
  simp [calculateBlobGasPriceAt, blobBaseFeeUpdateFractionAt, Evm.Fork.atLeast,
        Evm.Fork.ord, Evm.Cancun.Spec.calculateBlobGasPrice]

/-- `calculate_excess_blob_gas` at fork `f` (the target is the fork's):
    `max(0, parent_excess + parent_used − target)`. -/
def calculateExcessBlobGasAt (f : Evm.Fork) (parentExcess parentUsed : Nat) : Nat :=
  let sum := parentExcess + parentUsed
  if sum < targetBlobGasPerBlockAt f then 0 else sum - targetBlobGasPerBlockAt f

theorem calculateExcessBlobGasAt_cancun (pe pu : Nat) :
    calculateExcessBlobGasAt .cancun pe pu = Evm.Cancun.Spec.calculateExcessBlobGas pe pu := by
  simp [calculateExcessBlobGasAt, targetBlobGasPerBlockAt, Evm.Fork.atLeast, Evm.Fork.ord,
        Evm.Cancun.Spec.calculateExcessBlobGas]

end Evm.Prague.Spec
