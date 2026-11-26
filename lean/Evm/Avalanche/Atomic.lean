/-
  Evm.Avalanche.Atomic — Avalanche C-Chain atomic ImportTx / ExportTx gas and state effects.

  Source: avalanchego d38de7e0
    vms/saevm/cchain/tx             gasUsed (intrinsic + codec version + unsigned bytes + sigs)
    graft/coreth/plugin/evm/atomic  EVMStateTransfer (nAVAX -> wei at x2cRate = 10^9)
-/

namespace Evm.Avalanche.Atomic

/-- nAVAX (9 decimals) to wei (18 decimals): `coreth` `x2cRate`. -/
def x2cRate            : Nat := 1000000000
def atomicIntrinsicGas : Nat := 10000
def atomicGasPerSig    : Nat := 1000
def codecVersionBytes  : Nat := 2

/-- Gas charged for one atomic ImportTx or ExportTx (`cchain/tx` `gasUsed`). -/
def atomicTxGas (unsignedBytes numSigs : Nat) : Nat :=
  atomicIntrinsicGas + codecVersionBytes + unsignedBytes + atomicGasPerSig * numSigs

/-- Convert an atomic nAVAX amount to wei. -/
def weiOfNavax (nAvax : Nat) : Nat := nAvax * x2cRate

/-- Consensus header `gasUsed` of an SAE block: sum of tx gas limits plus total atomic gas. -/
def saeHeaderGas (txGasLimits atomicGas : Nat) : Nat :=
  txGasLimits + atomicGas

theorem atomicTxGas_ge_base (u s : Nat) :
    atomicTxGas u s ≥ atomicIntrinsicGas + codecVersionBytes := by
  unfold atomicTxGas atomicIntrinsicGas codecVersionBytes atomicGasPerSig; omega

theorem weiOfNavax_pos {n : Nat} (h : n > 0) : weiOfNavax n > 0 := by
  unfold weiOfNavax x2cRate; omega

-- Measured vector from avalanche-sae-execution.md §6: 228 unsigned bytes, 1 sig -> 10000 + 2 + 228 + 1000 = 11230
theorem atomicTxGas_measured_vector : atomicTxGas 228 1 = 11230 := by rfl

end Evm.Avalanche.Atomic
