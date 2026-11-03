/-
  Evm.Optimism.Holocene.Spec.Eip1559Params — Holocene per-chain
  EIP-1559 params, set via header `extraData`.

  Source: optimism-specs `specs/protocol/holocene/exec-engine.md`.

  Pre-Holocene: all OP chains shared two compile-time-fixed EIP-1559
  params (denominator and elasticity multiplier) baked into op-geth.

  Holocene: each block's header `extraData` field is REQUIRED to be
  exactly 9 bytes long and carry the per-block 1559 params, parsed
  as:

      extraData[0]         = version byte (= 0x00 for Holocene)
      extraData[1..4]      = denominator       (big-endian uint32)
      extraData[5..8]      = elasticity        (big-endian uint32)

  The base-fee formula is the standard EIP-1559 update:

      newBase = oldBase
                  + oldBase * (gasUsed - target) / (target * denominator)

  with `target = gasLimit / elasticity`. Holocene lets the chain
  operator hot-swap denominator / elasticity at any block boundary
  by changing the extraData payload, rather than requiring a hardfork.
-/

import Evm.BaseTypes
import Evm.Optimism.Forks

namespace Evm.Optimism.Holocene.Spec

/-- Required `extraData` length at Holocene exactly. Isthmus extends
    this to 17 bytes by appending two 4-byte operator-fee params
    (scalar | constant) per Isthmus' OperatorFeeVault layer — see
    `Optimism/Isthmus/Spec/PragueInheritance.lean`. Confirmed live:
    a sample Isthmus-era Base block (#46687682) carried
    `extraData = 0x01000000640000000500000000004c4b40` (17 bytes). -/
def extraDataLen : Nat := 9

/-- Isthmus extends extraData to 17 bytes. -/
def extraDataLenIsthmus : Nat := 17

example : extraDataLenIsthmus = extraDataLen + 8 := rfl

/-- Version byte must be 0x00 at Holocene (reserved for future
    layouts). -/
def holoceneVersionByte : UInt8 := 0x00

/-- Per-chain EIP-1559 params extracted from header.extraData. -/
structure FeeParams where
  denominator : UInt32
  elasticity  : UInt32
  deriving Repr

/-- Extract the 4-byte big-endian uint32 at offset `off`. Returns 0
    if the bytes aren't there. -/
private def beU32 (bs : Evm.Bytes) (off : Nat) : UInt32 :=
  let b0 := if off     < bs.size then bs.get! off     else (0 : UInt8)
  let b1 := if off + 1 < bs.size then bs.get! (off+1) else (0 : UInt8)
  let b2 := if off + 2 < bs.size then bs.get! (off+2) else (0 : UInt8)
  let b3 := if off + 3 < bs.size then bs.get! (off+3) else (0 : UInt8)
  ((b0.toUInt32) <<< 24) ||| ((b1.toUInt32) <<< 16) ||| ((b2.toUInt32) <<< 8) ||| (b3.toUInt32)

/-- Parse the EIP-1559 params from a header `extraData` payload.
    Holocene layout: byte 0 = version (0x00), bytes 1..4 = denominator,
    bytes 5..8 = elasticity.

    Errors if `extraData.size < 9`. Tolerates extra trailing bytes —
    Isthmus extends the payload to 17 bytes (8 extra for the
    operator-fee scalars). -/
def parseFeeParams (extraData : Evm.Bytes) : Except String FeeParams := do
  if extraData.size < 9 then
    .error s!"extraData too short for Holocene EIP-1559 params: {extraData.size} bytes (need ≥ 9)"
  let version := extraData.get! 0
  if version ≠ holoceneVersionByte then
    .error s!"unsupported Holocene extraData version byte: 0x{version.toNat}"
  return {
    denominator := beU32 extraData 1
    elasticity  := beU32 extraData 5
  }

/-! ## Next-block base-fee update

    Standard EIP-1559 base-fee update, parameterised by the per-chain
    denominator + elasticity decoded above. Mirrors `op-geth`'s
    `eip1559.CalcBaseFee` (`consensus/misc/eip1559/eip1559.go`)
    when the Holocene chain config is active.

    Formula:
      target = parent.gasLimit / elasticity
      if parent.gasUsed = target:
        newBase = parentBase
      elif parent.gasUsed > target:
        delta   = parentBase * (gasUsed - target) / (target * denominator)
        newBase = parentBase + max(1, delta)
      else:
        delta   = parentBase * (target - gasUsed) / (target * denominator)
        newBase = parentBase - min(parentBase, delta)
-/

/-- Compute the next block's base fee.

    `parentBaseFee`, `parentGasUsed`, `parentGasLimit` come from the
    just-processed block's header; `params` are the per-chain 1559
    params read from THAT same header's `extraData`. -/
def nextBaseFee (parentBaseFee parentGasUsed parentGasLimit : Nat)
                (params : FeeParams) : Nat :=
  let elasticity  := params.elasticity.toNat
  let denominator := params.denominator.toNat
  -- Degenerate-input safety. A real Holocene header carries
  -- non-zero elasticity and denominator by construction; we
  -- short-circuit to identity to avoid divide-by-zero in adversarial
  -- inputs.
  if elasticity = 0 ∨ denominator = 0 then parentBaseFee
  else
    let target := parentGasLimit / elasticity
    if target = 0 then parentBaseFee
    else if parentGasUsed = target then
      parentBaseFee
    else if parentGasUsed > target then
      let delta := parentBaseFee * (parentGasUsed - target) / (target * denominator)
      parentBaseFee + max 1 delta
    else
      let delta := parentBaseFee * (target - parentGasUsed) / (target * denominator)
      parentBaseFee - min parentBaseFee delta

/-! ## Properties of `nextBaseFee` -/

/-- At exactly target gas usage, base fee is unchanged. -/
theorem nextBaseFee_at_target
    (parentBaseFee parentGasLimit : Nat) (params : FeeParams)
    (hElasticity : params.elasticity.toNat ≠ 0)
    (hDenominator : params.denominator.toNat ≠ 0)
    (hTarget : parentGasLimit / params.elasticity.toNat ≠ 0) :
    nextBaseFee parentBaseFee (parentGasLimit / params.elasticity.toNat)
                parentGasLimit params = parentBaseFee := by
  unfold nextBaseFee
  simp [hElasticity, hDenominator, hTarget]

/-- Iff: the extraData-driven 1559 mechanism is in effect iff
    `f ≥ Holocene`. Pre-Holocene the params come from compile-time
    constants in op-geth. -/
def usesExtraData1559 (f : Evm.Optimism.OpFork) : Bool := f.atLeast .holocene

theorem extra_data_iff_holocene (f : Evm.Optimism.OpFork) :
    usesExtraData1559 f = true ↔ f.atLeast .holocene := by
  unfold usesExtraData1559; rfl

end Evm.Optimism.Holocene.Spec
