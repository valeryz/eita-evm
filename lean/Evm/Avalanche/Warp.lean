/-
  Evm.Avalanche.Warp — Avalanche Warp Messenger precompile (0x0200..0005), Granite rules.

  Source: avalanchego v1.15.3
    graft/coreth/precompile/contracts/warp/config.go     graniteGasConfig
    graft/coreth/precompile/contracts/warp/contract.go   sendWarpMessage, getBlockchainID,
                                                         getVerifiedWarpMessage, getVerifiedWarpBlockHash
    vms/evm/predicate/predicate.go                       Predicate.Bytes (0xff delimiter)
    vms/platformvm/warp/message.go                       UnsignedMessage, SignedMessage
    vms/platformvm/warp/payload/addressed_call.go        AddressedCall (typeId = 1, max 24 KiB)
-/

import Evm.BaseTypes

namespace Evm.Avalanche.Warp

/-- Granite Warp gas constants (`graft/coreth/precompile/contracts/warp` `graniteGasConfig`). -/
def getBlockchainIdGas : Nat := 200
def verifiedReadGas    : Nat := 750
def sendGas            : Nat := 41500
def sendPerByteGas     : Nat := 8
def verifyGas          : Nat := 125000
def perKeyGas          : Nat := 512
def perSignerGas       : Nat := 250

/-- Codec limits and constants. -/
def codecVersion         : Nat := 0
def payloadHashTypeId    : Nat := 0
def payloadCallTypeId    : Nat := 1
def bitSetSigTypeId      : Nat := 0
def maxPayloadSize       : Nat := 24576   -- 24 KiB
def blsSignatureLen      : Nat := 96
def predicateDelimiter   : UInt8 := 0xff
def addressedCallOverhead : Nat := 14     -- 2 (version) + 4 (typeId) + 4 (srcLen) + 4 (payloadLen)

/-- Gas charged by `sendWarpMessage(bytes)` given the raw ABI argument length (excluding 4-byte selector). -/
def sendWarpGas (argLen : Nat) : Nat :=
  sendGas + sendPerByteGas * argLen

/-- Gas charged by `getVerifiedWarpMessage` / `getVerifiedWarpBlockHash` when reading a verified
    predicate packed across `numKeys` 32-byte access-list storage keys. -/
def readWarpGas (numKeys : Nat) : Nat :=
  verifiedReadGas + perKeyGas * numKeys

/-- Intrinsic predicate gas charged in place of standard EIP-2930 access-list gas for one Warp
    message tuple of `numKeys` storage keys signed by `numSigners` validators (`PredicateGas`). -/
def predicateGas (numKeys numSigners : Nat) : Nat :=
  verifyGas + perKeyGas * numKeys + perSignerGas * numSigners

/-- Byte length of an encoded `AddressedCall(sourceAddr[20], payload)`. -/
def addressedCallLen (payloadLen : Nat) : Nat :=
  addressedCallOverhead + 20 + payloadLen

/-- Whether an `AddressedCall` payload fits within the 24 KiB Warp codec limit. -/
def validAddressedCallLen (payloadLen : Nat) : Bool :=
  decide (addressedCallLen payloadLen ≤ maxPayloadSize)

/-- Number of 32-byte access-list keys needed to pack a message of `msgLen` bytes
    (message bytes + 1 delimiter byte `0xff`, padded up to a multiple of 32). -/
def predicateKeyCount (msgLen : Nat) : Nat :=
  (msgLen + 1 + 31) / 32

theorem sendWarpGas_monotone {a b : Nat} (h : a ≤ b) :
    sendWarpGas a ≤ sendWarpGas b := by
  unfold sendWarpGas sendGas sendPerByteGas; omega

theorem predicateGas_ge_verify (k s : Nat) :
    predicateGas k s ≥ verifyGas := by
  unfold predicateGas verifyGas perKeyGas perSignerGas; omega

theorem predicateKeyCount_pos (msgLen : Nat) :
    predicateKeyCount msgLen ≥ 1 := by
  unfold predicateKeyCount; omega

-- Granite appendix vector: sendWarpMessage(0xdeadbeef) has 96-byte ABI args -> 41500 + 8*96 = 42268
theorem sendWarpGas_granite_appendix : sendWarpGas 96 = 42268 := by rfl

-- Single-key, single-signer Warp predicate: 125000 + 512 + 250 = 125762
theorem predicateGas_one_key_one_signer : predicateGas 1 1 = 125762 := by rfl

end Evm.Avalanche.Warp
