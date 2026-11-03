/-
  Evm.Constantinople.Utils.Address — EIP-1014 deterministic CREATE2
  address derivation.

  EELS reference:
  ethereum/forks/constantinople/utils/address.py line 66
  (`compute_create2_contract_address`).

  Per EIP-1014:

      address = keccak256(0xff || sender || salt || keccak256(init_code))[12:]

  where `sender` is 20 bytes, `salt` is 32 bytes, and the keccak of the
  init code is 32 bytes. The leading `0xff` byte exists so that the
  preimage can never collide with a CREATE-style RLP-encoded
  `[sender, nonce]` preimage (RLP would never start with 0xff there).
-/

import Evm.BaseTypes
import Evm.Crypto.Hash

namespace Evm.Constantinople.Utils

/-- Compute the contract address for a CREATE2 invocation.

    EELS `compute_create2_contract_address`
    (forks/constantinople/utils/address.py lines 66-92).

    `salt` is the U256 popped from the stack, re-encoded as 32 big-
    endian bytes (EELS `salt = pop(...).to_be_bytes32()`).

    The result is the low 20 bytes of `keccak256(0xff || sender || salt
    || keccak256(initCode))`. -/
def computeCreate2Address
    (sender   : Evm.Address)
    (salt     : Evm.U256)
    (initCode : Evm.Bytes) :
    Evm.Address :=
  let senderBytes := Evm.Address.toBytesBE sender
  let saltBytes   := Evm.U256.toBytesBE salt
  let initHash    := Evm.Crypto.keccak256Bytes initCode
  let ffByte      := (ByteArray.empty.push (0xff : UInt8))
  let preimage    := ffByte ++ senderBytes ++ saltBytes ++ initHash
  let hash        := Evm.Crypto.keccak256Bytes preimage
  Evm.Address.ofBytesBE (Evm.Bytes.sliceZeroPad hash 12 20)

end Evm.Constantinople.Utils
