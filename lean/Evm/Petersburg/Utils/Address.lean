/-
  Evm.Petersburg.Utils.Address — CREATE2 address derivation (EIP-1014).

  EELS reference: ethereum/forks/constantinople/utils/address.py.

  EELS reuses one `utils/address.py` for both Constantinople and what we
  call Petersburg (EELS has no separate Petersburg directory; its
  `forks/constantinople/` is the no-EIP-1283 fork our project labels
  "Petersburg" — the with-EIP-1283 variant was never mainnet code).

  `compute_create2_contract_address`:

      preimage = b"\xff" + address + salt + keccak256(call_data)
      computed_address = keccak256(preimage)
      return Address(left_pad_zero_bytes(computed_address[-20:], 20))

  The 0xff prefix domain-separates CREATE2 outputs from any plausible
  RLP encoding used by CREATE, so an attacker can't forge a CREATE2
  collision against an existing CREATE address.
-/

import Evm.BaseTypes
import Evm.Crypto.Hash

namespace Evm.Petersburg.Utils

/-- The address that would be assigned to a `CREATE2` issued by `sender`
    with the given 32-byte `salt` and `initCode` (the call_data passed
    to CREATE2, i.e. the contract's init code).

    EELS `compute_create2_contract_address` (forks/constantinople/utils/
    address.py): `Address(keccak256(b"\xff" + address + salt + keccak256(call_data))[-20:])`. -/
def computeCreate2Address
    (sender : Evm.Address) (salt : Evm.U256) (initCode : Evm.Bytes) :
    Evm.Address :=
  let senderBytes := Evm.Address.toBytesBE sender
  let saltBytes   := Evm.U256.toBytesBE salt
  let codeHash    := Evm.Crypto.keccak256Bytes initCode
  let ffByte  : Evm.Bytes := ByteArray.mk #[0xff]
  let preimage    := ffByte ++ senderBytes ++ saltBytes ++ codeHash
  let hash        := Evm.Crypto.keccak256Bytes preimage
  Evm.Address.ofBytesBE (Evm.Bytes.sliceZeroPad hash 12 20)

end Evm.Petersburg.Utils
