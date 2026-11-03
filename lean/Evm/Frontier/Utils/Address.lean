/-
  Evm.Frontier.Utils.Address — contract-creation address derivation.

  EELS reference: ethereum/frontier/utils/address.py.

  The CREATE opcode and contract-creation transactions derive the new
  contract's address from `keccak256(rlp([sender, nonce]))[12:32]`. The
  CREATE2 variant (Constantinople, EIP-1014) lives at a later fork.
-/

import Evm.BaseTypes
import Evm.Rlp
import Evm.Crypto.Hash

namespace Evm.Frontier.Utils

/-- Encode a `Nat` as the minimal big-endian byte string per RLP rules:
    no leading zero bytes; zero itself encodes to the empty string. -/
private def natToMinBytes (n : Nat) : Evm.Bytes := Id.run do
  if n = 0 then return Evm.Bytes.empty
  let mut out : List UInt8 := []
  let mut x := n
  while x > 0 do
    out := UInt8.ofNat (x % 256) :: out
    x := x / 256
  pure (ByteArray.mk out.toArray)

/-- The contract address that would be assigned to a `CREATE` issued by
    `sender` with the given current `nonce`. -/
def computeContractAddress (sender : Evm.Address) (nonce : Nat) : Evm.Address :=
  let senderBytes := Evm.Address.toBytesBE sender
  let nonceBytes  := natToMinBytes nonce
  let rlpEncoded  := Evm.Rlp.encode (.list [.bytes senderBytes, .bytes nonceBytes])
  let hash        := Evm.Crypto.keccak256Bytes rlpEncoded
  -- Take the low 20 bytes of the hash.
  Evm.Address.ofBytesBE (Evm.Bytes.sliceZeroPad hash 12 20)

end Evm.Frontier.Utils
