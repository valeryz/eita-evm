/-
  Evm.Homestead.Utils.Signature — sender recovery with the EIP-2 low-s
  signature requirement.

  EELS reference: ethereum/homestead/transactions.py.

  Homestead introduces (via EIP-2) the requirement that the signature's
  `s` value be in `[1, secp256k1n / 2]`. Signing-hash construction is
  unchanged from Frontier; we just gate the recovery on the s-range.
-/

import Evm.BaseTypes
import Evm.Frontier.Transactions
import Evm.Frontier.Utils.Signature

namespace Evm.Homestead.Utils

/-- Half of the secp256k1 group order. Signatures with `s > this` are
    rejected at Homestead+. -/
def secp256k1nHalf : Nat :=
  0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0

def recoverSender (tx : Evm.Frontier.Transaction) : Option Evm.Address :=
  if tx.s.toNat > secp256k1nHalf then none
  else Evm.Frontier.Utils.recoverSender tx

end Evm.Homestead.Utils
