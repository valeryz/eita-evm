/-
  Evm.Frontier.Utils.Signature — transaction signing hash + sender
  recovery for the pre-EIP-155 (Frontier / Homestead) format.

  EELS reference: ethereum/frontier/transactions.py (signing_hash and
  recover_sender).

  Signing hash: `keccak256(rlp([nonce, gasPrice, gas, to, value, data]))`.
  EIP-155 (Spurious Dragon) extends this to include chainId in the
  hashed payload; that variant goes in a later fork's Utils module.
-/

import Evm.BaseTypes
import Evm.Rlp
import Evm.Crypto.Hash
import Evm.Crypto.EcRecover
import Evm.Frontier.Transactions

namespace Evm.Frontier.Utils

/-- The Frontier / Homestead signing hash of `tx`. -/
def signingHash (tx : Transaction) : Evm.Hash32 :=
  let toItem : Evm.Rlp.Item :=
    match tx.to with
    | some a => .bytes (Evm.Address.toBytesBE a)
    | none   => .bytes Evm.Bytes.empty
  let payload := Evm.Rlp.encode (.list
    [ .bytes (Evm.Rlp.natToBytes tx.nonce.toNat)
    , .bytes (Evm.Rlp.natToBytes tx.gasPrice.toNat)
    , .bytes (Evm.Rlp.natToBytes tx.gas.toNat)
    , toItem
    , .bytes (Evm.Rlp.natToBytes tx.value.toNat)
    , .bytes tx.data
    ])
  Evm.Crypto.keccak256 payload

/-- Recover the sender of `tx`. Returns `none` on a malformed signature.
    Frontier does not check the s-value upper bound; Homestead does
    (EIP-2). -/
def recoverSender (tx : Transaction) : Option Evm.Address :=
  Evm.Crypto.recover (signingHash tx) tx.v tx.r tx.s

end Evm.Frontier.Utils
