/-
  Evm.SpuriousDragon.Utils.Signature — EIP-155 chainId-aware sender
  recovery.

  EELS reference: ethereum/spurious_dragon/transactions.py.

  EIP-155 introduces two distinct transaction-signing schemes that
  coexist post-SD:
    * Legacy / pre-EIP-155 form: `v ∈ {27, 28}`. Signing hash is the
      Frontier form `keccak256(rlp([nonce, gasPrice, gas, to, value, data]))`.
    * EIP-155 form: `v ∈ {2·chainId+35, 2·chainId+36}`. Signing hash
      includes the chainId as a "phantom" three-field suffix:
      `keccak256(rlp([nonce, gasPrice, gas, to, value, data, chainId, 0, 0]))`.

  Mainnet (and the test fixtures we run) use chainId = 1.
-/

import Evm.BaseTypes
import Evm.Rlp
import Evm.Crypto.Hash
import Evm.Crypto.EcRecover
import Evm.Frontier.Transactions
import Evm.Frontier.Utils.Signature
import Evm.Homestead.Utils.Signature

namespace Evm.SpuriousDragon.Utils

/-- Test-fixture chainId (= mainnet chainId). -/
def chainId : Nat := 1

/-- The EIP-155 signing hash form. -/
def signingHashEIP155 (tx : Evm.Frontier.Transaction) : Evm.Hash32 :=
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
    , .bytes (Evm.Rlp.natToBytes chainId)
    , .bytes Evm.Bytes.empty
    , .bytes Evm.Bytes.empty
    ])
  Evm.Crypto.keccak256 payload

/-- Recover the sender of `tx`. Tries the EIP-155 form if `v` matches
    the chainId-augmented range; otherwise falls back to Homestead's
    pre-EIP-155 recovery (which already enforces the low-s rule). -/
def recoverSender (tx : Evm.Frontier.Transaction) : Option Evm.Address :=
  let vN := tx.v.toNat
  if vN = chainId * 2 + 35 ∨ vN = chainId * 2 + 36 then
    -- EIP-155 form. Normalise v to {27, 28} for ecrecover, and reuse
    -- the low-s check from Homestead.
    if tx.s.toNat > Evm.Homestead.Utils.secp256k1nHalf then none
    else
      let recoverV := Evm.U256.ofNat (vN - chainId * 2 - 35 + 27)
      Evm.Crypto.recover (signingHashEIP155 tx) recoverV tx.r tx.s
  else
    Evm.Homestead.Utils.recoverSender tx

end Evm.SpuriousDragon.Utils
