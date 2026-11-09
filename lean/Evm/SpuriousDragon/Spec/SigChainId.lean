/-
  Evm.SpuriousDragon.Spec.SigChainId — EIP-155 chainId in signing
  hash. The relation states the recovery side: given `(tx, sender)`,
  when is `sender` the correct recovery for `tx` under SD's
  chainId-augmented rule?

  EELS reference: `forks/spurious_dragon/transactions.py::
  recover_sender` (selects between the legacy 27/28 form and the
  EIP-155 form keyed on `v`'s range).

  EIP-155 introduces two co-existing transaction-signing schemes
  post-SD:

    * **Legacy / pre-EIP-155**: `v ∈ {27, 28}`. Signing hash is the
      Frontier form `keccak256(rlp([nonce, gasPrice, gas, to, value,
      data]))`. Inherited from Frontier.

    * **EIP-155**: `v ∈ {2·chainId + 35, 2·chainId + 36}`. Signing
      hash includes a chainId suffix:
      `keccak256(rlp([nonce, gasPrice, gas, to, value, data,
      chainId, 0, 0]))`. The recovery `v` is normalised to {27, 28}
      before being fed to ecrecover.

  Mainnet (and the test fixtures the impl runs) use chainId = 1.

  Implementation: `Evm.SpuriousDragon.Utils.recoverSender`, proved
  against `IsRecoverSenderStep` in `Refinement.recoverSender_sound`.
-/

import Evm.Frontier.Vm
import Evm.Frontier.Transactions
import Evm.SpuriousDragon.Utils.Signature
import Evm.Frontier.Vm.Tx

namespace Evm.SpuriousDragon.Spec

open Evm.Frontier (Transaction)

/-! ## Discriminator: which signing form does this tx use?

    Recall EIP-155: `v ∈ {2·chainId + 35, 2·chainId + 36}` ⇒ new
    form, otherwise legacy. -/

/-- The currently-deployed chainId for the spec. Matches the impl's
    `Evm.SpuriousDragon.Utils.chainId = 1` and is mainnet's id. -/
def chainId : Nat := Evm.SpuriousDragon.Utils.chainId

/-- `tx` is signed under the EIP-155 chainId form. -/
def IsEip155Signed (tx : Transaction) : Prop :=
  tx.v.toNat = chainId * 2 + 35 ∨ tx.v.toNat = chainId * 2 + 36

/-- `tx` is signed under the legacy Frontier/Homestead form. -/
def IsLegacySigned (tx : Transaction) : Prop :=
  tx.v.toNat = 27 ∨ tx.v.toNat = 28

/-! ## Signing hashes (EELS `forks/spurious_dragon/transactions.py`)

    `signing_hash_pre155` 201-221: `keccak256(rlp((nonce, gas_price, gas, to,
    value, data)))`; `signing_hash_155` 224-249: the same list followed by
    `chain_id, 0, 0`. An RLP integer is its minimal big-endian bytes
    (`Rlp.natToBytes`), `0` the empty string; a contract creation's `to` is the
    empty string. -/

/-- RLP item of the `to` field (EELS `Bytes0` for a creation). -/
def toItem (tx : Transaction) : Evm.Rlp.Item :=
  match tx.to with
  | some a => .bytes (Evm.Address.toBytesBE a)
  | none   => .bytes Evm.Bytes.empty

/-- EELS `signing_hash_pre155`. -/
def signingHashPre155 (tx : Transaction) : Evm.Hash32 :=
  Evm.Crypto.keccak256 (Evm.Rlp.encode (.list
    [ .bytes (Evm.Rlp.natToBytes tx.nonce.toNat), .bytes (Evm.Rlp.natToBytes tx.gasPrice.toNat),
      .bytes (Evm.Rlp.natToBytes tx.gas.toNat), toItem tx,
      .bytes (Evm.Rlp.natToBytes tx.value.toNat), .bytes tx.data ]))

/-- EELS `signing_hash_155 (tx, chain_id)`. -/
def signingHash155 (tx : Transaction) (cid : Nat) : Evm.Hash32 :=
  Evm.Crypto.keccak256 (Evm.Rlp.encode (.list
    [ .bytes (Evm.Rlp.natToBytes tx.nonce.toNat), .bytes (Evm.Rlp.natToBytes tx.gasPrice.toNat),
      .bytes (Evm.Rlp.natToBytes tx.gas.toNat), toItem tx,
      .bytes (Evm.Rlp.natToBytes tx.value.toNat), .bytes tx.data,
      .bytes (Evm.Rlp.natToBytes cid), .bytes Evm.Bytes.empty, .bytes Evm.Bytes.empty ]))

/-! ## IsRecoverSenderStep — EELS `recover_sender` 166-198, clause by clause

    The curve recovery `secp256k1_recover` is a trusted oracle, a parameter
    `ecrecover hash v r s` in the precompile's convention (`v ∈ {27, 28}` is
    the recovery id + 27; the address is the low 20 bytes of the key's
    keccak). The clauses EELS itself states are explicit:

      * `0 < r < SECP256K1N` ("bad r"), `0 < s ≤ SECP256K1N // 2` ("bad s");
      * `v ∈ {27, 28}`: recover over `signing_hash_pre155` with `v`;
      * otherwise the EIP-155 form, `chain_id = (v - 35) >> 1` and recovery
        id `(v - 35) & 1`, over `signing_hash_155(tx, chain_id)`. The chain id
        must be the block's (`check_transaction` 390-395, `chain_id != block
        chain_id` raises), here mainnet's `chainId = 1`, so `v ∈ {37, 38}`.

    Restated 2026-11-09: this relation used to be `recoverSender tx = some
    sender` — the implementation itself. -/
def IsRecoverSenderStep (ecrecover : Evm.Hash32 → Evm.U256 → Evm.U256 → Evm.U256 → Option Evm.Address)
    (tx : Transaction) (sender : Evm.Address) : Prop :=
  0 < tx.r.toNat ∧ tx.r.toNat < Evm.Frontier.Vm.Tx.secp256k1n ∧
  0 < tx.s.toNat ∧ tx.s.toNat ≤ Evm.Frontier.Vm.Tx.secp256k1n / 2 ∧
  ((IsLegacySigned tx ∧ ecrecover (signingHashPre155 tx) tx.v tx.r tx.s = some sender) ∨
   (IsEip155Signed tx ∧
    ecrecover (signingHash155 tx chainId) (Evm.U256.ofNat ((tx.v.toNat - 35) % 2 + 27))
      tx.r tx.s = some sender))

/-! ## Structural fact: recovery is at most one of the two paths -/

/-- The two `v`-ranges are disjoint for chainId = 1: legacy is
    {27, 28}, EIP-155 is {37, 38}. -/
theorem signing_forms_disjoint (tx : Transaction)
    (hLeg : IsLegacySigned tx) (hEip : IsEip155Signed tx) : False := by
  -- chainId = 1, so EIP-155 v ∈ {37, 38}; legacy v ∈ {27, 28}.
  -- These don't overlap.
  rcases hLeg with hL | hL <;> rcases hEip with hE | hE <;>
    (simp only [chainId, Evm.SpuriousDragon.Utils.chainId] at hL hE; omega)

/-! ## Notes

    - For mainnet replay starting at SD's activation block, the
      `IsEip155Signed` branch dominates: every wallet-signed tx
      includes the chainId. Pre-SD txs in the chain history use
      `IsLegacySigned` and continue to recover.

    - `chainId` is a constant in this spec. The dynamic chainId
      (different chains, different testnets) lands at Istanbul as
      the CHAINID opcode (EIP-1344) — but for the recovery rule,
      the chain's own id is read out of the protocol context
      (`Environment.chainId`), not the opcode. We keep `chainId =
      1` here to match the impl + replay corpus.

    - The `tx.s ≤ n/2` low-s rule is from Homestead (EIP-2). Re-
      asserted here to make the SD recovery predicate fully self-
      contained.

    - Berlin's typed-tx envelope (EIP-2718) introduces new tx
      shapes whose signing hashes don't go through this relation.
      Tx decoding is the host's (no Lean decoder), so no typed-tx
      envelope relation is stated in Lean. -/

end Evm.SpuriousDragon.Spec
