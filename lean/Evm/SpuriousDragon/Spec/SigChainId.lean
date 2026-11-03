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

  Implementation reference: `Evm.SpuriousDragon.Utils.Signature.
  recoverSender` (lines 53-63) and `signingHashEIP155` (lines 32-48).
-/

import Evm.Frontier.Vm
import Evm.Frontier.Transactions
import Evm.SpuriousDragon.Utils.Signature

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

/-! ## Signing hash

    The two hash forms differ only in the RLP payload's tail:
    EIP-155 appends `[chainId, 0, 0]`. We re-use the impl-side
    function for the EIP-155 hash to avoid duplicating the RLP
    construction in the spec. -/

/-- The signing hash under EIP-155 (re-exported from the impl). -/
def signingHashEIP155 (tx : Transaction) : Evm.Hash32 :=
  Evm.SpuriousDragon.Utils.signingHashEIP155 tx

/-! ## IsRecoverSenderStep — the recovery relation

    `IsRecoverSenderStep tx sender` holds iff `sender` is the
    address that signed `tx` under SD's combined rule. The
    relation just lifts the impl's `recoverSender` (which is an
    `Option`) into a `Prop` so it can be composed with other tx-
    level specs without committing to either signing scheme. -/
def IsRecoverSenderStep (tx : Transaction) (sender : Evm.Address) : Prop :=
  Evm.SpuriousDragon.Utils.recoverSender tx = some sender

/-! ## EIP-155 path: low-s and chainId-aware recovery

    Sub-relations that pin down each clause separately. Useful for
    refinement proofs that case-split on the signing form. -/

/-- The EIP-155 path. Decomposed:
      1. `v` is in the chainId-augmented range,
      2. `s` ≤ secp256k1.n / 2 (low-s; Homestead carry-over),
      3. ecrecover on the EIP-155 hash with v normalised to {27,28}
         returns `sender`. -/
def IsRecoverSenderEip155 (tx : Transaction) (sender : Evm.Address) : Prop :=
  IsEip155Signed tx ∧
  tx.s.toNat ≤ Evm.Homestead.Utils.secp256k1nHalf ∧
  let recoverV := Evm.U256.ofNat (tx.v.toNat - chainId * 2 - 35 + 27)
  Evm.Crypto.recover (signingHashEIP155 tx) recoverV tx.r tx.s = some sender

/-- The legacy (Homestead-form) path. Inherited unchanged from
    Homestead's recoverSender — restated here just to label the
    branch. -/
def IsRecoverSenderLegacy (tx : Transaction) (sender : Evm.Address) : Prop :=
  IsLegacySigned tx ∧
  Evm.Homestead.Utils.recoverSender tx = some sender

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
      The recovery relation for typed txs lives at
      `Evm.Berlin.Spec.TypedTx`. -/

end Evm.SpuriousDragon.Spec
