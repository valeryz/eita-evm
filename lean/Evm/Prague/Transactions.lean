/-
  Evm.Prague.Transactions — Prague transaction envelopes (5 variants).

  EELS reference: ethereum/forks/prague/transactions.py.

  Type-byte registry (EIP-2718 envelope):
    * none / 0xc0..0xff — Legacy (Frontier shape; EIP-155 signing at SD).
    * 0x01             — AccessList (EIP-2930, Berlin).
    * 0x02             — FeeMarket  (EIP-1559, London).
    * 0x03             — Blob       (EIP-4844, Cancun).
    * 0x04             — SetCode    (EIP-7702, Prague).

  EIP-7702 set-code adds an `authorization_list`: for each authorization,
  if the signature is valid, the *authority's* code (an EOA's) is set to
  the delegation designator `0xef0100 || delegated_address` (23 bytes).
  A subsequent CALL into that EOA follows the delegation, executing the
  delegated contract's code in the EOA's storage/balance context.

  See `Prague.Utils.Authorization` for the per-authorization processing
  rules (chainId check, nonce bump, signature recovery, etc.).
-/

import Evm.BaseTypes

namespace Evm.Prague

/-- EIP-7702 authorization tuple. EELS: `Authorization` dataclass in
    `ethereum/forks/prague/transactions.py`.

    Wire form: `rlp([chain_id, address, nonce, y_parity, r, s])`.
    `chain_id == 0` is a wildcard meaning "valid on any chain".

    The signed message hash for an authorization is:
        keccak256(MAGIC || rlp([chain_id, address, nonce]))
    with `MAGIC = 0x05` (EIP-7702 §"Behavior"). The authority address is
    `ecrecover(message_hash, y_parity, r, s)`. -/
structure Authorization where
  chainId : Evm.U256
  address : Evm.Address
  nonce   : Evm.U64
  yParity : Evm.U256
  r       : Evm.U256
  s       : Evm.U256
  deriving Repr, Inhabited

/-- Typed access-list entry: an account plus a set of storage slots that
    a transaction declares it will access. EELS:
    `ethereum/forks/prague/transactions.py::Access` (EIP-2930). -/
structure Access where
  account : Evm.Address
  slots   : List Evm.U256
  deriving Repr, Inhabited

/-- Per-EIP-2718 transaction envelope. Same five variants and field
    orders as EELS `LegacyTransaction` / `AccessListTransaction` /
    `FeeMarketTransaction` / `BlobTransaction` / `SetCodeTransaction`. -/
inductive Transaction where
  /-- Pre-Berlin legacy shape (also the only form before EIP-2718). -/
  | legacy
      (nonce    : Evm.U64)
      (gasPrice : Evm.U256)
      (gasLimit : Evm.U64)
      (to       : Option Evm.Address)
      (value    : Evm.U256)
      (data     : Evm.Bytes)
      (v r s    : Evm.U256)
  /-- EIP-2930 type-1: legacy + chainId + accessList. -/
  | accessList
      (chainId    : Evm.U64)
      (nonce      : Evm.U64)
      (gasPrice   : Evm.U256)
      (gasLimit   : Evm.U64)
      (to         : Option Evm.Address)
      (value      : Evm.U256)
      (data       : Evm.Bytes)
      (accessList : List Access)
      (yParity    : Evm.U256)
      (r s        : Evm.U256)
  /-- EIP-1559 type-2: dynamic-fee tx with `maxPriorityFeePerGas` +
      `maxFeePerGas` replacing the single `gasPrice`. -/
  | feeMarket
      (chainId              : Evm.U64)
      (nonce                : Evm.U64)
      (maxPriorityFeePerGas : Evm.U256)
      (maxFeePerGas         : Evm.U256)
      (gasLimit             : Evm.U64)
      (to                   : Option Evm.Address)
      (value                : Evm.U256)
      (data                 : Evm.Bytes)
      (accessList           : List Access)
      (yParity              : Evm.U256)
      (r s                  : Evm.U256)
  /-- EIP-4844 type-3: blob-carrying tx. `to` is mandatory (no blob
      CREATEs). Adds `maxFeePerBlobGas` + `blobVersionedHashes`. -/
  | blob
      (chainId              : Evm.U64)
      (nonce                : Evm.U64)
      (maxPriorityFeePerGas : Evm.U256)
      (maxFeePerGas         : Evm.U256)
      (gasLimit             : Evm.U64)
      (to                   : Evm.Address)
      (value                : Evm.U256)
      (data                 : Evm.Bytes)
      (accessList           : List Access)
      (maxFeePerBlobGas     : Evm.U256)
      (blobVersionedHashes  : List Evm.Hash32)
      (yParity              : Evm.U256)
      (r s                  : Evm.U256)
  /-- EIP-7702 type-4: set-code tx. `to` is mandatory (no
      authorization-only CREATEs). Adds `authorizationList`. -/
  | setCode
      (chainId              : Evm.U64)
      (nonce                : Evm.U64)
      (maxPriorityFeePerGas : Evm.U256)
      (maxFeePerGas         : Evm.U256)
      (gasLimit             : Evm.U64)
      (to                   : Evm.Address)
      (value                : Evm.U256)
      (data                 : Evm.Bytes)
      (accessList           : List Access)
      (authorizationList    : List Authorization)
      (yParity              : Evm.U256)
      (r s                  : Evm.U256)
  deriving Inhabited

namespace Transaction

-- Field counts:
--   legacy:     9  (n, gp, gl, to, v, d, vSig, rSig, sSig)
--   accessList: 11 (cid, n, gp, gl, to, v, d, al, y, r, s)
--   feeMarket:  12 (cid, n, mpf, mf, gl, to, v, d, al, y, r, s)
--   blob:       14 (cid, n, mpf, mf, gl, to, v, d, al, mfbg, bvh, y, r, s)
--   setCode:    13 (cid, n, mpf, mf, gl, to, v, d, al, authl, y, r, s)

/-- Gas-limit projection — `Transaction.gas` in EELS. -/
def gasLimit : Transaction → Evm.U64
  | .legacy     _ _ g _ _ _ _ _ _                 => g
  | .accessList _ _ _ g _ _ _ _ _ _ _             => g
  | .feeMarket  _ _ _ _ g _ _ _ _ _ _ _           => g
  | .blob       _ _ _ _ g _ _ _ _ _ _ _ _ _       => g
  | .setCode    _ _ _ _ g _ _ _ _ _ _ _ _         => g

/-- Calldata projection (the EVM "input" / `tx.data`). -/
def data : Transaction → Evm.Bytes
  | .legacy     _ _ _ _ _ d _ _ _                 => d
  | .accessList _ _ _ _ _ _ d _ _ _ _             => d
  | .feeMarket  _ _ _ _ _ _ _ d _ _ _ _           => d
  | .blob       _ _ _ _ _ _ _ d _ _ _ _ _ _       => d
  | .setCode    _ _ _ _ _ _ _ d _ _ _ _ _         => d

/-- Sender-side nonce. -/
def nonce : Transaction → Evm.U64
  | .legacy     n _ _ _ _ _ _ _ _                 => n
  | .accessList _ n _ _ _ _ _ _ _ _ _             => n
  | .feeMarket  _ n _ _ _ _ _ _ _ _ _ _           => n
  | .blob       _ n _ _ _ _ _ _ _ _ _ _ _ _       => n
  | .setCode    _ n _ _ _ _ _ _ _ _ _ _ _         => n

/-- `to` field. `none` for legacy/accessList/feeMarket = CREATE; blob /
    setCode txs never CREATE so they are lifted to `some`. -/
def to : Transaction → Option Evm.Address
  | .legacy     _ _ _ t _ _ _ _ _                 => t
  | .accessList _ _ _ _ t _ _ _ _ _ _             => t
  | .feeMarket  _ _ _ _ _ t _ _ _ _ _ _           => t
  | .blob       _ _ _ _ _ t _ _ _ _ _ _ _ _       => some t
  | .setCode    _ _ _ _ _ t _ _ _ _ _ _ _         => some t

def value : Transaction → Evm.U256
  | .legacy     _ _ _ _ v _ _ _ _                 => v
  | .accessList _ _ _ _ _ v _ _ _ _ _             => v
  | .feeMarket  _ _ _ _ _ _ v _ _ _ _ _           => v
  | .blob       _ _ _ _ _ _ v _ _ _ _ _ _ _       => v
  | .setCode    _ _ _ _ _ _ v _ _ _ _ _ _         => v

/-- Single-byte EIP-2718 type tag. `none` for legacy. -/
def typeByte : Transaction → Option UInt8
  | .legacy     .. => none
  | .accessList .. => some 0x01
  | .feeMarket  .. => some 0x02
  | .blob       .. => some 0x03
  | .setCode    .. => some 0x04

/-- The authorization list, empty for non-setCode txs. EIP-7702. -/
def authorizationList : Transaction → List Authorization
  | .setCode _ _ _ _ _ _ _ _ _ al _ _ _           => al
  | _                                              => []

/-- The access list (empty for legacy). Named `accesses` to avoid
    clashing with the `accessList` constructor. -/
def accesses : Transaction → List Access
  | .accessList _ _ _ _ _ _ _ al _ _ _            => al
  | .feeMarket  _ _ _ _ _ _ _ _ al _ _ _          => al
  | .blob       _ _ _ _ _ _ _ _ al _ _ _ _ _      => al
  | .setCode    _ _ _ _ _ _ _ _ al _ _ _ _        => al
  | .legacy     ..                                 => []

/-- Blob versioned hashes (empty for non-blob txs). -/
def blobVersionedHashes : Transaction → List Evm.Hash32
  | .blob _ _ _ _ _ _ _ _ _ _ vh _ _ _            => vh
  | _                                              => []

end Transaction

end Evm.Prague
