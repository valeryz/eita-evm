/-
  Evm.Prague.Requests — EIP-7685 execution-layer requests.

  EELS reference: ethereum/forks/prague/requests.py and
  ethereum/forks/prague/fork.py (the `apply_body` block where each
  request type is collected and `compute_requests_hash` runs).

  Three request types in Prague:

    * `DEPOSIT_REQUEST_TYPE = 0x00` (EIP-6110): parsed from receipts
      whose `address == DEPOSIT_CONTRACT_ADDRESS`. The deposit contract
      emits a `DepositEvent` log; the request payload is the
      ABI-decoded log data: pubkey (48) || withdrawal_credentials (32)
      || amount (8, LE) || signature (96) || index (8, LE) = 192 bytes.

    * `WITHDRAWAL_REQUEST_TYPE = 0x01` (EIP-7002): after txs run,
      `apply_body` makes a SYSTEM call into
      WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS; its return data is a
      sequence of 76-byte tuples (source_address 20 ||
      validator_pubkey 48 || amount 8 bytes BE).

    * `CONSOLIDATION_REQUEST_TYPE = 0x02` (EIP-7251): same shape as
      withdrawal requests but to
      CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS; return data is 116-byte
      tuples (source_address 20 || source_pubkey 48 || target_pubkey 48).

  The block-level commitment is, per EIP-7685:

      requests_hash :=
          sha256( concat for each non-empty type t in [0x00, 0x01, 0x02]:
                    sha256(bytes([t]) || concat(payloads_of_type_t)) )

  Empty request lists for a given type are skipped (not included in the
  inner sha256 list). The header field is this 32-byte digest.

  We expose:

    * `Request` (re-exported from Blocks)
    * helpers to compute the canonical hash
    * the type tags

  SHA-256 itself is provided by `Evm.Crypto.Hash` (already wired for
  the SHA256 precompile).
-/

import Evm.BaseTypes
import Evm.Prague.Blocks
import Evm.Crypto.Sha256

namespace Evm.Prague.Requests

/-- EIP-6110 — deposits from the deposit-contract logs. -/
def depositRequestType        : UInt8 := 0x00
/-- EIP-7002 — EL-triggered partial withdrawals. -/
def withdrawalRequestType     : UInt8 := 0x01
/-- EIP-7251 — validator consolidations. -/
def consolidationRequestType  : UInt8 := 0x02

/-- The deposit contract on mainnet. EELS:
    `forks/prague/fork.py::DEPOSIT_CONTRACT_ADDRESS`. -/
def depositContractAddress : Evm.Address :=
  Evm.Address.ofNat 0x00000000219ab540356cBB839Cbe05303d7705Fa

/-- EIP-7002 system contract. EELS:
    `forks/prague/fork.py::WITHDRAWAL_REQUEST_PREDEPLOY_ADDRESS`. -/
def withdrawalRequestPredeploy : Evm.Address :=
  Evm.Address.ofNat 0x00000961Ef480Eb55e80D19ad83579A64c007002

/-- EIP-7251 system contract. EELS:
    `forks/prague/fork.py::CONSOLIDATION_REQUEST_PREDEPLOY_ADDRESS`. -/
def consolidationRequestPredeploy : Evm.Address :=
  Evm.Address.ofNat 0x0000BBdDc7CE488642fb579F8B00f3a590007251

/-- EIP-4788 beacon-roots system contract (Cancun, reused at Prague). -/
def beaconRootsAddress : Evm.Address :=
  Evm.Address.ofNat 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02

/-- EIP-2935 (Prague) historical-block-hashes contract. The BLOCKHASH
    opcode reads here instead of walking the parent chain. -/
def historyStorageAddress : Evm.Address :=
  Evm.Address.ofNat 0x0000F90827F1C53a10cb7A02335B175320002935

/-- System caller address used by `apply_body` for the four post-tx
    system calls. EELS: `forks/prague/fork.py::SYSTEM_ADDRESS`. -/
def systemAddress : Evm.Address :=
  Evm.Address.ofNat 0xfffffffffffffffffffffffffffffffffffffffe

/-- Group requests by type, preserving in-block order. -/
private def groupByType (rs : List Evm.Prague.Request) :
    List (UInt8 × List Evm.Bytes) := Id.run do
  let mut deposits      : List Evm.Bytes := []
  let mut withdrawals   : List Evm.Bytes := []
  let mut consolidations: List Evm.Bytes := []
  for r in rs do
    if r.type = depositRequestType then deposits := deposits ++ [r.payload]
    else if r.type = withdrawalRequestType then withdrawals := withdrawals ++ [r.payload]
    else if r.type = consolidationRequestType then consolidations := consolidations ++ [r.payload]
  let mut out : List (UInt8 × List Evm.Bytes) := []
  if ¬ deposits.isEmpty then out := out ++ [(depositRequestType, deposits)]
  if ¬ withdrawals.isEmpty then out := out ++ [(withdrawalRequestType, withdrawals)]
  if ¬ consolidations.isEmpty then out := out ++ [(consolidationRequestType, consolidations)]
  pure out

/-- Concatenate a list of byte strings. -/
private def concatBytes : List Evm.Bytes → Evm.Bytes
  | []      => Evm.Bytes.empty
  | b :: bs => b ++ concatBytes bs

/-- EIP-7685 requests-hash. Sha256 of the concatenated per-type
    commitments, each commitment being `sha256(type_byte || concat
    payloads)`. Empty types are excluded.

    EELS: `compute_requests_hash` in
    `ethereum/forks/prague/requests.py`. -/
def computeRequestsHash (rs : List Evm.Prague.Request) : Evm.Hash32 :=
  let groups := groupByType rs
  -- For each non-empty (type, payloads) group:
  --   inner := sha256(byte(type) || concat(payloads))
  let inners : List Evm.Bytes := groups.map fun (t, payloads) =>
    let typeByte : Evm.Bytes := ByteArray.mk (Array.mk [t])
    Evm.Crypto.sha256 (typeByte ++ concatBytes payloads)
  Evm.U256.ofBytesBE (Evm.Crypto.sha256 (concatBytes inners))

end Evm.Prague.Requests
