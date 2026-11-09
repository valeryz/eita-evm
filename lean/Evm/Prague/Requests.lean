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

/-- A system call's output as a request list: nothing for an empty output, else one
    request of `type` (EELS `process_general_purpose_requests`, fork.py 794-810:
    `if len(output.return_data) > 0: requests_from_execution.append(TYPE + data)`). -/
def ofOutput (type : UInt8) (out : Evm.Bytes) : List Evm.Prague.Request :=
  if out.size = 0 then [] else [{ type := type, payload := out }]

/-- Concatenate a list of byte strings. -/
private def concatBytes : List Evm.Bytes → Evm.Bytes
  | []      => Evm.Bytes.empty
  | b :: bs => b ++ concatBytes bs

/-- EIP-7685 requests-hash: the SHA2-256 of the concatenated SHA2-256 of each
    request, a request being its type byte followed by its data. EELS
    `forks/prague/requests.py::compute_requests_hash` 289-308 (`for request in
    requests: m.update(sha256(request).digest())`). The list is one request per
    non-empty type in type order (`applyBlock`'s `ofOutput`s; EELS
    `process_general_purpose_requests`), so there is no grouping step here.
    (2026-11-09: a by-type regrouping `groupByType` that EELS does not have was
    deleted.) -/
def computeRequestsHash (rs : List Evm.Prague.Request) : Evm.Hash32 :=
  Evm.U256.ofBytesBE (Evm.Crypto.sha256 (concatBytes (rs.map fun r =>
    Evm.Crypto.sha256 (ByteArray.mk (Array.mk [r.type]) ++ r.payload))))

end Evm.Prague.Requests
