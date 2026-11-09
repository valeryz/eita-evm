/-
  Evm.Prague.Spec.Requests — EIP-7685 execution-layer requests
  commitment.

  EELS reference: `forks/prague/requests.py::compute_requests_hash`
  and the per-type processing in `forks/prague/fork.py::apply_body`.

  EIP-7685 commits to a list of execution-layer requests (deposit,
  withdrawal, consolidation, ...) via the header field
  `requestsHash`. The formula:

      requests_hash :=
          sha256( concat over t in [0x00, 0x01, 0x02, ...]:
                    if any request of type t exists:
                      sha256(byte(t) || concat(payloads_of_type_t))
                    else:
                      skip )

  Two key points:

    1. The PER-TYPE prefix byte is included EXACTLY ONCE inside the
       inner sha256, not per-request. So a block with 5 deposits has
       ONE inner hash for type 0x00, computed over
       `0x00 || dep1 || dep2 || dep3 || dep4 || dep5`.

    2. Empty types are SKIPPED — not included as a zero-length inner
       sha256. A block with no requests at all has
       `requests_hash = sha256("")` (the outer hash of an empty
       concatenation).

  This file states the commitment from EELS (`requestsHash`,
  `requestsFromExecution`); `Evm.Prague.Requests.computeRequestsHash` is
  the implementation it refines.

  Inheritance: introduced at Prague.
-/

import Evm.BaseTypes
import Evm.Prague.Blocks
import Evm.Prague.Requests
import Evm.Crypto.Sha256

namespace Evm.Prague.Spec

open Evm.Prague (Request)

/-! ## Type tags. EELS: `forks/prague/fork.py`. -/

def depositRequestType        : UInt8 := 0x00
def withdrawalRequestType     : UInt8 := 0x01
def consolidationRequestType  : UInt8 := 0x02

/-! ## The commitment (EIP-7685)

    EELS `forks/prague/requests.py::compute_requests_hash` 289-308: the
    SHA2-256 of the concatenation of the SHA2-256 of each request, where a
    request is the type byte followed by the request data. The request list
    is the block's (EELS `forks/prague/fork.py::process_general_purpose_requests`
    767-810): deposits (type 0x00), then the EIP-7002 withdrawal predeploy's
    output (0x01), then the EIP-7251 consolidation predeploy's output (0x02),
    each included only when non-empty. Restated 2026-11-09: the predicate used
    to be the implementation's `computeRequestsHash`, so its refinement was
    circular. -/

/-- One request: the type byte, then the data (EELS `TYPE + data`). -/
def typedRequest (type : UInt8) (data : Evm.Bytes) : Evm.Bytes :=
  ByteArray.mk (Array.mk [type]) ++ data

/-- EELS `compute_requests_hash`: `sha256(sha256(r₀) ‖ sha256(r₁) ‖ …)`. -/
def requestsHash (requests : List Evm.Bytes) : Evm.Hash32 :=
  Evm.U256.ofBytesBE (Evm.Crypto.sha256
    (requests.foldr (fun r acc => Evm.Crypto.sha256 r ++ acc) Evm.Bytes.empty))

/-- EELS `process_general_purpose_requests`: the block's requests, from the
    concatenated deposit data and the two predeploys' outputs. -/
def requestsFromExecution (deposits withdrawals consolidations : Evm.Bytes) :
    List Evm.Bytes :=
  (if deposits.size = 0 then [] else [typedRequest depositRequestType deposits]) ++
  (if withdrawals.size = 0 then [] else [typedRequest withdrawalRequestType withdrawals]) ++
  (if consolidations.size = 0 then [] else
    [typedRequest consolidationRequestType consolidations])

/-- The header's `requestsHash` is EIP-7685's commitment to the block's requests. -/
def IsRequestsHashValid (requests : List Evm.Bytes) (headerHash : Evm.Hash32) : Prop :=
  headerHash = requestsHash requests

/-! ## Properties

    The empty block's commitment. -/

/-- Empty requests list collapses to `sha256("")`. -/
theorem requests_hash_empty :
    Evm.Prague.Requests.computeRequestsHash [] =
    Evm.U256.ofBytesBE (Evm.Crypto.sha256 Evm.Bytes.empty) := by
  rfl

/-! ## Notes

    * The implementation's `computeRequestsHash` (in `Evm.Prague.Requests`)
      works over `Request` records; `Refinement.requestsHashValid_sound`
      proves it equal to `requestsHash ∘ requestsFromExecution` on the
      lists `applyBlock` builds. -/

end Evm.Prague.Spec
