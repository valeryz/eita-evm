/-
  Evm.Amsterdam.Spec.IntrinsicGasFloor — EIP-7981 calldata floor
  re-pricing.

  EELS reference: `forks/amsterdam/transactions.py` lines 32-49 +
  580-587.

  Pre-Amsterdam (Prague, EIP-7623):

      tokens_in_calldata = num_zeros + num_non_zeros * 4
      calldata_floor_gas_cost = (
          tokens_in_calldata * TX_DATA_TOKEN_FLOOR + TX_BASE
      )

  Amsterdam (EIP-7981) adds two new contributions to the data-token
  count: each access-list entry contributes a fixed number of "floor
  tokens" so an access-list-heavy tx pays at least as much for the
  pre-warming as the calldata floor would suggest.

      ACCESS_LIST_ADDRESS_FLOOR_TOKENS     = 80
      ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS = 128
      ...
      data_tokens = (
          num_zeros
          + num_non_zeros * TOKENS_PER_NON_ZERO_BYTE
          + num_access_list_addresses     * ACCESS_LIST_ADDRESS_FLOOR_TOKENS
          + num_access_list_storage_keys  * ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS
      )
      data_floor_gas_cost = data_tokens * TX_DATA_TOKEN_FLOOR + TX_BASE

  Per the SPEC-METHODOLOGY: an intrinsic-gas / fee predicate is a
  tx-level relation, not an opcode step. This file declares it; the
  refinement target is the (currently TODO) `Amsterdam.intrinsicGas`
  that overrides Prague's.
-/

import Evm.BaseTypes
import Evm.Prague.Transactions

namespace Evm.Amsterdam.Spec

/-- EELS `ACCESS_LIST_ADDRESS_FLOOR_TOKENS`. -/
def accessListAddressFloorTokens : Nat := 80
/-- EELS `ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS`. -/
def accessListStorageKeyFloorTokens : Nat := 128

/-- EELS `TOKENS_PER_NON_ZERO_BYTE` (= 4, unchanged from EIP-7623). -/
def tokensPerNonZeroByte : Nat := 4

/-- EELS `TX_DATA_TOKEN_FLOOR` (= 10, unchanged from EIP-7623). -/
def txDataTokenFloor : Nat := 10

/-- EELS `TX_BASE` (= 21000, unchanged from Frontier). -/
def txBase : Nat := 21000

/-- Count of zero / non-zero bytes in the calldata. -/
def calldataTokenCounts (data : Evm.Bytes) : Nat × Nat := Id.run do
  let mut nz : Nat := 0
  let mut nnz : Nat := 0
  for i in [0:data.size] do
    if data.get! i = (0 : UInt8) then nz := nz + 1
    else nnz := nnz + 1
  return (nz, nnz)

/-- EIP-7981 data-floor cost: tokens × floor + base. Includes the
    access-list floor-token surcharges over EIP-7623. -/
def dataFloorGasCost
    (data : Evm.Bytes)
    (numAccessListAddresses numAccessListStorageKeys : Nat) : Nat :=
  let (nZ, nNZ) := calldataTokenCounts data
  let tokens :=
    nZ +
    nNZ * tokensPerNonZeroByte +
    numAccessListAddresses * accessListAddressFloorTokens +
    numAccessListStorageKeys * accessListStorageKeyFloorTokens
  tokens * txDataTokenFloor + txBase

end Evm.Amsterdam.Spec
