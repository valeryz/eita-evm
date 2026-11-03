/-
  Evm.Prague.Spec.CalldataCost — EIP-7623 calldata gas (intrinsic cost + floor).

  EELS reference (execution-specs 958b142):
    src/ethereum/forks/prague/vm/gas.py:100-105   TX_BASE 21000, TX_DATA_TOKEN_STANDARD 4,
                                                  TX_DATA_TOKEN_FLOOR 10, access-list 2400/1900
    src/ethereum/forks/prague/vm/gas.py:61        AUTH_PER_EMPTY_ACCOUNT 25000
    src/ethereum/forks/prague/transactions.py:594-660  calculate_intrinsic_cost
    src/ethereum/forks/prague/transactions.py:578-579  validate: max(regular, floor) ≤ tx.gas
    src/ethereum/forks/prague/fork.py:913-925     gas used = max(used − refund, floor)

  EIP-7623 does NOT reprice standard calldata: a zero byte is 1 token, a nonzero byte 4,
  and the regular intrinsic cost charges TX_DATA_TOKEN_STANDARD (4) per token — the same
  4/16 per byte as Istanbul. What it adds is a FLOOR:

      tokens        := #zero + 4·#nonzero
      regular       := TX_BASE + 4·tokens + create + access_list + auth
      calldataFloor := TX_BASE + 10·tokens                 (no create/access/auth terms)

  and it uses the floor twice: validity needs `max(regular, calldataFloor) ≤ tx.gas`,
  and settlement charges `max(gasUsed − refund, calldataFloor)`. Execution starts with
  `tx.gas − regular`; the floor is never taken up front.

  (Until 2026-10-20 this file had 40/10 per byte and a floor of 10 per byte plus the
  extras. Nothing executable used it — the replay's cost formula is GasEmit's — and
  Evm.CL.GasEmitPrague now proves the two agree, so they cannot drift apart again.)

  Inheritance: introduced at Prague.
-/

import Evm.BaseTypes
import Evm.Frontier.Transactions

namespace Evm.Prague.Spec

open Evm.Frontier (Transaction)

/-! ## Constants (EELS `GasCosts`) -/

/-- `TX_BASE`. Unchanged from Frontier. -/
def txBaseCost           : Nat := 21000
/-- `TX_DATA_TOKEN_STANDARD`: regular-cost gas per calldata token. -/
def txDataTokenStandard  : Nat := 4
/-- `TX_DATA_TOKEN_FLOOR`: EIP-7623 floor gas per calldata token. -/
def txDataTokenFloor     : Nat := 10
/-- Tokens per nonzero byte (a zero byte is one token). -/
def tokensPerNonZero     : Nat := 4
/-- `TX_CREATE`: added on top of `TX_BASE` for contract-creation txs. -/
def txCreateCost         : Nat := 32000
/-- EIP-3860 initcode word cost (Shanghai, unchanged). -/
def initCodeWordCost     : Nat := 2
/-- `AUTH_PER_EMPTY_ACCOUNT`: EIP-7702 intrinsic cost per authorization. -/
def authPerEmptyAccount  : Nat := 25000

/-! ## Per-byte counting -/

/-- Count zero bytes and non-zero bytes in `data`. -/
def countBytes (data : Evm.Bytes) : Nat × Nat := Id.run do
  let mut zeros : Nat := 0
  let mut nonZeros : Nat := 0
  for i in [0:data.size] do
    if data.get! i = (0 : UInt8) then zeros := zeros + 1
    else nonZeros := nonZeros + 1
  pure (zeros, nonZeros)

/-- `tokens_in_calldata = num_zeros + num_non_zeros * 4` (transactions.py:624). -/
def tokens (zeros nonZeros : Nat) : Nat := zeros + tokensPerNonZero * nonZeros

/-! ## The two costs -/

/-- `IntrinsicGasCost.regular` (transactions.py:651-658): charged before execution.
    `baseExtras` = create + access-list + authorization costs. -/
def standardCost (zeros nonZeros baseExtras : Nat) : Nat :=
  txBaseCost + txDataTokenStandard * tokens zeros nonZeros + baseExtras

/-- `IntrinsicGasCost.calldata_floor` (transactions.py:626-628): no EVM costs, no extras. -/
def floorCost (zeros nonZeros : Nat) : Nat :=
  txBaseCost + txDataTokenFloor * tokens zeros nonZeros

/-- What `validate_transaction` requires the tx gas to cover (transactions.py:579). -/
def intrinsicCost (zeros nonZeros baseExtras : Nat) : Nat :=
  max (standardCost zeros nonZeros baseExtras) (floorCost zeros nonZeros)

/-- Settlement (fork.py:913-923): gas used after the refund (capped at used/5),
    raised to the calldata floor. `used` is `tx.gas − gas_left`. -/
def gasUsedAfterRefund (used refundCounter floor : Nat) : Nat :=
  max (used - min (used / 5) refundCounter) floor

/-! ## High-level predicate

    A predicate that connects a `Transaction` and a `Nat` (the
    declared `gas` field) to the EIP-7623 floor + standard formula.

    The Prague intrinsic-gas calculation also includes EIP-2930
    access-list extras and EIP-7702 authorization extras, both of
    which the impl computes from the typed-tx envelope. Here we
    factor them out into `baseExtras` so this file stays focused on
    the calldata side. -/

/-- The intrinsic-gas obligation: `tx.gas ≥ intrinsicCost(...)`. The
    caller is responsible for computing `baseExtras` from the tx's
    creation / access-list / authorization fields (since those have
    different shapes across tx types). -/
def IsIntrinsicGasSufficient (txGas : Nat) (data : Evm.Bytes)
                              (baseExtras : Nat) : Prop :=
  let (zeros, nonZeros) := countBytes data
  txGas ≥ intrinsicCost zeros nonZeros baseExtras

/-! ## Notes

    * The floor only binds for calldata-heavy txs that execute little:
      it caps worst-case block size without repricing ordinary calls.

    * `baseExtras` is the sum of:
        - 32000 if tx-CREATE (EIP-2 / Homestead)
        - 2 · ceil(initcode_len / 32) if tx-CREATE (EIP-3860 / Shanghai)
        - 2400 · #accessList_addresses (EIP-2930 / Berlin)
        - 1900 · #accessList_storageKeys (EIP-2930 / Berlin)
        - 25000 · #authorizations (EIP-7702 / Prague, AUTH_PER_EMPTY_ACCOUNT)
      They are part of the regular cost only; the floor ignores them.

    * The `Frontier.Transaction` type only exposes legacy-shape fields
      (`data` etc.); the typed-tx breakdown that yields `baseExtras`
      lives in `Prague.Transactions`. -/

end Evm.Prague.Spec
