/-
  Evm.Optimism.Bedrock.Spec.DepositReceipt — what a deposit (type 0x7E) commits to in the
  block: its receipt in the receipts root, and the gas it uses when it cannot execute.

  Sources: optimism-specs `specs/protocol/deposits.md` §"Deposit Receipt" and §"Execution"
  (specs@main 2026-11); op-geth@79e9d24 `core/types/receipt.go` `Receipts.EncodeIndex`
  (lines 568-592, what `DeriveSha` hashes), `core/state_processor.go` `MakeReceipt`
  (lines 217-229), `core/state_transition.go` `execute` / `innerExecute` (lines 474-600).

  **The receipt.** `rlp([status, cumulativeGasUsed, logsBloom, logs])` behind the type byte,
  like every typed receipt; a deposit's receipt carries `depositNonce` (the sender's nonce
  before the deposit, Regolith+) and `depositReceiptVersion` (1, Canyon+), but the receipts
  root hashes them only from Canyon: "Before Canyon, these `depositNonce` &
  `depositNonceVersion` fields must always be omitted. With Canyon, these … fields must
  always be included" (deposits.md), op-geth `EncodeIndex`: the extended form only when
  `DepositReceiptVersion != nil`, which `MakeReceipt` sets from Canyon.

  **A deposit that cannot execute.** Deposits skip the user-tx validation (no signature, fee,
  nonce or EOA check), but the message's own consensus checks still run in op-geth's
  `innerExecute` — the intrinsic gas within the gas limit, the EIP-7623 floor within it
  (Prague / Isthmus+), the value within the balance (after the mint), the EIP-3860 init-code
  cap (Shanghai / Canyon+; op-geth applies `CheckMaxInitCodeSize` to deposits although the
  spec's list says no init-code check is performed — op-geth is the deployed rule). One
  failing makes it a *failed deposit* (`execute`): the state is rolled back to just after
  the mint, the sender's nonce is bumped, and the receipt reports status 0 and the whole gas
  limit (deposits.md: "the deposit will always be included, but its receipt will indicate
  a failure"; Regolith: "the tx is invalid so is recorded as using all gas").
-/

import Evm.BaseTypes
import Evm.Rlp
import Evm.Optimism.Forks

namespace Evm.Optimism.Bedrock.Spec

open Evm.Optimism (OpFork)

/-- The fields after `logs` that the receipts root hashes for a deposit at fork `f`. -/
def depositReceiptExtension (f : OpFork) (depositNonce : Nat) : List Nat :=
  if f.atLeast .canyon then [depositNonce, 1] else []

theorem deposit_receipt_extension_iff_canyon (f : OpFork) (nonce : Nat) :
    depositReceiptExtension f nonce ≠ [] ↔ f.atLeast .canyon := by
  unfold depositReceiptExtension; cases f <;> simp [OpFork.atLeast, OpFork.ord]

/-- The deposit receipt's RLP item (`depositReceiptRLP` / `receiptRLP`). `logs` are the
    already-encoded log items. -/
def depositReceiptItem (f : OpFork) (status cumulativeGas : Nat) (bloom : Evm.Bytes)
    (logs : List Evm.Rlp.Item) (depositNonce : Nat) : Evm.Rlp.Item :=
  .list ([.bytes (Evm.Rlp.natToBytes status), .bytes (Evm.Rlp.natToBytes cumulativeGas),
          .bytes bloom, .list logs] ++
         (depositReceiptExtension f depositNonce).map (fun k => .bytes (Evm.Rlp.natToBytes k)))

/-- The bytes the receipts trie stores at the deposit's index: `0x7E ‖ rlp(item)`. -/
def depositReceiptBytes (f : OpFork) (status cumulativeGas : Nat) (bloom : Evm.Bytes)
    (logs : List Evm.Rlp.Item) (depositNonce : Nat) : Evm.Bytes :=
  ByteArray.mk #[0x7E] ++ Evm.Rlp.encode (depositReceiptItem f status cumulativeGas bloom logs depositNonce)

/-- Before Canyon the deposit receipt hashes exactly as any typed receipt. -/
theorem deposit_receipt_pre_canyon_is_standard (f : OpFork) (h : ¬ f.atLeast .canyon = true)
    (status cumulativeGas nonce : Nat) (bloom : Evm.Bytes) (logs : List Evm.Rlp.Item) :
    depositReceiptItem f status cumulativeGas bloom logs nonce
      = .list [.bytes (Evm.Rlp.natToBytes status), .bytes (Evm.Rlp.natToBytes cumulativeGas),
               .bytes bloom, .list logs] := by
  simp [depositReceiptItem, depositReceiptExtension, h]

/-- The checks whose failure makes a *failed deposit*, at OP fork `f`: the intrinsic gas and
    (Isthmus+, else 0) the calldata floor within the gas limit, the value within the
    balance after the mint, the init-code cap for a creation (Canyon+). -/
def depositFails (f : OpFork) (gasLimit intrinsic floor value balance dataLen : Nat)
    (create : Bool) : Bool :=
  gasLimit < intrinsic || gasLimit < floor || balance < value ||
    (create && f.atLeast .canyon && 49152 < dataLen)

/-- A failed deposit uses its whole gas limit (status 0). -/
def failedDepositGasUsed (gasLimit : Nat) : Nat := gasLimit

end Evm.Optimism.Bedrock.Spec
