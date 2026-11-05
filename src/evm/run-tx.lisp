;;;; evm/run-tx.lisp — one user transaction, chain-neutral: the EIP-1559 effective gas price,
;;;; upfront debit, execution (apply-tx), the refund cap (EIP-3529 London+, else EIP-3/2),
;;;; the EIP-7623 calldata floor (Prague+), the unused-gas refund, fee settlement, and the
;;;; observation tx boundaries. Everything a chain changes about it is a hook:
;;;;
;;;;   *chain-tx-prewarm-hook*  (from target value)  — pre-execution warming after
;;;;                            reset-tx-state (Arc: blocklist slots; OP Fjord+: 0x100)
;;;;   *chain-upfront-extra-hook* (tx receipt) -> wei — extra upfront fee (OP: L1 data fee)
;;;;   *chain-fee-hook*         (from coinbase egp base-fee gas-used tx receipt)
;;;;                            — fee routing after the unused-gas refund. Default =
;;;;                            Ethereum: the Lean-emitted spec-coinbase-fee-effect.
;;;;
;;;; Deposit/system transactions are not user transactions and stay in their chain module.

(in-package #:eita.evm)

(defvar *chain-tx-prewarm-hook* nil)
(defvar *chain-upfront-extra-hook* nil)
(defvar *chain-fee-hook* nil)
(defvar *receipt-cumulative-gas* 0 "Gas used by the block's txs so far (receipts-push!).")
(defvar *block-blob-gas* 0 "EIP-4844 blob gas of the block's txs so far (run-evm-tx).")

(defconstant +fork-ord-prague+ 17)

(defun effective-gas-price (tx base-fee)
  "Seam: a fee-market tx (type >= 2) prices by the Lean-emitted EIP-1559 formula;
   a legacy/2930 tx pays its gas price."
  (if (and (>= (tx-type tx) 2) (tx-max-fee tx))
      (spec-effective-gas-price (tx-max-fee tx) base-fee (tx-max-priority tx))
      (tx-gas-price tx)))

(defun ethereum-fee-settlement (from coinbase egp base-fee gas-used tx receipt)
  "Default fee routing: the derived settlement's coinbase half (Evm.CL.EffectSettle, proved
   in EffectSettleProof): the priority fee to the coinbase as a delta, the base fee (London+)
   and the blob fee (Cancun+, debited upfront) burned, EIP-161's zero-fee rule."
  (declare (ignore from tx receipt))
  (spec-coinbase-fee-effect coinbase gas-used egp base-fee))

(defun run-evm-tx (world tx block-ctx coinbase blk idx &key receipt)
  "One user tx. Returns (values gas-used status egp): GAS-USED after the refund cap and
   the calldata floor, STATUS 1/0, EGP the effective gas price. RECEIPT (optional) only
   feeds the sanity gates."
  (let* ((from (tx-sender tx))
         (gas-limit (tx-gas-limit tx))
         (to (tx-to tx))
         (value (tx-value tx))
         (base-fee (getf block-ctx :base-fee))
         (egp (effective-gas-price tx base-fee)))
    (declare (ignore world))
    ;; Block-level validity (EELS check_transaction, osaka/fork.py 468-476): the gas limit
    ;; within what the block has left; from Cancun the blob gas within what is left of the
    ;; block's MAX_BLOB_GAS_PER_BLOCK (counted here, compared with the header by
    ;; verify-block-header).
    (let ((left (- (getf block-ctx :gas-limit) *receipt-cumulative-gas*))
          (blob-gas (* 131072 (length (tx-blob-hashes tx)))))     ; EIP-4844 GAS_PER_BLOB
      (when (> gas-limit left)
        (invalid! "gas allowance" "blk=~D tx=~D is invalid: gas limit ~D above the block's ~D left" blk idx gas-limit left))
      (when (and (plusp blob-gas) (>= (el-fork) 16)
                 (> (+ *block-blob-gas* blob-gas) (spec-max-blob-gas-per-block (el-fork))))
        (invalid! "blob gas allowance" "blk=~D tx=~D is invalid: blob gas ~D above the block's ~D left" blk idx
                  blob-gas (- (spec-max-blob-gas-per-block (el-fork)) *block-blob-gas*)))
      (incf *block-blob-gas* blob-gas))
    (observe-tx-begin!)                       ; observers: pre-images start before the first fault
    (fault-account! from)
    (when (eql (tx-type tx) 4) (incf (getf *stats* :type4)))
    (when (and receipt (getf receipt :effective-gas-price))
      (gate blk idx "effectiveGasPrice" (getf receipt :effective-gas-price) egp))
    (reset-tx-state gas-limit)
    ;; A chain's pre-execution warming (Arc: blocklist slots) — the creation's address is
    ;; derived here for it only.
    (when *chain-tx-prewarm-hook*
      (funcall *chain-tx-prewarm-hook* from (or to (derive-create-address from (nonce-of *current-world* from)))
               value))
    ;; The tx's effect up to the end of its message (Evm.CL.EffectTx): the validation, the
    ;; upfront charge (the gas, EIP-4844's blob fee, the chain's extra — OP's L1 fee), the
    ;; accessed sets, EIP-7702's authorizations and delegation, the message. A tx it
    ;; rejects cannot be in a canonical block: our state or the source is wrong.
    (multiple-value-bind (success exec-used rej)
        (apply-tx tx coinbase block-ctx :egp egp
                  :extra (if *chain-upfront-extra-hook* (funcall *chain-upfront-extra-hook* tx receipt) 0))
      (unless (zerop rej)
        (invalid! (aref +tx-invalid-reasons+ (1- rej)) "blk=~D tx=~D is invalid: ~A (sender nonce ~D balance ~D)" blk idx
               (aref +tx-invalid-reasons+ (1- rej)) (nonce-of *current-world* from)
               (balance-of *current-world* from)))
      ;; Settlement is the Lean-emitted spec-tx-gas-used (Evm.CL.GasEmit.txGasUsed, proved
      ;; equal to EELS prague/fork.py:913-923 in Evm.CL.GasEmitPrague): refund capped at
      ;; used/2 (used/5 London+), then the EIP-7623 calldata floor (Prague+).
      (let ((gas-used (multiple-value-bind (zero nz) (calldata-byte-counts tx)
                        (spec-tx-gas-used (+ (intrinsic-gas tx) exec-used) (ts-refund) zero nz (el-fork)))))
        ;; Unused gas back to the sender (a delta), then the chain's fee routing.
        (spec-gas-refund-effect from gas-limit gas-used egp)
        (funcall (or *chain-fee-hook* #'ethereum-fee-settlement)
                 from coinbase egp base-fee gas-used tx receipt)
        ;; End of tx (Evm.CL.EffectEndTx): the accounts_to_delete, then the EIP-161 sweep.
        (spec-destroy-effect)
        (spec-sweep-effect)
        (observe-tx-end! blk idx success)     ; observers: net changes + committed transfers
        (values gas-used (if success 1 0) egp)))))
