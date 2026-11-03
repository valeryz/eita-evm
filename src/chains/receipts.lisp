;;;; chains/receipts.lisp — the block's receiptsRoot, recomputed from OUR execution (generic EVM).
;;;;
;;;; Chain-neutral: EIP-658 status receipts in EIP-2718 envelopes, as every post-Byzantium
;;;; EVM chain encodes them: receipt = rlp([status, cumulativeGasUsed, logsBloom, logs]),
;;;; prefixed by the tx type byte when type > 0; receiptsRoot = trie root over
;;;; (rlp(index) -> receipt). A chain whose receipts carry extra fields (OP-Stack deposit
;;;; receipts: depositNonce, depositReceiptVersion) supplies `*chain-receipt-encode-hook*`.
;;;;
;;;; Why it exists: the header gate compared only Σ gas and the logs bloom. A tx that
;;;; FAILED on-chain but succeeded for us at equal gas and with no logs was invisible —
;;;; Arc block 21 418 236 tx 9 drifted the state that way and surfaced 235k blocks later.
;;;; The receipts root commits to every receipt's status, cumulative gas, bloom and logs,
;;;; so that class is caught in the block where it happens.
;;;;
;;;; Inputs per tx: type, status, gas used (after refunds and any floor), and the tx's
;;;; COMMITTED logs in order — `*last-tx-logs*`, captured by observe-tx-end! (replay-cl)
;;;; whether or not an observer is installed: no header gate depends on an output toggle.
;;;; Trie and RLP come from mpt.lisp (the Lean-mirrored implementation).

(in-package #:eita.chain)

(defvar *chain-receipt-encode-hook* nil
  "Optional (lambda (type status cumulative bloom logs) ...) returning the receipt bytes,
   or NIL for the standard encoding. Chain-specific receipt formats plug in here.")

(defvar *chain-header-foreign* '()
  "Header fields this chain defines otherwise than Ethereum, which verify-block-header does
   not compare (OP-Stack: withdrawalsRoot is the L2ToL1MessagePasser's storage root from
   Isthmus, blobGasUsed the DA footprint from Jovian). The driver's banner names them.")
(defvar *block-receipts* '()
  "The current block's receipts as executed, newest first: (type status cumulative-gas logs);
   encoded by verify-block-header (in a replay, on the verifier thread).")
(defvar *receipts-unverifiable* nil
  "No receiptsRoot to compare: T before Byzantium (receipts carry a per-tx state root),
   :SKIPPED when a tx in this block was not executed (OP's skipped type-4) — then no bloom
   either.")

(defun receipts-block-begin! ()
  (setf *block-receipts* '() *receipt-cumulative-gas* 0 *receipts-unverifiable* nil
        *block-blob-gas* 0 *block-requests-hash* nil *block-deposit-logs* '()))

(defun bloom-add! (bloom bytes)
  "EIP/EELS add_to_bloom: three 11-bit indices from keccak(BYTES)."
  (let ((h (keccak256-bytes bytes)))
    (declare (type octets h bloom))
    (dolist (i '(0 2 4) bloom)
      (let* ((bit (- #x7FF (logand (logior (ash (aref h i) 8) (aref h (1+ i))) #x7FF)))
             (byte-index (floor bit 8)))
        (setf (aref bloom byte-index)
              (logior (aref bloom byte-index) (ash 1 (- 7 (mod bit 8)))))))))

(defun logs-bloom (logs)
  "256-byte bloom of LOGS, each (address topics data)."
  (let ((bloom (make-array 256 :element-type '(unsigned-byte 8) :initial-element 0)))
    (dolist (l logs bloom)
      (bloom-add! bloom (u256->octets (first l) 20))
      (dolist (tp (second l)) (bloom-add! bloom (u256->octets tp 32))))))

(defun receipt-encode (type status cumulative logs)
  "One receipt's bytes, and its bloom."
  (let ((bloom (logs-bloom logs)))
    (values
     (or (and *chain-receipt-encode-hook*
             (funcall *chain-receipt-encode-hook* type status cumulative bloom logs))
        (let* ((rlp-logs (eita.mpt:rlp-list*
                          (mapcar (lambda (l)
                                    (eita.mpt:rlp-list
                                     (eita.mpt:rlp-bytes (u256->octets (first l) 20))
                                     (eita.mpt:rlp-list* (mapcar (lambda (tp) (eita.mpt:rlp-bytes (u256->octets tp 32)))
                                                                  (second l)))
                                     (eita.mpt:rlp-bytes (third l))))
                                  logs)))
               (body (eita.mpt:rlp-encode
                      (eita.mpt:rlp-list (eita.mpt:rlp-uint status)
                                          (eita.mpt:rlp-uint cumulative)
                                          (eita.mpt:rlp-bytes bloom)
                                          rlp-logs))))
          (if (and type (plusp type))
              (let ((out (make-array (1+ (length body)) :element-type '(unsigned-byte 8))))
                (setf (aref out 0) type) (replace out body :start1 1) out)
              body)))
     bloom)))

(defun receipts-push! (type status gas-used logs)
  "Record one executed tx's receipt (STATUS 1/0, GAS-USED after refunds/floor). The
   deposit contract's DepositEvent logs are kept for the EIP-6110 requests (EELS prague
   requests.py parse_deposit_requests reads them from the receipts, as here)."
  (incf *receipt-cumulative-gas* gas-used)
  (dolist (l logs)
    (when (and (= (first l) +deposit-contract-address+) (second l) (= (first (second l)) +deposit-event-signature+))
      (push (third l) *block-deposit-logs*)))
  (push (list type status *receipt-cumulative-gas* logs) *block-receipts*))

(defun block-verify-inputs ()
  "What verify-block-header reads of the current block's execution, as its keyword
   arguments: captured, for the verifier thread."
  (list :receipts (reverse *block-receipts*) :unverifiable *receipts-unverifiable*
        :blob-gas *block-blob-gas* :requests-hash *block-requests-hash*))

;;; --- The block body's roots: what transactionsRoot / withdrawalsRoot commit to ----------
;;; The header hash (fetch-verified-block) covers the header only; these tie the body we
;;; execute to it: the envelopes are encoded from the decoded TX structs (chain-io
;;; decode-tx), the values that run, not from the source's text.

(defun tx-envelope (tx &key unsigned)
  "The EIP-2718 bytes of TX: rlp(fields) for a legacy tx, type ‖ rlp(fields) for a typed
   one (EIP-2930/1559/4844/7702, and the OP-Stack deposit 0x7e). UNSIGNED: the signing
   payload instead (no v/r/s; a legacy EIP-155 tx's chain id, 0, 0 in their place)."
  (flet ((u (x) (eita.mpt:rlp-uint (or x 0)))
         (a (x) (eita.mpt:rlp-bytes (if x (u256->octets x 20) #())))   ; NIL: a creation's `to`
         (h (x) (eita.mpt:rlp-bytes (u256->octets x 32))))
    (let* ((type (tx-type tx)) (v (or (tx-v tx) 0))
           (data (eita.mpt:rlp-bytes (tx-data tx)))
           (al (eita.mpt:rlp-list* (mapcar (lambda (e) (eita.mpt:rlp-list (a (car e)) (eita.mpt:rlp-list* (mapcar #'h (cdr e)))))
                                            (tx-access-list tx))))
           (head (and (<= 2 type 4) (list (u (tx-nonce tx)) (u (tx-max-priority tx)) (u (tx-max-fee tx)) (u (tx-gas-limit tx))
                                          (a (tx-to tx)) (u (tx-value tx)) data al)))
           (sig (and (<= 1 type 4) (not unsigned) (list (u v) (u (tx-r tx)) (u (tx-s tx)))))
           (fields (case type
                     (0 (append (list (u (tx-nonce tx)) (u (tx-gas-price tx)) (u (tx-gas-limit tx)) (a (tx-to tx)) (u (tx-value tx)) data)
                                (cond ((not unsigned) (list (u v) (u (tx-r tx)) (u (tx-s tx))))
                                      ((>= v 35) (list (u (floor (- v 35) 2)) (u 0) (u 0))))))
                     (1 (append (list (u (tx-chain-id tx)) (u (tx-nonce tx)) (u (tx-gas-price tx)) (u (tx-gas-limit tx))
                                      (a (tx-to tx)) (u (tx-value tx)) data al)
                                sig))
                     (2 (append (list (u (tx-chain-id tx))) head sig))
                     (3 (append (list (u (tx-chain-id tx))) head
                                (list (u (tx-max-blob-fee tx)) (eita.mpt:rlp-list* (mapcar #'h (tx-blob-hashes tx))))
                                sig))
                     (4 (append (list (u (tx-chain-id tx))) head
                                (list (eita.mpt:rlp-list* (mapcar (lambda (au) (eita.mpt:rlp-list (u (getf au :chain-id)) (a (getf au :address))
                                                                                                    (u (getf au :nonce)) (u (getf au :y-parity))
                                                                                                    (u (getf au :r)) (u (getf au :s))))
                                                                   (tx-auth-list tx))))
                                sig))
                     (#x7e (list (h (tx-source-hash tx)) (a (tx-sender tx)) (a (tx-to tx)) (u (tx-mint tx)) (u (tx-value tx))
                                 (u (tx-gas-limit tx)) (u (if (tx-system-p tx) 1 0)) data))
                     (t (error "transactionsRoot: tx type ~D has no encoding here" type))))
           (body (eita.mpt:rlp-encode (eita.mpt:rlp-list* fields))))
      (if (zerop type) body (concatenate 'octets (vector type) body)))))

;;; --- The sender: recovered from the signature, never taken from the source ---------------
;;; The envelope carries v, r, s but not the sender, so the header hash and transactionsRoot
;;; do not cover a source's "from" (an RPC node's, an exporter's): it is input. Checked here,
;;; per block, on the verifier thread like the body roots (EELS recover_sender).

(defun recover-tx-sender (tx)
  "The address whose key signed TX: keccak(the signing payload, tx-envelope :unsigned) and
   v, r, s — a legacy v 27/28, or EIP-155's 35 + 2·chainId + parity; a typed tx's v its
   yParity. NIL when the signature does not recover."
  (let ((v (tx-v tx)) (r (tx-r tx)) (s (tx-s tx)))
    (and v r s
         (ecrecover-address (keccak256-bytes (tx-envelope tx :unsigned t))
                            (cond ((plusp (tx-type tx)) (+ 27 v)) ((>= v 35) (+ 27 (mod (- v 35) 2))) (t v))
                            r s))))

(defun tx-sender-verified-p (tx)
  "TX names the sender its signature recovers. An OP deposit (0x7e) is unsigned: its
   sender is in its envelope, which transactionsRoot covers."
  (or (= (tx-type tx) #x7e) (eql (tx-sender tx) (recover-tx-sender tx))))

;; eita_ecrecover creates its secp256k1 context on first use, unlocked: create it here, on
;; the loading (or starting) thread, before the verifier and the replay thread can race to.
(at-startup secp256k1-context
  (ecrecover-address (make-array 32 :initial-element 1) 27 1 1))

(defun list-root (values)
  "The trie root over (rlp(index) -> value) of the byte strings VALUES, in order (octets)."
  (eita.mpt:trie-root (loop for x in values for i from 0
                            collect (cons (eita.mpt:rlp-encode (eita.mpt:rlp-uint i)) x))))

(defun withdrawal-rlp (w)
  "EIP-4895: rlp([index, validatorIndex, address, amount (gwei)]) of a decoded withdrawal."
  (destructuring-bind (index validator address amount) w
    (eita.mpt:rlp-encode (eita.mpt:rlp-list (eita.mpt:rlp-uint index) (eita.mpt:rlp-uint validator)
                                              (eita.mpt:rlp-bytes (u256->octets address 20)) (eita.mpt:rlp-uint amount)))))

;;; --- Header verification (every chain, every block) ---------------------------

(defun verify-block-header (blk total-gas &key (receipts (reverse *block-receipts*))
                                                (unverifiable *receipts-unverifiable*)
                                                (blob-gas *block-blob-gas*)
                                                (requests-hash *block-requests-hash*))
  "Compare our execution of the decoded block BLK (by default the current block's: `block-verify-inputs`) with
   its header: Σ gas used, the logs bloom, the receiptsRoot (not when UNVERIFIABLE:
   pre-Byzantium per-tx roots; nor the bloom after a skipped tx), the
   blobGasUsed, the requestsHash (Prague+, after the post-block system calls; a chain that
   runs no request calls has none, i.e. the empty hash), and the body against the header:
   transactionsRoot, withdrawalsRoot, every tx's sender (its signature's). Returns the header fields we do NOT reproduce — NIL
   when the block reproduced. A field the header lacks must be one we have nothing for; a
   field the chain defines otherwise (*chain-header-foreign*) is not compared."
  (let* ((bad '())
         (bloom (make-array 256 :element-type '(unsigned-byte 8) :initial-element 0))
         (encoded (loop for r in receipts
                        collect (multiple-value-bind (bytes b) (apply #'receipt-encode r)
                                  (dotimes (i 256 bytes) (setf (aref bloom i) (logior (aref bloom i) (aref b i)))))))
         (hdr-requests (blk-requests-hash blk))
         (hdr-wroot (blk-withdrawals-root blk))
         (withdrawals (blk-withdrawals blk)))
    (flet ((check (field ok) (unless (or ok (member field *chain-header-foreign* :test #'string=)) (push field bad))))
      (check "gasUsed" (= total-gas (blk-gas-used blk)))
      (check "logsBloom" (or (eq unverifiable :skipped) (equalp bloom (blk-logs-bloom blk))))
      (check "receiptsRoot" (or unverifiable (equalp (list-root encoded) (blk-receipts-root blk))))
      (check "blobGasUsed" (= blob-gas (or (blk-blob-gas-used blk) 0)))
      (check "requestsHash" (if hdr-requests
                                (equalp (or requests-hash (requests-hash '())) hdr-requests)
                                (null requests-hash)))
      (check "transactionsRoot" (equalp (list-root (mapcar #'tx-envelope (blk-txs blk))) (blk-transactions-root blk)))
      (let ((i (position-if-not #'tx-sender-verified-p (blk-txs blk))))
        (check (format nil "the sender of tx ~D" i) (null i)))
      (check "withdrawalsRoot" (if hdr-wroot
                                   (equalp (list-root (mapcar #'withdrawal-rlp withdrawals)) hdr-wroot)
                                   (null withdrawals))))
    (nreverse bad)))

;; Every libeita pointer cached above is still the one libeita has (nothing opened a
;; second image of it: native/libraries.lisp is the one place that opens libraries).
(at-startup cached-foreign-pointers
  (check-cached-foreign-pointers! "loading the trie for the receipts root"))
