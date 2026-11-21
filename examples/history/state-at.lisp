;;;; examples/history/state-at.lisp — an account and an ERC-20 balance at the end of a block,
;;;; from the fact log's history index (docs/fact-log.md, docs/hooks.md "Querying history").
;;;;
;;;;   (load "examples/history/state-at.lisp")
;;;;   (history.state:account-at "factlog/" "0xd8dA…6045" 24538111)   ; (:nonce … :balance … :code-hash …)
;;;;   (history.state:erc20-balance-at "factlog/" "0xC02a…6Cc2" "0xHolder…" 24538111 :slot 3)
;;;;
;;;; A lookup, not a scan: blooms.idx and each shard's filter skip the shards that never
;;;; changed the key, and inside a shard its index finds the key's rows by binary search. The
;;;; answer is :unknown when the log never changed the key (its value is older than the log).

(defpackage #:history.state (:use #:cl) (:export #:account-at #:erc20-balance-at #:mapping-slot))
(in-package #:history.state)

(defun account-at (dir address block)
  "ADDRESS's nonce, balance and code hash at the end of BLOCK, or :unknown."
  (let ((v (eita-factlog:state-at dir :account_diff (list (eita:addr address)) block)))
    (if (eq v :unknown)
        v
        (destructuring-bind (nonce balance code-hash) v
          (list :nonce nonce :balance balance :code-hash code-hash)))))

(defun mapping-slot (key slot)
  "The storage slot of KEY in a Solidity mapping declared at SLOT: keccak256 of the two as
   32-byte big-endian words."
  (let ((b (make-array 64 :element-type '(unsigned-byte 8) :initial-element 0)))
    (dotimes (i 32)
      (setf (aref b (- 31 i)) (ldb (byte 8 (* 8 i)) key)
            (aref b (- 63 i)) (ldb (byte 8 (* 8 i)) slot)))
    (reduce (lambda (n x) (+ (* n 256) x)) (eita.core:keccak256-bytes b) :initial-value 0)))

(defun erc20-balance-at (dir token holder block &key (slot 0))
  "HOLDER's balance of TOKEN at the end of BLOCK, for a token that keeps balances in a
   mapping declared at SLOT (WETH9: 3), or :unknown."
  (eita-factlog:state-at dir :storage_diff
                         (list (eita:addr token) (mapping-slot (eita:addr holder) slot)) block))
