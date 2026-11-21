;;;; examples/hooks/transfers.lisp — a token-transfer fold: ERC-20 Transfer logs and native
;;;; value moves, with the top senders and tokens in bounded memory (docs/hooks.md).
;;;;
;;;;   bin/eita replay --chain ethereum --blocks DIR --from 1 --to 1000 --observer examples/hooks/transfers.lisp
;;;;
;;;; then (hooks.transfers:summary). Top-k by the Space-Saving algorithm: K counters whatever
;;;; the number of addresses; a reported count is at most its error above the true one.

(defpackage #:hooks.transfers (:use #:cl) (:export #:summary #:top #:*k*))
(in-package #:hooks.transfers)

(defparameter *k* 256 "Counters per top-k table.")
(defparameter *undo-blocks* 128 "Blocks a rollback can undo (deeper than any reorg).")
(defparameter +transfer-topic+ #xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef
  "keccak256(\"Transfer(address,address,uint256)\"): an ERC-20 Transfer log's first topic.")

;;; Space-Saving: KEY -> (count . error). A new key, when the table is full, replaces the
;;; smallest counter and inherits its count as its error.
(defun make-top () (make-hash-table :test 'eql))

(defun top-add (table key weight)
  (let ((e (gethash key table)))
    (cond (e (incf (car e) weight))
          ((minusp weight))                                   ; undoing a key already evicted
          ((< (hash-table-count table) *k*) (setf (gethash key table) (cons weight 0)))
          (t (let ((min-key nil) (min most-positive-fixnum))
               (maphash (lambda (k v) (when (< (car v) min) (setf min (car v) min-key k))) table)
               (remhash min-key table)
               (setf (gethash key table) (cons (+ min weight) min)))))))

(defun top (table &optional (n 10))
  "The N largest entries of TABLE as (key count error), largest first."
  (let ((all '()))
    (maphash (lambda (k v) (push (list k (car v) (cdr v)) all)) table)
    (subseq (sort all #'> :key #'second) 0 (min n (length all)))))

(defvar *senders* (make-top) "Transfers sent, ERC-20 and native, by sender.")
(defvar *tokens* (make-top) "ERC-20 Transfer logs by token contract.")
(defvar *counts* (list :erc20 0 :native 0 :native-wei 0))
(defvar *last* nil "The newest block folded.")
(defvar *pending* '() "This block's additions: (table . key), and (:count key . amount).")
(defvar *undo* '() "(block . additions) of the newest *undo-blocks* blocks, newest first.")

(defun add (table key)
  (top-add table key 1)
  (push (cons table key) *pending*))

(defun counted (key amount)
  (incf (getf *counts* key) amount)
  (push (list* :count key amount) *pending*))

(defun erc20-transfer-p (log)
  (let ((topics (getf log :topics)))
    ;; three topics (signature, from, to) and the value as 32 bytes of data; ERC-721's
    ;; Transfer has the token id as a fourth topic
    (and (= (length topics) 3) (eql (first topics) +transfer-topic+) (= (length (getf log :data)) 32))))

(defun on-log (log)
  (when (erc20-transfer-p log)
    (counted :erc20 1)
    (add *senders* (ldb (byte 160 0) (second (getf log :topics))))
    (add *tokens* (getf log :address))))

(defun on-transfer (x)
  (when (plusp (getf x :value))
    (counted :native 1)
    (counted :native-wei (getf x :value))
    (add *senders* (getf x :from))))

(defun on-start (n)
  "A run starts at block N: a fold that does not end at N-1 starts over."
  (unless (eql *last* (1- n))
    (setf *senders* (make-top) *tokens* (make-top) *counts* (list :erc20 0 :native 0 :native-wei 0)
          *last* nil *pending* '() *undo* '())))

(defun on-block (block)
  (setf *last* (getf block :number))
  (push (cons (getf block :number) *pending*) *undo*)
  (setf *pending* '())
  (let ((tail (nthcdr (1- *undo-blocks*) *undo*))) (when tail (setf (cdr tail) nil))))

(defun on-rollback (n)
  "Undo the blocks above N (the counts of keys evicted since are already approximate)."
  (setf *pending* '())
  (loop while (and *undo* (> (car (first *undo*)) n))
        do (loop for (table . key) in (cdr (pop *undo*))
                 do (if (eq table :count)
                        (decf (getf *counts* (car key)) (cdr key))
                        (top-add table key -1))))
  (when (and *last* (> *last* n)) (setf *last* n)))

(defun summary (&optional (n 10))
  "The counts and the N top senders and tokens as (address count error), addresses in hex."
  (flet ((hexed (entries) (mapcar (lambda (e) (cons (eita:hex (first e)) (rest e))) entries)))
    (eita:with-fold-state (b)
      (list :block b :counts (copy-list *counts*)
            :top-senders (hexed (top *senders* n)) :top-tokens (hexed (top *tokens* n))))))

(eita:subscribe "transfers" :start 'on-start :log 'on-log :transfer 'on-transfer :block 'on-block :rollback 'on-rollback)
