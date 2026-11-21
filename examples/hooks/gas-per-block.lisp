;;;; examples/hooks/gas-per-block.lisp — a per-block fold: gas and fees per block, and a
;;;; rolling one-hour window over them (docs/hooks.md).
;;;;
;;;;   bin/eita replay --chain ethereum --blocks DIR --from 1 --to 1000 --observer examples/hooks/gas-per-block.lisp
;;;;
;;;; or (load "examples/hooks/gas-per-block.lisp") in a REPL before running blocks, then
;;;; (hooks.gas:summary). The state is the rows of the last hour plus running totals: it
;;;; scales with the window, not with the history.

(defpackage #:hooks.gas (:use #:cl) (:export #:summary #:*window-seconds*))
(in-package #:hooks.gas)

(defparameter *window-seconds* 3600)

(defstruct row number timestamp gas-used gas-limit burnt tips txs)

(defvar *last* nil "The newest block folded.")
(defvar *window* '() "The rows of the blocks of the last *window-seconds*, newest first.")
(defvar *window-gas* 0)
(defvar *window-fees* 0)
(defvar *totals* (list :blocks 0 :txs 0 :gas 0 :burnt 0 :tips 0) "Since the fold started.")

(defun fees (block)
  "(values burnt tips) of BLOCK on Ethereum's fee rules: each tx's gas times the base fee is
   burnt (EIP-1559), the rest of its price goes to the block's producer."
  (let ((base (getf block :base-fee)) (burnt 0) (tips 0))
    (dolist (tx (getf block :txs) (values burnt tips))
      (let ((gas (getf tx :gas-used)) (price (getf tx :gas-price)))
        (incf burnt (* gas base))
        (incf tips (* gas (- price base)))))))

(defun count-row (r sign)
  "Add (SIGN 1) or remove (SIGN -1) the row R from the window sums and the totals."
  (incf *window-gas* (* sign (row-gas-used r)))
  (incf *window-fees* (* sign (+ (row-burnt r) (row-tips r))))
  (loop for (k v) on (list :blocks 1 :txs (row-txs r) :gas (row-gas-used r) :burnt (row-burnt r) :tips (row-tips r)) by #'cddr
        do (incf (getf *totals* k) (* sign v))))

(defun on-start (n)
  "A run starts at block N: a fold that does not end at N-1 starts over."
  (unless (eql *last* (1- n))
    (setf *last* nil *window* '() *window-gas* 0 *window-fees* 0
          *totals* (list :blocks 0 :txs 0 :gas 0 :burnt 0 :tips 0))))

(defun on-block (block)
  (multiple-value-bind (burnt tips) (fees block)
    (let ((r (make-row :number (getf block :number) :timestamp (getf block :timestamp)
                       :gas-used (getf block :gas-used) :gas-limit (getf block :gas-limit)
                       :burnt burnt :tips tips :txs (length (getf block :txs)))))
      (push r *window*)
      (count-row r 1)
      (setf *last* (row-number r))
      ;; rows older than the window leave it (they stay in the totals)
      (let ((cut (- (row-timestamp r) *window-seconds*)))
        (loop for cell on *window*
              when (and (cdr cell) (<= (row-timestamp (cadr cell)) cut))
                do (dolist (old (cdr cell))
                     (decf *window-gas* (row-gas-used old))
                     (decf *window-fees* (+ (row-burnt old) (row-tips old))))
                   (setf (cdr cell) nil)
                   (return))))))

(defun on-rollback (n)
  "The chain is rolled back to block N: the rows above N leave the window and the totals.
   A reorg is shallower than an hour, so the rows it undoes are in the window."
  (loop while (and *window* (> (row-number (first *window*)) n))
        do (count-row (pop *window*) -1))
  (when (and *last* (> *last* n)) (setf *last* n)))

(defun summary ()
  "The fold as of the newest block delivered, read under the fold lock."
  (eita:with-fold-state (n)
    (let* ((rows *window*)
           (span (if (rest rows) (- (row-timestamp (first rows)) (row-timestamp (car (last rows)))) 0)))
      (list :block n :window-blocks (length rows) :window-gas *window-gas* :window-fees *window-fees*
            :gas-per-second (if (plusp span) (float (/ *window-gas* span)) nil)
            :totals (copy-list *totals*)))))

;; Symbols, not #'functions: a redefined handler takes effect at the next block.
(eita:subscribe "gas-per-block" :start 'on-start :block 'on-block :rollback 'on-rollback)
