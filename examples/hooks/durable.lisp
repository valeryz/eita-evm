;;;; examples/hooks/durable.lisp — a fold that survives restarts and reorgs: checkpoints to
;;;; files at the node's layer points, resumes from the one the node resumes from, and undoes
;;;; rolled-back blocks from an undo log (docs/hooks.md).
;;;;
;;;;   bin/eita replay --chain ethereum --blocks DIR --state STATE --from 1 --to 100000 \
;;;;       --checkpoint-every 10000 --observer examples/hooks/durable.lisp
;;;;
;;;; and after a stop, the same with --resume <anchor>: the fold loads its checkpoint at the
;;;; anchor and goes on. The fold itself is small (counts and sums); the pattern is the point.

(defpackage #:hooks.durable (:use #:cl) (:export #:state #:*dir* #:*keep*))
(in-package #:hooks.durable)

(defparameter *dir* "hooks-checkpoints/" "Where the checkpoints go.")
(defparameter *keep* 8 "Checkpoints kept: a resume point is one of the newest layer points.")
(defparameter *undo-depth* 128 "Blocks the undo log holds (deeper than any reorg).")

(defun empty () (list :from nil :block nil :blocks 0 :txs 0 :failed 0 :gas 0))
(defvar *state* (empty) "The fold: the blocks it covers (:from … :block) and its sums.")
(defvar *undo* '() "(block . delta) of the newest *undo-depth* blocks, newest first.")

(defun apply-delta (delta sign)
  (loop for (k v) on delta by #'cddr do (incf (getf *state* k) (* sign v))))

(defun on-block (block)
  (let* ((txs (getf block :txs))
         (delta (list :blocks 1 :txs (length txs) :failed (count 0 txs :key (lambda (tx) (getf tx :status)))
                      :gas (getf block :gas-used))))
    (apply-delta delta 1)
    (setf (getf *state* :block) (getf block :number))
    (push (cons (getf block :number) delta) *undo*)
    (let ((tail (nthcdr (1- *undo-depth*) *undo*))) (when tail (setf (cdr tail) nil)))))

(defun on-rollback (n)
  "Undo the blocks above N, newest first."
  (let ((at (getf *state* :block)))
    (when (and at (> at n))
      (unless (and *undo* (<= (car (car (last *undo*))) (1+ n)))
        (error "rollback to ~D: the undo log does not reach back to block ~D" n (1+ n)))
      (loop while (and *undo* (> (car (first *undo*)) n)) do (apply-delta (cdr (pop *undo*)) -1))
      (setf (getf *state* :block) n))))

;;; --- Checkpoints: one file per layer point, written whole then renamed ------------------
(defun checkpoint-path (n) (merge-pathnames (format nil "durable-~D.sexp" n) *dir*))

(defun checkpoints ()
  "The block numbers of the checkpoints on disk, newest first."
  (sort (loop for p in (directory (merge-pathnames "durable-*.sexp" *dir*))
              for n = (ignore-errors (parse-integer (subseq (pathname-name p) 8)))
              when n collect n)
        #'>))

(defun on-checkpoint (n)
  "The node is about to make block N a layer point: the state through N is on disk before
   this returns (the layer waits for it)."
  (let ((at (getf *state* :block))
        (path (checkpoint-path n)) (tmp (merge-pathnames (format nil ".durable-~D.tmp" n) *dir*)))
    (cond ((null at))                    ; nothing folded yet (subscribed since)
          ((/= at n) (error "checkpoint at ~D, but the fold is at ~D" n at))
          (t (ensure-directories-exist path)
             (with-open-file (s tmp :direction :output :if-exists :supersede)
               (with-standard-io-syntax (prin1 *state* s))
               (finish-output s))
             (rename-file tmp path)
             (dolist (old (nthcdr *keep* (checkpoints))) (delete-file (checkpoint-path old)))))))

(defun on-start (n)
  "The fold's first block is N: go on in this heap, load the checkpoint at N-1, or start
   over (and say so when blocks before N are missing)."
  (cond ((eql (getf *state* :block) (1- n)))
        ((probe-file (checkpoint-path (1- n)))
         (setf *state* (with-open-file (s (checkpoint-path (1- n))) (with-standard-io-syntax (read s)))
               *undo* '()))
        (t (setf *state* (empty) *undo* '())
           (when (> n 1)
             (format *error-output* "~&[durable] no checkpoint at block ~D: the fold covers blocks ~D.. only~%" (1- n) n))))
  (unless (getf *state* :from) (setf (getf *state* :from) n)))

(defun state () (eita:with-fold-state () (copy-list *state*)))

(eita:subscribe "durable" :start 'on-start :block 'on-block :checkpoint 'on-checkpoint :rollback 'on-rollback)
