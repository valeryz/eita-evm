;;;; examples/history/daily.lisp — analytics as a reduce over the shards: per UTC day, the
;;;; txs, the gas, the fees burnt and the distinct senders, over a block range.
;;;;
;;;;   (load "examples/history/daily.lisp")
;;;;   (history.daily:daily "factlog/" 24000000 24538111)
;;;;   ;; => ((:day "2026-02-25" :txs … :gas … :burnt … :senders …) …)
;;;;
;;;; Memory: the answer (one entry per day), one shard's block table (its days and base fees)
;;;; and the current day's senders — not the range. Only the columns used are decoded: the
;;;; block table's timestamp and base fee, the tx table's sender and gas used.

(defpackage #:history.daily (:use #:cl) (:export #:daily))
(in-package #:history.daily)

(defun day-of (timestamp)
  (multiple-value-bind (s m h day month year) (decode-universal-time (+ timestamp 2208988800) 0)
    (declare (ignore s m h))
    (format nil "~D-~2,'0D-~2,'0D" year month day)))

(defun daily (dir from to &key (shard eita-factlog:*shard-blocks*))
  "Per UTC day of blocks FROM..TO: plists (:day :txs :gas :burnt :senders), oldest first."
  (let ((out '()) (day nil) (senders (make-hash-table)) (txs 0) (gas 0) (burnt 0))
    (flet ((close-day ()
             (when day
               (push (list :day day :txs txs :gas gas :burnt burnt :senders (hash-table-count senders)) out)
               (clrhash senders) (setf txs 0 gas 0 burnt 0))))
      (loop for lo from (* shard (floor from shard)) to to by shard
            for a = (max lo from) for b = (min (+ lo shard -1) to)
            do (let ((blocks (make-hash-table)))            ; block -> (day . base-fee), this shard's
                 ;; block: (block timestamp coinbase base-fee …); tx: (block tx hash from to value type gas-used …)
                 (eita-factlog:map-rows (lambda (r) (setf (gethash (first r) blocks) (cons (day-of (second r)) (fourth r))))
                                        dir :block a b :cols '(1 3))
                 (eita-factlog:map-rows
                  (lambda (r)
                    (destructuring-bind (d . base-fee) (gethash (first r) blocks)
                      (unless (equal d day) (close-day) (setf day d))
                      (incf txs) (incf gas (eighth r)) (incf burnt (* (eighth r) base-fee))
                      (setf (gethash (fourth r) senders) t)))
                  dir :tx a b :cols '(3 7))))
      (close-day))
    (nreverse out)))
