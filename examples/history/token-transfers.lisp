;;;; examples/history/token-transfers.lisp — every ERC-20 Transfer of a token between two
;;;; blocks, optionally only those of one address, from the log shards.
;;;;
;;;;   (load "examples/history/token-transfers.lisp")
;;;;   (history.transfers:transfers "factlog/" "0xA0b8…eB48" 24538000 24538111)
;;;;   (history.transfers:transfers "factlog/" "0xA0b8…eB48" 24538000 24538111 :address "0x…")
;;;;
;;;; A scan of the range's log shards, one group in memory at a time: the emitter column is
;;;; decoded first and the topics and data only at the token's logs.

(defpackage #:history.transfers (:use #:cl) (:export #:transfers))
(in-package #:history.transfers)

(defparameter +transfer-topic+ #xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef
  "keccak256(\"Transfer(address,address,uint256)\").")

(defun transfers (dir token from to &key address)
  "TOKEN's Transfer logs in blocks FROM..TO (from or to ADDRESS, when given), in chain order:
   plists (:block :tx :from :to :value)."
  (let ((who (and address (eita:addr address))) (out '()))
    (eita-factlog:map-rows
     (lambda (row)
       ;; (block tx log-index address topics data): ERC-20 has three topics and 32 bytes of data
       (destructuring-bind (block tx i a topics data) row
         (declare (ignore i a))
         (when (and (= (length topics) 3) (eql (first topics) +transfer-topic+) (= (length data) 64)
                    (or (null who) (eql who (second topics)) (eql who (third topics))))
           (push (list :block block :tx tx :from (second topics) :to (third topics)
                       :value (parse-integer data :radix 16))
                 out))))
     dir :log from to :where (cons 3 (let ((tk (eita:addr token))) (lambda (a) (eql a tk)))))
    (nreverse out)))
