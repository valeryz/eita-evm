;;;; test-genesis-alloc.lisp — the Ethereum mainnet genesis allocation for the MPT oracles,
;;;; read from chains/ethereum/genesis.json (geth format; every mainnet genesis account has a
;;;; decimal balance and nothing else). Loaded after mpt.lisp, in its package.

(in-package #:eita.mpt)

(defun genesis-alloc (&optional (path (merge-pathnames "../chains/ethereum/genesis.json"
                                                        (or *load-truename* *default-pathname-defaults*))))
  "The mainnet genesis accounts as plists (:addr :nonce :balance :code)."
  (let* ((text (with-open-file (in path) (let ((s (make-string (file-length in)))) (subseq s 0 (read-sequence s in)))))
         (start (+ (search "\"alloc\"" text) 7)) (out '()))
    (loop with i = start
          for q = (position #\" text :start i)
          while (and q (< (+ q 41) (length text)) (char= (char text (+ q 41)) #\"))
          do (let* ((addr (parse-integer text :start (1+ q) :end (+ q 41) :radix 16))
                    (b0 (+ (search "\"balance\":\"" text :start2 q) 11))
                    (b1 (position #\" text :start b0)))
               (push (list :addr addr :nonce 0 :balance (parse-integer text :start b0 :end b1) :code nil) out)
               (setf i (1+ (position #\} text :start b1)))))
    (nreverse out)))
