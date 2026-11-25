;;;; tests/op-l1-fee.lisp — the OP-Stack L1 data fee on real Base transactions, every fork.
;;;;
;;;; tests/data/op-l1-fee.sexp: 72 user txs from Base blocks 2M..47M (Bedrock to Azul), each
;;;; with its signed EIP-2718 bytes, op-geth's FastLZ length of them and the l1Fee its receipt
;;;; reports with the L1 attributes it was priced at. Checks: the bytes are the tx (their
;;;; keccak is its hash), the emitted spec-flz-compress-len (Evm.Optimism.Fjord.Spec.FastLz)
;;;; gives op-geth's length, and the emitted spec-op-l1-fee (Evm.Optimism.Replay.Emit,
;;;; proved = Replay.l1FeeWei) gives the receipt's fee. The replay reads the same attributes
;;;; from the L1Block predeploy's storage (chains/op.lisp tx-l1-fee).

(in-package #:eita.evm)

(let ((fails 0) (n 0))
  (with-open-file (in (asdf:system-relative-pathname "eita" "tests/data/op-l1-fee.sexp"))
    (loop for row = (read in nil) while row
          do (destructuring-bind (blk ord hash hex flz fee base overhead scalar blob bfs bbfs) row
               (let* ((bytes (hex->bytes hex)) (zero (count 0 bytes)))
                 (incf n)
                 (flet ((check (what got want)
                          (unless (eql got want)
                            (incf fails)
                            (format t "~&  FAIL block ~D tx ~A: ~A ~D, expected ~D~%" blk hash what got want))))
                   (check "keccak" (octets-int (keccak256-bytes bytes)) (parse-integer hash :radix 16))
                   (check "FastLZ length" (spec-flz-compress-len bytes) flz)
                   (check "l1Fee" (spec-op-l1-fee ord zero (- (length bytes) zero) (if (>= ord 3) flz 0)
                                                  base overhead scalar blob bfs bbfs)
                          fee))))))
  (format t "~&  ~D txs, ~D failures~%" n fails)
  (unless (and (= n 72) (zerop fails)) (eita.test:finish :code 1)))
