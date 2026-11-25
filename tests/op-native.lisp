;;;; tests/op-native.lisp — Base's native precompiles (Denim) through the engine's host.
;;;;
;;;; 1. The Lean table (spec-op-native-kind, Evm.Optimism.Beryl.Spec.nativeKind) and the
;;;;    linked code's (eita_base_precompile_kind: base/base provider.rs + lookup.rs) agree on
;;;;    every OP fork from Azul to Denim, on the installed addresses, B-20 token addresses of
;;;;    both variants, and near misses.
;;;; 2. A REAL Base mainnet tx, replayed from its prestate (tests/data/base-b20-approve.sexp:
;;;;    prestateTracer of block 62,112,528's `approve` on a B-20 asset token, called straight
;;;;    from an EOA): the receipt's gasUsed, status and Approval log.
;;;; 3. On the state it leaves, the token's own answers (the golden behaviour of base/base
;;;;    tests/b20_asset_v3_golden.rs): `allowance` is the approved amount; a call with value
;;;;    reverts `NonPayable()` (b20_asset/dispatch.rs:50-53); a
;;;;    DELEGATECALL reverts `DelegateCallNotAllowed()` at no gas (macros.rs:13-19).
;;;;
;;;; Run: (eita.test:run-all :only '("op-native")), or (asdf:test-system "eita") for all suites.

(in-package #:eita.chain.op)

(defparameter *fails* 0)

(defun chk (name got want)
  (if (equalp got want)
      (format t "  ok    ~A~%" name)
      (progn (incf *fails*)
             (format t "  FAIL  ~A~%        got  ~S~%        want ~S~%" name got want))))

(defun hex-octets (s) (if (zerop (length s)) (make-array 0 :element-type '(unsigned-byte 8)) (hex->bytes s)))
(defun word (x) (let ((v (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)))
                  (loop for i below 32 do (setf (aref v (- 31 i)) (ldb (byte 8 (* 8 i)) x))) v))
(defun abi (selector &rest words)
  (apply #'concatenate '(vector (unsigned-byte 8))
         (let ((s (make-array 4 :element-type '(unsigned-byte 8))))
           (dotimes (i 4 s) (setf (aref s i) (ldb (byte 8 (* 8 (- 3 i))) selector))))
         (mapcar #'word words)))

;;; 1. The two classifications
(base-ensure-lib!)
(let ((addrs (list #xB20F000000000000000000000000000000000000 #x8453000000000000000000000000000000000001
                   #x8453000000000000000000000000000000000002 #x8453000000000000000000000000000000000003
                   #x813000000000000000000000000000000000aa01 #x813000000000000000000000000000000000aa02
                   #xb200000000000000000000f1a0f91e34892e4718 #xb200000000000000000001f1a0f91e34892e4718
                   #xb200000000000000000002f1a0f91e34892e4718 #xb200000000000000000100000000000000000000
                   #xb2cc000000000000000000000000000000000001 #xb3000000000000000000000000000000000000ff
                   #x4200000000000000000000000000000000000030 0 1)))
  (cffi:with-foreign-object (p :uint8 20)
    (dolist (f '(8 9 10 11))
      (dolist (a addrs)
        (be-write p 20 a)
        (chk (format nil "kind of ~40,'0x at OP fork ~D" a f)
             (spec-op-native-kind f a) (%base-precompile-kind p f))))))

;;; 2. The mainnet tx from its prestate (Base's chain spec for the duration; the suites after
;;; this one run Ethereum's, so it is restored on the way out)
(unwind-protect
(let* ((fx (with-open-file (in (asdf:system-relative-pathname "eita" "tests/data/base-b20-approve.sexp")) (read in)))
       (b (getf fx :block)) (tx (getf fx :tx)) (rc (getf fx :receipt))
       (alloc (loop for (a . pl) in (getf fx :alloc)
                    collect (list a :balance (getf pl :balance) :nonce (getf pl :nonce)
                                    :code (hex-octets (getf pl :code)) :storage (getf pl :storage)))))
  (install-chain-spec! (op-chain-spec "base"))
  (let ((w (eita:new-world :fork "Osaka" :alloc alloc))
        (token (getf tx :to)) (owner (getf tx :from)))
    (setf *op-fork* +op-denim+
          eita::*block* (list :number (getf b :number) :timestamp (getf b :timestamp) :base-fee 0
                              :gas-limit 300000000 :coinbase (getf b :coinbase) :prev-randao 0
                              :chain-id 8453 :excess-blob-gas 0))
    (let ((r (eita:transact w :from owner :to token :data (hex-octets (getf tx :data))
                              :gas (getf tx :gas) :value (getf tx :value))))
      (chk "approve: status" (getf r :status) (getf rc :status))
      (chk "approve: gasUsed" (getf r :gas-used) (getf rc :gas-used))
      (chk "approve: logs" (mapcar (lambda (l) (list (first l) (second l) (third l))) (getf r :logs))
           (mapcar (lambda (l) (list (first l) (second l) (hex-octets (third l)))) (getf rc :logs))))
    ;; 3. The token's answers on that state
    (let* ((data (hex-octets (getf tx :data)))
           (spender (octets-int (subseq data 4 36))) (amount (octets-int (subseq data 36 68))))
      (chk "allowance(owner, spender) = the approved amount"
           (getf (eita:call w :from owner :to token :data (abi #xdd62ed3e owner spender)) :output) (word amount))
      (let ((r (eita:call w :from owner :to token :value 1 :data (abi #x313ce567))))
        (chk "a call with value: reverted" (getf r :status) 0)
        (chk "a call with value: NonPayable()" (getf r :output)
             (subseq (keccak256-bytes (map '(vector (unsigned-byte 8)) #'char-code "NonPayable()")) 0 4))))
    ;; the DELEGATECALL boundary, at the hook: a revert with no gas used
    (cffi:with-foreign-object (in :uint8 4)
      (multiple-value-bind (used out ok)
          (let ((*current-world* w)) (op-native-precompile-run token 2 owner in 0 100000 nil 0))
        (chk "DELEGATECALL: no gas" used 0)
        (chk "DELEGATECALL: reverted" ok nil)
        (chk "DELEGATECALL: DelegateCallNotAllowed()" out
             (subseq (keccak256-bytes (map '(vector (unsigned-byte 8)) #'char-code "DelegateCallNotAllowed()")) 0 4))))))
  (install-chain-spec! (make-chain-spec))
  (setf *op-fork* 0
        eita::*block* (list :number 1 :timestamp 1700000000 :base-fee 0 :gas-limit 30000000
                            :coinbase 0 :prev-randao 0 :chain-id 1 :excess-blob-gas 0)))

(format t "~&  op-native: ~D failure~:P~%" *fails*)
(unless (zerop *fails*) (eita.test:finish :code 1))
