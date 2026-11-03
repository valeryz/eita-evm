;;;; evm/precompiles.lisp — the precompiled contracts 0x01..0x11 and 0x100.

(in-package #:eita.evm)

(defun read-input-byte (input-ptr input-len i)
  "Read INPUT-PTR[i], zero-padded past INPUT-LEN."
  (if (< i input-len) (mem-aref input-ptr :uint8 i) 0))

(defun read-input-be-u64 (input-ptr input-len off width)
  "Read big-endian unsigned integer of WIDTH bytes from INPUT-PTR[off..off+width]."
  (let ((v 0))
    (loop for i below width do
      (setf v (+ (* v 256) (read-input-byte input-ptr input-len (+ off i)))))
    v))

(defun modexp-gas (input-ptr input-len)
  "MODEXP (0x05) gas. Reads the input header (the hand-written CL SEAM) and defers
   the gas FORMULA to the Lean-emitted `spec-modexp-gas` (src/generated/host.lisp,
   from Evm.CL.GasEmit.modexpGas — fork-aware EIP-198 pre-Berlin / EIP-2565 Berlin+,
   eval kernel-checked against the EIPs' own numbers). #260/#261: there is no
   hand-written gas curve here anymore — it is derived from the verified spec."
  (let* ((base-sz  (read-input-be-u64 input-ptr input-len 0 32))
         (exp-sz   (read-input-be-u64 input-ptr input-len 32 32))
         (mod-sz   (read-input-be-u64 input-ptr input-len 64 32))
         ;; first min(exp_len,32) bytes of the exponent, big-endian, as an integer
         (exp-head (read-input-be-u64 input-ptr input-len (+ 96 base-sz) (min exp-sz 32))))
    (spec-modexp-gas base-sz exp-sz mod-sz exp-head *fork-ord*)))

(defun run-precompile (addr input-ptr input-len gas-budget)
  "Dispatch precompile at ADDR with INPUT-LEN bytes at INPUT-PTR. Returns
   (values gas-used output-bytes). On OOG returns (gas-budget nil) and the
   caller pushes 0 onto the stack. On success returns the precompile's gas
   cost and output bytes (possibly empty)."
  (let ((cost
          ;; Precompile gas is DERIVED from the Lean spec (Evm.CL.GasEmit, emitted to
          ;; src/generated/host.lisp). #261: no hand-written precompile gas here.
          (case addr
            (1 (spec-ecrecover-gas))                                ; ECRECOVER
            (2 (spec-sha256-gas input-len))                         ; SHA256
            (3 (spec-ripemd160-gas input-len))                      ; RIPEMD160
            (4 (spec-identity-gas input-len))                       ; IDENTITY
            (5 (modexp-gas input-ptr input-len))                    ; MODEXP (seam→spec-modexp-gas)
            (6 (spec-bn256-add-gas *fork-ord*))                     ; BN254 ADD
            (7 (spec-bn256-mul-gas *fork-ord*))                     ; BN254 MUL
            (8 (spec-bn256-pairing-gas input-len *fork-ord*))       ; BN254 PAIRING
            (9 (if (= input-len 213)                                ; BLAKE2F (EIP-152)
                   (read-input-be-u64 input-ptr input-len 0 4)
                   most-positive-fixnum))
            (10 (spec-point-evaluation-gas))                        ; POINT_EVALUATION (EIP-4844)
            (256 (if (eq *p256verify* :rip7212)                     ; P256VERIFY: RIP-7212 (OP
                     (spec-rip7212-gas)                             ;  Fjord..Isthmus) or
                     (spec-p256verify-gas)))                        ;  EIP-7951
            ;; EIP-2537 BLS12-381 (Prague+). An invalid length still gets a cost here
            ;; and then fails in the operation, which consumes the whole pool anyway.
            (11 (spec-bls-g1add-gas))                               ; G1ADD
            (12 (spec-bls-g1msm-gas input-len))                     ; G1MSM
            (13 (spec-bls-g2add-gas))                               ; G2ADD
            (14 (spec-bls-g2msm-gas input-len))                     ; G2MSM
            (15 (spec-bls-pairing-gas input-len))                   ; PAIRING_CHECK
            (16 (spec-bls-map-fp-to-g1-gas))                        ; MAP_FP_TO_G1
            (17 (spec-bls-map-fp2-to-g2-gas))                       ; MAP_FP2_TO_G2
            (t most-positive-fixnum))))
    ;; An in-range precompile with no implementation is a LOUD stop, never a quiet
    ;; answer: the missing 0x0b..0x11 read as empty accounts and cost one call base
    ;; (Arc 21 142 242, −131 592 gas).
    (unless (member addr +precompile-impls+)
      (error "precompile ~2,'0x is in range at fork ord ~D but has no implementation~@[ (also missing: ~{0x~2,'0x~^, ~})~]"
             addr *fork-ord* (remove addr (precompile-coverage-gaps))))
    (when (> cost gas-budget)
      (return-from run-precompile (values gas-budget nil)))
    (case addr
      (1 ; ECRECOVER — input is right-zero-padded to 128 bytes per ABI
       (with-foreign-object (in-buf :uint8 128)
         (loop for i below 128 do
           (setf (mem-aref in-buf :uint8 i)
                 (if (< i input-len) (mem-aref input-ptr :uint8 i) 0)))
         (with-foreign-object (out-buf :uint8 32)
           (let ((ok (plusp (%eita-ecrecover in-buf 128 out-buf))))
             (if ok
                 (let ((out (make-array 32 :element-type '(unsigned-byte 8))))
                   (loop for i below 32 do
                     (setf (aref out i) (mem-aref out-buf :uint8 i)))
                   (values cost out))
                 ;; Invalid sig: per EELS, precompile returns empty but
                 ;; the call still SUCCEEDS (pushes 1 on stack). Use the
                 ;; cost we already charged and an empty byte array.
                 (values cost (make-array 0 :element-type '(unsigned-byte 8))))))))
      (2 ; SHA256
       (let ((out (make-array 32 :element-type '(unsigned-byte 8))))
         (with-foreign-object (out-buf :uint8 32)
           (%sha256-hash input-ptr input-len out-buf)
           (loop for i below 32 do
             (setf (aref out i) (mem-aref out-buf :uint8 i))))
         (values cost out)))
      (3 ; RIPEMD160 — output is 20 bytes, returned as 32-byte left-zero-padded
       (let ((out (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)))
         (with-foreign-object (out-buf :uint8 20)
           (%ripemd160-hash input-ptr input-len out-buf)
           (loop for i below 20 do
             (setf (aref out (+ 12 i)) (mem-aref out-buf :uint8 i))))
         (values cost out)))
      (4 ; IDENTITY: return input verbatim
       (let ((out (make-array input-len :element-type '(unsigned-byte 8))))
         (when (plusp input-len)
           (loop for i below input-len do
             (setf (aref out i) (mem-aref input-ptr :uint8 i))))
         (values cost out)))
      (5 ; MODEXP
       (let* ((mod-sz (read-input-be-u64 input-ptr input-len 64 32)))
         ;; EIP-7823 (Osaka+, EELS osaka/vm/precompiled_contracts/modexp.py 31-41): an
         ;; operand length over 1024 bytes is an ExceptionalHalt — the call fails and
         ;; consumes its whole pool (Evm.Osaka.Spec.ModexpGas.IsValidModexpInput).
         (when (and (>= *fork-ord* 18)
                    (or (> (read-input-be-u64 input-ptr input-len 0 32) 1024)
                        (> (read-input-be-u64 input-ptr input-len 32 32) 1024)
                        (> mod-sz 1024)))
           (return-from run-precompile (values gas-budget nil)))
         (with-foreign-objects ((out-buf :uint8 (max mod-sz 1))
                                (out-len :uint64))
           (let ((ok (plusp (%eita-modexp input-ptr input-len out-buf out-len))))
             (if ok
                 (let* ((n (mem-ref out-len :uint64))
                        (out (make-array n :element-type '(unsigned-byte 8))))
                   (loop for i below n do
                     (setf (aref out i) (mem-aref out-buf :uint8 i)))
                   (values cost out))
                 (values gas-budget nil))))))
      ((6 7) ; BN254 ECADD / ECMUL — both return 64 bytes
       (with-foreign-object (out-buf :uint8 64)
         (let ((ok (plusp (if (= addr 6)
                              (%eita-bn254-add  input-ptr input-len out-buf)
                              (%eita-bn254-mul  input-ptr input-len out-buf)))))
           (if ok
               (let ((out (make-array 64 :element-type '(unsigned-byte 8))))
                 (loop for i below 64 do
                   (setf (aref out i) (mem-aref out-buf :uint8 i)))
                 (values cost out))
               ;; EELS treats invalid bn254 input as OutOfGasError, so
               ;; consume all available gas and return nil output (caller
               ;; pushes 0 onto the stack).
               (values gas-budget nil)))))
      (8 ; BN254 PAIRING — returns 32 bytes
       (with-foreign-object (out-buf :uint8 32)
         (let ((ok (plusp (%eita-bn254-pairing input-ptr input-len out-buf))))
           (if ok
               (let ((out (make-array 32 :element-type '(unsigned-byte 8))))
                 (loop for i below 32 do
                   (setf (aref out i) (mem-aref out-buf :uint8 i)))
                 (values cost out))
               (values gas-budget nil)))))
      (9 ; BLAKE2F — returns 64 bytes
       (with-foreign-object (out-buf :uint8 64)
         (let ((ok (plusp (%eita-blake2f input-ptr input-len out-buf))))
           (if ok
               (let ((out (make-array 64 :element-type '(unsigned-byte 8))))
                 (loop for i below 64 do
                   (setf (aref out i) (mem-aref out-buf :uint8 i)))
                 (values cost out))
               (values gas-budget nil)))))
      (256 ; P256VERIFY — Evm.Osaka.Spec.P256VerifyStep: gas charged above; input must be
           ; exactly 160 bytes, else empty output; success = 32-byte big-endian 1, else empty.
       (if (and (= input-len 160) (plusp (%eita-p256-verify input-ptr)))
           (let ((out (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)))
             (setf (aref out 31) 1)
             (values cost out))
           (values cost (make-array 0 :element-type '(unsigned-byte 8)))))
      (10 ; POINT_EVALUATION (EIP-4844) — gas charged above; every KZGProofError
          ; (length, versioned hash, malformed or failing proof) consumes the pool.
       (with-foreign-object (out-buf :uint8 64)
         (if (plusp (%eita-point-evaluation input-ptr input-len out-buf))
             (let ((out (make-array 64 :element-type '(unsigned-byte 8))))
               (loop for i below 64 do
                 (setf (aref out i) (mem-aref out-buf :uint8 i)))
               (values cost out))
             (values gas-budget nil))))
      ((11 12 13 14 15 16 17)   ; EIP-2537 BLS12-381 — all seven share one shape
       (let ((out-len (case addr ((11 12 16) 128) ((13 14 17) 256) (15 32)))
             (fn (case addr
                   (11 #'%eita-bls-g1add) (12 #'%eita-bls-g1msm)
                   (13 #'%eita-bls-g2add) (14 #'%eita-bls-g2msm)
                   (15 #'%eita-bls-pairing)
                   (16 #'%eita-bls-map-fp-to-g1) (17 #'%eita-bls-map-fp2-to-g2))))
         (with-foreign-object (out-buf :uint8 out-len)
           (if (plusp (funcall fn input-ptr input-len out-buf))
               (let ((out (make-array out-len :element-type '(unsigned-byte 8))))
                 (loop for i below out-len do
                   (setf (aref out i) (mem-aref out-buf :uint8 i)))
                 (values cost out))
               ;; Invalid encoding, off-curve, wrong subgroup or bad length: the EIP
               ;; fails the precompile and consumes every gas forwarded to it.
               (values gas-budget nil)))))
      (otherwise
       ;; ECRECOVER and other unimplemented precompiles: charge the gas (or
       ;; OOG via the cost > gas-budget check above), but return empty
       ;; output. ECRECOVER with valid signature should return a 32-byte
       ;; address, but tests in scope so far have invalid inputs where the
       ;; precompile returns empty per EELS — so this is correct for them.
       (values cost (make-array 0 :element-type '(unsigned-byte 8)))))))
