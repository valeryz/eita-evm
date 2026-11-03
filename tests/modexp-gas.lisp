(in-package #:eita.evm)
;;;; #260 verification: modexp-gas against the EIPs' OWN published numbers.
;;;; Canonical EIP-198 example: modexp(3, 2^256-2^32-978, 2^256-2^32-977),
;;;;   base_len=exp_len=mod_len=32.
;;;;   EIP-198 (pre-Berlin): mult_complexity(32)=1024, adj_exp_len=255,
;;;;                         gas = 1024*255/20 = 13056.
;;;;   EIP-2565 (Berlin+):   words=4, mc=16, gas = max(200,16*255/3) = 1360.
;;;; These two numbers are stated in EIP-198 / EIP-2565 themselves.

(defun u256-be-bytes (n) (let ((v (make-array 32 :element-type '(unsigned-byte 8))))
  (dotimes (i 32 v) (setf (aref v (- 31 i)) (ldb (byte 8 (* 8 i)) n)))))

(defun make-modexp-input (base exp modulus base-len exp-len mod-len)
  "EIP-198 ABI: 3x 32-byte BE lengths, then base|exp|mod each its declared length."
  (let* ((hdr (concatenate 'vector
                (u256-be-bytes base-len) (u256-be-bytes exp-len) (u256-be-bytes mod-len)))
         (body (concatenate 'vector
                 (subseq (u256-be-bytes base) (- 32 base-len))
                 (subseq (u256-be-bytes exp)  (- 32 exp-len))
                 (subseq (u256-be-bytes modulus) (- 32 mod-len))))
         (all (concatenate 'vector hdr body))
         (n (length all))
         (p (foreign-alloc :uint8 :count n)))
    (dotimes (i n) (setf (mem-aref p :uint8 i) (aref all i)))
    (values p n)))

(defun check (label fork-ord input-ptr input-len expected)
  (let* ((*fork-ord* fork-ord)
         (got (modexp-gas input-ptr input-len)))
    (format t "~&[~A] fork=~D  got=~D  expected=~D  ~A~%"
            label fork-ord got expected (if (= got expected) "PASS" "*** FAIL ***"))
    (= got expected)))

(let ((exp (- (expt 2 256) (expt 2 32) 978))
      (mod (- (expt 2 256) (expt 2 32) 977))
      (ok t))
  (multiple-value-bind (p n) (make-modexp-input 3 exp mod 32 32 32)
    ;; EIP-198 number, all pre-Berlin forks (Byzantium=5 .. Istanbul=8/9)
    (dolist (f '(5 6 7 8))
      (unless (check "EIP-198 canonical" f p n 13056) (setf ok nil)))
    ;; EIP-2565 number, Berlin+ (10,11,...)
    (dolist (f '(10 11 16))
      (unless (check "EIP-2565 canonical" f p n 1360) (setf ok nil))))
  ;; edge: exp_len > 32 — adj = 8*(exp_len-32) + (bit_length(head32)-1).
  ;; base_len=mod_len=1, exp_len=64, exponent bit 511 set (first byte 0x80).
  ;; head32 = 2^255 → bit_length=256 → head term 255; plus 8*(64-32)=256 → adj=511.
  ;; maxlen=1 → mc=1 (EIP-198). gas = floor(1*511/20) = 25.  Build bytes directly.
  (let* ((bytes (make-array (+ 96 1 64 1) :element-type '(unsigned-byte 8) :initial-element 0)))
    (setf (aref bytes 31) 1)         ; base_len = 1
    (setf (aref bytes 63) 64)        ; exp_len  = 64
    (setf (aref bytes 95) 1)         ; mod_len  = 1
    (setf (aref bytes 96) 1)         ; base = 0x01
    (setf (aref bytes 97) #x80)      ; exponent MSB byte → bit 511
    (setf (aref bytes (+ 97 64)) 1)  ; modulus = 0x01
    (let* ((n (length bytes)) (p (foreign-alloc :uint8 :count n)))
      (dotimes (i n) (setf (mem-aref p :uint8 i) (aref bytes i)))
      (unless (check "EIP-198 exp_len>32 (adj=511,maxlen=1)" 5 p n 25) (setf ok nil))))
  (format t "~&==== modexp-gas: ~A ====~%" (if ok "ALL VECTORS PASS" "FAILURES"))
  (eita.test:finish :code (if ok 0 1)))
