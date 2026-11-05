;;;; core/u256.lisp — u256 values as four little-endian 64-bit limbs in foreign memory.

(in-package #:eita.core)

;; u256 <-> four little-endian 64-bit limbs. Small values stay fixnums (no
;; allocation); large ones (addresses, keccak slots, token balances) are read
;; and written digit by digit through SBCL's bignum accessors instead of a
;; shift+logior per limb, which allocated a fresh bignum at every step
;; (BIGNUM-ASHIFT-RIGHT-DIGITS / %NORMALIZE-BIGNUM, ~6 % of the Arc replay).
;; Bignum digits are 64-bit two's-complement words, least significant first,
;; on both supported targets (x86-64, arm64).
(eval-when (:compile-toplevel :load-toplevel :execute)
  (assert (= sb-vm:n-word-bits 64)))
(declaim (inline u256-write-slow))
(defun u256-write-slow (ptr value)
  (loop for i from 0 below 4 do
    (setf (mem-aref ptr :uint64 i)
          (logand (ash value (- (* i 64))) #xFFFFFFFFFFFFFFFF))))
(defun u256-write (ptr value)
  (cond ((sb-sys:system-area-pointer-p value)          ; an opaque word in place: copy it
         (dotimes (i 4) (setf (mem-aref ptr :uint64 i) (mem-aref value :uint64 i))))
        ((typep value '(and fixnum unsigned-byte))
         (setf (mem-aref ptr :uint64 0) value
               (mem-aref ptr :uint64 1) 0
               (mem-aref ptr :uint64 2) 0
               (mem-aref ptr :uint64 3) 0))
        ((and (typep value 'bignum) (plusp value))
         (let ((n (sb-bignum:%bignum-length value)))
           (dotimes (i 4)
             (setf (mem-aref ptr :uint64 i)
                   (if (< i n) (sb-bignum:%bignum-ref value i) 0)))))
        (t (u256-write-slow ptr value))))

(defun u256-read (ptr)
  (words-u256 (mem-aref ptr :uint64 0) (mem-aref ptr :uint64 1) (mem-aref ptr :uint64 2) (mem-aref ptr :uint64 3)))

(declaim (inline word-int))
(defun word-int (w)
  "The integer of W: W itself, or the four limbs W points at. A storage KEY crosses the
   SLOAD/SSTORE seam as the pointer to its stack slot (an opaque word, valid for the
   callback): the tables, the access sets and the journal copy its limbs; whatever
   KEEPS a key (an observer, the read stream, the root tracker, a fault hook) takes its
   integer here."
  (if (sb-sys:system-area-pointer-p w) (u256-read w) w))

(defun words-u256 (l0 l1 l2 l3)
  "The integer whose four 64-bit limbs (least significant first) are L0..L3, built digit by
   digit (no intermediate bignums)."
  (declare (type (unsigned-byte 64) l0 l1 l2 l3) (optimize speed))
  (progn
    (if (and (zerop l1) (zerop l2) (zerop l3))
        l0
        ;; top nonzero limb, plus one zero digit when its sign bit is set
        (let* ((top (cond ((/= l3 0) 3) ((/= l2 0) 2) (t 1)))
               (top-limb (case top (3 l3) (2 l2) (t l1)))
               (len (+ top 1 (if (logbitp 63 top-limb) 1 0)))
               (b (sb-bignum:%allocate-bignum len)))
          (setf (sb-bignum:%bignum-ref b 0) l0)
          (when (>= top 1) (setf (sb-bignum:%bignum-ref b 1) l1))
          (when (>= top 2) (setf (sb-bignum:%bignum-ref b 2) l2))
          (when (>= top 3) (setf (sb-bignum:%bignum-ref b 3) l3))
          (when (> len (1+ top)) (setf (sb-bignum:%bignum-ref b (1+ top)) 0))
          (sb-bignum::%normalize-bignum b len)))))

(defun u256->octets (n &optional (width 32))
  "Big-endian WIDTH-byte octet vector of the non-negative integer N (mod 2^(8·WIDTH))."
  (let ((o (make-array width :element-type '(unsigned-byte 8) :initial-element 0)))
    (cffi:with-foreign-object (w :uint64 4)
      (u256-write w n)
      (dotimes (k (min width 32) o)
        (setf (aref o (- width 1 k)) (mem-aref w :uint8 k))))))
