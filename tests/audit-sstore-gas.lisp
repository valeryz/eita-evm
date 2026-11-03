;;;; audit-sstore-gas.lisp — differential audit of the emitted SSTORE
;;;; gas plans and the _eita_access_costs table against their Lean
;;;; oracles:
;;;;   legacy  -> _eita_sstore_gas_legacy   (Frontier sstoreGas)
;;;;   eip1283 -> _eita_sstore_gas_eip1283  (Constantinople sstoreGas)
;;;;   eip2200 -> _eita_sstore_gas_eip2200  (Istanbul sstoreGas)
;;;;   berlin  -> _eita_sstore_gas_berlin   (Berlin sstoreGas)
;;;;   london  -> _eita_sstore_gas_london   (London sstoreGas)
;;;;   access  -> _eita_access_costs[ord*8 + kind*2 + (cold ? 0 : 1)]
;;;;
;;;; Vectors come from `lake exe sstoreGasVectors`. SSTORE lines carry
;;;; full-width u256 orig/cur/new (single-limb diffs included — the
;;;; native plans fold zero/eq across all 4 limbs); the native must
;;;; reproduce cost AND newRefund exactly, including each plan's refund
;;;; clamp discipline. access lines check the table's byte layout via
;;;; the same index formula src/evm/'s access-cost uses.
;;;;
;;;; Run: (eita.test:run-all :only '("audit-sstore-gas")), or (asdf:test-system "eita") for all suites.

(defpackage #:eita.test.audit-sstore-gas (:use #:cl #:cffi))
(in-package :eita.test.audit-sstore-gas)

(defcfun ("eita_sstore_gas_legacy" %sstore-legacy) :void
  (out :pointer) (refund :uint64) (orig :pointer) (cur :pointer)
  (new :pointer) (cold :uint64))
(defcfun ("eita_sstore_gas_eip1283" %sstore-eip1283) :void
  (out :pointer) (refund :uint64) (orig :pointer) (cur :pointer)
  (new :pointer) (cold :uint64))
(defcfun ("eita_sstore_gas_eip2200" %sstore-eip2200) :void
  (out :pointer) (refund :uint64) (orig :pointer) (cur :pointer)
  (new :pointer) (cold :uint64))
(defcfun ("eita_sstore_gas_berlin" %sstore-berlin) :void
  (out :pointer) (refund :uint64) (orig :pointer) (cur :pointer)
  (new :pointer) (cold :uint64))
(defcfun ("eita_sstore_gas_london" %sstore-london) :void
  (out :pointer) (refund :uint64) (orig :pointer) (cur :pointer)
  (new :pointer) (cold :uint64))

(defun u256-write (ptr v)
  (loop for i below 4
        do (setf (mem-aref ptr :uint64 i)
                 (ldb (byte 64 (* 64 i)) v))))

(defun main ()
  (let ((vectors-path (or eita.test:*argument*
                          "/tmp/sstore_gas_vectors.txt"))
        (access-tbl (foreign-symbol-pointer "eita_access_costs"))
        (total 0) (bad 0))
    (assert access-tbl () "eita_access_costs not found in libeita")
    (with-foreign-objects ((out :uint64 2)
                           (orig :uint64 4) (cur :uint64 4) (new :uint64 4))
      (with-open-file (in vectors-path)
        (loop for line = (read-line in nil)
              while line
              unless (string= line "")
              do (with-input-from-string (s line)
                   (let ((plan (read s)))
                     (incf total)
                     (if (eq plan 'access)
                         (let* ((ord (read s)) (kind (read s))
                                (cold (read s)) (cost (read s))
                                (got (mem-aref access-tbl :uint64
                                               (+ (* ord 8) (* kind 2)
                                                  (if (plusp cold) 0 1)))))
                           (unless (= got cost)
                             (incf bad)
                             (format t "MISMATCH access ord=~D kind=~D cold=~D: native ~D lean ~D~%"
                                     ord kind cold got cost)))
                         (let ((refund (read s)) (o (read s)) (c (read s))
                               (n (read s)) (cold (read s))
                               (cost (read s)) (new-refund (read s)))
                           (u256-write orig o)
                           (u256-write cur c)
                           (u256-write new n)
                           (ecase plan
                             (legacy  (%sstore-legacy  out refund orig cur new cold))
                             (eip1283 (%sstore-eip1283 out refund orig cur new cold))
                             (eip2200 (%sstore-eip2200 out refund orig cur new cold))
                             (berlin  (%sstore-berlin  out refund orig cur new cold))
                             (london  (%sstore-london  out refund orig cur new cold)))
                           (let ((nc (mem-aref out :uint64 0))
                                 (nr (mem-aref out :uint64 1)))
                             (unless (and (= nc cost) (= nr new-refund))
                               (incf bad)
                               (format t "MISMATCH plan=~A refund=~D o=~X c=~X n=~X cold=~D: native {~D ~D} lean {~D ~D}~%"
                                       plan refund o c n cold nc nr cost new-refund))))))))))
    (format t "sstore-gas audit: ~D vectors, ~D mismatches~%" total bad)
    (eita.test:finish :code (if (zerop bad) 0 1))))

(main)
