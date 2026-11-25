;;;; tests/p256verify.lisp — P256VERIFY at 0x100 per rule set, on canonical Base inputs.
;;;;
;;;; Regression: OP-Stack Fjord..Isthmus has RIP-7212 at 0x100 for 3450 gas
;;;; (Evm.Optimism.Fjord.Spec.p256VerifyGas). The replay once treated 0x100 as an empty
;;;; account there (only Osaka+ or Arc enabled it), so passkey wallets fell back to an
;;;; in-EVM verifier (MODEXP) and their ERC-4337 validation ran out of gas: Base 33554432
;;;; tx 203, 37748736 tx 86, 45088768 tx 236 failed where the chain succeeded. The inputs
;;;; below are those txs' 0x100 calls (debug_traceTransaction callTracer: output 1, 3450 gas).

(in-package #:eita.evm)

(defparameter *base-p256-inputs*
  '(;; Base 33554432 tx 203
    "032863bc9bc69fa311ab0f532a4a1a00d53080b42d249de8647a5ad7c012a46d68af4c313bcfdf538d4e0f0d27da604e7d4bbff7227b061540171ea64a78f35262a2f530cd9781d78769ba30b571165310f472a3a33d12823f64fb6af9b87731b91548a7471175c93715b4f4c51157f2ff4b6a410033a5f1e74a3d85a0f2b1fbea2f9d0852046f31ad80fb758237d02e2643cb0b657c5fa7535c95595b0dd184"
    ;; Base 45088768 tx 236
    "283fcf929fa281c119c65363a7f798c0da2ace33fa4397a7a6b6b679c2bed14bbb80edae42797723ae992a3520069295e73d448911db7688a97546a49a6d5a191aa6cf56dc23598cebfe9ab0e4b87cc3959df632c8f31ccbd2ff82fbc1622536bb1e45ddec2e4d7dca4223dc6c502d7031b6b2ec95170031221a0d57391323965e98a445978d25833642b1c237143ca724516d583054581df2508e32fa3c1fe5"))

(defun p256-run (hex)
  "(values gas output) of 0x100 on HEX's bytes, with a large budget."
  (let* ((n (/ (length hex) 2)) (p (foreign-alloc :uint8 :count n)))
    (dotimes (i n) (setf (mem-aref p :uint8 i) (parse-integer hex :start (* 2 i) :end (+ 2 (* 2 i)) :radix 16)))
    (unwind-protect (run-precompile 256 p n 100000) (foreign-free p))))

(let ((fails 0))
  (flet ((check (label got expected)
           (format t "~&  ~A: ~S~:[  FAIL (expected ~S)~;~*~]~%" label got (equalp got expected) expected)
           (unless (equalp got expected) (incf fails))))
    (let ((one (let ((v (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0))) (setf (aref v 31) 1) v)))
      ;; the rule each OP fork installs (op-block-setup, by timestamp)
      (dolist (c '((1720627201 :rip7212) (1746806401 :rip7212) (1776966883 :rip7212)
                   (1779991200 t) (1710374401 nil)))
        (destructuring-bind (ts want) c
          ;; op-block-setup moves the native table to the block's fork: back to 16 after
          (let ((*p256verify* :unset) (*fork-ord* 16) (*el-fork-ord* *el-fork-ord*)
                (eita.chain.op::*op-fork* 0) (eita.chain::*chain-header-foreign* nil))
            (eita.chain.op::op-block-setup 0 nil ts)
            (check (format nil "OP block at ts ~D: *p256verify*" ts) *p256verify* want))
          (%set-fork 16)))
      ;; Fjord..Jovian: a precompile at the Cancun / Prague tables, 3450 gas
      (let ((*p256verify* :rip7212) (*fork-ord* 16))
        (check "Fjord..Isthmus: 0x100 is a precompile" (precompile-address-p 256) t)
        (check "Fjord..Isthmus: 0x100 is warmed by the tx seed" (and (member 256 (precompile-seed-addrs)) t) t)
        (dolist (hex *base-p256-inputs*)
          (multiple-value-bind (gas out) (p256-run hex)
            (check "Fjord..Isthmus: canonical input -> (3450 1)" (list gas out) (list 3450 one)))))
      ;; EIP-7951 (Osaka, Arc, OP Azul): 6900
      (let ((*p256verify* t) (*fork-ord* 16))
        (multiple-value-bind (gas out) (p256-run (first *base-p256-inputs*))
          (check "EIP-7951: canonical input -> (6900 1)" (list gas out) (list 6900 one))))
      ;; pre-Fjord Cancun: an ordinary account
      (let ((*p256verify* nil) (*fork-ord* 16))
        (check "pre-Fjord / Cancun: 0x100 is not a precompile" (precompile-address-p 256) nil))))
  (format t "~&p256verify: ~:[~D failure(s)~;all checks pass~]~%" (zerop fails) fails)
  (eita.test:finish :code (if (zerop fails) 0 1)))
