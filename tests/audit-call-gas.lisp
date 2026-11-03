;;;; audit-call-gas.lisp — differential audit of the emitted call-gas
;;;; plan symbols against their Lean oracles:
;;;;   berlin    -> _eita_call_gas           (Berlin callGasPlan)
;;;;   frontier  -> _eita_call_gas_frontier  (Frontier callGasPlan)
;;;;   tangerine -> _eita_call_gas_tangerine (TangerineWhistle callGasPlan)
;;;;
;;;; Vectors come from `lake exe callGasVectors` (one per line:
;;;; plan flags delegated gasArg avail charge forward stipend — the
;;;; last three computed by the Lean definition named by `plan`). The
;;;; native symbol must reproduce all three outputs exactly on every
;;;; vector, including the Nat-subtraction clamp (avail < charge), the
;;;; EIP-150 /64 cap boundaries, u64-max gas arguments, and — for the
;;;; pre-Berlin plans — ignoring exactly the inputs the spec ignores.
;;;;
;;;; Run: (eita.test:run-all :only '("audit-call-gas")), or (asdf:test-system "eita") for all suites.

(defpackage #:eita.test.audit-call-gas (:use #:cl #:cffi))
(in-package :eita.test.audit-call-gas)

(defcfun ("eita_call_gas" %call-gas-berlin) :void
  (out :pointer) (flags :uint64) (delegated :uint64)
  (gas-arg :uint64) (avail :uint64))

(defcfun ("eita_call_gas_frontier" %call-gas-frontier) :void
  (out :pointer) (flags :uint64) (delegated :uint64)
  (gas-arg :uint64) (avail :uint64))

(defcfun ("eita_call_gas_tangerine" %call-gas-tangerine) :void
  (out :pointer) (flags :uint64) (delegated :uint64)
  (gas-arg :uint64) (avail :uint64))

(defun main ()
  (let ((vectors-path (or eita.test:*argument*
                          "/tmp/call_gas_vectors.txt"))
        (total 0) (bad 0))
    (with-foreign-object (out :uint64 3)
      (with-open-file (in vectors-path)
        (loop for line = (read-line in nil)
              while line
              unless (string= line "")
              do (with-input-from-string (s line)
                   (let ((plan (read s))
                         (flags (read s)) (d (read s)) (g (read s)) (a (read s))
                         (charge (read s)) (forward (read s)) (stipend (read s)))
                     (incf total)
                     (ecase plan
                       (berlin    (%call-gas-berlin out flags d g a))
                       (frontier  (%call-gas-frontier out flags d g a))
                       (tangerine (%call-gas-tangerine out flags d g a)))
                     (let ((nc (mem-aref out :uint64 0))
                           (nf (mem-aref out :uint64 1))
                           (ns (mem-aref out :uint64 2)))
                       (unless (and (= nc charge) (= nf forward) (= ns stipend))
                         (incf bad)
                         (format t "MISMATCH plan=~A flags=~D d=~D g=~D a=~D: native {~D ~D ~D} lean {~D ~D ~D}~%"
                                 plan flags d g a nc nf ns charge forward stipend))))))))
    (format t "call-gas audit: ~D vectors, ~D mismatches~%" total bad)
    (eita.test:finish :code (if (zerop bad) 0 1))))

(main)
