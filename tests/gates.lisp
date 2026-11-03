;;;; tests/gates.lisp — the Lean gates (EITA_TEST_GATES=1): the emitted artifacts against the
;;;; Lean emitters, the axiom closure, the refinement-coverage ratchet (docs/testing.md).

(defpackage #:eita.test.gates (:use #:cl))
(in-package #:eita.test.gates)

(let ((ok t))
  (dolist (g '("verify-host-emit.sh" "verify-axioms.sh" "verify-coverage.sh"))
    (let ((p (sb-ext:run-program "/bin/bash" (list (eita.test::home (concatenate 'string "scripts/" g)))
                                 :output *standard-output* :error *standard-output*)))
      (format t "  ~A: exit ~D~%" g (sb-ext:process-exit-code p))
      (unless (zerop (sb-ext:process-exit-code p)) (setf ok nil))))
  (eita.test:finish :code (if ok 0 1)))
