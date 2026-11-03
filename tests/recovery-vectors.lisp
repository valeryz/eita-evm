;;;; recovery-vectors.lisp — the P1 refinement check: src/state/recovery.lisp decides
;;;; exactly what the proved Lean definitions decide (lean/Evm/Persist/Recovery.lean).
;;;;
;;;;   (cd lean && lake exe recoveryVectors) > /tmp/rv.txt
;;;; Run: (eita.test:run-all :only '("recovery-vectors")), or (asdf:test-system "eita") for all suites.
;;;;
;;;; Each line is ((anchors) (dumps) resume (gc)), or for layered files (Part D of
;;;; lean/Evm/Persist/Layered.lean) (:layered (anchors) (files) (points) resume (gcfiles));
;;;; exits 1 if any differs.

(let ((n 0) (bad 0))
  (with-open-file (in eita.test:*argument*)
    (loop for line = (read-line in nil nil) while line
          do (let* ((form (let ((*read-eval* nil) (*package* (find-package :cl-user)))
                            (read-from-string line)))
                    (layered (eq (first form) :layered)))
               (destructuring-bind (anchors dumps resume gc &optional gcf)
                   (if layered (cdr form) form)
                 (let* ((anchors (mapcar (lambda (a) (list (first a) (second a) nil)) anchors))
                        (r (if layered
                               (eita.state.recovery:resume-point anchors (eita.state.recovery:dumps-of dumps resume))
                               (eita.state.recovery:resume-point anchors dumps)))
                        (g (if layered
                               (eita.state.recovery:gc-files anchors dumps resume)
                               (eita.state.recovery:gc-set anchors dumps))))
                   ;; layered: DUMPS is the files, RESUME the points, GC the resume, GCF the gc
                   (incf n)
                   (unless (if layered
                               (and (eql r gc) (equal g gcf))
                               (and (eql r resume) (equal g gc)))
                     (incf bad)
                     (when (<= bad 5)
                       (format t "MISMATCH ~A~%  lisp: ~S ~S~%" line r g))))))))
  (format t "~D vectors, ~D mismatches~%" n bad)
  (eita.test:finish :code (if (zerop bad) 0 1)))
