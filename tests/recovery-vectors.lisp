;;;; recovery-vectors.lisp — the P1 refinement check: src/state/recovery.lisp decides
;;;; exactly what the proved Lean definitions decide (lean/Evm/Persist/Recovery.lean).
;;;;
;;;;   (cd lean && lake exe recoveryVectors) > /tmp/rv.txt
;;;; Run: (eita.test:run-all :only '("recovery-vectors")), or (asdf:test-system "eita") for all suites.
;;;;
;;;; Each line is ((anchors) (dumps) resume (gc)), or for layered files (Part D of
;;;; lean/Evm/Persist/Layered.lean) (:layered (anchors) (files) (points) resume (gcfiles)),
;;;; or for a key-range merge (Part E) (:compose (sources) merged filtered): the sources'
;;;; runs are laid out as snapshot records (a 4-byte key, a 32-byte value) and merged by
;;;; `compose-range`, without and with its tombstone filter; exits 1 if any differs.

(defun compose-vector (sources)
  "`compose-range` over SOURCES (((k v) ...) stop), newest first, as records in memory:
   (values merged filtered)."
  (let* ((bufs (mapcar (lambda (src)
                         (let ((v (make-array (+ 4096 (* 36 (length (first src)))) :element-type '(unsigned-byte 8)
                                                                                   :initial-element 0)))
                           (loop for (k val) in (first src) for i from 0
                                 do (replace v (eita.state.snapshot:int->octets k 4) :start1 (+ 4096 (* 36 i)))
                                    (replace v (eita.state.snapshot:int->octets val 32) :start1 (+ 4096 (* 36 i) 4)))
                           v))
                       sources)))
    (sb-sys:with-pinned-objects (bufs)
      (flet ((merge-all (drop)
               (let ((out '()))
                 (eita.state.snapshot:compose-range
                  (loop for src in sources for v in bufs
                        collect (eita.state.snapshot:make-run (sb-sys:vector-sap v) 0 (length (first src)) 36 4 (second src)))
                  (lambda (sap off) (push (list (eita.state.snapshot:sap-be sap off 4) (eita.state.snapshot:sap-be sap (+ off 4) 32)) out))
                  :drop-zero (and drop 4))
                 (nreverse out))))
        (values (merge-all nil) (merge-all t))))))

(let ((n 0) (bad 0))
  (with-open-file (in eita.test:*argument*)
    (loop for line = (read-line in nil nil) while line
          do (let* ((form (let ((*read-eval* nil) (*package* (find-package :cl-user)))
                            (read-from-string line)))
                    (layered (eq (first form) :layered)))
               (if (eq (first form) :compose)
                   (destructuring-bind (sources merged filtered) (cdr form)
                     (multiple-value-bind (m f) (compose-vector (mapcar (lambda (s) (list (first s) (eq (second s) t))) sources))
                       (incf n)
                       (unless (and (equal m merged) (equal f filtered))
                         (incf bad)
                         (when (<= bad 5) (format t "MISMATCH ~A~%  lisp: ~S ~S~%" line m f)))))
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
                           (format t "MISMATCH ~A~%  lisp: ~S ~S~%" line r g)))))))))
  (format t "~D vectors, ~D mismatches~%" n bad)
  (eita.test:finish :code (if (zerop bad) 0 1)))
