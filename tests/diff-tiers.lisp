;;;; tests/diff-tiers.lisp — the differential mode (EITA_DIFF_TIERS, interp.lisp diff-run-tiers)
;;;; must not diverge against itself.
;;;;
;;;; The differential runs a tx's top frame on tier A, restores the pre-state, runs it on tier B
;;;; and compares. With both tiers the bytecode interpreter, every comparison must agree; a
;;;; divergence is a hole in the restore, which would also show up as a false TIERDIFF (or a
;;;; wrong kept result) against the JIT. The restore missed two things (2026-11-06): tier A's
;;;; memory arena was left dirty, so tier B's memory expansion read tier A's bytes instead of
;;;; zeros, and tier A's logs and transfers stayed in the tx's event buffer (16 divergences and
;;;; 11 receipt mismatches in 30 mainnet blocks).
;;;; Run: (eita.test:run-all :only '("diff-tiers")).

(defpackage #:eita.test.diff-tiers (:use #:cl))
(in-package #:eita.test.diff-tiers)

(defparameter *ok* t)

(let ((root (eita.test::fixtures-dir)))
  (dolist (sub '("bcExample/" "bcStateTests/"))
    (let* ((dir (concatenate 'string root sub))
           (eita.evm::*force-interp* t)
           (eita.evm::*diff-tiers* t)
           (eita.evm::*diff-every* 1)
           (eita.evm::*diff-stats* (list :txs 0 :checked 0 :divergences 0))
           (out (with-output-to-string (*standard-output*)
                  (let ((*error-output* *standard-output*)) (eita.fixtures:main (list dir)))))
           (line (find-if (lambda (l) (eql 0 (search "summary:" l)))
                          (uiop:split-string out :separator '(#\Newline))))
           (st eita.evm::*diff-stats*)
           (pass (and line (search " fail=0 " line) (not (search "pass=0 " line))
                      (plusp (or (getf st :checked) (getf st :txs))) (zerop (getf st :divergences)))))
      (format t "  ~A: ~A; differential ~S~%" sub line st)
      (unless pass
        (setf *ok* nil)
        (dolist (l (uiop:split-string out :separator '(#\Newline)))
          (when (search "TIERDIFF" l)
            (format t "    ~A~%" (subseq l 0 (min 200 (length l))))))))))

(eita.test:finish :code (if *ok* 0 1))
