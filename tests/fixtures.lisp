;;;; tests/fixtures.lisp — a BlockchainTests sample on both tiers (the full battery:
;;;; docs/testing.md). ValidBlocks/bcExample and bcStateTests from EITA_TEST_FIXTURES (a
;;;; ValidBlocks directory), on the threaded interpreter and, with the emitJIT daemon, the JIT.

(defpackage #:eita.test.fixtures (:use #:cl))
(in-package #:eita.test.fixtures)

(defun run-tier (dir interp)
  "Run the fixture runner over DIR; its summary line."
  (let* ((eita.evm::*force-interp* interp)
         (out (with-output-to-string (*standard-output*) (eita.fixtures:main (list dir))))
         (line (find-if (lambda (l) (eql 0 (search "summary:" l)))
                        (uiop:split-string out :separator '(#\Newline)))))
    (format t "  ~A ~:[jit~;interp~]: ~A~%" (car (last (pathname-directory dir))) interp line)
    (unless (and line (search " fail=0 " line) (not (search "pass=0 " line)))
      (format t "~A~%" out))
    (and line (search " fail=0 " line) (not (search "pass=0 " line)))))

(let ((ok t) (root (eita.test::fixtures-dir)))
  (dolist (sub '("bcExample/" "bcStateTests/"))
    (let ((dir (concatenate 'string root sub)))
      (unless (run-tier dir t) (setf ok nil))
      (when (probe-file (eita.native:emit-jit-path))
        (unless (run-tier dir nil) (setf ok nil)))))
  (eita.test:finish :code (if ok 0 1)))
