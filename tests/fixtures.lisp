;;;; tests/fixtures.lisp — a BlockchainTests sample (the full battery: docs/testing.md).
;;;; ValidBlocks/bcExample and bcStateTests from EITA_TEST_FIXTURES (a ValidBlocks
;;;; directory), on the threaded interpreter.

(defpackage #:eita.test.fixtures (:use #:cl))
(in-package #:eita.test.fixtures)

(defun run-dir (dir)
  "Run the fixture runner over DIR; true when it passed with no failure."
  (let* ((out (with-output-to-string (*standard-output*) (eita.fixtures:main (list dir))))
         (line (find-if (lambda (l) (eql 0 (search "summary:" l)))
                        (uiop:split-string out :separator '(#\Newline))))
         (ok (and line (search " fail=0 " line) (not (search "pass=0 " line)))))
    (format t "  ~A: ~A~%" (car (last (pathname-directory dir))) line)
    (unless ok (format t "~A~%" out))
    ok))

(let ((ok t) (root (eita.test::fixtures-dir)))
  (dolist (sub '("bcExample/" "bcStateTests/"))
    (unless (run-dir (concatenate 'string root sub)) (setf ok nil)))
  (eita.test:finish :code (if ok 0 1)))
