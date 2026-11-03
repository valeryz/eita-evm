;;;; fixtures/api.lisp — the fixture functions of the EITA API (src/eita.lisp).

(in-package #:eita.fixtures)

(defun eita:load-fixture (path &optional test-name)
  "A world holding the pre-state of the BlockchainTest TEST-NAME (default: the first) in the
   fixture file PATH, at the test's fork. Returns (values world test-name network)."
  (let* ((json (jsown:parse (alexandria:read-file-into-string path)))
         (name (or test-name (first (jsown:keywords json))))
         (test (parse-test name (jval json name)))
         (world (make-world)))
    (eita:set-fork (getf test :network))
    (populate-world world (getf test :pre))
    (values world name (getf test :network))))

(defun eita:run-fixture-file (path)
  "Run every BlockchainTest in PATH (a file or a flat directory), as `eita fixtures` does."
  (main (list (namestring path))))
