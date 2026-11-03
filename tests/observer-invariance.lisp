;;;; tests/observer-invariance.lisp — observers see, never steer: the same blocks run with no
;;;; observer and with one that reads every touched-state summary the seam offers (net account
;;;; and storage changes with code hashes, call frames, committed transfers and logs) must give
;;;; byte-identical runner output — every per-test verdict, gas, receipts root and bloom.
;;;;
;;;; Inputs: Eita's mainnet repro block (tests/data/mainnet-24538111.json.gz, 300+ real txs;
;;;; receipts root, gasUsed and bloom checked) and ValidBlocks/bcStateTests when a checkout is
;;;; present (eita.test::fixtures-dir).

(defpackage #:eita.test.observer-invariance (:use #:cl #:eita.evm))
(in-package #:eita.test.observer-invariance)

(defvar *seen* 0 "Summary items the observer read (it must have been active).")

(defun reading-observer ()
  "An observer that walks everything tx-end exposes, as a data writer would."
  (make-observer
   :name "invariance-probe"
   :tx-end (lambda (block tx success)
             (declare (ignore block tx))
             (eita.evm::do-account-changes (a n0 n1 b0 b1 h0 h1) (incf *seen*) (list a n0 n1 b0 b1 h0 h1))
             (eita.evm::do-storage-changes (a s pre post) (incf *seen*) (list a s pre post))
             (eita.evm::do-call-frames (f p d k from to v sel il g gu st)
               (incf *seen*) (list f p d k from to v sel il g gu st))
             (when success
               (eita.evm::do-tx-events (:transfer (k d from to v) :log (i a topics data))
                 (:transfer (incf *seen*) (list k d from to v))
                 (:log (incf *seen*) (list i a topics data)))))))

(defun run-fixtures (paths observer)
  "The fixture runner over PATHS with OBSERVER installed (NIL: none); its output, less the
   image's cumulative JIT counters (`jit: …`, a statistic of the process, not a result)."
  (let* ((eita.state:*observer* observer)
         (eita.evm::*observe-calls* (and observer t))
         (out (with-output-to-string (*standard-output*) (eita.fixtures:main paths))))
    (format nil "~{~A~^~%~}" (remove-if (lambda (l) (eql 0 (search "jit: " l)))
                                        (uiop:split-string out :separator '(#\Newline))))))

(defun gunzip-to-temp (gz)
  (let ((out (format nil "/tmp/eita-test-obsinv-~D-~A.json" (sb-posix:getpid) (pathname-name (pathname-name gz)))))
    (with-open-file (s out :direction :output :if-exists :supersede)
      (sb-ext:run-program "gzip" (list "-dc" gz) :search t :output s :error nil))
    out))

(let* ((mainnet (gunzip-to-temp (eita.test::home "tests/data/mainnet-24538111.json.gz")))
       (paths (append (list mainnet)
                      (let ((d (eita.test::fixtures-dir))) (and d (list (concatenate 'string d "bcStateTests/"))))))
       (ok t))
  (unwind-protect
       (let* ((off (run-fixtures paths nil))
              (on (progn (setf *seen* 0) (run-fixtures paths (reading-observer))))
              (summary (find-if (lambda (l) (eql 0 (search "summary:" l))) (uiop:split-string off :separator '(#\Newline)))))
         (format t "  observer off: ~A~%  observer read ~D summary items~%" summary *seen*)
         (unless (string= off on)
           (setf ok nil)
           (let ((a (uiop:split-string off :separator '(#\Newline)))
                 (b (uiop:split-string on :separator '(#\Newline))))
             (format t "  FAIL: output differs with the observer on; first differing lines:~%")
             (loop for x in a for y in b for k from 0 with shown = 0
                   unless (or (string= x y) (>= shown 10))
                     do (incf shown) (format t "    off: ~A~%    on:  ~A~%" x y))))
         (unless (and summary (search " fail=0 " summary) (not (search "pass=0 " summary)))
           (setf ok nil) (format t "  FAIL: the runs must pass~%~A~%" off))
         (unless (plusp *seen*)
           (setf ok nil) (format t "  FAIL: the observer saw nothing (not installed?)~%")))
    (delete-file mainnet))
  (format t "~&observer-invariance: ~:[FAIL~;results identical with and without the observer~]~%" ok)
  (eita.test:finish :code (if ok 0 1)))
