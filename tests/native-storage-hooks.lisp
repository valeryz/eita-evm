;;;; tests/native-storage-hooks.lisp — the native storage path's hook tiers (docs/native-storage.md,
;;;; owner note 6 step 5) give observers exactly what the Lisp path gives them.
;;;;
;;;; Each fixture directory runs twice under an observer, with the native SLOAD/SSTORE path on
;;;; and off (*native-storage*: off is the hook mode, tier (c): the vtable's slots are the Lisp
;;;; callbacks). Both runs must produce the same rows, in the same order:
;;;;   (a) every tx's net storage changes (do-storage-changes: the first-touch log the native
;;;;       hits and the Lisp path share), and its account changes;
;;;;   (b) every SLOAD/SSTORE of the watched accounts (*storage-access-hook*), the watch set
;;;;       being the accounts the first run changed most.
;;;; And the native path must have run (its hit counters move). Run:
;;;; (eita.test:run-all :only '("native-storage-hooks")).

(defpackage #:eita.test.native-storage-hooks (:use #:cl))
(in-package #:eita.test.native-storage-hooks)

(defparameter *ok* t)
(defvar *rows*)
(defparameter *hits* 0 "Native hits in the native runs, over every directory.")

(defun observed-run (dir native watch)
  "The rows of DIR's fixtures: (values storage/account rows, watched-access rows, summary)."
  (let* ((*rows* '()) (accesses '())
         (eita.evm::*force-interp* t)
         (eita.evm::*native-storage* native)
         (eita.evm::*storage-access-hook*
           (lambda (op a slot v) (push (list op a slot v) accesses)))
         (eita.state:*observer*
           (eita.evm::make-observer
            :name "native-storage-hooks"
            :tx-end (lambda (block tx success)
                      (eita.evm::do-storage-changes (a s pre post)
                        (push (list :storage block tx a s pre post) *rows*))
                      (eita.evm::do-account-changes (a n0 n1 b0 b1 h0 h1)
                        (push (list :account block tx a n0 n1 b0 b1 h0 h1) *rows*))
                      (push (list :tx block tx success) *rows*)))))
    (eita.evm::storage-watch-clear!)
    (dolist (a watch) (eita.evm::storage-watch! a))
    (let* ((out (with-output-to-string (*standard-output*)
                  (let ((*error-output* *standard-output*)) (eita.fixtures:main (list dir)))))
           (line (find-if (lambda (l) (eql 0 (search "summary:" l)))
                          (uiop:split-string out :separator '(#\Newline)))))
      (eita.evm::storage-watch-clear!)
      (values (reverse *rows*) (reverse accesses) line))))

(defun native-hits ()
  (let ((h (cffi:foreign-symbol-pointer "eita_sh_g")))
    (+ (cffi:mem-ref h :uint64 40) (cffi:mem-ref h :uint64 64))))

(defun busiest (rows n)
  "The N accounts with the most storage rows."
  (let ((count (make-hash-table)))
    (dolist (r rows) (when (eq (first r) :storage) (incf (gethash (fourth r) count 0))))
    (let ((all '())) (maphash (lambda (a c) (push (cons a c) all)) count)
      (mapcar #'car (subseq (sort all #'> :key #'cdr) 0 (min n (length all)))))))

(let ((root (eita.test::fixtures-dir)))
  (dolist (sub '("bcStateTests/" "bcExample/"))
    (let* ((dir (concatenate 'string root sub)) (h0 (native-hits)))
      (multiple-value-bind (rows-ref acc0 line-ref) (observed-run dir nil '())
        (declare (ignore acc0))
        (let ((watch (busiest rows-ref 8)))
          (multiple-value-bind (rows-ref2 acc-ref) (observed-run dir nil watch)
            (let ((h1 (native-hits)))
              (multiple-value-bind (rows-nat acc-nat line-nat) (observed-run dir t watch)
                (let ((hits (- (native-hits) h1))
                      (pass (and (equal rows-ref rows-ref2) (equal rows-ref rows-nat) (equal acc-ref acc-nat)
                                 (equal line-ref line-nat) (search " fail=0 " line-nat))))
                  (format t "  ~A: ~D rows, ~D watched accesses (~D accounts), native hits ~D (reference runs ~D); ~A~%"
                          sub (length rows-nat) (length acc-nat) (length watch) hits (- h1 h0)
                          (if pass "identical" "DIFFERENT"))
                  (incf *hits* hits)
                  (unless (and pass (zerop (- h1 h0)) (plusp (length acc-nat)))
                    (setf *ok* nil)
                    (unless (equal rows-ref rows-nat)
                      (let ((i (mismatch rows-ref rows-nat :test #'equal)))
                        (format t "    first row difference at ~A: ~S vs ~S~%" i
                                (and i (nth i rows-ref)) (and i (nth i rows-nat)))))))))))))))

(format t "  native hits over the native runs: ~D~%" *hits*)
(unless (plusp *hits*) (setf *ok* nil))
(eita.test:finish :code (if *ok* 0 1))
