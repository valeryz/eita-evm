;;;; tests/native-storage-hooks.lisp — observers see SLOAD/SSTORE exactly as the deleted Lisp
;;;; effect path showed them (docs/native-storage.md, owner note 6 step 5 and addendum 2).
;;;;
;;;; Each fixture directory runs twice under an observer: without and with the watch filter
;;;; (tier (b): the accounts the first run changed most, *storage-access-hook* on each of their
;;;; SLOADs/SSTOREs). Then:
;;;;   - both runs produce the same rows (hooks observe, never perturb): every tx's net storage
;;;;     changes (do-storage-changes: the native first-touch log, tier (a)) and account changes;
;;;;   - the rows, the watched accesses and the summary hash to the digest recorded from the
;;;;     Lisp effect path (step 5's hook mode, rel-ns5, before it was deleted): +reference+;
;;;;   - the native SLOADs/SSTOREs ran (eita_sh_g's counters move).
;;;; Run: (eita.test:run-all :only '("native-storage-hooks")).

(defpackage #:eita.test.native-storage-hooks (:use #:cl))
(in-package #:eita.test.native-storage-hooks)

(defparameter *ok* t)
(defvar *rows*)

(defparameter +reference+
  ;; (directory rows accesses digest), recorded from the Lisp path at e7fcd13 (*native-storage* nil)
  '(("bcStateTests/" 12301 6128 "36135509b72cbb1d")
    ("bcExample/" 162 40 "2e1f450cd773cb2c")))

(defun observed-run (dir watch)
  "The rows of DIR's fixtures: (values storage/account rows, watched-access rows, summary)."
  (let* ((*rows* '()) (accesses '())
         (eita.evm::*force-interp* t)
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

(defun digest (&rest parts)
  "FNV-1a 64 over the standard printing of PARTS, as 16 hex digits."
  (let ((h #xcbf29ce484222325))
    (loop for c across (with-standard-io-syntax (let ((*print-readably* nil)) (prin1-to-string parts)))
          do (setf h (ldb (byte 64 0) (* (logxor h (char-code c)) #x100000001b3))))
    (format nil "~(~16,'0X~)" h)))

(defun counters ()
  (let ((h (cffi:foreign-symbol-pointer "eita_sh_g")))
    (+ (cffi:mem-ref h :uint64 40) (cffi:mem-ref h :uint64 64))))

(defun busiest (rows n)
  "The N accounts with the most storage rows."
  (let ((count (make-hash-table)))
    (dolist (r rows) (when (eq (first r) :storage) (incf (gethash (fourth r) count 0))))
    (let ((all '())) (maphash (lambda (a c) (push (cons a c) all)) count)
      (mapcar #'car (subseq (sort all #'> :key #'cdr) 0 (min n (length all)))))))

(let ((root (eita.test::fixtures-dir)))
  (dolist (ref +reference+)
    (destructuring-bind (sub n-rows n-acc want) ref
      (let* ((dir (concatenate 'string root sub)) (c0 (counters)))
        (multiple-value-bind (rows0 acc0 line0) (observed-run dir '())
          (declare (ignore acc0))
          (let ((watch (busiest rows0 8)))
            (multiple-value-bind (rows acc line) (observed-run dir watch)
              (let* ((got (digest rows acc line)) (ran (- (counters) c0))
                     (pass (and (equal rows0 rows) (equal line0 line) (search " fail=0 " line)
                                (= n-rows (length rows)) (= n-acc (length acc)) (string= want got)
                                (plusp ran) (plusp (length acc)))))
                (format t "  ~A: ~D rows, ~D watched accesses (~D accounts), digest ~A (reference ~A), ~D SLOAD/SSTOREs; ~A~%"
                        sub (length rows) (length acc) (length watch) got want ran (if pass "PASS" "FAIL"))
                (unless (equal rows0 rows)
                  (let ((i (mismatch rows0 rows :test #'equal)))
                    (format t "    the watch changed the rows: first difference at ~A: ~S vs ~S~%" i
                            (and i (nth i rows0)) (and i (nth i rows)))))
                (unless pass (setf *ok* nil))))))))))

(eita.test:finish :code (if *ok* 0 1))
