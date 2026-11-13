;;;; tests/readset.lisp — the read-set recorder (evm/readset.lisp, docs/readset-format.md), and
;;;; observers see, never steer:
;;;;   1. the segments decode to exactly the per-tx sets of the read stream they were fed (accounts
;;;;      with the fields read and the written bit, code by hash, slots with the written bit,
;;;;      block hashes), recomputed here independently from the raw events;
;;;;   2. every account and slot a block's txs changed (the observer's net diffs, an independent
;;;;      path: pre-images and the first-touch log) is in that block's recorded set, written;
;;;;   3. the runner's output (every verdict, gas, receipts root, bloom) is byte-identical with no
;;;;      observer and no read stream, and with an observer that walks every summary the seam
;;;;      offers (net diffs with code hashes, call frames, committed transfers and logs) and the
;;;;      read stream on.
;;;; Inputs: Eita's mainnet repro block (tests/data/mainnet-24538111.json.gz, 300+ real txs),
;;;; and for 3 also ValidBlocks/bcStateTests when a checkout is present (eita.test::fixtures-dir).

(defpackage #:eita.test.readset (:use #:cl #:eita.evm))
(in-package #:eita.test.readset)

(defvar *changed* (make-hash-table :test 'equal) "block -> list of (:acct addr) / (:slot addr slot)")
(defvar *seen* 0 "Summary items the observer read (it must have been active).")

(defun reading-observer ()
  "An observer that walks everything tx-end exposes, as a data writer would."
  (make-observer
   :name "readset-test"
   :tx-end (lambda (block tx success)
             (declare (ignore tx))
             (eita.evm::do-account-changes (a n0 n1 b0 b1 h0 h1)
               (incf *seen*) (list n0 n1 b0 b1 h0 h1) (push (list :acct a) (gethash block *changed*)))
             (eita.evm::do-storage-changes (a s pre post)
               (incf *seen*) (list pre post) (push (list :slot a s) (gethash block *changed*)))
             (eita.evm::do-call-frames (f p d k from to v sel il g gu st)
               (incf *seen*) (list f p d k from to v sel il g gu st))
             (when success
               (eita.evm::do-tx-events (:transfer (k d from to v) :log (i a topics data))
                 (:transfer (incf *seen*) (list k d from to v))
                 (:log (incf *seen*) (list i a topics data)))))))

(defun run-fixtures (paths on)
  "The runner over PATHS; ON: the reading observer and the read stream; (values output events)."
  (let* ((eita.state:*observer* (and on (reading-observer)))
         (eita.evm::*observe-calls* on)
         (eita.evm::*capture-reads* on)
         (eita.evm::*fw-batch* (eita.evm::make-fw-batch 4096))
         (fns '(eita.evm::run-evm-tx eita.chain::run-pre-block! eita.chain::run-post-block!))
         (origs (mapcar #'fdefinition fns))
         (out (unwind-protect
                   (flet ((tag (name block-of tx-of)        ; (block, tx) tags, as the driver sets them
                            (let ((orig (fdefinition name)))
                              (setf (fdefinition name)
                                    (lambda (&rest args)
                                      (setf eita.evm:*cur-block* (funcall block-of args) eita.evm:*cur-tx* (funcall tx-of args))
                                      (apply orig args))))))
                     (tag 'eita.evm::run-evm-tx #'fifth #'sixth)
                     (tag 'eita.chain::run-pre-block! #'second (constantly eita.chain::+preblock-tx+))
                     (tag 'eita.chain::run-post-block! #'second (constantly eita.chain::+postblock-tx+))
                     (with-output-to-string (*standard-output*) (eita.fixtures:main paths)))
                (mapc (lambda (f o) (setf (fdefinition f) o)) fns origs)))
         (b eita.evm::*fw-batch*) (v (eita.evm::fw-batch-vec b)))
    (values (format nil "~{~A~^~%~}" (remove-if (lambda (l) (eql 0 (search "jit: " l)))
                                                (uiop:split-string out :separator '(#\Newline))))
            (loop for i from 0 below (eita.evm::fw-batch-fill b) by 2
                  when (eql (svref v i) eita.evm::+fw-event+) collect (svref v (1+ i))))))

(defun code-hash (code) (let ((h 0)) (loop for x across (eita.core:keccak256-bytes code) do (setf h (logior (ash h 8) x))) h))

(defun expected (events)
  "(block tx) -> (accounts slots blockhashes), each a sorted list, from the raw events."
  (let ((txs (make-hash-table :test 'equal)))
    (dolist (ev events)
      (when (member (car ev) '(:read :write :delta))
        (destructuring-bind (kind block tx addr key value &rest more) (cdr ev)
          (declare (ignore more))
          (let ((e (or (gethash (list block tx) txs)
                       (setf (gethash (list block tx) txs)
                             (list (make-hash-table) (make-hash-table) (make-hash-table :test 'equal) '())))))
            (destructuring-bind (masks codes slots bh) e
              (flet ((acct (bits) (setf (gethash addr masks) (logior bits (gethash addr masks 0)))))
                (cond ((and (eq (car ev) :read) (eq kind :blockhash)) (setf (fourth e) (adjoin key bh)))
                      ((eq kind :storage)
                       (acct 0)
                       (setf (gethash (list addr key) slots)
                             (or (gethash (list addr key) slots) (not (eq (car ev) :read)))))
                      ((eq (car ev) :read)
                       (acct (ecase kind (:balance 1) (:nonce 2) (:code 4) (:codehash 8) (:present 16)))
                       (when (and (eq kind :code) (not (gethash addr codes))) (setf (gethash addr codes) (code-hash value))))
                      (t (acct 128)))))))))
    (let ((out (make-hash-table :test 'equal)))
      (maphash (lambda (k e)
                 (destructuring-bind (masks codes slots bh) e
                   (setf (gethash k out)
                         (list (sort (loop for a being the hash-keys of masks using (hash-value m)
                                           collect (list a m (and (logtest m 4) (gethash a codes))))
                                     #'< :key #'first)
                               (sort (loop for s being the hash-keys of slots using (hash-value w)
                                           collect (list (first s) (second s) w))
                                     (lambda (x y) (or (< (first x) (first y)) (and (= (first x) (first y)) (< (second x) (second y))))))
                               (sort (copy-list bh) #'<)))))
               txs)
      out)))

(defun gunzip-to-temp (gz)
  (let ((out (format nil "/tmp/eita-test-readset-~D.json" (sb-posix:getpid))))
    (with-open-file (s out :direction :output :if-exists :supersede)
      (sb-ext:run-program "gzip" (list "-dc" gz) :search t :output s :error nil))
    out))

(let* ((mainnet (gunzip-to-temp (eita.test::home "tests/data/mainnet-24538111.json.gz")))
       (more (let ((d (eita.test::fixtures-dir))) (and d (list (concatenate 'string d "bcStateTests/")))))
       (dir (format nil "/tmp/eita-test-readset-~D/" (sb-posix:getpid)))
       (fails 0) (ntx 0) (nkeys 0))
  (flet ((fail (fmt &rest args) (incf fails) (format t "  FAIL: ~?~%" fmt args)))
    (unwind-protect
         (let* ((off (run-fixtures (cons mainnet more) nil))
                (on (progn (setf *seen* 0) (run-fixtures (cons mainnet more) t)))
                (summary (find-if (lambda (l) (eql 0 (search "summary:" l))) (uiop:split-string off :separator '(#\Newline)))))
           ;; 3. observers and the stream do not steer
           (format t "  off: ~A~%  observer read ~D summary items~%" summary *seen*)
           (unless (string= off on)
             (fail "the runner's output differs with the observer and the read stream on; first differing lines:")
             (loop for x in (uiop:split-string off :separator '(#\Newline))
                   for y in (uiop:split-string on :separator '(#\Newline)) with shown = 0
                   unless (or (string= x y) (>= shown 10))
                     do (incf shown) (format t "    off: ~A~%    on:  ~A~%" x y)))
           (unless (and summary (search " fail=0 " summary) (not (search "pass=0 " summary)))
             (fail "the runs must pass:~%~A" off))
           (unless (plusp *seen*) (fail "the observer saw nothing (not installed?)"))
           ;; the recorder, fed the mainnet block's events as its subscriber thread would be
           (clrhash *changed*)
           (let ((events (nth-value 1 (run-fixtures (list mainnet) t))))
             (multiple-value-bind (on-event finish) (eita.evm::make-readset-recorder dir)
               (mapc on-event events) (funcall finish))
             (let ((want (expected events)) (got (make-hash-table :test 'equal)))
               (dolist (p (directory (concatenate 'string dir "*.rset")))
                 (dolist (blk (nth-value 2 (eita.evm::readset-read-segment p)))
                   (dolist (tx (cdr blk))
                     (destructuring-bind (idx accts slots bh) tx
                       (incf ntx) (incf nkeys (+ (length accts) (length slots)))
                       (setf (gethash (list (car blk) idx) got)
                             (list (sort (copy-list accts) #'< :key #'first)
                                   (sort (copy-list slots) (lambda (x y) (or (< (first x) (first y)) (and (= (first x) (first y)) (< (second x) (second y))))))
                                   (sort (copy-list bh) #'<)))))))
               ;; 1. decoded = recomputed, tx by tx
               (unless (= (hash-table-count want) (hash-table-count got))
                 (fail "~D txs in the stream, ~D recorded" (hash-table-count want) (hash-table-count got)))
               (maphash (lambda (k w) (unless (equal w (gethash k got)) (fail "tx ~S: recorded ~S~%   stream ~S" k (gethash k got) w)))
                        want)
               (unless (> ntx 300) (fail "only ~D txs recorded" ntx))
               ;; 2. every net change of a block is in its recorded set, written
               (maphash (lambda (block changes)
                          (let ((accts (make-hash-table)) (slots (make-hash-table :test 'equal)))
                            (maphash (lambda (k e)
                                       (when (eql (first k) block)
                                         (dolist (a (first e)) (setf (gethash (first a) accts) (logior (second a) (gethash (first a) accts 0))))
                                         (dolist (s (second e)) (when (third s) (setf (gethash (list (first s) (second s)) slots) t)))))
                                     got)
                            (dolist (c changes)
                              (ecase (first c)
                                (:acct (unless (logtest 128 (gethash (second c) accts 0)) (fail "block ~D: changed account ~X not recorded as written" block (second c))))
                                (:slot (unless (gethash (rest c) slots) (fail "block ~D: changed slot ~X/~X not recorded as written" block (second c) (third c))))))))
                        *changed*)
               (format t "  ~D txs, ~D account/slot entries, ~D net changes covered; ~D bytes of segments~%"
                       ntx nkeys (loop for c being the hash-values of *changed* sum (length c))
                       (loop for p in (directory (concatenate 'string dir "*.rset")) sum (with-open-file (s p) (file-length s)))))))
      (delete-file mainnet)
      (sb-ext:run-program "rm" (list "-rf" dir) :search t)))
  (format t "~&readset: ~:[FAIL~;the segments are the stream's per-tx read sets, every change covered; results identical with and without observer and stream~]~%" (zerop fails))
  (eita.test:finish :code (if (zerop fails) 0 1)))
