;;;; tests/factlog-resume.lisp — a resume never drops fact-log rows (src/factlog/writer.lisp).
;;;; A suite of (asdf:test-system "eita"); also loadable on its own in an executable that
;;;; carries the engine (it exits 1 on a failure).
;;;;
;;;; Drives the real encoder (block-begin, row queue, commit, checkpoint, finalize) on
;;;; synthetic rows of the block and tx tables, shards of 10 blocks, log from block 5. Every
;;;; scenario ends with a run to block 39; then the rows on disk must be exactly those of
;;;; blocks 5..39 and every sealed range complete (first-block = lo, except the log's first).
;;;; A run "crashes" by dropping its live shards unsealed. Scenarios, around range 20-29:
;;;;   at-lo         sealed by an older code version; resume at 20 (its first block)
;;;;   at-lo+1       the same, resume at 21: block 20 kept from the sealed range
;;;;   straddle      the same, the sealed range one group (a converted shard): block 20 cut
;;;;                 out of the group and re-encoded
;;;;   retire-crash  the same, and the resuming run dies after retiring the footer (`.was`)
;;;;                 and before keeping the prefix; the next resume at 21 (without the
;;;;                 `.was`, the second run would seal 20-29 without block 20)
;;;;   checkpoint    a run checkpoints at 20 and crashes at 25; resume at 21
;;;;   lo-crash      a run checkpoints at 19 and crashes at 25; resume at 20
;;;;   refuse        a run crashes at 25 with no checkpoint in the range; resume at 21 must
;;;;                 signal (the rows of 20 are nowhere), not open the range without them
;;;;   power-N       catching up (barriers only at layer points and where `committed` moves),
;;;;                 a run checkpoints at 20, moves `committed` at 33 (odd N) and the machine dies
;;;;                 at 37, losing or tearing what was not durable at random (seed N); on that
;;;;                 disk footers and `committed` hold (`check-crashed`); resume at 21
;;;   tip-N/catch-up `committed` at every commit within 8 blocks of the head, else only when due
;;;; Exit 1 on any failure.

(defpackage #:eita.test.factlog-resume
  (:use #:cl)
  (:shadow #:*fails* #:report #:+kinds+ #:rows-of #:crash! #:run! #:check #:scenario #:crash-in-scan-prefix
           #:*version*))
(in-package #:eita.test.factlog-resume)
(eval-when (:compile-toplevel :load-toplevel :execute)
  (dolist (p '(:eita.factlog.writer :eita.evm :eita.chain :eita.input :eita.state :eita.core :eita.native))
    (do-symbols (s p)
      (when (and (eq (symbol-package s) (find-package p)) (not (find-symbol (symbol-name s) *package*)))
        (import s)))))

;; the code version a run writes as (the scenarios change it the way a deploy does)
(defvar *version* "v1")
(sb-int:encapsulate 'engine-code-version 'test (lambda (f) (declare (ignore f)) *version*))

(defvar *fails* 0)
(defun report (ok what &rest args)
  (unless ok (incf *fails*))
  (format t "~&  ~A ~?~%" (if ok "ok  " "FAIL") what args)
  (finish-output))

(defparameter +kinds+ '(:block :tx))
(defun rows-of (kind b)
  "The synthetic rows of block B: one block row; B mod 3 txs (blocks without tx rows too)."
  (ecase kind
    (:block (list (list b (+ 1000 b) #xc0ffee b (* 7 b) 30000000 (* 11 b) nil nil)))
    (:tx (loop for i below (mod b 3) collect (list b i (+ (* 100 b) i) #xaa (and (oddp i) #xbb) 0 2 21000 1 7)))))

(defun crash! ()
  "The process dies: live shards are left as they are on disk, unsealed; what waited is gone."
  (maphash (lambda (k sh) (declare (ignore k)) (ignore-errors (close (factlog-shard-stream sh)))) *factlog-shards*)
  (clrhash *factlog-shards*) (clrhash *factlog-dirty*) (setf *factlog-after-barrier* '()))

(defun committed-on-disk ()
  (ignore-errors (with-open-file (in (merge-pathnames "committed" *factlog-dir*)) (parse-integer (read-line in)))))

(defun run! (version from to &key checkpoint (commit-every 1) crash catch-up marks head seen)
  "Blocks FROM..TO by code VERSION: rows queued, `committed` forced every COMMIT-EVERY blocks
   (a group per commit), a checkpoint after each block of CHECKPOINT; then sealed, or CRASH.
   CATCH-UP (full state): unforced commits flush every block; behind the head they move
   `committed` only at the blocks of MARKS (the 30 s due). HEAD: following, the head is this
   many blocks above each block. SEEN: called with each block and `committed` after it."
  (setf *version* version *factlog-last-committed* nil *full-state* catch-up *tip-freeze* nil
        *chain-head* nil)
  (clrhash *factlog-shards*) (clrhash *factlog-skip*)
  (loop for b from from to to
        do (%factlog-block-begin! b)
           (dolist (kind +kinds+)
             (dolist (row (rows-of kind b))
               (%factlog-queue-row! (position kind eita-factlog:+kinds+) (coerce row 'simple-vector) 0)))
           (when head (setf *chain-head* (+ b head)))
           (cond (catch-up (setf *factlog-flushed-at* most-negative-fixnum
                                 *factlog-committed-at* (if (member b marks) most-negative-fixnum (get-internal-real-time)))
                           (%factlog-commit! b))
                 ((zerop (mod (1+ (- b from)) commit-every)) (%factlog-commit! b :force t))
                 (t (setf *factlog-last-committed* b)))
           (when seen (funcall seen b (committed-on-disk)))
           (when (member b checkpoint) (%factlog-checkpoint! b)))
  (if crash (crash!) (%factlog-finalize!))
  (setf *full-state* nil *chain-head* nil))

;;; The power-loss model: the tree at the last barrier (`%factlog-sync` returned) and now.
(defvar *durable* (make-hash-table :test 'equal) "relative path -> bytes, at the last barrier")
(defun tree ()
  (let ((h (make-hash-table :test 'equal)) (root (length (namestring (truename *factlog-dir*)))))
    (dolist (p (directory (merge-pathnames "**/*.*" *factlog-dir*)) h)
      (when (pathname-name p) (setf (gethash (subseq (namestring p) root) h) (eita-factlog::read-file-bytes p))))))
(sb-int:encapsulate '%factlog-sync 'power (lambda (f) (funcall f) (setf *durable* (tree))))

(defun power-loss! (seed)
  "The machine dies (after `crash!`): every change since the last barrier kept, undone or torn
   past what was durable (not a rename of durable bytes: that is the old name or the new)."
  (let ((now (tree)) (*random-state* (sb-ext:seed-random-state seed)) (synced (make-hash-table :test 'equalp)))
    (maphash (lambda (k v) (setf (gethash v synced) t) (unless (gethash k now) (setf (gethash k now) nil))) *durable*)
    (loop for rel in (sort (loop for k being the hash-keys of now collect k) #'string<)
          for d = (gethash rel *durable*) for c = (gethash rel now) for path = (merge-pathnames rel *factlog-dir*)
          for lo = (if (and d c (<= (length d) (length c)) (equalp d (subseq c 0 (length d)))) (length d) 0)
          for keep = (cond ((equalp c d) c)
                           ((or (null c) (gethash c synced)) (if (zerop (random 2)) d c))
                           (t (case (random 4)
                                (0 d) (1 c) (2 (subseq c 0 (+ lo (random (1+ (- (length c) lo))))))
                                (t (concatenate '(vector (unsigned-byte 8)) (subseq c 0 lo) (make-array (random 64) :initial-element 0))))))
          do (if keep
                 (with-open-file (o (ensure-directories-exist path) :direction :output :element-type '(unsigned-byte 8) :if-exists :supersede)
                   (write-sequence keep o))
                 (when (probe-file path) (delete-file path))))))

(defun check-crashed (name)
  "On the crashed disk every footer describes its rows (P0), and the whole groups hold the rows
   of every block <= `committed`, exactly (I5)."
  (let ((m (ignore-errors (with-open-file (in (merge-pathnames "committed" *factlog-dir*)) (parse-integer (read-line in))))))
    (report m "~A: `committed` is a number after the power loss (~A)" name m)
    (dolist (kind +kinds+)
      (loop for lo from 0 to 30 by 10 for hi = (+ lo 9) for rows = (factlog-shard-file kind lo hi "fct")
            for ft = (eita-factlog:read-footer (factlog-shard-file kind lo hi "sealed")) for got = '()
            do (when ft
                 (report (equal (multiple-value-list (eita-factlog:digest rows)) (list (getf ft :bytes) (getf ft :fnv)))
                         "~A: ~(~A~) ~D-~D footer describes its rows" name kind lo hi))
               (when (and m (<= lo m))
                 (ignore-errors (eita-factlog::map-fct-groups (lambda (cols next) (declare (ignore next))
                                                                (setf got (append got (eita-factlog::columns->rows cols))))
                                                              (eita-factlog::read-file-bytes rows) kind))
                 (let ((got (remove-if (lambda (r) (> (first r) m)) got))
                       (want (loop for b from (max lo 5) to (min hi m) append (rows-of kind b))))
                   (report (equal got want) "~A: ~(~A~) ~D-~D rows of blocks <= ~D (~D of ~D)" name kind lo hi m (length got) (length want))))))))

(defun check (name)
  "Every row of blocks 5..39 on disk, nothing else, every sealed range complete."
  (dolist (kind +kinds+)
    (let ((got '()) (ok t))
      (loop for lo from 0 to 30 by 10 for hi = (+ lo 9)
            for ft = (eita-factlog:read-footer (factlog-shard-file kind lo hi "sealed"))
            do (unless (and ft (eql (getf ft :first-block) (max lo 5)) (eql (getf ft :last-block) hi))
                 (setf ok nil)
                 (format t "~&       ~(~A~) ~D-~D footer: first ~A last ~A~%" kind lo hi (getf ft :first-block) (getf ft :last-block)))
               (setf got (append got (eita-factlog::read-fct-rows (factlog-shard-file kind lo hi "fct") kind))))
      (let ((want (loop for b from 5 to 39 append (rows-of kind b))))
        (report (and ok (equal got want)) "~A: ~(~A~) rows of blocks 5..39 (~D of ~D~@[, missing blocks ~A~])"
                name kind (length got) (length want)
                (let ((m (remove-duplicates (mapcar #'first (set-difference want got :test #'equal)))))
                  (and m (sort m #'<))))))))

(defun scenario (name thunk)
  (let ((dir (format nil "/tmp/eita-test-factlog-resume-~D/~A/" (sb-posix:getpid) name)))
    (ensure-directories-exist dir)
    (setf *factlog-dir* (pathname dir) *factlog-on* t *factlog-shard-blocks* 10 *factlog-kinds* +kinds+)
    (format t "~&~A~%" name)
    (handler-case (progn (funcall thunk) (check name))
      (error (e) (report nil "~A: ~A" name e)))))

(defun crash-in-scan-prefix (thunk)
  "Run THUNK with the first `factlog-scan-prefix` dying (a resume that dies there, on
   a straddling group); the run crashes."
  (sb-int:encapsulate 'factlog-scan-prefix 'crash
                      (lambda (f &rest args)
                        (sb-int:unencapsulate 'factlog-scan-prefix 'crash)
                        (error "simulated death in scan-prefix (~A)" (first args) f)))
  (unwind-protect
       (handler-case (progn (funcall thunk) (error "the run did not die"))
         (simple-error (e) (unless (search "simulated death" (princ-to-string e)) (error e))))
    (sb-int:unencapsulate 'factlog-scan-prefix 'crash))
  (crash!))

(scenario "at-lo" (lambda () (run! "v1" 5 29) (run! "v2" 20 39)))
(scenario "at-lo+1" (lambda () (run! "v1" 5 29) (run! "v2" 21 39)))
(scenario "straddle" (lambda () (run! "v1" 5 29 :commit-every 1000) (run! "v2" 21 39)))
(scenario "retire-crash" (lambda ()
                           (run! "v1" 5 29 :commit-every 1000)
                           (crash-in-scan-prefix (lambda () (run! "v2" 21 39)))
                           (run! "v2" 21 39)))
(scenario "checkpoint" (lambda () (run! "v1" 5 25 :checkpoint '(20) :crash t) (run! "v1" 21 39)))
(scenario "lo-crash" (lambda () (run! "v1" 5 25 :checkpoint '(19) :crash t) (run! "v1" 20 39)))
(let ((name "refuse"))
  (scenario name (lambda ()
                   (run! "v1" 5 25 :checkpoint '(15) :crash t)
                   (let ((e (handler-case (progn (run! "v1" 21 39) nil) (error (e) (princ-to-string e)))))
                     (report (and e (search "would drop the rows of blocks 20..20" e)) "~A: resume at 21 refused (~A)" name (or e "accepted"))
                     (crash!))
                   ;; the way out the error names: resume from a snapshot before the range
                   (run! "v1" 20 39))))

(dotimes (seed 40)
  (let ((name (format nil "power-~D" seed)))
    (scenario name (lambda ()
                     (run! "v1" 5 37 :checkpoint '(20) :catch-up t :marks (and (oddp seed) '(33)) :crash t)
                     (power-loss! seed)
                     (check-crashed name)
                     (run! "v1" 21 39 :catch-up t)))))

;; `committed`'s cadence, full state (the distance to the head decides "at the tip", not the
;; reorg window *tip-freeze*, which is 0 on a chain without reorgs): following the head, 1 or 8
;; blocks above, it moves at every commit; catching up (no head, or 9+ below it) only when due
;; (MARKS: block 30)
(dolist (c '(("tip-1" 1 t) ("tip-8" 8 t) ("catch-up" nil nil) ("catch-up-9" 9 nil)))
  (destructuring-bind (name head every) c
    (scenario name (lambda ()
                     (let ((bad '()))
                       (run! "v1" 5 39 :catch-up t :head head :marks '(30)
                                       :seen (lambda (b m)
                                               (unless (eql m (if every b (and (>= b 30) 30))) (push (list b m) bad))))
                       (report (null bad) "~A: `committed` ~:[only when due~;at every block~] (wrong at ~A)"
                               name every (reverse bad)))))))

(format t "~&~:[ALL PASS~;~:*~D FAILED~]~%" (and (plusp *fails*) *fails*))
;; the engine as the other suites expect it
(sb-int:unencapsulate 'engine-code-version 'test)
(setf *factlog-shard-blocks* 1000 *factlog-kinds* (copy-list eita-factlog:+kinds+) *full-state* nil
      *chain-head* nil *factlog-last-committed* nil)
(clrhash *factlog-shards*) (clrhash *factlog-skip*)
(sb-ext:run-program "rm" (list "-rf" (format nil "/tmp/eita-test-factlog-resume-~D/" (sb-posix:getpid))) :search t)
(let ((code (if (plusp *fails*) 1 0)))     ; a suite of eita/test, or a script of an executable
  (if (find-package :eita.test)
      (uiop:symbol-call :eita.test :finish :code code)
      (sb-ext:exit :code code :abort t)))
