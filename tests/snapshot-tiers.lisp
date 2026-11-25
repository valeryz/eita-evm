;;;; tests/snapshot-tiers.lisp — BlockchainTests over a snapshot-backed world, version 1 and
;;;; version 2 (docs/layered-snapshots.md, "A stack over a version 2 base").
;;;;
;;;; Each fixture runs three times on the driver's block pipeline (the fixture runner's
;;;; `run-block-checked`): in RAM, then over a base snapshot of its pre-state in version 1,
;;;; and in version 2: that same base converted (keys hashed, every address field zero, as
;;;; an import from reth leaves them). Over a snapshot every block is a layer (the hot set
;;;; frozen, written by the writer thread) and the block's root is the streaming root of the
;;;; stack (state/root.lisp: base + layers); after the last block the layers are composed
;;;; (minor compaction) and compacted into a base (major), both root-checked. Required: every
;;;; block's root equal across the three tiers and to the header (for an expected failure,
;;;; src/fixtures/expected-failures.txt, to RAM's only: these are the creations over storage),
;;;; the post-state as the fixture says, and the observers' output (each tx's account and
;;;; storage changes, transfers, logs and call frames: the fact log's inputs) identical
;;;; between version 1 and version 2. Then the cost of hashed keys: a mainnet block (300+
;;;; txs, tests/data/mainnet-24538111.json.gz) executed over each tier, best of five.
;;;;
;;;; Run: (eita.test:run-all :only '("snapshot-tiers")) (Istanbul and Cancun variants; about an hour
;;;; on an M-series Mac); one directory of them:
;;;; (eita.test::run-suite "snapshot-tiers" "snapshot-tiers.lisp" :argument (lambda () "ValidBlocks/bcExample/")).
;;;; EITA_TEST_FIXTURES: the ValidBlocks
;;;; directory of a LegacyTests/Cancun/BlockchainTests checkout (its sibling
;;;; GeneralStateTests is read too).

(defpackage #:eita.test.snapshot-tiers (:use #:cl))
(in-package #:eita.test.snapshot-tiers)

(defparameter *dirs*
  '("ValidBlocks/bcStateTests/" "ValidBlocks/bcExample/" "GeneralStateTests/stSStoreTest/"
    "GeneralStateTests/stCreate2/" "GeneralStateTests/stRevertTest/" "GeneralStateTests/stEIP158Specific/"
    "GeneralStateTests/stSystemOperationsTest/" "GeneralStateTests/stExtCodeHash/")
  "Where wipes, creations over storage, reverts, refunds and empty accounts are.")
(defparameter *networks* '("Istanbul" "Cancun")
  "SELFDESTRUCT before and after EIP-6780; the other forks' variants add little here.")

(defvar *dir* (format nil "/tmp/test-snapshot-tiers-~D/" (sb-posix:getpid)))
(defvar *rows* '())
(defvar *exec* 0 "Time in the blocks' execution (`run-block-checked`), internal units.")

(defun hk (addr) (eita.core:keccak256-bytes (eita.state.snapshot:int->octets addr 20)))
(defun hs (slot) (eita.core:keccak256-bytes (eita.state.snapshot:int->octets slot 32)))

(defparameter *observer*
  (eita.evm::make-observer
   :name "snapshot-tiers"
   :tx-end (lambda (block tx success)
             (declare (ignore block))
             (push (list :tx tx success) *rows*)
             (eita.evm::do-account-changes (a n0 n1 b0 b1 h0 h1) (push (list :account a n0 n1 b0 b1 h0 h1) *rows*))
             (eita.evm::do-storage-changes (a s pre post) (push (list :storage a s pre post) *rows*))
             (eita.evm::do-call-frames (frame parent depth kind from to value selector input-len gas gas-used status)
               (push (list :frame frame parent depth kind from to value selector input-len gas gas-used status) *rows*))
             (when success
               (eita.evm::do-tx-events (:transfer (kind depth from to value) :log (index addr topics data))
                 (:transfer (push (list :transfer kind depth from to value) *rows*))
                 (:log (push (list :log index addr topics data) *rows*)))))))

(defun convert-to-v2 (v1 tmp)
  "The version 1 base V1 (open) rewritten as a version 2 base at TMP: keys hashed, records
   in hashed order, every address field zero (unknown, as an import leaves it)."
  (let ((slots (make-hash-table)) (accts '()))
    (eita.state.snapshot:snap-map-storage v1 (lambda (a s v) (push (cons (hs s) v) (gethash a slots))))
    (eita.state.snapshot:snap-map-accounts v1 (lambda (a n b c flag) (push (list (hk a) a n b c flag) accts)))
    (let ((w (eita.state.snapshot:make-writer tmp 1 (eita.state.snapshot:snap-block v1) "0x00")))
      (flet ((key (o) (eita.state.snapshot:octets->int o)))
        (dolist (e (sort accts #'< :key (lambda (e) (key (first e)))))
          (destructuring-bind (h a n b c flag) e
            (dolist (kv (sort (gethash a slots) #'< :key (lambda (kv) (key (car kv)))))
              (eita.state.snapshot:writer-slot w h (car kv) (cdr kv)))
            (eita.state.snapshot:writer-account w h 0 (if flag 1 0) n b c))))
      (eita.state.snapshot:writer-finish w (eita.state.snapshot::layer-codes (list v1))))))

(defun stack-root (base layers)
  "The streaming root of BASE (an open snap) under LAYERS (newest first), 0x-prefixed."
  (concatenate 'string "0x"
               (eita.state.root:snapshot-root (eita.state.snapshot:snap-dir base) :threads 2
                                              :layers (mapcar #'eita.state.snapshot:snap-dir (reverse layers)))))

(defun root-of (dir) (concatenate 'string "0x" (eita.state.root:snapshot-root dir :threads 2)))

(defun run-tier (test version)
  "TEST in RAM (VERSION NIL) or over a snapshot of its pre-state in VERSION (1 or 2).
   Returns (values verdict rows roots): VERDICT :pass, or (:fail why...) at the first
   block the driver's gates refuse or whose root is not the header's (an expected failure:
   not stopped by the root), or a post-state mismatch; ROWS, the observers' output; ROOTS,
   the state root after each block (a stack's: base + layers)."
  (let* ((dir (format nil "~Av~D/" *dir* version))
         (world (eita.state:make-world))
         (xfail (eita.fixtures::expected-failure (getf test :name)))
         (*rows* '()) (roots '()))
    (sb-ext:run-program "rm" (list "-rf" *dir*) :search t)
    (ensure-directories-exist dir)
    (sb-posix:setenv "EITA_STATE_DIR" (format nil "~Av1/" *dir*) 1)
    (eita.fixtures::set-fork! (getf test :network))
    (eita.state:populate-world world (getf test :pre))
    (when version
      (let ((eita.state::*current-world* world)) (eita.state:genesis-base! world 0 "0x00")))
    (when (eql version 2)
      (sb-posix:setenv "EITA_STATE_DIR" dir 1)
      (let ((tmp (eita.state.snapshot:snap-tmp-path dir 0)))
        (convert-to-v2 eita.state::*base* tmp)
        (eita.state.snapshot:snap-publish dir 0 tmp)
        (eita.state.snapshot:snap-close eita.state::*base*)
        (eita.state::back-world! world (eita.state.snapshot:snap-open (eita.state.snapshot:snap-path dir 0)) '())))
    (let ((blocks (eita.fixtures::canonical-blocks test))
          (eita.state::*current-world* world))
      (eita.fixtures::install-block-hashes! test blocks)
      (let ((eita.fixtures::*recent-headers* (and (getf test :genesis-header) (list (getf test :genesis-header))))
            (eita.fixtures::*partial-pre-state* t)      ; the root is checked below
            (eita.chain::*receipts-mode* :on-mismatch)  ; fixture blocks carry no receipts: never fetch them
            (last nil))
        (flet ((fail (&rest why) (return-from run-tier (values (list* :fail why) (reverse *rows*) (reverse roots)))))
          (dolist (blk blocks)
            (let ((why (let ((t0 (get-internal-real-time)))
                         (prog1 (eita.fixtures::run-block-checked world blk)
                           (incf *exec* (- (get-internal-real-time) t0))))))
              (when why (fail :block (blk-n blk) why)))
            (let ((got (if version
                           (progn (eita.state::freeze! world (blk-n blk) (eita.input::blk-state-root blk))
                                  (eita.state::writer-drain!)
                                  (stack-root eita.state::*base* eita.state::*layers*))
                           (eita.state:world-state-root world))))
              (push got roots)
              (unless (or xfail (getf test :partial-pre) (string-equal got (eita.input::blk-state-root blk)))
                (fail :root (blk-n blk) got (eita.input::blk-state-root blk))))
            (setf last blk))
          (unless xfail
            ;; compare-post reads the tables as they are: fault in what it compares first
            (dolist (e (getf test :post))
              (eita.state:fault-account! (car e))
              (dolist (kv (getf (cdr e) :storage)) (eita.state:fault-slot! (car e) (car kv))))
            (let ((post (eita.fixtures::compare-post world (getf test :post))))
              (when post (fail :post post))))
          ;; compaction: every layer composed into one (minor), and everything into a base
          ;; (major): both read as the stack did
          (when (and version last (>= (length eita.state::*layers*) 2))
            (let* ((n (blk-n last)) (want (first roots)) (sd (eita.state::snapshot-dir))
                   (tmp (eita.state.snapshot:layer-tmp-path sd 0 n)) (fin (eita.state.snapshot:layer-path sd 0 n)))
              (eita.state.snapshot:write-composed tmp 1 n want eita.state::*layers* nil :parent 0)
              (eita.state.snapshot:snap-publish sd n tmp :final fin)
              (let* ((l (eita.state.snapshot:snap-open fin)) (got (stack-root eita.state::*base* (list l))))
                (eita.state.snapshot:snap-close l)
                (unless (string-equal got want) (fail :minor-root got want)))
              (let ((tmp (eita.state.snapshot:snap-tmp-path sd n)))
                (eita.state.snapshot:write-composed tmp 1 n want eita.state::*layers* eita.state::*base*)
                (eita.state.snapshot:snap-publish sd n tmp)
                (let ((got (root-of (eita.state.snapshot:snap-path sd n))))
                  (unless (string-equal got want) (fail :major-root got want)))))))
        (values (list :pass) (reverse *rows*) (reverse roots))))))

(defun blk-n (blk) (eita.input::blk-number blk))

(defun close-stack ()
  (eita.state::writer-drain!)
  (mapc #'eita.state.snapshot:snap-close
        (remove-if-not #'eita.state.snapshot:snap-p (cons eita.state::*base* eita.state::*layers*)))
  (setf eita.state::*base* nil eita.state::*layers* '()
        eita.state::*keep-zero-slots* nil eita.state::*fault-account-hook* nil
        eita.state::*fault-slot-hook* nil eita.state::*storage-wipe-hook* nil))

(defparameter *vars*
  '(eita.state::*base* eita.state::*layers* eita.state::*current-world* eita.state::*keep-zero-slots*
    eita.state::*fault-account-hook* eita.state::*fault-slot-hook* eita.state::*storage-wipe-hook*
    eita.evm::*observer* eita.evm::*observe-calls* eita.state::*written*))

(defun short (x) (let ((s (let ((*print-pretty* nil)) (prin1-to-string x)))) (subseq s 0 (min 600 (length s)))))

(let ((root (eita.test::fixtures-dir))
      (saved (mapcar #'symbol-value *vars*))
      (old-env (sb-ext:posix-getenv "EITA_STATE_DIR"))
      (counts (list :tests 0 :xfail 0 :blocks 0 :pass 0 :skipped 0 :ram-fail 0 :bad 0 :ram-rows-differ 0))
      (time (list 0 0 0)) (differ '()))
  (setf eita.evm::*observer* *observer* eita.evm::*observe-calls* t)
  (unwind-protect
       (progn
       (dolist (sub (if eita.test:*argument* (list eita.test:*argument*) *dirs*))
         (dolist (f (eita.fixtures::collect-json-files (merge-pathnames (concatenate 'string "../" sub) root)))
           (let ((json (jsown:parse (alexandria:read-file-into-string f))))
             (dolist (name (jsown:keywords json))
               (let ((test (eita.fixtures:parse-test name (eita.evm::jval json name))))
                 (if (not (member (getf test :network) *networks* :test #'string=))
                     (incf (getf counts :skipped))
                     (let ((out (loop for v in '(nil 1 2) for i from 0
                                      collect (let ((t0 (get-internal-real-time)))
                                                (prog1 (multiple-value-list
                                                        (handler-case (let ((*standard-output* (make-broadcast-stream))) (run-tier test v))
                                                          (error (e) (values (list :fail :error (princ-to-string e)) nil nil))))
                                                  (close-stack)
                                                  (incf (nth i time) (- (get-internal-real-time) t0)))))))
                       (incf (getf counts :tests))
                       (when (eita.fixtures::expected-failure name) (incf (getf counts :xfail)))
                       (incf (getf counts :blocks) (length (eita.fixtures::canonical-blocks test)))
                       (destructuring-bind ((v0 r0 s0) (v1 r1 s1) (v2 r2 s2)) out
                         (cond ((not (eq (first v0) :pass)) (incf (getf counts :ram-fail)))
                               ((and (eq (first v1) :pass) (eq (first v2) :pass) (equalp r1 r2)
                                     (equalp s0 s1) (equalp s1 s2))
                                (incf (getf counts :pass))
                                (unless (equalp r0 r1) (incf (getf counts :ram-rows-differ)) (push name differ)))
                               (t (incf (getf counts :bad))
                                  (when (<= (getf counts :bad) 10)
                                    (format t "FAIL ~A (~A)~%  v1 ~A~%  v2 ~A~%  rows v1=v2 ~A, roots ram=v1 ~A v1=v2 ~A~%"
                                            name (getf test :network) (short v1) (short v2)
                                            (equalp r1 r2) (equalp s0 s1) (equalp s1 s2)))))))))))))
    ;; the cost of hashed keys: a real mainnet block (300+ txs, its accounts and slots all
    ;; faulted from the base) executed over each tier, best of five; and the hash itself
    (let* ((gz (eita.test::home "tests/data/mainnet-24538111.json.gz"))
           (file (format nil "/tmp/test-snapshot-tiers-~D.json" (sb-posix:getpid)))
           (test (progn (with-open-file (o file :direction :output :if-exists :supersede)
                          (sb-ext:run-program "gzip" (list "-dc" gz) :search t :output o))
                        (let ((json (jsown:parse (alexandria:read-file-into-string file))))
                          (eita.fixtures:parse-test "mainnet_24538111" (eita.evm::jval json "mainnet_24538111")))))
           (best (list nil nil nil)) (faults (list nil nil nil)) (rows '()))
      (delete-file file)
      (dotimes (k 5)
             (loop for v in '(nil 1 2) for i from 0
                   do (let ((*exec* 0) (stats (copy-list eita.state::*snap-stats*)))
                        (multiple-value-bind (verdict r) (let ((*standard-output* (make-broadcast-stream))) (run-tier test v))
                          (unless (eq (first verdict) :pass)
                            (incf (getf counts :bad)) (format t "FAIL mainnet_24538111 tier ~A: ~A~%" v (short verdict)))
                          (when (zerop k) (push r rows)))
                        (setf (nth i faults) (list (- (getf eita.state::*snap-stats* :acct-faults) (getf stats :acct-faults))
                                                   (- (getf eita.state::*snap-stats* :slot-faults) (getf stats :slot-faults))))
                        (close-stack)
                        (setf (nth i best) (min (or (nth i best) *exec*) *exec*)))))
      (destructuring-bind (r2 r1 r0) rows
        (unless (and (equalp r1 r2) (equalp r0 r1))
          (incf (getf counts :bad)) (format t "FAIL mainnet_24538111: observer rows differ between tiers~%")))
      (let ((ms (mapcar (lambda (x) (/ (* 1000.0 x) internal-time-units-per-second)) best))
            (n 200000) (a #xf39fd6e51aad88f6f4ce6ab8827279cfffb92266))
        (format t "mainnet 24538111 (~D txs), execution best of 5: RAM ~,1F ms, v1 ~,1F ms, v2 ~,1F ms (v2/v1 ~,3F); faults over a stack (accounts slots): ~S~%"
                (length (eita.input::blk-txs (first (getf test :blocks)))) (first ms) (second ms) (third ms)
                (/ (third ms) (max 1e-9 (second ms))) (second faults))
        (let ((t0 (get-internal-real-time)))
          (dotimes (i n) (eita.state::key-hash (+ a i) 20))
          (let ((t1 (get-internal-real-time)))
            (dotimes (i n) (eita.state::key-hash (+ a i) 32))
            (format t "keccak of a key: ~,0F ns (20 bytes), ~,0F ns (32 bytes)~%"
                    (/ (* 1e9 (- t1 t0)) internal-time-units-per-second n)
                    (/ (* 1e9 (- (get-internal-real-time) t1)) internal-time-units-per-second n)))))))
    (close-stack)
    (eita.state::stop-background!)
    (loop for v in *vars* for x in saved do (setf (symbol-value v) x))
    (if old-env (sb-posix:setenv "EITA_STATE_DIR" old-env 1) (sb-posix:unsetenv "EITA_STATE_DIR"))
    (sb-ext:run-program "rm" (list "-rf" *dir*) :search t))
  (format t "snapshot tiers: ~S~%  time: RAM ~,1F s, v1 ~,1F s, v2 ~,1F s~%  observer rows differ from RAM in: ~{~A~^, ~}~%"
          counts (/ (first time) internal-time-units-per-second) (/ (second time) internal-time-units-per-second)
          (/ (third time) internal-time-units-per-second) (subseq differ 0 (min 30 (length differ))))
  (eita.test:finish :code (if (and (zerop (getf counts :bad)) (plusp (getf counts :pass))) 0 1)))
