;;;; tests/hooks.lisp — subscriptions (evm/hooks.lisp) and the examples of docs/hooks.md, run
;;;; on Eita's mainnet repro block (tests/data/mainnet-24538111.json.gz, 756 txs), and on
;;;; ValidBlocks/bcExample when a checkout is present:
;;;;   1. subscriptions observe, never steer: the runner's output is the same with and without
;;;;      them, and nothing stays installed after a run;
;;;;   2. the records: each block's txs' gas sums to its header's, logs are indexed in order;
;;;;   3. each example's fold equals the same quantity recomputed here from the records;
;;;;   4. the stream's checkpoint and rollback reach the handlers; a rollback below a block a
;;;;      subscription without :rollback has seen detaches it; a failing handler is detached,
;;;;      the others go on;
;;;;   5. the durable fold: checkpoint, restart and rollback give the straight run's state.

(defpackage #:eita.test.hooks (:use #:cl))
(in-package #:eita.test.hooks)

(defvar *fails* 0)
(defun fail (fmt &rest args) (incf *fails*) (format t "  FAIL: ~?~%" fmt args))
(defmacro check (form fmt &rest args) `(unless ,form (fail ,fmt ,@args)))

(defun gunzip-to-temp (gz)
  (let ((out (format nil "/tmp/eita-test-hooks-~D.json" (sb-posix:getpid))))
    (with-open-file (s out :direction :output :if-exists :supersede)
      (sb-ext:run-program "gzip" (list "-dc" gz) :search t :output s :error nil))
    out))

(defun run (paths)
  "The runner's output over PATHS."
  (with-output-to-string (*standard-output*) (eita.fixtures:main paths)))

(defun clear () (dolist (s (eita:subscriptions)) (eita:unsubscribe (first s))))
(defun example (name) (load (eita.test::home (format nil "examples/hooks/~A.lisp" name))))
(defun sub-error (name) (getf (rest (find name (eita:subscriptions) :key #'first :test #'equal)) :error))

;; What a recording subscription saw (globals: the handlers run on the hooks thread).
(defvar *blocks* '()) (defvar *changes* '()) (defvar *transfers* '()) (defvar *events* '())
(defun record! ()
  (setf *blocks* '() *changes* '() *transfers* '() *events* '())
  (eita:subscribe "record" :block (lambda (b) (push b *blocks*))
                           :state-change (lambda (c) (push c *changes*))
                           :transfer (lambda (x) (push x *transfers*))
                           :start (lambda (n) (push (list :start n) *events*))
                           :checkpoint (lambda (n) (push (list :checkpoint n) *events*))
                           :rollback (lambda (n) (push (list :rollback n) *events*))
                           :finalize (lambda () (push (list :finalize) *events*))))

(defun renumbered (block n &key (dt 12))
  "BLOCK as block N, DT seconds after it per block."
  (let ((b (copy-list block)))
    (setf (getf b :timestamp) (+ (getf block :timestamp) (* dt (- n (getf block :number)))) (getf b :number) n)
    b))

(defparameter +examples+ '("gas-per-block" "transfers" "watch" "notify" "durable"))
;; loaded once here so that their packages exist when the forms below are read; each
;; subscribes as it loads, and is subscribed again (by loading it again) after the plain run
(mapc #'example +examples+)
(hooks.notify:stop)
(clear)

(let* ((mainnet (gunzip-to-temp (eita.test::home "tests/data/mainnet-24538111.json.gz")))
       (more (let ((d (eita.test::fixtures-dir))) (and d (list (concatenate 'string d "bcExample/")))))
       (dir (format nil "/tmp/eita-test-hooks-~D/" (sb-posix:getpid))))
  (unwind-protect
       (progn
         (clear)
         ;; --- 1. no steering, nothing left installed --------------------------------------
         (let ((off (run (cons mainnet more))))
           (mapc #'example +examples+)
           (setf hooks.durable:*dir* dir)
           (hooks.notify:start :deliver (lambda (m) m))
           (record!)
           (let ((on (run (cons mainnet more))))
             (check (string= off on) "the runner's output differs with subscriptions:~%~A~%---~%~A" off on)
             (check (search " fail=0 " on) "the runs must pass:~%~A" on)
             (check (and (null eita.state:*observer*) (null eita.evm::*hooks-observer*) (null eita.evm::*hooks-sub*))
                    "the hooks observer is still installed after the run")
             (format t "  runner output identical with ~D subscriptions; ~D blocks delivered~%"
                     (length (eita:subscriptions)) (length *blocks*))))
         ;; --- 2. the records, on the mainnet block ----------------------------------------
         (record!)
         (run (list mainnet))
         (let ((b (first *blocks*)))
           (check (= 1 (length *blocks*)) "~D blocks delivered, expected 1" (length *blocks*))
           (check (= 756 (length (getf b :txs))) "~D txs, expected 756" (length (getf b :txs)))
           (check (= (getf b :gas-used) (reduce #'+ (getf b :txs) :key (lambda (tx) (getf tx :gas-used))))
                  "the txs' gas does not sum to the header's ~D" (getf b :gas-used))
           (check (equal (loop for tx in (getf b :txs) append (mapcar (lambda (l) (getf l :index)) (getf tx :logs)))
                         (loop for i below (loop for tx in (getf b :txs) sum (length (getf tx :logs))) collect i))
                  "the log indices are not 0, 1, … in order")
           (check (every (lambda (tx) (member (getf tx :status) '(0 1))) (getf b :txs)) "a status other than 0/1")
           (check (equal (reverse *events*) (list (list :start (getf b :number)) (list :finalize)))
                  "start/finalize events: ~S" (reverse *events*))
           (check (eql (eita:with-fold-state (n) n) (getf b :number)) "with-fold-state's block")
           (eita:unsubscribe "record")          ; *changes* and *transfers* are this run's from here
           (format t "  block ~D: ~D txs, ~D logs, ~D state changes, ~D transfers~%" (getf b :number) (length (getf b :txs))
                   (loop for tx in (getf b :txs) sum (length (getf tx :logs))) (length *changes*) (length *transfers*))
           ;; --- 3. the examples' folds, recomputed ----------------------------------------
           ;; gas-per-block: the totals, and the window over the block renumbered as 10
           ;; blocks 600 s apart (the hour holds the newest 6), then a rollback of 3
           (let ((s (hooks.gas:summary)))
             (multiple-value-bind (burnt tips) (hooks.gas::fees b)
               (check (equal (getf s :totals) (list :blocks 1 :txs 756 :gas (getf b :gas-used) :burnt burnt :tips tips))
                      "gas totals ~S" (getf s :totals))
               (check (and (plusp burnt) (plusp tips)) "fees ~D ~D" burnt tips)))
           (hooks.gas::on-start 1)
           (loop for n from 1 to 10 do (hooks.gas::on-block (renumbered b n :dt 600)))
           (let ((s (hooks.gas:summary)))
             (check (and (= 6 (getf s :window-blocks)) (= (getf s :window-gas) (* 6 (getf b :gas-used)))
                         (= 10 (getf (getf s :totals) :blocks)))
                    "window ~S" s))
           (hooks.gas::on-rollback 7)
           (let ((s (hooks.gas:summary)))
             (check (and (= 3 (getf s :window-blocks)) (= 7 (getf (getf s :totals) :blocks))) "window after rollback ~S" s))
           ;; transfers: the counts and the top senders against exact counts
           (let* ((erc20 0) (native 0) (exact (make-hash-table)) (s (hooks.transfers:summary 5))
                  (top (eita:with-fold-state () (hooks.transfers:top hooks.transfers::*senders* 5))))
             (dolist (tx (getf b :txs))
               (dolist (l (getf tx :logs))
                 (let ((topics (getf l :topics)))
                   (when (and (= 3 (length topics)) (= (first topics) hooks.transfers::+transfer-topic+) (= 32 (length (getf l :data))))
                     (incf erc20) (incf (gethash (ldb (byte 160 0) (second topics)) exact 0))))))
             (dolist (x *transfers*) (when (plusp (getf x :value)) (incf native) (incf (gethash (getf x :from) exact 0))))
             (check (and (= erc20 (getf (getf s :counts) :erc20)) (= native (getf (getf s :counts) :native)))
                    "transfer counts ~S, recomputed erc20 ~D native ~D" (getf s :counts) erc20 native)
             (check (<= (hash-table-count hooks.transfers::*senders*) hooks.transfers:*k*) "the sender table is over K")
             (loop for (key count err) in top
                   do (check (<= (- count err) (gethash key exact 0) count) "sender ~X: ~D-~D vs exact ~D" key count err (gethash key exact 0)))
             (when (<= (hash-table-count exact) hooks.transfers:*k*)    ; every sender fits: exact
               (check (every (lambda (e) (and (zerop (third e)) (= (second e) (gethash (first e) exact)))) top)
                      "the top senders are not exact"))
             (format t "  transfers: ~D ERC-20, ~D native, ~D senders (~D kept)~%" erc20 native (hash-table-count exact)
                     (hash-table-count hooks.transfers::*senders*)))
           ;; watch: the most-changed slot and the fee recipient's balance
           (let* ((counts (make-hash-table :test 'equal))
                  (slot (progn (dolist (c *changes*) (when (eq (getf c :kind) :storage)
                                                       (incf (gethash (list (getf c :address) (getf c :slot)) counts 0))))
                               (let (k (n 0)) (maphash (lambda (key c) (when (> c n) (setf k key n c))) counts) k)))
                  (coinbase (getf b :coinbase))
                  (seen '()) (lock (sb-thread:make-mutex)))
             (flet ((note (c) (sb-thread:with-mutex (lock) (push c seen)))
                    (want (pred) (reverse (remove-if-not pred *changes*))))
               (hooks.watch:watch (first slot) :slot (second slot) :notify #'note)
               (hooks.watch:watch coinbase :kind :balance :notify #'note)
               (run (list mainnet))
               (let ((got (reverse seen)))
                 (check (equal (remove :balance got :key (lambda (c) (getf c :kind)))
                               (want (lambda (c) (and (eq (getf c :kind) :storage) (equal (list (getf c :address) (getf c :slot)) slot)))))
                        "the slot watch's changes differ")
                 (check (equal (remove :storage got :key (lambda (c) (getf c :kind)))
                               (want (lambda (c) (and (eq (getf c :kind) :balance) (= (getf c :address) coinbase)))))
                        "the balance watch's changes differ")
                 (check (loop for (x y) on (remove :balance got :key (lambda (c) (getf c :kind)))
                              always (or (null y) (= (getf x :post) (getf y :pre))))
                        "the slot's changes do not chain (post = next pre)")
                 (format t "  watch: ~D changes of the busiest slot, ~D of the fee recipient's balance~%"
                         (count :storage got :key (lambda (c) (getf c :kind))) (count :balance got :key (lambda (c) (getf c :kind))))))
             (hooks.watch:unwatch (first slot) :slot (second slot))
             (hooks.watch:unwatch coinbase :kind :balance))
           ;; notify: three at once (burst 3, no refill), the rest rate-limited and counted
           (let* ((sent '()) (lock (sb-thread:make-mutex))
                  (want (+ (count-if (lambda (x) (>= (getf x :value) (expt 10 17))) *transfers*)
                           (if (> (* 100 (getf b :gas-used)) (* 95 (getf b :gas-limit))) 1 0))))
             (setf hooks.notify:*large-value* (expt 10 17))   ; global: the handlers' thread reads it
             (hooks.notify:start :deliver (lambda (m) (sb-thread:with-mutex (lock) (push m sent))) :burst 3 :rate 0)
             (run (list mainnet))
             (let ((stats (hooks.notify:notifier-stats hooks.notify:*notifier*)))
               (check (and (> want 3) (= 3 (length sent)) (= 3 (getf stats :sent)) (= (- want 3) (getf stats :rate-limited)))
                      "notify: ~D conditions, ~D sent, ~S" want (length sent) stats)
               (check (string= "large-transfer"
                               (jsown:val (jsown:parse (with-output-to-string (s) (hooks.notify:json-line (first sent) s))) "event"))
                      "the JSON line does not parse back")
               (format t "  notify: ~D conditions, ~S~%" want stats))
             (hooks.notify:start :deliver (lambda (m) (declare (ignore m)) (error "unreachable")) :burst 1 :rate 0)
             (run (list mainnet))
             (check (= 1 (getf (hooks.notify:notifier-stats hooks.notify:*notifier*) :failed)) "a failed delivery is not counted")
             (hooks.notify:stop)
             (setf hooks.notify:*large-value* (expt 10 20)))
           ;; --- 4. checkpoint and rollback through the stream; failures -------------------
           (let ((commit (fdefinition 'eita.evm:stream-commit!)) (kept nil) (n (getf b :number)))
             (record!)
             (eita:subscribe "boom" :block (lambda (blk) (declare (ignore blk)) (error "boom")) :rollback #'identity)
             (eita:subscribe "no-rollback" :block #'identity)
             (setf (fdefinition 'eita.evm:stream-commit!)
                   (lambda (k &rest more)
                     (apply commit k more)
                     (when (= k n)
                       (funcall (eita.evm:stream-checkpoint! k))   ; waits for every subscriber's checkpoint
                       (eita.evm:stream-rollback! k)              ; nothing above K was delivered
                       (setf kept (null (sub-error "no-rollback")))
                       (eita.evm:stream-rollback! (1- k)))))      ; block K was: undone, or detached
             (unwind-protect (run (list mainnet))
               (setf (fdefinition 'eita.evm:stream-commit!) commit))
             (check (equal (reverse *events*) (list (list :start n) (list :checkpoint n) (list :rollback n)
                                                    (list :rollback (1- n)) (list :finalize)))
                    "stream events ~S" (reverse *events*))
             (check (and kept (sub-error "no-rollback"))
                    "a subscription without :rollback must stay through a rollback at its block and go at one below it")
             (check (eql (1- n) (getf (hooks.durable:state) :block)) "the durable fold did not roll back to ~D" (1- n))
             (check (eql (1- n) (eita:with-fold-state (blk) blk)) "with-fold-state's block after the rollback")
             (eita:unsubscribe "no-rollback")
             (check (sub-error "boom") "the failing handler was not detached")
             (check (= 1 (length *blocks*)) "the other subscriptions did not go on")
             (check (probe-file (hooks.durable::checkpoint-path n)) "the durable fold wrote no checkpoint at ~D" n)
             (eita:unsubscribe "boom"))
           ;; subscribing during a run: from the next block, complete; unsubscribing: none after
           (when more
             (clear)
             (let ((commit (fdefinition 'eita.evm:stream-commit!)) (finalize (fdefinition 'eita.evm:stream-finalize!))
                   (late '()) (off (run more)) on)
               (setf (fdefinition 'eita.evm:stream-commit!)
                     (lambda (k &rest args)
                       (apply commit k args)
                       (case k
                         (1 (eita:subscribe "late" :block (lambda (blk) (push blk late))))
                         (2 (eita.evm::fw-drain) (eita:unsubscribe "late"))))
                     (fdefinition 'eita.evm:stream-finalize!)
                     (lambda () (eita:unsubscribe "late") (funcall finalize)))   ; a one-block run: gone at its end
               (unwind-protect (setf on (run more))
                 (setf (fdefinition 'eita.evm:stream-commit!) commit (fdefinition 'eita.evm:stream-finalize!) finalize))
               (check (string= off on) "the runner's output differs with a subscription during the run")
               (check (and late (every (lambda (blk) (and (= 2 (getf blk :number))
                                                          (= (getf blk :gas-used) (reduce #'+ (getf blk :txs) :key (lambda (tx) (getf tx :gas-used))))))
                                       late))
                      "a subscription during the run got ~S" (mapcar (lambda (blk) (getf blk :number)) late))
               (check (null eita.state:*observer*) "the hooks observer stayed installed")
               (format t "  subscribed at block 1, unsubscribed at 2, in ~D runs: block 2 each time~%" (length late))))
           (eita:subscribe "record" :block #'identity)          ; replaced by name, not added
           (check (= 1 (count "record" (eita:subscriptions) :key #'first :test #'equal)) "a same-name subscription was added")
           ;; --- 5. the durable fold: restart and rollback ---------------------------------
           (labels ((fresh () (setf hooks.durable::*state* (hooks.durable::empty) hooks.durable::*undo* '()))
                    (feed (from to) (loop for k from from to to do (hooks.durable::on-block (renumbered b k)))))
             (map nil #'delete-file (directory (concatenate 'string dir "*.*")))
             (fresh) (hooks.durable::on-start 1) (feed 1 10)
             (let ((straight (hooks.durable:state)))
               (fresh) (hooks.durable::on-start 1) (feed 1 5) (hooks.durable::on-checkpoint 5) (feed 6 8)
               (hooks.durable::on-rollback 6) (feed 7 10)
               (check (equal straight (hooks.durable:state)) "after a rollback: ~S vs ~S" (hooks.durable:state) straight)
               (fresh) (hooks.durable::on-start 6) (feed 6 10)        ; a restart from the checkpoint at 5
               (check (equal straight (hooks.durable:state)) "after a restart: ~S vs ~S" (hooks.durable:state) straight)
               (fresh) (hooks.durable::on-start 4)
               (check (eql 4 (getf (hooks.durable:state) :from)) "without a checkpoint the fold must say where it starts")
               (format t "  durable: rollback and restart give the straight run's ~S~%" straight)))))
    (clear)
    (ignore-errors (delete-file mainnet))
    (sb-ext:run-program "rm" (list "-rf" dir) :search t))
  (format t "~&hooks: ~:[FAIL~;subscriptions deliver verified blocks, never steer; the examples' folds check out~]~%" (zerop *fails*))
  (eita.test:finish :code (if (zerop *fails*) 0 1)))
