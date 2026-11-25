;;;; evm/hooks.lisp — subscriptions: user handlers fed each verified block (docs/hooks.md).

(in-package #:eita.evm)

;;; A SUBSCRIPTION is a name and handlers (`eita:subscribe`). While any exists, the hooks
;;; observer is installed (at a block's start, on the replay thread; combined with an observer
;;; already there) and copies each block's header and each tx's results into the event stream;
;;; the hooks subscriber, one stream subscriber on its own thread, collects a block's records
;;; between (:block-begin n) and (:commit n …), waits for N's verdict, and calls the handlers
;;; holding *fold-lock*. Records of a block that never commits are dropped. With no
;;; subscription nothing is installed: a block start costs one call.

(defstruct (subscription (:constructor make-subscription (name handlers)))
  name handlers (started nil) (error nil))

(defvar *fold-lock* (sb-thread:make-mutex :name "folds")
  "Held while handlers run (one block at a time) and by `eita:with-fold-state`.")
(defvar *hooks* '() "The subscriptions, oldest first (a list replaced, never mutated).")
(defvar *hooks-observer* nil "The installed observer while subscriptions exist, or NIL.")
(defvar *hooks-base* nil "The observer *hooks-observer* wraps, restored when it goes.")
(defvar *hooks-sub* nil "This run's hooks subscriber (the stream's), or NIL.")
(defvar *hooks-last* nil "The newest block delivered.")
(defvar *hooks-tx* nil "Replay thread: the user tx whose tx-end ran, awaiting its tx-result.")
(defvar *hooks-log-index* 0 "Replay thread: the block's next user-tx log index (logIndex).")
(defvar *hooks-executed* nil
  "Replay thread: (header . records, newest first) of the block running, kept while some
   subscription has an :executed handler.")
(defvar *sim-block* nil
  "The context `eita:sim-tx` runs in: the newest block's, numbered one above it.")

(defparameter +transfer-kinds+ #(:tx :call :create :selfdestruct :chain))

(defun eita:subscribe (name &rest handlers &key start block tx log transfer state-change checkpoint rollback finalize executed)
  "Subscribe NAME (a string or symbol; one with the same name is replaced, and the
   replacement continues where it left off) with HANDLERS, each a function: START (n), its
   first block is N; BLOCK (block) a verified block, after its TX, LOG, TRANSFER and
   STATE-CHANGE handlers; CHECKPOINT (n) persist the state through block N now; ROLLBACK
   (n) the chain is rolled back to block N; FINALIZE () the run ends; EXECUTED (block) on the
   replay thread as soon as the block ran, before its verdict, the world after it at hand
   (`eita:simulate`). The records are plists (docs/hooks.md). Returns NAME."
  (declare (ignore start block tx log transfer state-change checkpoint rollback finalize executed))
  (let ((new (make-subscription name (loop for (k f) on handlers by #'cddr when f append (list k f)))))
    (sb-thread:with-recursive-lock (*fold-lock*)
      (let ((old (find name *hooks* :key #'subscription-name :test #'equal)))
        (when old (setf (subscription-started new) (subscription-started old)))
        (setf *hooks* (if old (substitute new old *hooks*) (append *hooks* (list new))))))
    name))

(defun eita:unsubscribe (name)
  "Remove the subscription NAME (no handler of it runs after this returns); true if it existed."
  (sb-thread:with-recursive-lock (*fold-lock*)
    (let ((old (find name *hooks* :key #'subscription-name :test #'equal)))
      (setf *hooks* (remove old *hooks*))
      (and old t))))

(defun eita:subscriptions ()
  "Each subscription as (name :handlers kinds :error why), WHY NIL unless it was detached."
  (mapcar (lambda (s) (list (subscription-name s)
                            :handlers (loop for k in (subscription-handlers s) by #'cddr collect k)
                            :error (subscription-error s)))
          *hooks*))

(defmacro eita:with-fold-state ((&optional (block (gensym "BLOCK"))) &body body)
  "Run BODY while no handler runs, BLOCK bound to the newest block delivered (NIL: none):
   every fold reflects whole blocks through it. Keep BODY short (copy, then work outside):
   the handlers wait, and behind them, once their queue is full, the replay."
  `(sb-thread:with-recursive-lock (*fold-lock*)
     (let ((,block *hooks-last*)) (declare (ignorable ,block)) ,@body)))

;;; --- Capture: the hooks observer, on the replay thread -----------------------------------
(defun hooks-tx-record (block tx success)
  "The tx-end summary as a record: its committed logs and transfers, its net state changes."
  (let* ((user (< eita.chain:+preblock-tx+ tx eita.chain:+postblock-tx+))
         (idx (cond (user tx) ((= tx eita.chain:+preblock-tx+) :pre-block) (t :post-block)))
         (logs '()) (xfers '()) (changes '()))
    (when success
      (do-tx-events (:transfer (kind depth from to value) :log (i addr topics data))
        (:transfer (push (list :block block :tx idx :kind (svref +transfer-kinds+ kind) :depth depth
                               :from from :to to :value value)
                         xfers))
        (:log (declare (ignore i))         ; the index in the block's user-tx logs instead
              (push (list :block block :tx idx :index (and user (prog1 *hooks-log-index* (incf *hooks-log-index*)))
                          :address addr :topics topics :data data)
                    logs))))
    (do-account-changes (addr n0 n1 b0 b1 h0 h1)
      (unless (= b0 b1) (push (list :block block :tx idx :kind :balance :address addr :pre b0 :post b1) changes))
      (unless (= n0 n1) (push (list :block block :tx idx :kind :nonce :address addr :pre n0 :post n1) changes))
      (unless (= h0 h1) (push (list :block block :tx idx :kind :code :address addr :pre h0 :post h1) changes)))
    (do-storage-changes (addr slot pre post)
      (push (list :block block :tx idx :kind :storage :address addr :slot slot :pre pre :post post) changes))
    (list :block block :index idx :logs (nreverse logs) :transfers (nreverse xfers) :changes (nreverse changes))))

(defun hooks-observer ()
  (make-observer
   :name "hooks"
   :attach (lambda () (hooks-attach!))
   :block (lambda (blk fork-ord)
            (declare (ignore fork-ord))
            (setf *hooks-log-index* 0 *hooks-tx* nil)
            (let ((header (list :number (eita.input:blk-number blk) :hash (eita.input:blk-hash blk) :parent-hash (eita.input:blk-parent-hash blk)
                                :timestamp (eita.input:blk-timestamp blk) :coinbase (eita.input:blk-miner blk)
                                :base-fee (or (eita.input:blk-base-fee blk) 0) :gas-limit (eita.input:blk-gas-limit blk)
                                :gas-used (eita.input:blk-gas-used blk) :received-ms (eita.input::blk-received-ms blk))))
              (setf *hooks-executed* (and (hooks-with-p :executed) (list header)))
              (fw-push (list :hooks-block header))))
   :tx-end (lambda (block tx success)
             (let ((r (hooks-tx-record block tx success)))
               (if (integerp (getf r :index)) (setf *hooks-tx* r) (hooks-record! r))))
   :tx-result (lambda (n idx tx gas-used status egp)
                (let ((r (if (and *hooks-tx* (eql (getf *hooks-tx* :index) idx))
                             *hooks-tx*
                             (list :block n :index idx :logs '() :transfers '() :changes '()))))
                  (setf *hooks-tx* nil)
                  (hooks-record! (list* :hash (tx-hash tx) :type (tx-type tx) :from (tx-sender tx) :to (tx-to tx)
                                        :value (tx-value tx) :nonce (tx-nonce tx) :gas-limit (tx-gas-limit tx)
                                        :gas-used gas-used :status status :gas-price egp r))))))

(defun hooks-with-p (kind)
  (some (lambda (s) (and (getf (subscription-handlers s) kind) (not (subscription-error s)))) *hooks*))

(defun hooks-record! (r)
  "Replay thread: a tx record to the stream (the hooks thread's), and to the block's
   :executed delivery when one is due."
  (when *hooks-executed* (push r (cdr *hooks-executed*)))
  (fw-push (list :hooks-tx r)))

(defun hooks-executed! (n block-ctx)
  "Replay thread, block N just ran (its layer point made, its verdict pending): each
   :executed handler with the block's record, and with `eita:sim-tx` at the next block's
   context. Not under the fold lock: the replay never waits for the hooks thread."
  (let ((e *hooks-executed*))
    (setf *hooks-executed* nil)
    (when (and e (eql (getf (car e) :number) n))
      (let ((block (append (car e) (list :txs (remove-if-not (lambda (r) (integerp (getf r :index))) (reverse (cdr e))))))
            (*sim-block* (list* :number (1+ n) block-ctx)))
        (dolist (s *hooks*)
          (when (getf (subscription-handlers s) :executed)
            (hook-call s :executed block)))))))

(defun combine-observers (a b)
  "An observer calling A's hooks, then B's."
  (flet ((both (fa fb) (if (and fa fb) (lambda (&rest args) (apply fa args) (apply fb args)) (or fa fb))))
    (make-observer :name (format nil "~A+~A" (observer-name a) (observer-name b)) :retain (observer-retain a)
                   :attach (both (observer-attach a) (observer-attach b)) :start (both (observer-start a) (observer-start b))
                   :block (both (observer-block a) (observer-block b)) :tx-end (both (observer-tx-end a) (observer-tx-end b))
                   :tx-result (both (observer-tx-result a) (observer-tx-result b)))))

(defun hooks-boundary! ()
  "At a block's start (stream-block-begin!): install the hooks observer while subscriptions
   exist, remove it when none is left."
  (cond ((and *hooks* (not *hooks-observer*))
         (let ((o (hooks-observer)))
           (setf *hooks-base* *observer*
                 *hooks-observer* (if *observer* (combine-observers *observer* o) o)
                 *observer* *hooks-observer*)
           (when *subscribers* (hooks-attach!))))      ; else (observe attach) at the next flush
        ((and (null *hooks*) *hooks-observer*)
         (hooks-uninstall!))))

(defun hooks-uninstall! ()
  (when (eq *observer* *hooks-observer*) (setf *observer* *hooks-base*))
  (setf *hooks-observer* nil *hooks-base* nil))

(defun hooks-end-run! ()
  "The stream ended (stream-finalize!): the next run installs afresh."
  (setf *hooks-sub* nil)
  (when *hooks-observer* (hooks-uninstall!)))

;;; --- Delivery: the hooks subscriber, on its own thread -----------------------------------
(defun detach! (s e)
  "S failed with E: no handler of it runs again (it stays in *hooks*, with E)."
  (setf (subscription-error s) e)
  (format *error-output* "~&[hooks] ~A detached: ~A~%" (subscription-name s) e))

(defun hook-call (s kind &rest args)
  "S's handler for KIND on ARGS; an error detaches S."
  (let ((f (getf (subscription-handlers s) kind)))
    (when (and f (not (subscription-error s)))
      (handler-case (apply f args)
        (error (e) (detach! s (format nil "its ~(~A~) handler failed: ~A" kind e)))))))

(defun hooks-rollback (n)
  "The chain is rolled back to block N: each subscription's :rollback handler; one without
   that has seen a block above N is detached (it would be ahead of the chain)."
  (sb-thread:with-recursive-lock (*fold-lock*)
    (let ((above (and *hooks-last* (> *hooks-last* n))))
      (dolist (s *hooks*)
        (cond ((getf (subscription-handlers s) :rollback) (hook-call s :rollback n))
              ((and above (subscription-started s) (not (subscription-error s)))
               (detach! s (format nil "rolled back to block ~D, below its newest block ~D, without a :rollback handler"
                                  n *hooks-last*)))))
      (when above (setf *hooks-last* n)))))

(defun hooks-deliver (header recs)
  (let* ((n (getf header :number))
         (block (append header (list :txs (remove-if-not (lambda (r) (integerp (getf r :index))) recs)))))
    (sb-thread:with-recursive-lock (*fold-lock*)
      (dolist (s *hooks*)
        (unless (subscription-started s)
          (setf (subscription-started s) t)
          (hook-call s :start n))
        (let ((h (subscription-handlers s)))
          (when (or (getf h :tx) (getf h :log) (getf h :transfer) (getf h :state-change))
            (dolist (r recs)
              (when (integerp (getf r :index)) (hook-call s :tx r))
              (dolist (x (getf r :transfers)) (hook-call s :transfer x))
              (dolist (l (getf r :logs)) (hook-call s :log l))
              (dolist (c (getf r :changes)) (hook-call s :state-change c)))))
        (hook-call s :block block))
      (setf *hooks-last* n))))

(defun hooks-each (kind &rest args)
  (sb-thread:with-recursive-lock (*fold-lock*)
    (dolist (s *hooks*) (apply #'hook-call s kind args))))

(defun make-hooks-event ()
  (let ((open nil) (header nil) (recs '()))
    (lambda (ev)
      (case (car ev)
        (:block-begin (setf open (second ev) header nil recs '()))
        (:hooks-block (setf header (second ev)))
        (:hooks-tx (when open (push (second ev) recs)))
        (:commit (destructuring-bind (n force durable verdict) (cdr ev)
                   (declare (ignore force durable))
                   (when (and open header (= n open) (verdict-passed-p verdict))   ; a refused block: dropped
                     (hooks-deliver header (nreverse recs)))
                   (setf open nil recs '())))
        (:checkpoint (hooks-each :checkpoint (second ev)))
        (:rollback (setf open nil recs '())
         (hooks-rollback (second ev)))
        (:finalize (setf open nil recs '())
         (hooks-each :finalize)
         (sb-thread:with-recursive-lock (*fold-lock*)
           (dolist (s *hooks*) (setf (subscription-started s) nil))))))))

(defun hooks-attach! ()
  (unless *hooks-sub*
    (setf *hooks-sub* (attach-subscriber! "hooks" (make-hooks-event) :rolls-back t))))
