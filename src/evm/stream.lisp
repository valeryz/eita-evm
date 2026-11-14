;;;; evm/stream.lisp — the event stream: one capture, many subscribers, the verifier.

(in-package #:eita.evm)

;;; --- Bounded pipe: one producer thread, one consumer thread ---
;;; Bounded by items (MAX) and, with MAX-BYTES, by the bytes its items are estimated to hold
;;; (an item always enters an empty pipe, so one larger than the bound cannot deadlock).
(defstruct (pipe (:constructor make-pipe (max &optional max-bytes)))
  max max-bytes (lock (sb-thread:make-mutex :name "pipe")) (cv (sb-thread:make-waitqueue))
  (head nil) (tail nil) (count 0 :type fixnum) (bytes 0 :type fixnum)
  (waited 0))                           ; internal real time producers waited on it

(defun pipe-put (p x &optional (bytes 0))
  "Append X, of BYTES (an estimate); wait while P is full."
  (sb-thread:with-mutex ((pipe-lock p))
    (loop while (or (>= (pipe-count p) (pipe-max p))
                    (and (pipe-max-bytes p) (plusp (pipe-bytes p)) (> (+ (pipe-bytes p) bytes) (pipe-max-bytes p))))
          do (let ((t0 (get-internal-real-time)))
               (sb-thread:condition-wait (pipe-cv p) (pipe-lock p))
               (incf (pipe-waited p) (- (get-internal-real-time) t0))))
    (let ((cell (list (cons x bytes))))
      (if (pipe-tail p) (setf (cdr (pipe-tail p)) cell) (setf (pipe-head p) cell))
      (setf (pipe-tail p) cell))
    (incf (pipe-count p))
    (incf (pipe-bytes p) bytes)
    (sb-thread:condition-broadcast (pipe-cv p))))

(defun pipe-take (p)
  "Remove and return the oldest item; wait while P is empty."
  (sb-thread:with-mutex ((pipe-lock p))
    (loop until (pipe-head p) do (sb-thread:condition-wait (pipe-cv p) (pipe-lock p)))
    (let ((e (pop (pipe-head p))))
      (unless (pipe-head p) (setf (pipe-tail p) nil))
      (decf (pipe-count p))
      (decf (pipe-bytes p) (cdr e))
      (sb-thread:condition-broadcast (pipe-cv p))
      (car e))))

;;; --- The event stream: one capture, many subscribers ---------------------------------
;;; The replay thread captures a block's events — fw-push, one hand-over per block at its
;;; commit, (block, txIndex, ordinal) order preserved — and every SUBSCRIBER consumes the
;;; same batches on its own thread off its own bounded pipe (256 blocks and +pipe-bytes+ of
;;; them, estimated: a full pipe blocks the replay, a slow subscriber delays the commit, no
;;; event is ever dropped; a pipe in blocks alone held 0.3 GB of Arc's densest). Observers
;;; (the observation seam, below) attach theirs first, so their view of block N is complete
;;; before anything later claims N. A subscriber that wants read events declares
;;; :on-access; `*capture-reads*` is recomputed at attach, and while it is true the storage
;;; view (every effect-layer access to world state) captures each tx's
;;; reads, writes and deltas (access records, below).
;;;
;;; The VERIFIER, the standing subscriber, runs each block's header check (:verify verdict
;;; check) while the replay runs on, at most 16 blocks behind. Nothing durable claims a
;;; block before its verdict: a layer at N (`stream-checkpoint!`'s waiter) and an observer's
;;; commit of N wait for it. A refusal covers every later block. Reports run on the replay
;;; thread at its next flush (`verifier-note!`).
;;;
;;; Records in a block's buffer, each a code and its fields: an EVENT (+fw-event+, a list):
;;; (:block-begin block) (:verify verdict check) (:commit n force durable verdict) (:checkpoint
;;; n sem) (:rollback n) (:finalize) — (:sync sem) and (:stop) are control messages, outside a
;;; batch; an ACCESS (codes below +fw-event+: op × kind), the storage view's stream, flat (no
;;; list per access): block tx addr slot then value (a :read, a :delta) or pre post (a :write);
;;; a ROW (codes 0…), an observer's (fw-reserve): its columns, `*fw-widths*` long. A subscriber
;;; with :on-access gets (op kind block tx addr slot a b), with :on-row (code vector index end)
;;; and returns the next index; it skips what it has no handler for (fw-walk).
(defconstant +fw-event+ -1 "The record code of one event list (rows have their writer's codes).")
(defvar *fw-widths* (vector)
  "Record width by row code, set by the observer that writes rows (none: no rows).")
(defvar *fw-access-ops* #(:read :write :delta))
(defvar *fw-access-kinds* #(:balance :nonce :code :storage :present :account :codehash :blockhash))
(defstruct (fw-batch (:constructor make-fw-batch (cap &aux (vec (make-array cap)))))
  (vec #() :type simple-vector) (fill 0 :type fixnum))
(defconstant +pipe-bytes+ (* 64 1024 1024) "A subscriber pipe's bound in estimated bytes.")
(defun fw-batch-bytes (b)
  "A batch's heap, estimated: 16 bytes a slot (the word and, on average, what it boxes)."
  (* 16 (fw-batch-fill b)))

(declaim (inline fw-width))
(defun fw-width (code)
  (declare (type fixnum code))
  (cond ((>= code 0) (svref *fw-widths* code)) ((= code +fw-event+) 2) ((<= -17 code -10) 7) (t 6)))

(defun fw-walk (b on-event &key on-access on-row on-error)
  "Each record of the batch B in capture order to its handler (above). ON-ERROR: an access or
   row handler's error is passed to it, and every later access and row skipped; none: raised."
  (let ((v (fw-batch-vec b)) (n (fw-batch-fill b)) (i 0))
    (declare (type simple-vector v) (type fixnum n i))
    (flet ((walk ()
             (loop while (< i n)
                   do (let ((code (svref v i)))
                        (declare (type fixnum code))
                        (cond ((and (>= code 0) on-row) (setf i (funcall on-row code v i n)))
                              (t (cond ((= code +fw-event+) (funcall on-event (svref v (1+ i))))
                                       ((and (< code +fw-event+) on-access)
                                        (multiple-value-bind (op kind) (floor (- -2 code) 8)
                                          (funcall on-access (svref *fw-access-ops* op) (svref *fw-access-kinds* kind)
                                                   (svref v (+ i 1)) (svref v (+ i 2)) (svref v (+ i 3)) (svref v (+ i 4))
                                                   (svref v (+ i 5)) (and (= op 1) (svref v (+ i 6)))))))
                                 (incf i (fw-width code))))))))
      (if on-error
          (loop while (< i n)
                do (handler-case (walk)
                     (error (e) (funcall on-error e) (setf on-access nil on-row nil) (incf i (fw-width (svref v i))))))
          (walk)))))

(defstruct subscriber name pipe thread on-event on-access on-row on-checkpoint on-finalize
  rolls-back (error nil))
(defvar *subscribers* '() "The attached subscribers, an observer's first.")
(defvar *capture-reads* nil "True while some subscriber wants read events.")
(defstartup *readset-dir* (nonempty-env "EITA_READSET_DIR")
  "The read-set recorder's directory (evm/readset.lisp, docs/readset-format.md); NIL: off.")
(declaim (ftype function readset-attach!))
(defvar *fw-batch* (make-fw-batch 4096) "This block's records (replay thread only).")

(declaim (inline fw-reserve))
(defun fw-reserve (n)
  "N slots at the end of this block's buffer: (values vector start)."
  (let* ((b *fw-batch*) (i (fw-batch-fill b)) (v (fw-batch-vec b)))
    (declare (type fixnum i n))
    (when (> (+ i n) (length v))
      (setf v (replace (make-array (* 2 (+ i n))) v :end2 i)
            (fw-batch-vec b) v))
    (setf (fw-batch-fill b) (+ i n))
    (values v i)))

(defun subscriber-loop (sub)
  (labels ((run (ev)
             (case (car ev)
               (:stop (return-from subscriber-loop))
               (:sync (sb-thread:signal-semaphore (second ev)))
               (t (unless (subscriber-error sub)
                    (handler-case
                        (progn (funcall (subscriber-on-event sub) ev)
                               (when (and (eq (car ev) :checkpoint) (subscriber-on-checkpoint sub))
                                 (funcall (subscriber-on-checkpoint sub) (second ev))))
                      (error (e) (fail e))))
                  ;; a checkpoint is acknowledged whatever happened (a failure is re-raised on the
                  ;; replay thread by `check-subscribers`; the waiter must not hang on it)
                  (when (eq (car ev) :checkpoint) (sb-thread:signal-semaphore (third ev))))))
           (fail (e)
             (setf (subscriber-error sub) e)
             (format *error-output* "~&[stream] subscriber ~A failed: ~A~%" (subscriber-name sub) e))
           (records (b)
             (if (subscriber-error sub)
                 (fw-walk b #'run)                ; failed: only the checkpoint acknowledgements
                 (fw-walk b #'run :on-access (subscriber-on-access sub) :on-row (subscriber-on-row sub)
                                  :on-error #'fail))))
    (loop
      (let ((item (pipe-take (subscriber-pipe sub))))
        (if (listp item) (mapc #'run item) (records item))))))

(defun attach-subscriber! (name on-event &key on-access on-row on-checkpoint on-finalize rolls-back (depth 256))
  "Register a consumer of the event stream and start its thread; returns the subscriber.
   DEPTH: the blocks it may lag behind the replay (and at most +pipe-bytes+ of them).
   ON-ACCESS: it takes the storage view's stream. ROLLS-BACK: it handles (:rollback n) (a
   reorg with a subscriber that cannot stops the run instead)."
  (let ((sub (make-subscriber :name name :on-event on-event :on-access on-access :on-row on-row :on-checkpoint on-checkpoint
                              :pipe (make-pipe depth +pipe-bytes+) :on-finalize on-finalize
                              :rolls-back rolls-back)))
    (setf (subscriber-thread sub)
          (sb-thread:make-thread (lambda () (subscriber-loop sub)) :name (format nil "stream ~A" name)))
    (setf *subscribers* (append *subscribers* (list sub))
          *capture-reads* (and (some #'subscriber-on-access *subscribers*) t))
    sub))

;;; --- Verdicts (the verifier's, above) ---
(defstruct (verdict (:constructor make-verdict (block))) block (ok :pending))
(defvar *verdict-lock* (sb-thread:make-mutex :name "verdicts"))
(defvar *verdict-cv* (sb-thread:make-waitqueue))
(defvar *last-verdict* nil "The verdict of the newest block handed to the verifier (replay thread).")
(defvar *verifier-notes* '() "Reports for the replay thread (closures), newest first.")

(defun require-verified (v)
  "Wait for the verdict V (NIL: none to wait for); signal unless it passed."
  (when v
    (sb-thread:with-mutex (*verdict-lock*)
      (loop while (eq (verdict-ok v) :pending) do (sb-thread:condition-wait *verdict-cv* *verdict-lock*)))
    (unless (verdict-ok v)
      (error "block ~D is not verified (it or a block before it did not reproduce its header): nothing durable may claim it"
             (verdict-block v)))))

(defun verifier-note! (report)
  (sb-thread:with-mutex (*verdict-lock*) (push report *verifier-notes*)))

(defun make-verifier-event ()
  "Every verdict resolved, in order; a check that signals is a refusal, reported."
  (let ((refused nil))
    (lambda (ev)
      (when (eq (car ev) :verify)
        (destructuring-bind (v check) (cdr ev)
          (setf refused (or refused
                            (not (handler-case (funcall check)
                                   (error (e) (verifier-note! (lambda () (error "verifying block ~D: ~A" (verdict-block v) e))) nil)))))
          (sb-thread:with-mutex (*verdict-lock*)
            (setf (verdict-ok v) (not refused))
            (sb-thread:condition-broadcast *verdict-cv*)))))))

(defun check-subscribers ()
  "Run the verifier's reports, then re-raise a subscriber's failure, on the replay thread."
  (unless *subscribers*
    (observe attach)                    ; an observer's subscribers first
    (when *readset-dir* (readset-attach!))
    (attach-subscriber! "verifier" (make-verifier-event) :depth 16 :rolls-back t))
  (dolist (report (sb-thread:with-mutex (*verdict-lock*) (reverse (shiftf *verifier-notes* '()))))
    (funcall report))
  (dolist (sub *subscribers*)
    (when (subscriber-error sub)
      (error "subscriber ~A failed: ~A" (subscriber-name sub) (subscriber-error sub)))))

(defun fw-push (ev)
  "Capture the event EV (a list)."
  (multiple-value-bind (v i) (fw-reserve 2)
    (setf (svref v i) +fw-event+ (svref v (1+ i)) ev)))
(defun fw-access! (op kind block tx addr slot a b)
  "Capture an access: OP 0 a read (A the value), 1 a write (A, B before and after), 2 a delta."
  (declare (type (integer 0 2) op))
  (multiple-value-bind (v i) (fw-reserve (if (= op 1) 7 6))
    (setf (svref v i) (- -2 (* 8 op) (position kind *fw-access-kinds*)) (svref v (+ i 1)) block
          (svref v (+ i 2)) tx (svref v (+ i 3)) addr (svref v (+ i 4)) slot (svref v (+ i 5)) a)
    (when (= op 1) (setf (svref v (+ i 6)) b))))

(defun fw-flush ()
  "Hand this block's records to every subscriber (waiting while a pipe is full) as an
   exact-size copy; the capture buffer is cleared and reused, so a block allocates its records
   once (a fresh buffer per block, grown by doubling, allocated ~3x)."
  (check-subscribers)
  (let* ((b *fw-batch*) (n (fw-batch-fill b)) (batch (make-fw-batch 0)))
    (when (plusp n)
      (setf (fw-batch-vec batch) (subseq (fw-batch-vec b) 0 n) (fw-batch-fill batch) n)
      (fill (fw-batch-vec b) 0 :end n)
      (setf (fw-batch-fill b) 0)
      (let ((bytes (fw-batch-bytes batch)))
        (dolist (sub *subscribers*) (pipe-put (subscriber-pipe sub) batch bytes))))))

(defun fw-drain ()
  "Wait until every subscriber has consumed everything captured so far."
  (fw-flush)
  (let ((sems (loop for sub in *subscribers*
                    collect (let ((sem (sb-thread:make-semaphore)))
                              (pipe-put (subscriber-pipe sub) (list (list :sync sem)))
                              sem))))
    (mapc #'sb-thread:wait-on-semaphore sems))
  (check-subscribers))

(defun stream-block-begin! (block)
  "Block BLOCK begins (an observer's subscribers see (:block-begin block))."
  (when *observer* (fw-push (list :block-begin block))))
(defun stream-commit! (n &key force durable)
  "Block N's events to the subscribers (the verifier's too); with an observer, (:commit …)
   carries N's verdict, which the observer waits for before claiming N."
  (when *observer* (fw-push (list :commit n force durable *last-verdict*)))
  (fw-flush))
(defun stream-checkpoint! (n)
  "Block N is a layer point: every subscriber persists its state through N, on its own
   thread, in stream order — the replay does not wait. Returns a function that waits until
   all have and N has verified (the layer writer calls it before publishing the layer at N:
   a durable layer implies them)."
  (let ((v *last-verdict*) (acks nil))
    (when *observer*
      (check-subscribers)
      (let ((sem (sb-thread:make-semaphore)) (k (length *subscribers*)))
        (fw-push (list :checkpoint n sem))
        (fw-flush)
        (setf acks (lambda () (sb-thread:wait-on-semaphore sem :n k)))))
    (lambda () (when acks (funcall acks)) (require-verified v))))
(defun stream-rollback! (n)
  "A reorg rolled the state back to block N: every subscriber rolls back (on its thread,
   after everything captured). A subscriber that cannot stops the run instead of being
   left ahead of the state."
  (when *observer*
    (let ((stuck (mapcar #'subscriber-name (remove-if #'subscriber-rolls-back *subscribers*))))
      (when stuck
        (error "reorg: subscribers ~{~A~^, ~} cannot roll back; restart from an anchor" stuck)))
    (fw-push (list :rollback n))
    (fw-drain)))

(defun stream-finalize! ()
  "End of the stream: every subscriber sees (:finalize) after the last commit, then stops,
   even when the drain raises."
  (unwind-protect (when (or *observer* *subscribers*)
                    (when *observer* (fw-push (list :finalize)))
                    (fw-drain))
    (dolist (sub *subscribers*)
      (when (and (subscriber-on-finalize sub) (not (subscriber-error sub))) (funcall (subscriber-on-finalize sub)))
      (let ((w (pipe-waited (subscriber-pipe sub))))   ; a subscriber that held the replay back
        (when (> w internal-time-units-per-second)
          (format t "~&[stream] the replay waited ~,1F s on subscriber ~A~%" (/ w internal-time-units-per-second) (subscriber-name sub))))
      (pipe-put (subscriber-pipe sub) (list (list :stop)))
      (sb-thread:join-thread (subscriber-thread sub) :default nil))
    (setf *subscribers* '() *capture-reads* nil *last-verdict* nil *verifier-notes* '())))

;; Per-tx state. Pre-images for the net changes; pending transfers and logs. All flat vectors
;; of field values (no list per touch, event or frame); the hash tables only deduplicate.
