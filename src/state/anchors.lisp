;;;; state/anchors.lisp — full-state replay integrity, chain-neutral: the genesis alloc
;;;; (geth genesis.json), the checkpoint schedule (Evm.Trie.CheckpointSchedule), anchors
;;;; (a checkpoint whose state root matched the header, recorded in anchors.sexp).
;;;;
;;;; The persisted state is a base snapshot under a stack of delta layers
;;;; (docs/layered-snapshots.md, snapshot-world.lisp). An ANCHOR freezes the hot set into a
;;;; layer (no pause) and queues a root check of the stack at that block: state/root.lisp
;;;; reads the base plus the layers in a background process, and a passed check records the
;;;; stack's composition in anchors.sexp; a resume maps the newest verified one.
;;;;
;;;; Env: EITA_CHECKPOINT_EVERY: the
;;;; anchor interval; layers are frozen at four times that rate (resume and bisect points).

(in-package #:eita.state)

;; Defined in chains/chain-spec.lisp (the installed chain) and state/snapshot-world.lisp.
(declaim (special *chain-spec* *compactor* *snap-stats*))

(defstartup *checkpoint-every*
  (let ((v (sb-ext:posix-getenv "EITA_CHECKPOINT_EVERY"))) (and v (parse-integer v)))
  "Bring-up / bisect override: when set, checkpoint iff n mod EVERY = 0 (plus block 0).")

;;; --- Full-state mode + integrity checkpoints --------------------------------
;;; EITA_FROM_GENESIS=1 replays with the FULL state: the world is populated from
;;; the chain's genesis alloc (arc-node assets/<net>/genesis.json, vendored in
;;; the cache dir), the lazy RPC hooks stay nil, and on the checkpoint schedule
;;; the state root of the checkpoint's snapshot is compared with the header
;;; stateRoot. Each result is appended to <state-dir>/anchors.sexp as
;;; (block expected computed ok content-hash); a mismatch stops the run loudly
;;; with the range to bisect.
;;;
;;; Fast-forward: Arc has no block rewards and empty blocks leave state
;;; untouched, so a prefix of blocks whose header roots all equal the genesis
;;; root can be skipped — equal roots ⇒ equal state. The driver checks the
;;; header root of the start block's predecessor against the genesis root
;;; before trusting the alloc as the state at `start − 1`.

(defun load-genesis-alloc (world path)
  "Populate WORLD from a geth-style genesis.json alloc. Returns the account count.
   Quantities are 0x-hex or decimal, as geth accepts (Ethereum's genesis is decimal)."
  (let* ((j (jsown:parse (alexandria:read-file-into-string path)))
         (alloc (jval j "alloc")) (n 0))
    (flet ((quantity (s) (if (and (> (length s) 1) (string-equal "0x" s :end2 2))
                             (hex->int s)
                             (parse-integer s))))
    (dolist (k (jsown:keywords alloc))
      (let* ((a (jval alloc k)) (addr (hex->int k))
             (bal (quantity (or (jnonnull (jval a "balance")) "0x0")))
             (nonce (quantity (or (jnonnull (jval a "nonce")) "0x0")))
             (code (jnonnull (jval a "code")))
             (storage (jnonnull (jval a "storage"))))
        (incf n)
        (when (plusp bal) (setf (balance-of world addr) bal))
        (when (plusp nonce) (setf (nonce-of world addr) nonce))
        (when (and code (> (length code) 2))
          (let* ((hex (subseq code 2)) (bytes (make-array (floor (length hex) 2) :element-type '(unsigned-byte 8))))
            (loop for i below (length bytes) do (setf (aref bytes i) (parse-integer hex :start (* 2 i) :end (+ 2 (* 2 i)) :radix 16)))
            (with-acct (tb a) world addr (setf (acct-code tb a) bytes))))
        (when storage
          (dolist (sk (jsown:keywords storage))
            (let ((v (hex->int (jval storage sk))))
              (unless (zerop v) (world-storage-set world addr (hex->int sk) v)))))
        ;; present-but-empty alloc entries still exist in the trie
        (when (and (zerop bal) (zerop nonce) (not (and code (> (length code) 2))))
          (with-acct (tb a) world addr (acct-set-flag! tb a +acct-marked+))))))
    n))

(defun state-dir ()
  "Where anchors, snapshots and root-check markers live: EITA_STATE_DIR (else, for existing
   deployments, EITA_FACTLOG_DIR)."
  (or (let ((d (sb-ext:posix-getenv "EITA_STATE_DIR"))) (and d (plusp (length d)) d))
      (sb-ext:posix-getenv "EITA_FACTLOG_DIR") "/tmp/eita-state/"))

(defun checkpoint-interval (h)
  "Mirror of Evm.Trie.CheckpointSchedule.checkpointInterval: 2^clamp(log2 h − 3, 10, 20)."
  (let* ((l (if (zerop h) 0 (1- (integer-length h))))
         (k (if (< l 3) 10 (min 20 (max 10 (- l 3))))))
    (expt 2 k)))

(defun checkpoint-p (h)
  (or (zerop h) (and (>= h 1024) (zerop (mod h (checkpoint-interval h))))))

(defun anchor-interval (n) (or *checkpoint-every* (checkpoint-interval n)))

(defun anchor-due-p (n)
  (if *checkpoint-every* (or (zerop n) (zerop (mod n *checkpoint-every*))) (checkpoint-p n)))

(defun layer-due-p (n)
  "A layer point that is not an anchor: a quarter of the anchor interval."
  (zerop (mod n (max 1 (floor (anchor-interval n) 4)))))

(defparameter *last-good-anchor* nil)

(defun anchors-path () (merge-pathnames "anchors.sexp" (state-dir)))

(defparameter *pending-root* nil
  "At most one root check in flight: (block expected-hex process out-path composition
   kind start-time) — KIND :stack (an anchor: the stack up to BLOCK) or :base (a compacted base
   snap-BLOCK, which replaces the old base once it passes). Collected later, which only
   changes WHEN a mismatch stops the run.")
(defparameter *anchor-queue* '()
  "Anchors frozen but not yet checked, oldest first: (block expected-hex). An anchor waits
   until its layer is on disk, and at the tip until it is `reorg-window` deep.")
(defparameter *base-check-due* nil "A compacted base (its block) whose check is to start.")
(defun reorg-window ()
  "Blocks a reorg may undo (the chain-spec's; Ethereum finality is two epochs). At the tip
   every block within it is a layer; compaction never touches those layers, and an anchor
   there is root-checked only once its block is this deep."
  (if *chain-spec* (chain-spec-reorg-depth *chain-spec*) 64)) ; @veil reorg-window/depth
(defvar *tip-freeze* nil "True while following the tip: freeze after every block (reorgs).")
(defvar *compacting-base* nil
  "A compacted base waiting for its root check (a snap, opened by the compactor).")
(defvar *no-new-compaction* nil "True while a bounded run winds down: finish, start nothing.")

(defun read-anchors ()
  "The records of anchors.sexp, one per line: (block expected computed ok [dump-fnv]).
   A line that does not read as such a list — the torn tail of a write a crash cut
   short — is skipped, not fatal (invariant I1)."
  (let ((path (anchors-path)))
    (when (probe-file path)
      (with-open-file (a path :direction :input)
        (loop for line = (read-line a nil nil) while line
              for form = (ignore-errors (let ((*read-eval* nil)) (read-from-string line)))
              when (and (consp form) (integerp (first form)) (>= (length form) 4))
                collect form)))))

(defun append-anchor! (record)
  "Append RECORD as one line and fsync it: a verdict is durable before it is acted on."
  (ensure-directories-exist (anchors-path))
  ;; after a torn append the file ends mid-line; without a fresh line this record would
  ;; be glued onto the torn one and skipped with it
  (let ((torn (with-open-file (b (anchors-path) :element-type '(unsigned-byte 8) :if-does-not-exist nil)
                (and b (plusp (file-length b))
                     (progn (file-position b (1- (file-length b))) (/= (read-byte b) 10))))))
    (with-open-file (a (anchors-path) :direction :output :if-exists :append :if-does-not-exist :create)
      (when torn (terpri a))
      (let ((*print-pretty* nil)) (prin1 record a) (terpri a))
      (finish-output a)
      (sb-posix:fsync (sb-sys:fd-stream-fd a)))
    ;; and the file's directory entry: the first append creates anchors.sexp
    (fsync-directory-of (anchors-path))))

(defun anchor-compositions (n)
  "Every composition recorded with a PASSED root check of block N (a block can carry
   several: the stack at N, a base compacted to N, a snapshot re-checked after a copy)."
  (loop for r in (read-anchors)
        when (and (eql (first r) n) (eq (fourth r) t))
          collect (eita.state.snapshot:parse-composition (and (stringp (fifth r)) (fifth r)) n)))

(defun root-strip-0x (hex)
  (let ((h (string-downcase hex)))
    (if (and (> (length h) 2) (string= "0x" (subseq h 0 2))) (subseq h 2) h)))

(defun root-out-path (n) (merge-pathnames (format nil "state-~D.rootout" n) (state-dir)))

(defun root-check-heap-mb ()
  (or (sb-ext:posix-getenv "EITA_ROOT_CHECK_HEAP_MB") "16000"))


(defun prune-dumps! ()
  "Delete what src/state/recovery.lisp's GC rule names (the supervisor uses the same rule):
   every base or layer that no kept resume point (the two newest verified, up to two
   unverified above them) is made of."
  ;; not while a compacted base waits for its root check: no point names it yet
  (unless *compacting-base* ; @veil prune-dumps!/not-compacting
    (let ((gone (eita.state.recovery:run-gc (state-dir) :pinned (live-components))))
      (when gone (format t "~&[anchor] gc: deleted ~{~A~^ ~}~%" gone) (force-output)))))

(defun kill-root-check! ()
  "Stop the root check in flight and forget it: no verdict is recorded, nothing acts on it."
  (let ((p (shiftf *pending-root* nil)))
    (when p
      (ignore-errors (sb-ext:process-kill (third p) 9))
      (sb-ext:process-wait (third p))
      (ignore-errors (delete-file (fourth p))))))

(defun root-check-finish! (&key force)
  "Collect the in-flight root check if it has finished (or FORCE a wait): append
   (N expected computed ok composition) to the anchors file, prune, error on mismatch.
   A passed check of a compacted base makes it the new base. A no-op when nothing is in
   flight, so it is safe to call every block."
  (let ((pending *pending-root*))
    (when (and pending (or force (not (sb-ext:process-alive-p (third pending)))))
      (destructuring-bind (n expected-hex proc out comps kind t0) pending
        ;; a forced wait says so, then every 5 min: the replay is paused, not hung (a
        ;; 25-min check at an x86-64 Linux anchor looked like a stall, 2026-11-01)
        (loop while (sb-ext:process-alive-p proc)
              do (format t "~&[anchor] waiting for the root check of block ~D (pid ~D, running ~D min)~%"
                         n (sb-ext:process-pid proc) (floor (- (get-universal-time) t0) 60))
                 (force-output)
                 (loop repeat 300 while (sb-ext:process-alive-p proc) do (sleep 1)))
        (sb-ext:process-wait proc)
        (setf *pending-root* nil)
        ;; A checker that was KILLED (out of memory, say) is an infrastructure failure,
        ;; not a consensus one: no anchors line, the replay continues, the anchor stays
        ;; unverified, loudly. Only a computed root decides.
        (let* ((code (sb-ext:process-exit-code proc))
               (text (or (ignore-errors
                           (with-open-file (s out :if-does-not-exist nil)
                             (when s (let ((buf (make-string (file-length s))))
                                       (subseq buf 0 (read-sequence buf s))))))
                         ""))
               (cl-root (let ((p (search "CL trie root : " text)))
                          (and p (string-trim '(#\Space #\Newline)
                                              (subseq text (+ p 15) (position #\Newline text :start p))))))
               (ok (and cl-root (string-equal cl-root (root-strip-0x expected-hex))))
               (computed (or cl-root text)))
          ;; `eita check-root` exits 1 on a mismatch, so its root line decides, not the code
          (unless cl-root ; @veil root-check-finish!/norun
            (ignore-errors (delete-file out))
            (format t "~&[anchor] block ~D root check could NOT RUN (eita check-root exited ~A) — not a root mismatch (its stderr: state-~D.rootout.err). Anchor UNVERIFIED, no anchors line written; replay continues.~%"
                    n code n)
            (force-output)
            (when (eq kind :base)                                 ; a later compaction retries; @veil root-check-finish!/norun-base
              (eita.state.snapshot:snap-close (shiftf *compacting-base* nil)))
            (prune-dumps!)
            (return-from root-check-finish! nil))
          (ignore-errors (delete-file out))
          ;; the composition rides with the verdict: resume maps only the exact bytes whose
          ;; root was checked (I3)
          (append-anchor! (list n expected-hex computed (if ok t nil) (eita.state.snapshot:composition-string comps)))
          (format t "~&[anchor] block ~D~:[~; (compacted base)~] root ~A ~A~%" n (eq kind :base)
                  (if ok "OK" "MISMATCH") (string-trim '(#\Newline) text))
          (force-output)
          (unless ok ; @veil root-check-finish!/mismatch
            (error "state-root MISMATCH at block ~D~:[~; in a COMPACTED BASE (the stack checked fine: a compaction bug)~] (last good anchor ~A): densify+bisect the range ~A..~D"
                   n (eq kind :base) *last-good-anchor* *last-good-anchor* n))
          (if (eq kind :base) ; @veil root-check-finish!/swap
              (compaction-swap! n)
              (setf *last-good-anchor* n))
          (prune-dumps!)
          t)))))

(defparameter *mpt-armed* nil
  "Incremental state-root validation (src/state/mpt-live.lisp, #237): the account trie
   maintained per block on a worker thread. Never T today — chains/driver.lisp refuses
   to arm it until step F gives it the snapshot (seeding and the anchor verdict); the
   per-block hook sites stay wired on this flag.")

(defun drop-stale-rootouts! ()
  "A pending root check cannot survive a restart, so its marker is noise on startup —
   and a monitor reading those markers would report a check as running."
  (dolist (p (directory (merge-pathnames "state-*.rootout" (state-dir))))
    (ignore-errors (delete-file p)))
  ;; a snapshot or layer directory never renamed into place, or one moved aside, is one a
  ;; crash interrupted: never a resume point
  (dolist (p (loop for pat in '(".tmp-snap-*/" ".old-snap-*/" ".tmp-layer-*/" ".old-layer-*/" ".root-*/")
                   append (directory (merge-pathnames pat (state-dir)))))
    (format t "~&[anchor] removing interrupted ~A~%" (namestring p))
    (sb-ext:run-program "rm" (list "-rf" (string-right-trim "/" (namestring p))) :search t)))

(defun root-check-threads ()
  "The checker shares the machine with the replay: half the hardware threads, at most 16
   (the streaming passes gain little past that; 30 on a 30-thread box contended with the
   replay)."
  (max 1 (min 16 (floor (eita.state.snapshot:hardware-threads) 2))))

(defun root-check-executable ()
  "The program that runs `eita check-root`: this executable when the engine runs as bin/eita,
   else the bin/eita built beside the sources (a replay started from a REPL)."
  (let ((exe (if *image-p* sb-ext:*runtime-pathname* (eita-file "bin/eita"))))
    (unless (probe-file exe)
      (error "the root check runs `eita check-root`, and ~A does not exist: build it (./build.sh)" exe))
    (namestring exe)))

(defun root-check-command (argv)
  "The program and arguments that run ARGV (the checker's own command line) at background priority:
   the root check reads the whole state from disk while the replay runs, and on a busy disk it must
   not take the replay's reads' place (GCP 2026-11-04: the replay fell behind during a root check).
   On Linux, through `ionice -c2 -n7` (best effort, lowest; not idle, which a busy replay could
   starve) and `nice -n 10`, when ionice exists; elsewhere ARGV as is."
  (if (and (member :linux *features*) (probe-file "/usr/bin/ionice") (probe-file "/usr/bin/nice"))
      (values "/usr/bin/ionice" (append (list "-c2" "-n7" "/usr/bin/nice" "-n" "10") argv))
      (values (first argv) (rest argv))))

(defun snapshot-root-proc (dirs out)
  "`eita check-root` (state/root.lisp) over DIRS (a base, then layers oldest first), in the
   background. The checker exits when this process does (--parent), and its output files
   are fresh inodes: a checker left from a previous life of the replay can write to neither."
  (ignore-errors (delete-file out))
  (ignore-errors (delete-file (concatenate 'string out ".err")))
  (multiple-value-bind (program args)
      (root-check-command (append (list (root-check-executable)
                                        "--dynamic-space-size" (root-check-heap-mb) "--end-runtime-options"
                                        "check-root" "--parent" (princ-to-string (sb-posix:getpid)))
                                  dirs (list (princ-to-string (root-check-threads)))))
    (sb-ext:run-program program args
                      :search t :output out :if-output-exists :supersede :wait nil
                      ;; stderr beside the verdict: a checker that dies says why (state-N.rootout.err)
                      :error (concatenate 'string (namestring out) ".err") :if-error-exists :supersede)))

(defun spawn-root-check! (n expected-hex comps kind)
  (let ((out (namestring (root-out-path n))))
    (setf *pending-root*
          (list n expected-hex (snapshot-root-proc (composition-dirs comps) out) out comps kind (get-universal-time)))
    (format t "~&[anchor] block ~D: root check of ~A running in the background~%" n
            (eita.state.snapshot:composition-string comps))
    (force-output)))

(defun root-check-poll! (n)
  "Every block (replay thread): take finished background work into the stack (a written
   layer, a compaction), collect a finished root check, start the next one, prune."
  (writer-check!)
  (root-check-finish!)
  (let ((m (compaction-step! n (mapcar #'first *anchor-queue*)))) ; @veil root-check-poll!/compact
    (when m (setf *base-check-due* m)))
  (unless *pending-root* ; @veil root-check-poll!/idle
    (if *base-check-due* ; @veil root-check-poll!/base-due
        (let* ((m (shiftf *base-check-due* nil))
               (path (eita.state.snapshot:snap-path (snapshot-dir) m))
               (manifest (eita.state.snapshot:read-manifest path)))
          (spawn-root-check! m (getf manifest :state-root) ; @veil root-check-poll!/manifest-root
                             (list (list :base m (getf manifest :content-hash))) :base))
        (let ((a (first *anchor-queue*))) ; @veil root-check-poll!/anchor
          (when a
            (destructuring-bind (b expected) a
              (let ((comps (and (or (not *tip-freeze*) (>= n (+ b (reorg-window))))
                                (stack-composition b)))) ; @veil root-check-poll!/compose
                (when comps
                  (pop *anchor-queue*)
                  (spawn-root-check! b expected comps :stack)))))))) ; @veil root-check-poll!/spawn-stack
  (close-retired!)
  (collect-written!))

(defun finish-anchors! (n)
  "A bounded run ends on its anchors' verdicts: every frozen layer written, every queued
   root check run (a compaction already running finishes; none starts)."
  (let ((*no-new-compaction* t) (*tip-freeze* nil))
    (writer-drain!)
    (loop
      (root-check-poll! n)
      (when (and (null *pending-root*) (null *anchor-queue*) (null *base-check-due*)
                 (null *compactor*) (null *compacting-base*))
        (return))
      (when *pending-root* (root-check-finish! :force t))
      (sleep 0.05))))

(defun anchor! (world n expected-hex &key (anchor t))
  "Block N is a layer point: the stream's subscribers checkpoint at N (its prefixes are durable before
   the layer is: the writer waits for them) and the hot set is frozen as the layer at N;
   with ANCHOR its root check is queued. The replay waits for neither."
  (let ((t0 (get-internal-real-time)) (hot (acct-table-faulted (world-accts world))))
    (freeze! world n expected-hex (stream-checkpoint! n))
    (let ((ms (/ (* 1000.0 (- (get-internal-real-time) t0)) internal-time-units-per-second)))
      (incf (getf *snap-stats* :freeze-ms 0) ms)
      (when (or anchor (not *tip-freeze*))
        (format t "~&[layers] block ~D frozen~:[~; (anchor)~] in ~,1F ms (~D accounts hot)~%" n anchor ms hot)
        (force-output))))
  (when anchor
    (setf *anchor-queue* (append *anchor-queue* (list (list n expected-hex))))))

(defun root-check! (n expected-hex comps)
  "Synchronous root check of the composition COMPS at block N: the genesis anchor and an
   unanchored resume point, where the run must not proceed on an unverified state."
  (root-check-finish! :force t)
  (spawn-root-check! n expected-hex comps :stack)
  (root-check-finish! :force t)
  (unless (member comps (anchor-compositions n) :test #'equalp)
    (error "state-root check at block ~D did not pass (see [anchor] above); refusing to run on an unverified state" n)))

;;; The layered world: snapshot.lisp + the stack, the writer and the compactor.
