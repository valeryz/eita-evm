;;;; state/snapshot-world.lisp — the replay's world over a LAYERED snapshot (docs/layered-snapshots.md;
;;;; format: docs/state-snapshot-format.md; Lean: lean/Evm/Persist/Layered.lean).
;;;;
;;;; Tiers, newest first:
;;;;   HOT     the world's hash tables: every account or slot touched since the last freeze,
;;;;           faulted on first touch (`snap-fault-account` / `snap-fault-slot`, the same seam
;;;;           as the lazy-RPC replays) and authoritative from then on;
;;;;   FROZEN  RAM layers: hot sets frozen at a layer point, read-only, being written out;
;;;;   LAYERS  layer-P-N/ directories (mmapped): what blocks P+1..N changed;
;;;;   BASE    snap-B/ (mmapped): the full state at B.
;;;; A FREEZE (a layer point: an anchor, a quarter of the anchor interval, the hot budget, or
;;;; every block at the tip) makes the hot set the newest frozen layer and starts an empty
;;;; one — O(1), the replay does not wait. A writer thread turns frozen layers into layer
;;;; directories (oldest first); a compactor thread folds old layers into one (minor) or into
;;;; a new base (major, root-checked before it replaces the old one). A reorg drops the
;;;; layers above the fork point (`rollback-to!`). Reads walk the stack through one reader
;;;; (`eita.state.snapshot::view-*`), with frozen RAM layers answering through *FOREIGN-LAYER*.

(in-package #:eita.state)

;; Defined in chains/chain-spec.lisp.
(declaim (special *chain-id*))

(defvar *base* nil "The base snapshot under the stack (eita.state.snapshot:snap), or NIL.")
(defvar *layers* '()
  "The stack above *BASE*, newest first: RAM-LAYER structs (frozen, not yet on disk), then
   layer snaps. Replaced, never mutated, under *STACK-LOCK*; read without it (a list) by
   the replay thread's faults. So every publication is preceded by a write barrier: the
   new conses (and the snap they name) are visible before the pointer to them on weakly
   ordered ARM64; a reader's loads through the pointer are address-dependent, which ARM64
   orders without a read barrier (SBCL's :data-dependency barrier is a no-op there).
   A reader that reads it twice (and needs one stack) takes the lock: `live-components`.")
(defvar *stack-lock* (sb-thread:make-mutex :name "layer stack"))

(defvar *code-intern* (make-hash-table :test 'eql :weakness :value)
  "codehash -> the one code vector for it (P4: proxies and clones share one copy). Weak
   on the value and kept across freezes: a code stays shared while anything — the world,
   the JIT cache's key — still holds it.")
(defvar *snap-stats* (list :acct-faults 0 :slot-faults 0 :freezes 0))

(defconstant +max-layers+ 16 "Over this many layers on disk, eight of them are composed into one (`minor-run`).")


(defun snapshot-dir () (state-dir))

(defun intern-code (hash code)
  (or (gethash hash *code-intern*) (setf (gethash hash *code-intern*) code)))

(defun layer-block (l) (if (eita.state.snapshot:snap-p l) (eita.state.snapshot:snap-block l) (ram-layer-block l)))
(defun stack-top-block ()
  (let ((l (first *layers*))) (if l (layer-block l) (and *base* (eita.state.snapshot:snap-block *base*)))))

;;; ---------------------------------------------------------------- frozen RAM layers

(defstruct ram-layer
  block parent root
  accts                                 ; the frozen hot set (an ACCT-TABLE): faulted, wiped bits
  ready                                 ; NIL, or a function that waits for the stream's checkpoint at BLOCK
  (bytes 0))                            ; ACCTS' memory, heap and native (`acct-table-bytes`)

(defun ram-layer-op (op l &rest args)
  "The reader's protocol (eita.state.snapshot:*foreign-layer*) for a frozen RAM layer. An account
   is in the layer when it was faulted there; a slot when its key is present (a lazy
   world keeps faulted zeros)."
  (ecase op
    (:account
     (let* ((tb (ram-layer-accts l)) (a (acct-table-find tb (first args))))
       (if (and (>= a 0) (acct-flag-p tb a +acct-faulted+))
           (let ((code (acct-code-entry tb a)))
             (values t (acct-nonce tb a) (acct-balance tb a)
                     (world-code-hash code) (acct-flag-p tb a +acct-marked+) code))
           nil)))
    (:slot
     (destructuring-bind (addr slot) args
       (let* ((tb (ram-layer-accts l)) (a (acct-table-find tb addr)))
         (multiple-value-bind (v present) (if (>= a 0) (acct-slot-get tb a slot) (values 0 nil))
           (if present
               (values t v nil)
               (values nil 0 (and (>= a 0) (acct-flag-p tb a +acct-wiped+))))))))
    (:map-slots
     (destructuring-bind (addr fn) args
       (let* ((tb (ram-layer-accts l)) (a (acct-table-find tb addr)))
         (when (>= a 0) (acct-slots-map fn tb a))
         (and (>= a 0) (acct-flag-p tb a +acct-wiped+)))))
    (:code nil)))                       ; codes come with their account (CODE above)

(setf eita.state.snapshot:*foreign-layer* #'ram-layer-op)

;;; ---------------------------------------------------------------- faults

(defun snap-fault-account (addr)
  "The fault hook: ADDR's fields from the stack (fault-account! called it on the account's
   first touch)."
  (incf (getf *snap-stats* :acct-faults))
  (multiple-value-bind (found nonce balance codehash exists-empty code)
      (eita.state.snapshot:view-account *layers* *base* addr)
    (when found
      (with-acct (tb a) *current-world* addr
        (when (plusp nonce) (setf (acct-nonce tb a) nonce))
        (when (plusp balance) (setf (acct-balance tb a) balance))
        (unless (= codehash eita.state.snapshot:+empty-code-hash+)
          (setf (acct-code tb a)
                (or code
                      (gethash codehash *code-intern*)
                      (let ((code (eita.state.snapshot:view-code *layers* *base* codehash)))
                        (unless code
                          (error "account ~X names code ~X that no layer and no base holds" addr codehash))
                        ;; seed the JIT cache's memo: no keccak for code read by hash
                        (setf (gethash code *code-hash-memo*) codehash)
                        (intern-code codehash code)))))
        (when exists-empty (acct-set-flag! tb a +acct-marked+))))))

(defun snap-fault-slot (addr slot)
  "A slot is faulted iff its key is present in ADDR's packed table (P5; fault-slot! calls
   this for an absent key only): the value read from the stack is installed even when it
   is 0, and stays present when set to 0."
  (with-acct (tb a) *current-world* addr
    (incf (getf *snap-stats* :slot-faults))
    (acct-slot-put! tb a slot (if (acct-flag-p tb a +acct-wiped+) 0 (eita.state.snapshot:view-slot *layers* *base* addr slot)))))

(defun snap-wipe (addr) (with-acct (tb a) *current-world* addr (acct-set-flag! tb a +acct-wiped+)))

(defun snap-cold-storage-map (addr fn)
  "FN (slot value) for every nonzero slot of ADDR below the hot set that the hot set has
   not faulted (and so not overridden), unless ADDR's storage was wiped since the freeze."
  (with-acct (tb a) *current-world* addr
   (unless (acct-flag-p tb a +acct-wiped+)
    (eita.state.snapshot:view-map-account-storage
     *layers* *base* addr (lambda (slot v)
                            (unless (acct-slot-present-p tb a slot)
                              (funcall fn slot v)))))))

(defun clear-hot! (world)
  "An empty hot set (fresh tables: the old ones may be a frozen layer now)."
  (forget-tx-sets!)
  (setf (world-accts world) (make-acct-table)))

(defun back-world! (world base layers)
  "Make BASE under LAYERS (newest first) the cold tiers of WORLD: an empty hot set, the
   fault hooks installed."
  (clear-hot! world)
  (sb-thread:with-mutex (*stack-lock*)
    (sb-thread:barrier (:write))
    (setf *base* base *layers* layers))
  (setf *keep-zero-slots* t
        *fault-account-hook* #'snap-fault-account
        *fault-slot-hook* #'snap-fault-slot
        *storage-wipe-hook* #'snap-wipe
        *cold-storage-map-hook* #'snap-cold-storage-map)
  ;; give a dropped hot set back to the OS now (2 GB -> 48 MB measured on x86-64 Linux)
  (sb-ext:gc :full t))

(defun world-code-hash (code)
  "keccak of CODE as an integer (memoized: replay thread only)."
  (if (and code (plusp (length code))) (code-hash-int code) eita.state.snapshot:+empty-code-hash+))

(defun fresh-code-hash (code)
  "keccak of CODE, without the replay thread's memo (any thread)."
  (if (and code (plusp (length code)))
      (eita.state.snapshot:octets->int (keccak256-bytes code))
      eita.state.snapshot:+empty-code-hash+))

;;; ---------------------------------------------------------------- writing RAM tables

(defun write-ram-tables (l below-layers below-base &key full)
  "Write the RAM layer L: FULL, the base snap-N of a world that is all in RAM (genesis);
   else the layer layer-P-N over the stack BELOW-LAYERS (disk, newest first) on
   BELOW-BASE. Every address a layer mentions gets its fields (FieldsCover): from RAM when
   faulted, else from the stack below. Codes the stack below already holds are not
   repeated. Publishes it and returns the open snap."
  (let* ((dir (snapshot-dir)) (n (ram-layer-block l)) (p (ram-layer-parent l)) (tb (ram-layer-accts l))
         (tmp (if full (eita.state.snapshot:snap-tmp-path dir n) (eita.state.snapshot:layer-tmp-path dir p n)))
         (final (if full (eita.state.snapshot:snap-path dir n) (eita.state.snapshot:layer-path dir p n)))
         (recs '()) (codes (make-hash-table :test 'eql)))
    (when (probe-file tmp) (sb-ext:run-program "rm" (list "-rf" (namestring tmp)) :search t))
    ;; the addresses the layer mentions: in a full world every account with an entry, in a
    ;; layer every faulted one, every one whose storage was touched or wiped
    (map-accts (lambda (r)
                 (when (if full
                           (or (not (eql 0 (acct-balance tb r))) (not (eql 0 (acct-nonce tb r)))
                               (acct-code-entry tb r) (acct-slots tb r) (acct-flag-p tb r +acct-marked+))
                           (or (acct-flag-p tb r (logior +acct-faulted+ +acct-wiped+)) (acct-slots tb r)))
                   (push r recs)))
               (ram-layer-accts l))
    (let ((m (eita.state.snapshot:make-merge tmp *chain-id* n (ram-layer-root l) nil :parent (and (not full) p))))
      (dolist (r (sort recs #'< :key (lambda (r) (acct-addr tb r))))
        (let* ((a (acct-addr tb r))
               (code (acct-code-entry tb r))
               (fields
                 (if (or full (acct-flag-p tb r +acct-faulted+))
                     (let ((h (fresh-code-hash code)))
                       (when (and code (plusp (length code)) (not (gethash h codes))
                                  (or full (not (eita.state.snapshot:view-code below-layers below-base h))))
                         (setf (gethash h codes) code))
                       (list (acct-nonce tb r) (acct-balance tb r) h (acct-flag-p tb r +acct-marked+)))
                     ;; storage touched, account never faulted: its fields as they are below
                     (multiple-value-bind (found nonce balance codehash flag)
                         (eita.state.snapshot:view-account below-layers below-base a)
                       (if found (list nonce balance codehash flag) (list 0 0 eita.state.snapshot:+empty-code-hash+ nil)))))
               (slots (let ((kv '()))
                        (acct-slots-map (lambda (k v) (push (cons k v) kv)) tb r)
                        (sort kv #'< :key #'car))))
          (eita.state.snapshot:merge-account m a :fields fields :slots slots :wiped (acct-flag-p tb r +acct-wiped+))))
      (eita.state.snapshot:merge-finish m (loop for h being the hash-keys of codes using (hash-value c) collect (cons h c))
                              :provenance (format nil "eita ~:[layer ~D-~D~;base ~*~D~], code ~A"
                                                  full p n (engine-code-version)))
      ;; the subscribers' state at N is durable before the layer at N is (I5 with layers)
      (when (ram-layer-ready l) (funcall (ram-layer-ready l)))
      (eita.state.snapshot:snap-publish dir n tmp :final final)
      (eita.state.snapshot:snap-open final))))

;;; ---------------------------------------------------------------- the writer thread

(defvar *compactor* nil "The compaction thread while a job runs.")
(defvar *compactor-job* nil "(:minor run parent block) or (:major layers block root): the running job.")
(defvar *compactor-result* nil "The finished job's result, for the replay thread.")
(defvar *compactor-error* nil)
(defvar *writer* nil)
(defvar *writer-pipe* nil "Frozen RAM layers to write, oldest first (bounded: back-pressure).")
(defvar *writer-busy* nil "True from taking a layer until it is on disk and in the stack.")
(defvar *writer-error* nil)
(defvar *retired* '() "Snaps swapped out of the stack, closed once no thread can be reading them.")
(defvar *written* '()
  "Frozen RAM layers the writer has put on disk since the last `collect-written!` (out of
   the stack: no reader can reach them), and the memory their tables hold: (bytes . layers).")

(defun stack-below (l)
  "The disk layers below L in the stack, newest first."
  (rest (member l *layers*)))

(defun write-layer! (l)
  (let (below base)
    (sb-thread:with-mutex (*stack-lock*)
      (setf *writer-busy* t below (stack-below l) base *base*))
    (when (some #'ram-layer-p below) (error "writer: a RAM layer below ~D" (ram-layer-block l)))
    (let ((snap (write-ram-tables l below base)))
      (sb-thread:with-mutex (*stack-lock*)
        (let ((new (substitute snap l *layers*)))
          (sb-thread:barrier (:write))
          (setf *layers* new *writer-busy* nil
                *written* (cons (+ (ram-layer-bytes l) (or (car *written*) 0)) (cons l (cdr *written*)))))))))

(defun collect-written! ()
  "Replay thread, between blocks: once the tables of the layers written since the last call
   hold a quarter of the state budget (`*hot-budget-bytes*`), drop them and run a full GC.
   Without it the dead hot sets are promoted with the live data (13.8 GB of them in gen 5
   against a live hot set of 3.5 GB, 250k blocks into a life at Ethereum 14.0M) and stay
   until those generations' rare collections, scattered over the heap; SBCL's large
   allocations search only upward from the highest page allocated since the last GC, so
   at 33-50 % heap use they found no free run of 64 KB-38 MB (four production deaths).
   Counted in the tables' memory, heap and native, not in their layers' bytes on disk: at
   the tip (a layer per block, Ethereum 25M) a block's layer is 0.27 MB on disk and its
   table 0.5 MB of heap plus 0.28 MB of native slot tables (0.8 MB of heap before those),
   so the old trigger, a quarter of the nursery in disk bytes, let 1.8 GB pile up at a
   10 GB heap and twice that at 20 GB, the native part unseen. The tables are cut loose first: the writer's stack may still hold the struct (a
   conservative root); their native slot tables go with them (finalizers). A full GC at
   ~2 GB live costs 1-2 s."
  (let ((w (and *written* (>= (car *written*) (floor (hot-budget-bytes) 4))
                (sb-thread:with-mutex (*stack-lock*) (shiftf *written* '())))))
    (when w
      (dolist (l (cdr w)) (setf (ram-layer-accts l) nil))
      (sb-ext:gc :full t)
      (format t "~&[layers] dropped ~D written hot sets (~,1F MB); heap ~,1F MB after a full GC~%"
              (length (cdr w)) (/ (car w) 1048576.0) (/ (sb-kernel:dynamic-usage) 1048576.0))
      (force-output))))

(defun writer-loop ()
  (loop
    (let ((l (pipe-take *writer-pipe*)))
      (when (eq l :stop) (return))
      (unless *writer-error*
        (handler-case (write-layer! l)
          (error (e)
            (setf *writer-error* e *writer-busy* nil)
            (format *error-output* "~&[layers] writing layer ~D failed: ~A~%" (ram-layer-block l) e)))))))

(defun ensure-writer! ()
  (unless *writer*
    (setf *writer-pipe* (make-pipe 4))
    (setf *writer* (sb-thread:make-thread #'writer-loop :name "layer writer"))))

(defun writer-check! ()
  (when *writer-error* (error "layer writer failed: ~A" *writer-error*))
  (when *compactor-error* (error "compaction failed: ~A" *compactor-error*)))

(defun writer-idle-p ()
  (and (not *writer-busy*) (or (null *writer-pipe*) (zerop (pipe-count *writer-pipe*)))
       (notany #'ram-layer-p *layers*)))

(defun writer-drain! ()
  "Wait until every frozen layer is on disk."
  (loop until (or (writer-idle-p) *writer-error*) do (sleep 0.01))
  (writer-check!))

(defun freeze! (world n root-hex &optional ready)
  "Block N's state becomes the newest layer: the hot set is frozen as a RAM layer (handed
   to the writer) and the world continues on an empty one. O(1); waits only when four
   frozen layers are already queued (bounded memory)."
  (ensure-writer!)
  (let ((l (make-ram-layer :block n :parent (stack-top-block) :root root-hex
                           :accts (world-accts world) :ready ready
                           :bytes (multiple-value-call #'+ (acct-table-bytes (world-accts world))))))
    (clear-hot! world)
    (sb-thread:with-mutex (*stack-lock*)
      (let ((new (cons l *layers*))) (sb-thread:barrier (:write)) (setf *layers* new)))
    (incf (getf *snap-stats* :freezes))
    (pipe-put *writer-pipe* l)
    l))

(defun stack-composition (n)
  "The composition of the state at layer boundary N: the base and the disk layers up to N,
   oldest first (`eita.state.snapshot:composition-string`). NIL when N is not a boundary of the
   current stack or a layer up to it is still in RAM."
  (let ((ls (member n *layers* :key #'layer-block)))
    (cond ((and ls (notany #'ram-layer-p ls))
           (cons (eita.state.snapshot:component-of *base*) (reverse (mapcar #'eita.state.snapshot:component-of ls))))
          ((and (null *layers*) *base* (eql n (eita.state.snapshot:snap-block *base*)))
           (list (eita.state.snapshot:component-of *base*))))))

(defun live-components ()
  "What GC must not delete under the replay, as recovery.lisp names files: the running
   stack's disk components, its frozen RAM layers (the writer publishes layer-P-N/ before
   the snap replaces the RAM layer in the stack: unpinned, a GC in that window deleted the
   layer under the writer — `rename: No such file`, the replay died; Arc stress, 2026-11-08),
   a compaction's output (written, not yet in the stack) and what the root check in flight
   reads (a minor compaction may have replaced it in the stack).
   One read of the stack, under *STACK-LOCK*: read twice, it was correct only because
   APPEND reads the RAM layers before the snaps; in the other order the writer's swap of
   layer N between the two reads drops N from both (a Veil protocol model, 10 steps)."
  (multiple-value-bind (base layers)
      (sb-thread:with-mutex (*stack-lock*) (values *base* *layers*))
   (append
    (loop for l in layers when (ram-layer-p l) collect (list :layer (ram-layer-parent l) (ram-layer-block l)))
    (mapcar (lambda (c) (subseq c 0 (1- (length c))))
            (append (mapcar #'eita.state.snapshot:component-of (remove-if-not #'eita.state.snapshot:snap-p (cons base layers)))
                    (and *pending-root* (fifth *pending-root*))))
    (and *compacting-base* (list (list :base (eita.state.snapshot:snap-block *compacting-base*))))
    (and *compactor-job*
         (ecase (first *compactor-job*)
           (:minor (list (list :layer (third *compactor-job*) (fourth *compactor-job*))))
           (:major (list (list :base (third *compactor-job*)))))))))

(defun composition-dirs (comps)
  (mapcar (lambda (c) (string-right-trim "/" (namestring (eita.state.snapshot:component-path (snapshot-dir) c)))) comps))

;;; ---------------------------------------------------------------- compaction


(defun layer-bytes (s) (reduce #'+ (getf (eita.state.snapshot:snap-manifest s) :files) :key #'second))

(defun start-compaction! (job)
  (format t "~&[layers] ~(~A~) compaction of ~D layers to block ~D started~%"
          (first job) (length (second job)) (car (last job)))
  (force-output)
  (setf *compactor-job* job *compactor-result* nil)
  (let ((base *base*))
    (setf *compactor*
          (sb-thread:make-thread
           (lambda ()
             (handler-case
                 (let ((dir (snapshot-dir)))
                   (setf *compactor-result*
                         (ecase (first job)
                           (:minor
                            (destructuring-bind (run p n) (rest job)
                              (let ((tmp (eita.state.snapshot:layer-tmp-path dir p n)) (fin (eita.state.snapshot:layer-path dir p n)))
                                (when (probe-file tmp) (sb-ext:run-program "rm" (list "-rf" (namestring tmp)) :search t))
                                (eita.state.snapshot:write-composed tmp *chain-id* n (getf (eita.state.snapshot:snap-manifest (first run)) :state-root)
                                                          run nil :parent p
                                                          :provenance (format nil "eita minor compaction ~D-~D, code ~A" p n (engine-code-version)))
                                (eita.state.snapshot:snap-publish dir n tmp :final fin)
                                (list :minor run (eita.state.snapshot:snap-open fin)))))
                           (:major
                            (destructuring-bind (run n) (rest job)
                              (let ((tmp (eita.state.snapshot:snap-tmp-path dir n)))
                                (when (probe-file tmp) (sb-ext:run-program "rm" (list "-rf" (namestring tmp)) :search t))
                                (eita.state.snapshot:write-composed tmp *chain-id* n (getf (eita.state.snapshot:snap-manifest (first run)) :state-root)
                                                          run base
                                                          :provenance (format nil "eita major compaction to ~D over ~D, code ~A"
                                                                              n (eita.state.snapshot:snap-block base) (engine-code-version)))
                                (eita.state.snapshot:snap-publish dir n tmp)
                                ;; opened here: its fence is built off the replay thread
                                (list :major run (eita.state.snapshot:snap-open (eita.state.snapshot:snap-path dir n)))))))))
               (error (e)
                 (setf *compactor-error* e)
                 (format *error-output* "~&[layers] compaction ~S failed: ~A~%" (subseq job 0 1) e))))
           :name "layer compactor"))))

(defun minor-run (eligible)
  "From ELIGIBLE (the oldest layers, oldest first), of the runs of eight consecutive layers
   within a factor of eight of each other in bytes, the one with the fewest bytes (the
   oldest on a tie), newest first; with none and more than twice +MAX-LAYERS+ eligible, the
   fewest-bytes run whatever its sizes (progress). NIL when nothing is due. Tiered by size,
   not span: a composition (about eight times its inputs) waits for peers before it is
   rewritten, and layers of mixed spans (budget freezes between quarter points, per-block
   layers at the tip) do not starve it."
  (when (>= (length eligible) 8)
    (let* ((v (coerce eligible 'vector)) (bytes (map 'vector #'layer-bytes v))
           (tiered nil) (tiered-sum nil) (any nil) (any-sum nil))
      (loop for i from 0 to (- (length v) 8)
            for w = (subseq bytes i (+ i 8))
            for sum = (reduce #'+ w)
            do (when (or (null any-sum) (< sum any-sum)) (setf any i any-sum sum))
               (when (and (<= (reduce #'max w) (* 8 (max 1 (reduce #'min w))))
                          (or (null tiered-sum) (< sum tiered-sum)))
                 (setf tiered i tiered-sum sum)))
      (let ((i (or tiered (and (> (length v) (* 2 +max-layers+)) any))))
        (and i (reverse (coerce (subseq v i (+ i 8)) 'list)))))))

(defun compaction-step! (n pending-anchors)
  "Replay thread, between blocks: take a finished job's result into the stack, and start
   the next job when one is due. PENDING-ANCHORS: blocks whose root checks are still to
   run (they must stay layer boundaries). Returns a block whose compacted base needs its
   root check, or NIL."
  (when (and *compactor* (not (sb-thread:thread-alive-p *compactor*)))
    (sb-thread:join-thread *compactor* :default nil)
    (setf *compactor* nil)
    (writer-check!)
    (let ((r *compactor-result*))
      (setf *compactor-job* nil *compactor-result* nil)
      (ecase (first r)
        (:minor
         (destructuring-bind (run composed) (rest r)
           (sb-thread:with-mutex (*stack-lock*)
             (let* ((pos (position (first run) *layers*))
                    (new (append (subseq *layers* 0 pos) (list composed) (nthcdr (+ pos (length run)) *layers*))))
               (sb-thread:barrier (:write))
               (setf *layers* new)))
           (setf *retired* (append run *retired*))
           (format t "~&[layers] composed ~D layers into layer-~D-~D~%" (length run)
                   (eita.state.snapshot:snap-parent composed) (eita.state.snapshot:snap-block composed))
           (prune-dumps!)))
        (:major
         ;; the new base replaces the old one only once its own root check passed
         (setf *compacting-base* (third r))
         (return-from compaction-step! (eita.state.snapshot:snap-block (third r)))))))
  (unless (or *compactor* *compacting-base* *no-new-compaction*)
    (let* ((disk (remove-if #'ram-layer-p *layers*))          ; newest first
           (old (reverse disk))
           (horizon (- n (reorg-window)))
           (fence (and pending-anchors (reduce #'min pending-anchors))))
      (let ((run (and (> (length disk) +max-layers+)
                      (minor-run (loop for l in old
                                       while (and (<= (eita.state.snapshot:snap-block l) horizon)
                                                  (or (null fence) (<= (eita.state.snapshot:snap-block l) fence)))
                                       collect l)))))
        (cond
          ;; minor (size-tiered, `minor-run`): over +max-layers+ on disk, eight consecutive
          ;; layers of like size composed into one, never past a pending anchor or into the
          ;; reorg window — the stack stays shallow for reads whatever the layers' spans
          (run                                  ; RUN: newest first
           (start-compaction! (list :minor run (eita.state.snapshot:snap-parent (car (last run)))
                                    (eita.state.snapshot:snap-block (first run)))))
          ;; major: the layers outweigh an eighth of the base. Strictly below a queued
          ;; anchor: a base AT it would take the anchor's boundary out of the stack before
          ;; its own check, which then never runs (`stack-composition` NIL; the twin)
          ((and *base* disk
                (> (reduce #'+ disk :key #'layer-bytes) (floor (layer-bytes *base*) 8)))
           (let ((run (remove-if (lambda (l) (or (> (eita.state.snapshot:snap-block l) horizon)
                                                 (and fence (>= (eita.state.snapshot:snap-block l) fence))))
                                 disk)))
             (when run
               (start-compaction! (list :major run (eita.state.snapshot:snap-block (first run)))))))))))
  nil)

(defun discard-compacting-base! (why)
  "The compacted base waiting for its root check (*COMPACTING-BASE*, snap-M) will never
   replace the base: its due check is forgotten, the snap closed and its directory deleted
   (no passed check names it: it is no resume point), and compaction and GC resume (both
   wait while it is set). Its root check, if running, was stopped first (`rollback-to!`)."
  (let ((s (shiftf *compacting-base* nil)))
    (when s
      (let ((m (eita.state.snapshot:snap-block s)))
        (when (eql *base-check-due* m) (setf *base-check-due* nil))
        (eita.state.snapshot:snap-close s)
        (sb-ext:run-program "rm" (list "-rf" (string-right-trim "/" (namestring (eita.state.snapshot:snap-dir s)))) :search t)
        (format t "~&[layers] compacted base snap-~D DISCARDED: ~A~%" m why)
        (force-output)))))

(defun compaction-swap! (m)
  "The compacted base snap-M passed its root check: it replaces the base and the layers up
   to M. Only while M is a layer boundary of the stack (snap-M is then the state there); a
   reorg below M discards it first (`rollback-to!`), so this refusal is a second line: it
   never installs a base that would sit under layers of another branch."
  (let ((s *compacting-base*))
    (unless (and s (eql m (eita.state.snapshot:snap-block s)) (member m *layers* :key #'layer-block))
      (format *error-output* "~&[layers] REFUSED to swap in compacted base snap-~D: ~:[none is pending~;~:*block ~D is not a layer boundary of the stack (a rollback went below it)~]~%"
              m (and s (eita.state.snapshot:snap-block s)))
      (when s (discard-compacting-base! (format nil "block ~D is not in the stack" m)))
      (return-from compaction-swap! nil))
    (sb-thread:with-mutex (*stack-lock*)
      (let ((gone (cons *base* (member m *layers* :key #'layer-block)))
            (keep (ldiff *layers* (member m *layers* :key #'layer-block))))
        (setf *retired* (append gone *retired*))
        (sb-thread:barrier (:write))
        (setf *base* s *layers* keep)))
    (setf *compacting-base* nil)
    (format t "~&[layers] base is now snap-~D (~D layers above it)~%" m (length *layers*))
    t))

(defun stop-background! ()
  "End of a run: the writer finishes its queue and stops; a running compaction finishes."
  (when *writer*
    (ignore-errors (pipe-put *writer-pipe* :stop))
    (sb-thread:join-thread *writer* :default nil)
    (setf *writer* nil))
  (when *compactor* (sb-thread:join-thread *compactor* :default nil)))

(defun close-retired! ()
  "Close swapped-out snaps once neither background thread can be reading them."
  (when (and *retired* (not *writer-busy*) (null *compactor*))
    (mapc #'eita.state.snapshot:snap-close *retired*)
    (setf *retired* '())))

;;; ---------------------------------------------------------------- reorg rollback

(defun rollback-to! (world b)
  "Roll the state back to the newest layer boundary T <= B (a reorg forked after B): drop
   every layer above T (frozen or on disk), the hot set, and the root check and pending
   compacted base above T. Returns T; the caller re-executes T+1..B and then the new
   branch. Lean: `rollback_view`."
  (writer-drain!)
  ;; a running compaction finishes first (its result is taken at the next poll); it never
  ;; touches the newest `reorg-window` blocks, so a reorg within the window leaves it valid
  (when *compactor* (sb-thread:join-thread *compactor* :default nil))
  (when (and *compactor-job* (> (layer-block (first (second *compactor-job*))) b))
    (error "rollback to ~D: a compaction covered blocks up to ~D (the reorg is deeper than the window)"
           b (layer-block (first (second *compactor-job*)))))
  (let* ((keep (member-if (lambda (l) (<= (layer-block l) b)) *layers*))
         (drop (ldiff *layers* keep))
         (top (if keep (layer-block (first keep)) (eita.state.snapshot:snap-block *base*))))
    (when (and (null keep) (> (eita.state.snapshot:snap-block *base*) b))
      (error "rollback to ~D: below the base snap-~D (the reorg is deeper than the layers)" b (eita.state.snapshot:snap-block *base*)))
    ;; everything above TOP belongs to the abandoned branch: a root check in flight (of an
    ;; anchor, or of a compacted base) and a finished compaction's base waiting for its check.
    ;; Left set, a killed base check stalled compaction, GC and `finish-anchors!` for good; a
    ;; check not yet started passed later (against snap-M's own root) and installed the old
    ;; branch's snap-M under the kept layers (a Veil model, CompactionDeepReorg, 17 steps)
    (when (and *pending-root* (> (first *pending-root*) top))
      (kill-root-check!))
    (when (and *compacting-base* (> (eita.state.snapshot:snap-block *compacting-base*) top))
      (discard-compacting-base! (format nil "rollback to ~D" top)))
    (sb-thread:with-mutex (*stack-lock*) (sb-thread:barrier (:write)) (setf *layers* keep))
    (dolist (l drop)
      (eita.state.snapshot:snap-close l)
      (sb-ext:run-program "rm" (list "-rf" (string-right-trim "/" (namestring (eita.state.snapshot:snap-dir l)))) :search t))
    (clear-hot! world)
    (format t "~&[layers] rolled back to block ~D (~D layers dropped)~%" top (length drop))
    (force-output)
    top))

;;; ---------------------------------------------------------------- starting states

(defun genesis-base! (world n root-hex)
  "The world is all in RAM (genesis alloc): write it as the base snap-N and back the world
   by it. Returns its composition."
  (let* ((l (make-ram-layer :block n :root root-hex :accts (world-accts world)))
         (s (write-ram-tables l '() nil :full t)))
    (back-world! world s '())
    (list (eita.state.snapshot:component-of s))))

(defun open-composition (comps &key trust)
  "Open COMPS (oldest first) after checking each one against its recorded content hash
   (I3; a component without one is accepted on its manifest): its bytes re-hashed, or with
   TRUST (the composition of a passed root check) its manifest — the files' names, sizes
   and FNVs, the sizes checked on disk — hashed, the bytes not re-read. A refused component
   is quarantined (*.corrupt) and the resume fails loudly. Returns (values base layers)."
  (let ((snaps '()))
    (dolist (c comps)
      (let* ((path (eita.state.snapshot:component-path (snapshot-dir) c))
             (want (car (last c)))
             (s (handler-case
                    (let* ((s (eita.state.snapshot:snap-open path :fence :background))
                           (got (if trust
                                    (eita.state.snapshot:snap-content-hash (eita.state.snapshot:snap-manifest s))
                                    (eita.state.snapshot:snap-verify s))))
                      (when (and want (not (string-equal want got)))
                        (eita.state.snapshot:snap-close s)
                        (error "content hash ~A, recorded ~A" got want))
                      s)
                  (error (e)
                    (mapc #'eita.state.snapshot:snap-close snaps)
                    (let ((q (format nil "~A.corrupt" (string-right-trim "/" (namestring path)))))
                      (ignore-errors (sb-posix:rename (string-right-trim "/" (namestring path)) q))
                      (error "resume: ~A refused (~A); quarantined as ~A" path e q))))))
        (push s snaps)))
    (let ((snaps (nreverse snaps)))
      (unless (and snaps (not (eita.state.snapshot:snap-layer-p (first snaps)))
                   (every #'eita.state.snapshot:snap-layer-p (rest snaps)))
        (error "resume: composition ~S is not a base under layers" comps))
      (values (first snaps) (reverse (rest snaps))))))

(defun resume-stack! (world comps &key trust)
  "Back WORLD by the composition COMPS (oldest first); TRUST: `open-composition`'s."
  (multiple-value-bind (base layers) (open-composition comps :trust trust)
    (back-world! world base layers)
    (format t "~&resume: ~A~{ + ~A~} (~D accounts, ~D slots in the base)~%"
            (eita.state.snapshot:snap-dir base) (mapcar #'eita.state.snapshot:snap-dir (reverse layers))
            (eita.state.snapshot:snap-n-accounts base) (eita.state.snapshot:snap-n-slots base))
    (force-output)))

;;; ---------------------------------------------------------------- the state budget

(defstartup *hot-budget-bytes*
  (let ((v (sb-ext:posix-getenv "EITA_HOT_BUDGET_MB"))) (and v (plusp (length v)) (* 1024 1024 (parse-integer v))))
  "EITA_HOT_BUDGET_MB: the memory the state's tables may hold, heap and native together
   (`acct-table-bytes`): the hot set is frozen early when it passes this (checked every
   1000 blocks), and the tables of written layers are dropped once they hold a quarter of
   it (`collect-written!`). Unset: a quarter of the heap (`hot-budget-bytes`).")

(defun hot-budget-bytes ()
  "The state budget in bytes: EITA_HOT_BUDGET_MB, else a quarter of the heap (10 GB: 2.5 GB;
   the nursery takes another quarter, and the GC's copy room is the live heap again)."
  (or *hot-budget-bytes* (floor (sb-ext:dynamic-space-size) 4)))

(defun hot-over-budget-p (n)
  "Is the live hot set over the state budget (every 1000 blocks, with a stack under the
   world)? While a frozen layer still waits for the writer the check waits too: a freeze
   then would only cut a small layer for memory the writer is about to release. The
   tables are measured (heap and native), not the heap: native slot tables are not in it,
   and garbage the next GC frees is."
  (and *base* (zerop (mod n 1000))
       (notany #'ram-layer-p *layers*)
       (> (multiple-value-call #'+ (acct-table-bytes (world-accts *current-world*))) (hot-budget-bytes))))
