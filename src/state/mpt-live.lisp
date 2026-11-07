;;;; mpt-live.lisp — incremental account state-root validator wired into the
;;;; live SBCL mainnet replay, running on a SEPARATE worker thread.
;;;;
;;;; Design (see #237 / project_state_root_validation):
;;;;   * The EXECUTION thread captures, per block, the set of addresses whose
;;;;     account leaf (nonce/balance/code/storageRoot) changed. The source is
;;;;     the revert journal (storage/balance/nonce/created carry the addr) plus
;;;;     the few NON-journaled per-block balance writers (tx sender debit/refund,
;;;;     coinbase fee, block/uncle rewards, withdrawals, DAO fork). Every such
;;;;     write calls (mpt-touch! addr) which unions addr into *mpt-dirty*.
;;;;   * At the post-block boundary (single-threaded — execution paused), a hook
;;;;     reads the CURRENT (nonce,balance,code,full-slot-list) of each dirty addr
;;;;     into an IMMUTABLE snapshot and pushes it onto a thread-safe mailbox.
;;;;     *mpt-dirty* is then cleared. The worker NEVER reads the live world
;;;;     (concurrent read+write segfaults the image — the project's hard lesson);
;;;;     it only ever sees the immutable boundary snapshots.
;;;;   * The WORKER thread maintains one mutable account mtrie. It dequeues block
;;;;     snapshots in order; for each dirty addr it deletes (if now absent from
;;;;     the trie) or inserts the freshly-encoded account leaf. After a check
;;;;     block it computes mtrie-root and compares to the header stateRoot.
;;;;
;;;; Account membership matches the full-state walk (the June stateroot check, git history) EXACTLY:
;;;;   addr ∈ trie  iff  balance>0 ∨ nonce>0 ∨ has-code ∨ has-nonzero-storage
;;;;                     ∨ addr ∈ world-accounts (empty-but-present set).
;;;;
;;;; This file does NOT touch / rebuild libeita. mpt.lisp loads it read-only.

(in-package #:eita.state)

;; Defined below, with the worker.
(declaim (special *mpt-mailbox*))

;;; --------------------------------------------------------------------
;;; Dirty-set capture (runs on the EXECUTION thread).
;;; --------------------------------------------------------------------

(defvar *mpt-tracking* nil
  "When true, mpt-touch! records changed addresses. Gated so a normal replay
   pays nothing.")

(defvar *mpt-dirty* (make-hash-table :test 'eql)
  "addr -> what changed this block. One of:
     :account            only the account leaf's own fields (balance/nonce/code)
     <hash-table>        slot -> t, the storage slots that changed
     :all                storage invalidated WHOLESALE — re-read the full list
   Reset at each post-block boundary after the snapshot is taken.

   Per-slot, not addr-level, because the worker now keeps a PERSISTENT storage
   trie per contract: touching Arc's largest contract (14 618 285 slots, 70% of
   the state) must cost the ~10 changed slots, not a 93 s / 7.6 GB rebuild of the
   whole thing, and it is touched in 10-46% of blocks.")

(defvar *mpt-introduced* (make-hash-table :test 'eql)
  "addr -> t once the worker has been given that contract's FULL slot list and so
   holds a trie for it. Until then a snapshot must carry the full list; afterwards
   it carries only the changed slots. Lives on the execution thread so the worker
   never has to ask the world anything.")

;; NOT inline — replaces the replay-cl stub at load time; callers funcall
;; through the symbol so this live definition takes effect.
(defun mpt-touch! (addr &optional slot)
  "Mark ADDR changed this block (execution thread). SLOT, when given, is the
   storage slot that changed (journal-push! passes it for entry type 0)."
  (let ((cur (gethash addr *mpt-dirty*)))
    (cond
      ((eq cur :all))                              ; already the strongest marker
      ((null slot) (unless cur (setf (gethash addr *mpt-dirty*) :account)))
      (t (let ((set (if (hash-table-p cur)
                        cur
                        (setf (gethash addr *mpt-dirty*) (make-hash-table :test 'eql)))))
           (setf (gethash slot set) t))))))

(defun mpt-touch-all! (addr)
  "Mark ADDR's storage invalidated WHOLESALE: the worker must drop its trie for
   ADDR and rebuild from a full slot list.

   Required because two paths clear storage with a single `remhash` on
   `world-storage` and no per-slot journal entry, so the changed slots are
   invisible to slot-level tracking:
     * `spec-destroy-effect` (end-of-tx deletion, every fork) — and the slots it
       drops were written in EARLIER txs/blocks, so nothing touched them;
     * the journal restore of entry type 10 (`created`), i.e. a reverted CREATE.
   Slots written inside a reverted CREATE are individually journaled (type 0) and
   so are covered, but a CREATE landing on an address that already held storage
   would not be, and selfdestruct is broken outright. Forcing the full re-read is
   the honest fix rather than reasoning each case out."
  (setf (gethash addr *mpt-dirty*) :all)
  (remhash addr *mpt-introduced*))

;;; --------------------------------------------------------------------
;;; Boundary snapshot → mailbox (execution thread, at the block boundary).
;;; --------------------------------------------------------------------

;; Header stateRoots to check against, by block number. For the oracle run we
;; only need block 499999; more can be added.
(defstartup *mpt-every* (and (sb-posix:getenv "EITA_MPT_EVERY") t)
  "Compute mtrie-root after EVERY block; under *mpt-all-roots* also COMPARE each
   block's root to the header stateRoot (full per-block consensus validation).")

(defparameter *mpt-all-roots* (make-hash-table :test 'eql :synchronized t)
  "Block -> header stateRoot hex, registered from each block's header at its boundary
   (EITA_MPT_EVERY) and consumed by the worker's per-block comparison.")

(defparameter *mpt-check-roots*
  '((499999 . "ce71e3f2f4edbb2c02b0bb1612f54c131b9bb1ad768aacf96afc2701d50062b1"))
  "Alist (block-number . expected-root-hex) for the worker to verify.")

(defvar *mpt-verdicts* (make-hash-table :test 'eql)
  "block -> (ok-p . computed-root-hex), written by the WORKER and read by the
   execution thread via `mpt-await-verdict`. The Arc driver needs a verdict it can
   act on: its anchors file is what the supervisor resumes from, so a root check
   that only prints cannot replace the dump+stateRoot path.")
(defvar *mpt-verdict-lock* (sb-thread:make-mutex :name "mpt-verdicts"))
(defvar *mpt-worker-block* nil
  "Highest block the worker has finished applying. Lets the driver tell
   \"not yet\" apart from \"no check configured at this block\".")

(defun mpt-record-verdict! (n ok rhex)
  (sb-thread:with-mutex (*mpt-verdict-lock*)
    (setf (gethash n *mpt-verdicts*) (cons ok rhex))))

(defun mpt-request-check (n expected-hex)
  "Ask the worker to verify its root at block N — processed strictly after every
   snapshot already queued, because the mailbox is FIFO."
  (sb-concurrency:send-message *mpt-mailbox* (list :check n :expect expected-hex)))

(defun mpt-clear-verdict! (n)
  (sb-thread:with-mutex (*mpt-verdict-lock*) (remhash n *mpt-verdicts*)))

(defun mpt-verdict (n)
  (sb-thread:with-mutex (*mpt-verdict-lock*) (gethash n *mpt-verdicts*)))

(defun mpt-await-verdict (n &key (timeout 1800))
  "Block until the worker has produced a root verdict for block N.
   Returns (values ok-p computed-hex) or (values :timeout nil)."
  (let ((deadline (+ (get-universal-time) timeout)))
    (loop
      (let ((v (mpt-verdict n)))
        (when v (return (values (car v) (cdr v)))))
      (when (> (get-universal-time) deadline) (return (values :timeout nil)))
      (sleep 0.25))))

(defvar *mpt-mailbox* nil
  "sb-concurrency mailbox carrying immutable per-block snapshots to the worker.")

(defparameter *mpt-queue-cap* 300
  "Backpressure high-water: when the mailbox holds more than this many block
   snapshots, the execution thread blocks until the worker drains to
   *MPT-QUEUE-LOW*. Bounds the in-flight memory: each queued snapshot pins the
   touched contracts' FULL non-zero slot lists, and in high-storage eras those
   are large — a deep backlog alone (worker is the slower, keccak-bound side)
   can climb toward the heap limit. A small buffer keeps the worker fed while
   keeping queued-snapshot memory tight; execution is throttled to validator
   throughput, which is fine (correctness + bounded memory are the goal).")
(defparameter *mpt-queue-low* 100
  "Backpressure low-water: resume execution once the mailbox drains to here.")
(defvar *mpt-worker* nil
  "The worker thread maintaining the incremental account trie.")

(defun mpt-full-slot-list (w addr)
  "ADDR's FULL list of (slot . value) for every non-zero slot it holds."
  (let ((storage '()))
    (with-acct (tb a) w addr
      (acct-slots-map (lambda (slot val) (unless (zerop val) (push (cons slot val) storage))) tb a))
    storage))

(defun mpt-account-snapshot (w addr &optional (dirt :all))
  "Read ADDR's CURRENT account state from world W into an immutable plist.
   Always: :addr :nonce :balance :code (a copy) :present.
   Storage, driven by DIRT and by whether the worker already holds a trie:
     :storage <full list>  — introduce (or re-introduce) the contract. Sent the
                             first time ADDR is touched, and whenever DIRT is
                             :all (wholesale invalidation), with :reset t so the
                             worker drops any trie it already had.
     :slots <(slot . val)> — only the slots that changed, with their CURRENT
                             values; value 0 means delete. This is the whole
                             point: ten conses instead of 14.6 million.
   Taken at the boundary where the world is not being mutated; every cons is
   freshly built and never shared with the live world."
  (let* ((nonce   (nonce-of w addr))
         (balance (balance-of w addr))
         (code    (with-acct (tb a) w addr (acct-code-entry tb a)))
         (present-set (with-acct (tb a) w addr (acct-flag-p tb a +acct-marked+)))
         (introduce (or (eq dirt :all) (not (gethash addr *mpt-introduced*))))
         (base (list :addr addr
                     :nonce nonce
                     :balance balance
                     ;; copy code so a later mutation of the (usually immutable)
                     ;; code vector can never race the worker.
                     :code (when (and code (plusp (length code))) (copy-seq code))
                     :present present-set)))
    (cond
      (introduce
       (setf (gethash addr *mpt-introduced*) t)
       (append base (list :reset (eq dirt :all) :storage (mpt-full-slot-list w addr))))
      ((hash-table-p dirt)
       (let ((slots '()))
         (maphash (lambda (slot v) (declare (ignore v))
                    (push (cons slot (world-storage-get w addr slot)) slots))
                  dirt)
         (append base (list :slots slots))))
      ;; :account — leaf fields only; storage is whatever the worker already holds.
      (t (append base (list :slots '()))))))

(defun mpt-post-block-hook (n world)
  "Post-block hook (execution thread, single-threaded boundary). Snapshots
   every dirty addr's CURRENT state, ships it to the worker, clears the dirty
   set. Cheap when nothing changed."
  (when *mpt-tracking*
    (when *mpt-every*
      (setf (gethash n *mpt-all-roots*) (string-downcase (subseq (blk-state-root (fetch-block n)) 2))))
    (let ((snaps '()))
      (when (sb-posix:getenv "EITA_MPT_TRACE")
        (let ((as '()))
          (maphash (lambda (a v) (declare (ignore v)) (push a as)) *mpt-dirty*)
          (format t "~&[mpt] block ~D dirty ~D (~D slot-sets, ~D wholesale): ~{~40,'0x~^ ~}~%"
                  n (length as)
                  (let ((k 0)) (maphash (lambda (a d) (declare (ignore a))
                                          (when (hash-table-p d) (incf k))) *mpt-dirty*) k)
                  (let ((k 0)) (maphash (lambda (a d) (declare (ignore a))
                                          (when (eq d :all) (incf k))) *mpt-dirty*) k)
                  (subseq as 0 (min 12 (length as))))
          (finish-output)))
      (maphash (lambda (addr dirt)
                 (push (mpt-account-snapshot world addr dirt) snaps))
               *mpt-dirty*)
      (clrhash *mpt-dirty*)
      ;; Always enqueue the block marker (even with no dirty addrs) so the
      ;; worker advances its block counter and can run a check at N.
      (sb-concurrency:send-message
       *mpt-mailbox* (list :block n :accounts snaps))
      ;; BACKPRESSURE. The worker's per-touch storage rebuild is CPU-bound and
      ;; the execution thread is much faster, so without a cap the mailbox
      ;; grows unbounded — each queued snapshot pins a full slot list, and in
      ;; high-storage eras that exhausts the heap (the worker crashed in
      ;; PATRICIALISE around block 700k). Block the execution thread until the
      ;; worker has drained below the cap. The worker is always actively
      ;; consuming, so this terminates; it just throttles execution to the
      ;; validator's throughput, bounding in-flight memory.
      (when (> (sb-concurrency:mailbox-count *mpt-mailbox*) *mpt-queue-cap*)
        (loop while (> (sb-concurrency:mailbox-count *mpt-mailbox*)
                       *mpt-queue-low*)
              do (sleep 0.001))))
    ;; AUDIT (debug): at a check block, snapshot the FULL world (safe — the
    ;; boundary is single-threaded) and ship it so the worker can full-rebuild
    ;; and diff against its incremental trie. Gated on EITA_MPT_AUDIT. The
    ;; audit carries each addr's FULL non-zero slot list (:full-storage) so the
    ;; worker can rebuild a contract's storage trie from scratch.
    (when (and (assoc n *mpt-check-roots*) (sb-posix:getenv "EITA_MPT_AUDIT"))
      (let ((all '()))
        (let ((addrs (make-hash-table :test 'eql)))
          (let ((tb (world-accts world)))
            (map-accts (lambda (r)
                         (when (or (not (eql 0 (acct-balance tb r))) (not (eql 0 (acct-nonce tb r)))
                                   (acct-code-entry tb r) (acct-slots tb r) (acct-flag-p tb r +acct-marked+))
                           (setf (gethash (acct-addr tb r) addrs) t)))
                       tb))
          (maphash (lambda (addr v) (declare (ignore v))
                     (push (mpt-account-snapshot-full world addr) all))
                   addrs))
        (sb-concurrency:send-message
         *mpt-mailbox* (list :audit n :accounts all))))))

(defun mpt-account-snapshot-full (w addr)
  "Audit-only snapshot: like mpt-account-snapshot but carrying ADDR's FULL
   non-zero slot list as :full-storage (for a from-scratch storage trie)."
  (let* ((nonce   (nonce-of w addr))
         (balance (balance-of w addr))
         (code    (with-acct (tb a) w addr (acct-code-entry tb a)))
         (present-set (with-acct (tb a) w addr (acct-flag-p tb a +acct-marked+)))
         (storage '()))
    (with-acct (tb a) w addr
      (acct-slots-map (lambda (slot val) (unless (zerop val) (push (cons slot val) storage))) tb a))
    (list :addr addr :nonce nonce :balance balance
          :code (when (and code (plusp (length code))) (copy-seq code))
          :full-storage storage :present present-set)))

;;; --------------------------------------------------------------------
;;; Worker thread: INCREMENTAL account trie + REBUILD-ON-TOUCH storage.
;;;
;;; The worker keeps ONE persistent account mtrie (incremental: insert/delete
;;; the touched account's leaf each block). It keeps NO persistent per-contract
;;; storage trie. For each touched contract it rebuilds the storageRoot from
;;; the snapshot's FULL non-zero slot list via eita.mpt:storage-root, then
;;; splices that account's leaf. The per-block storage rebuilds are transient
;;; and GC'd, so worker memory = the account trie + the current block's
;;; rebuilds — nothing storage-side accumulates over the chain.
;;; --------------------------------------------------------------------

(defstruct (mpt-wstate (:constructor make-mpt-wstate ()))
  (trie (eita.mpt:make-mtrie))               ; account trie (incremental)
  ;; addr -> that contract's PERSISTENT storage mtrie. This is the memory we
  ;; trade for not rebuilding: a touch now costs the changed slots plus the
  ;; re-hash of their root-to-leaf paths, instead of the contract's whole trie.
  (stries (make-hash-table :test 'eql)))

(defun mpt-strie (ws addr)
  (or (gethash addr (mpt-wstate-stries ws))
      (setf (gethash addr (mpt-wstate-stries ws)) (eita.mpt:make-mtrie))))

(defun mpt-strie-empty-p (trie)
  (null (eita.mpt:mtrie-top trie)))

(defun mpt-slot-key (slot)
  (eita.mpt:%keccak (eita.mpt:int->be-bytes-fixed slot 32)))

(defun mpt-slot-value (val)
  "The trie's leaf value for a slot: RLP(minimal-BE(val)). Byte-for-byte the
   same expression `eita.mpt:storage-root` uses, so an incrementally-maintained
   trie and a from-scratch rebuild cannot drift."
  (eita.mpt:rlp-encode (eita.mpt:rlp-uint val)))

(defvar *mpt-inserts* 0 "Leaves inserted by the worker; compared against the seeded count.")
(defvar *mpt-deletes* 0 "Accounts the membership rule judged ABSENT. A seed pass should
  produce ZERO of these: every address handed to it came from the world's own tables, so
  a delete means the snapshot rule and the dump's collection rule disagree.")

(defun mpt-apply-storage! (ws snap addr)
  "Bring ADDR's PERSISTENT storage trie up to date from SNAP, and return its root.

   `:storage` (a full slot list) introduces or re-introduces the contract — with
   `:reset` it first drops whatever trie was there, which is what makes wholesale
   invalidation (selfdestruct, reverted CREATE) safe. `:slots` applies only the
   slots that changed: value 0 deletes, anything else inserts. Taking the root
   afterwards is O(the re-hashed paths) because node hashes are cached."
  (let ((full (getf snap :storage))
        (has-full (not (null (member :storage snap))))
        (slots (getf snap :slots)))
    (when (and has-full (getf snap :reset))
      (remhash addr (mpt-wstate-stries ws)))
    (let ((trie (mpt-strie ws addr)))
      (cond
        (has-full
         ;; Introduce: the trie is empty (fresh, or just dropped by :reset).
         (dolist (kv full)
           (unless (zerop (cdr kv))
             (eita.mpt:mtrie-insert trie (mpt-slot-key (car kv))
                                    (mpt-slot-value (cdr kv))))))
        (t
         (dolist (kv slots)
           (if (zerop (cdr kv))
               (eita.mpt:mtrie-delete trie (mpt-slot-key (car kv)))
               (eita.mpt:mtrie-insert trie (mpt-slot-key (car kv))
                                      (mpt-slot-value (cdr kv)))))))
      (values (if (mpt-strie-empty-p trie)
                  (eita.mpt:empty-root-bytes)
                  (eita.mpt:mtrie-root trie))
              (not (mpt-strie-empty-p trie))))))

(defun mpt-apply-snapshot (ws snap)
  "Insert/delete one account SNAP into the worker state WS, maintaining that
   contract's PERSISTENT storage trie per-slot rather than rebuilding it."
  (let* ((addr (getf snap :addr))
         (akey (eita.mpt:%keccak (eita.mpt:int->be-bytes-fixed addr 20)))
         (nonce   (getf snap :nonce))
         (balance (getf snap :balance))
         (code    (getf snap :code))
         (present (getf snap :present)))
    (multiple-value-bind (sroot has-storage) (mpt-apply-storage! ws snap addr)
      ;; Membership mirrors %sr-collect: present iff balance>0 ∨ nonce>0 ∨
      ;; has-code ∨ has-nonzero-storage ∨ in world-accounts. HAS-STORAGE now comes
      ;; from the persistent trie, not from the snapshot: an incremental snapshot
      ;; only carries the CHANGED slots and so cannot answer the question.
      (if (or (plusp balance) (plusp nonce)
              (and code (plusp (length code)))
              has-storage
              present)
          (progn
            (incf *mpt-inserts*)
            (let* ((chash (if (and code (plusp (length code)))
                              (eita.mpt:%keccak code)
                              (eita.mpt:empty-code-hash)))
                   (leaf  (eita.mpt:account-leaf-value nonce balance sroot chash)))
              (eita.mpt:mtrie-insert (mpt-wstate-trie ws) akey leaf)))
          (progn (incf *mpt-deletes*)
                 ;; Gone from the account trie, so its storage trie is dead weight
                 ;; and must not resurface if the address is re-created later.
                 (remhash addr (mpt-wstate-stries ws))
                 (eita.mpt:mtrie-delete (mpt-wstate-trie ws) akey))))))

;; Audit-only: full-rebuild membership + apply over a :full-storage snapshot.
(defun mpt-account-present-full-p (snap)
  (let ((nonce (getf snap :nonce)) (balance (getf snap :balance))
        (code (getf snap :code)) (storage (getf snap :full-storage))
        (present (getf snap :present)))
    (or (plusp balance) (plusp nonce)
        (and code (plusp (length code)))
        (some (lambda (kv) (plusp (cdr kv))) storage)
        present)))

(defun mpt-apply-snapshot-full (trie snap)
  "Audit-only: from-scratch insert of a :full-storage SNAP into account TRIE."
  (let* ((addr (getf snap :addr))
         (akey (eita.mpt:%keccak (eita.mpt:int->be-bytes-fixed addr 20))))
    (if (mpt-account-present-full-p snap)
        (let* ((sroot (eita.mpt:storage-root (getf snap :full-storage)))
               (code  (getf snap :code))
               (chash (if (and code (plusp (length code)))
                          (eita.mpt:%keccak code)
                          (eita.mpt:empty-code-hash)))
               (leaf  (eita.mpt:account-leaf-value
                       (getf snap :nonce) (getf snap :balance) sroot chash)))
          (eita.mpt:mtrie-insert trie akey leaf))
        (eita.mpt:mtrie-delete trie akey))))

(defun mpt-worker-loop (mailbox)
  "Worker entry: maintain one account mtrie, draining block snapshots in order.
   Runs until it receives a :stop sentinel. Prints MATCH/MISMATCH at each
   configured check block."
  (let ((ws (make-mpt-wstate))
        (last-block -1))
    (handler-case
        (loop
          (let ((msg (sb-concurrency:receive-message mailbox)))
            (cond
              ((eq msg :stop)
               (format t "~&[mpt] worker stop — last applied block ~D~%" last-block)
               (finish-output)
               (return))
              ;; EXPLICIT check. The root must be evaluated AFTER everything queued
              ;; ahead of it has been applied, and `*mpt-check-roots*` cannot express
              ;; that: a seed pass enqueues many markers all carrying the same block
              ;; number, so registering the expected root turns the NEXT of them into a
              ;; trigger. At 174k accounts the verdict landed after 5 041 of them — a
              ;; wrong root from a quarter-built trie. The mailbox is FIFO, so a :check
              ;; sent after the batches is applied after the batches, exactly.
              ((and (consp msg) (eq (car msg) :check))
               (let* ((n (getf msg :check))
                      (expect (getf msg :expect))
                      (rhex (eita.mpt:bytes->hex (eita.mpt:mtrie-root (mpt-wstate-trie ws))))
                      (ok (and expect (string-equal rhex expect))))
                 (mpt-record-verdict! n (and ok t) rhex)
                 (format t "~&[mpt] block ~D root ~A ~A~%" n rhex (if ok "MATCH" "MISMATCH"))
                 (finish-output)))
              ;; AUDIT: full-rebuild from the whole-world snapshot; diff vs
              ;; incremental. Does NOT touch the incremental account trie.
              ((and (consp msg) (eq (car msg) :audit))
               (let ((full (eita.mpt:make-mtrie))
                     (present 0))
                 (dolist (snap (getf msg :accounts))
                   (when (mpt-account-present-full-p snap)
                     (incf present)
                     (mpt-apply-snapshot-full full snap)))
                 (let ((froot (eita.mpt:bytes->hex (eita.mpt:mtrie-root full)))
                       (iroot (eita.mpt:bytes->hex
                               (eita.mpt:mtrie-root (mpt-wstate-trie ws)))))
                   (format t "~&[mpt-audit] block ~D full-rebuild root ~A~%"
                           (getf msg :block) froot)
                   (format t "[mpt-audit] block ~D incremental   root ~A  ~A~%"
                           (getf msg :block) iroot
                           (if (string-equal froot iroot) "SAME" "DIFFER"))
                   (format t "[mpt-audit] full present-accounts: ~D~%" present)
                   (finish-output))))
              ;; Normal per-block snapshot.
              (t
               (let ((n     (getf msg :block))
                     (accts (getf msg :accounts)))
                 (dolist (snap accts)
                   (mpt-apply-snapshot ws snap))
                 (when *mpt-every*
                   (let ((rhex (eita.mpt:bytes->hex
                                (eita.mpt:mtrie-root (mpt-wstate-trie ws)))))
                     (when *mpt-all-roots*
                       (let ((exp (prog1 (gethash n *mpt-all-roots*) (remhash n *mpt-all-roots*))))
                         (when exp
                           (mpt-record-verdict! n (and (string-equal rhex exp) t) rhex)
                           (if (string-equal rhex exp)
                               (when (zerop (mod n 50000))
                                 (format t "~&[mpt] block ~D root MATCH~%" n) (finish-output))
                               (progn
                                 (format t "~&[mpt] block ~D root MISMATCH got ~A exp ~A~%"
                                         n rhex exp) (finish-output))))))))
                 (setf last-block n)
                 (let ((expect (cdr (assoc n *mpt-check-roots*))))
                   (when expect
                     (let* ((root (eita.mpt:mtrie-root (mpt-wstate-trie ws)))
                            (rhex (eita.mpt:bytes->hex root)))
                       (mpt-record-verdict! n (and (string-equal rhex expect) t) rhex)
                       (format t "~&[mpt] block ~D root ~A ~A~%"
                               n rhex
                               (if (string-equal rhex expect) "MATCH" "MISMATCH"))
                       (finish-output))))
                 (setf *mpt-worker-block* n))))))
      (error (e)
        (format t "~&[mpt] WORKER ERROR: ~A~%" e)
        (finish-output)))))

(defun mpt-start-worker ()
  "Create the mailbox + worker thread and arm dirty tracking. Idempotent."
  (unless *mpt-worker*
    (setf *mpt-mailbox* (sb-concurrency:make-mailbox :name "mpt-mailbox"))
    (setf *mpt-worker*
          (sb-thread:make-thread
           (lambda () (mpt-worker-loop *mpt-mailbox*))
           :name "mpt-worker"))
    (setf *mpt-tracking* t)
    (format t "~&[mpt] incremental state-root worker started~%")
    (finish-output)))

(defun mpt-stop-worker ()
  "Drain: send the stop sentinel and join the worker so all queued blocks are
   applied and checks printed before the process exits."
  (when *mpt-worker*
    (sb-concurrency:send-message *mpt-mailbox* :stop)
    (sb-thread:join-thread *mpt-worker*)
    (setf *mpt-worker* nil)
    (format t "~&[mpt] worker joined~%")
    (finish-output)))

;;; --------------------------------------------------------------------
;;; Lag visibility: how far behind execution is the worker's queue?
;;; --------------------------------------------------------------------

(defun mpt-queue-depth ()
  (if *mpt-mailbox* (sb-concurrency:mailbox-count *mpt-mailbox*) 0))
