;;;; chains/driver.lisp — the chain-neutral replay driver: one block (fetch, per-block
;;;; chain setup, continuity, observers, BLOCKHASH window, pre-block system calls, user txs,
;;;; header verification, post-block system work, layers/anchors, progress), the bounded
;;;; range, reorg rollback, and the entry point (lazy or full state, genesis or anchored
;;;; resume). Blocks come from the installed block source (input/); following a
;;;; chain head is a source's FOLLOW function (`<from> tip`).
;;;;
;;;; A chain module sets the chain settings below and installs its hooks (evm/run-tx.lisp,
;;;; block-system.lisp, the EVM-core hooks in src/evm/), then calls `replay-main`.
;;;;
;;;; Environment: EITA_<NAME>, or <prefix>_<NAME> with the chain's *chain-env-prefix*
;;;; (Arc: ARC_FROM_GENESIS, ARC_RESUME_FROM, …) so running deployments keep working.

(in-package #:eita.chain)

;; Defined in chains/receipts.lisp.
(declaim (special *receipts-unverifiable*))

(defun env (name)
  "EITA_<NAME>, else <chain prefix>_<NAME>."
  (or (sb-ext:posix-getenv (concatenate 'string "EITA_" name))
      (and *chain-env-prefix*
           (sb-ext:posix-getenv (concatenate 'string *chain-env-prefix* "_" name)))))

;;; --- Run policy (read by replay-main once the chain prefix is known) -----------
(defvar *full-state* nil
  "Full-state mode (FROM_GENESIS): genesis alloc or an anchored dump as the world, no lazy
   hooks; header verification is fatal and state roots are checked on the schedule.")
(defvar *receipts-mode* :always
  ":always (per-tx receipt gates) or :on-mismatch (header gates; receipts only to diagnose).")
(defvar *verbose* nil "Per-block header + per-tx lines; off: one progress line per 1000 blocks.")
(defparameter *progress-every* 1000)

(defun read-run-policy! ()
  (setf *full-state* (and (env "FROM_GENESIS") t)
        *receipts-mode* (cond ((env "RECEIPTS") (intern (string-upcase (env "RECEIPTS")) :keyword))
                              (*full-state* :on-mismatch)
                              (t :always))
        *verbose* (or (env "VERBOSE") (eq *receipts-mode* :always))))

;;; --- Progress and diagnosis ----------------------------------------------------
(defparameter *run-t0* nil)
(defparameter *run-blocks* 0)
(defparameter *run-txs* 0)

(defun progress! (n)
  (incf *run-blocks*)
  (when (zerop (mod n *progress-every*))
    (let* ((now (get-internal-real-time))
           (dt (/ (- now (or *run-t0* now)) internal-time-units-per-second)))
      (format t "~&… block ~D  ~D txs so far  ~,1F blocks/s  rpc=~D~%"
              n *run-txs* (if (plusp dt) (/ *run-blocks* dt) 0) *rpc-calls*)
      (finish-output)
      (setf *run-t0* now *run-blocks* 0))))

(defun receipt-table (txs receipts our-gas)
  "Per-tx receipt-vs-ours table (diagnosis of a header mismatch)."
  (loop for tx in txs for r in receipts for g in our-gas for idx from 0
        do (let* ((chain-gas (getf r :gas-used)) (d (- chain-gas g)))
             (format t "  tx ~3D  to ~22A  eita ~8D  chain ~8D  ~A~%"
                     idx (if (tx-to tx) (addr-hex (tx-to tx)) "CREATE") g chain-gas
                     (cond ((zerop d) "✓ exact")
                           ((plusp d) (format nil "Δ +~D  (chain charges more)" d))
                           (t (format nil "Δ ~D  (we charge more)" d)))))))

;;; --- One block -------------------------------------------------------------------
(defun block-prev-randao (blk fork-ord)
  "PREVRANDAO of BLK at FORK-ORD: the header's difficulty before the Merge (EIP-4399) when it
   has one (proof-of-stake headers have difficulty 0: Ethereum after Paris, OP-Stack from
   Bedrock, Arc), else mixHash."
  (if (and (< fork-ord 14) (plusp (blk-difficulty blk))) (blk-difficulty blk) (blk-mix-hash blk)))

(defun run-block (world n)
  (let* ((blk (fetch-verified-block n))
         (ts (blk-timestamp blk))
         (coinbase (blk-miner blk))
         (base-fee (or (blk-base-fee blk) 0))
         (gas-limit (blk-gas-limit blk))
         (header-gas (blk-gas-used blk))
         (mix-hash nil)                 ; PREVRANDAO: block-prev-randao, at the block's fork
         (parent-hash (blk-parent-hash blk))
         (excess-blob-gas (or (blk-excess-blob-gas blk) 0))
         (txs (blk-txs blk))
         ;; Receipts already in a chunk file (an exported source) are used whenever present:
         ;; they cost nothing and there may be no RPC to ask. Without a file (post-Merge
         ;; chunks: era archives carry none) and in :on-mismatch mode the block is gated on
         ;; its header alone; receipts are fetched for ONE block only when that gate fails.
         (receipts (and txs (or (blk-receipts blk)
                                (and (eq *receipts-mode* :always) (fetch-receipts n))))))
    (setf *current-block-number* n *cur-block* n *el-fork-ord* nil)
    (when *chain-block-setup-hook* (funcall *chain-block-setup-hook* n blk ts))
    ;; EIP-7702 delegation follows the block's EL fork (Prague+), whatever opcode table runs.
    (setf *prague-delegation* (>= (el-fork) +fork-ord-prague+))
    ;; Lazy state: pre-block state from the chain's debug traces, when it opts in.
    (when (and (not *full-state*) *chain-spec* (chain-spec-prestate-overlay *chain-spec*))
      (source-call #'block-source-prestate n))
    ;; Continuity: we replay the canonical chain, so the parent must be the block we just
    ;; replayed. At the tip a mismatch is a reorg (follow-chain! rolls the layers back);
    ;; behind it, a fault (stop loud; the supervisor resumes from an anchor).
    (let ((prev (gethash (1- n) *block-hashes*)))
      (when (and prev (/= prev parent-hash))
        (if *tip-freeze*
            (error 'reorg :block n)
            (error "block ~D parentHash ~(~x~) ≠ hash of our block ~D ~(~x~): chain discontinuity" n parent-hash (1- n) prev))))
    ;; Observers: the block begins (the stream), its header as it executes.
    (stream-block-begin! n)
    (setf mix-hash (block-prev-randao blk *fork-ord*))
    (observe block blk *fork-ord*)
    ;; BLOCKHASH window [n-256, n-1] (cb-block-hash does NOT fetch on a miss — a missing
    ;; hash reads as 0). Only absent entries are fetched: after the first block of a run,
    ;; one per block. The table is bounded (eviction).
    (loop for i from (max 0 (- n 256)) below n
          unless (gethash i *block-hashes*)
            do (setf (gethash i *block-hashes*) (fetch-block-hash i)))
    (remhash (- n 300) *block-hashes*)
    (receipts-block-begin!)
    (let ((block-ctx (list :timestamp ts :number n :base-fee base-fee
                           :gas-limit gas-limit :prev-randao mix-hash
                           :coinbase coinbase :chain-id *chain-id* :excess-blob-gas excess-blob-gas
                           ;; EIP-4844: the block's blob base fee, once per block (BLOBBASEFEE,
                           ;; spec-tx-effect), at the block's EL fork.
                           :blob-base-fee (block-blob-base-fee excess-blob-gas (el-fork))))
          (total-gas 0) (match 0) (delta 0) (our-gas '()) (rlist receipts))
      (when *verbose*
        (format t "~&── block ~D  (~D txs, header gas ~D) ─────────────~%" n (length txs) header-gas))
      (run-pre-block! world n blk coinbase block-ctx)
      (loop for tx in txs for idx from 0
            for receipt = (pop rlist)
            do (let* ((traced (and *trace-tx* (= idx *trace-tx*)))
                      (*trace-frames* (and traced *trace-frames*))
                      (*trace-step* (and traced *trace-step*)))
                 (when traced (format t "~&=== TRACE tx=~D ===~%" idx))
                 (incf (getf *stats* :txs)) (incf *run-txs*)
                 (setf *cur-tx* idx)
                 (multiple-value-bind (eita-gas status egp)
                     (if *chain-run-tx-hook*
                         (funcall *chain-run-tx-hook* world tx receipt block-ctx coinbase n idx)
                         (run-evm-tx world tx block-ctx coinbase n idx :receipt receipt))
                   ;; Per-tx receipt gates (whenever the receipt is at hand).
                   (when (and receipt (not (eq status :skip)))
                     (gate n idx "gasUsed" (getf receipt :gas-used) eita-gas)
                     (when (getf receipt :status)          ; no status before Byzantium
                       (gate n idx "status" (getf receipt :status) status)))
                   (if (eq status :skip)
                       (setf *receipts-unverifiable* :skipped)
                       (receipts-push! (tx-type tx) status eita-gas *last-tx-logs*))
                   (incf total-gas eita-gas)
                   (push eita-gas our-gas)
                   ;; observers: OUR gas-used / status (:skip = unverified) and OUR effective
                   ;; gas price (gated equal to the receipt's when present)
                   (observe tx-result n idx tx eita-gas status egp)
                   (when receipt
                     (let* ((chain-gas (getf receipt :gas-used)) (d (- chain-gas eita-gas)))
                       (cond ((eq status :skip))
                             ((zerop d) (incf match))
                             (t (incf delta)))
                       (when *verbose*
                         (format t "  tx ~2D  to ~22A  eita ~8@A  chain ~8D  ~A~%"
                                 idx
                                 (cond ((eq status :skip) "(skipped)")
                                       ((tx-to tx) (addr-hex (tx-to tx)))
                                       (t "CREATE"))
                                 (if (eq status :skip) "—" eita-gas) chain-gas
                                 (cond ((eq status :skip) "unverified")
                                       ((zerop d) "✓ exact")
                                       ((plusp d) (format nil "Δ +~D  (chain charges more)" d))
                                       (t (format nil "Δ ~D  (we charge more)" d))))))))))
      (setf our-gas (nreverse our-gas))
      (when (and *verbose* receipts)
        (format t "  ── ~D/~D exact, ~D deltas · eita-total ~D vs header ~D~%"
                match (length txs) delta total-gas header-gas))
      ;; Post-block state changes (rewards, withdrawals, request system calls — the last
      ;; yield the requestsHash the header commits to), then header verification, handed
      ;; to the verifier thread (`verify-block!`) while the replay runs on.
      (run-post-block! world n blk total-gas coinbase block-ctx)
      (verify-block! n blk total-gas txs our-gas receipts)
      (when *mpt-armed* (mpt-post-block-hook n world))
      ;; block N ends: its events to the subscribers (an observer claims N once it verified)
      (stream-commit! n)
      (setf (gethash n *block-hashes*) (blk-hash blk))
      ;; Layer points: freeze the hot set (no pause; written in the background). An anchor's
      ;; root check is queued; at the tip every block is a layer (a reorg drops layers).
      (when *full-state*
        (let ((anchor (anchor-due-p n)))
          (when (or anchor *tip-freeze* (layer-due-p n) (hot-over-budget-p n))
            (anchor! world n (blk-state-root blk) :anchor anchor)))
        ;; finished background work into the stack; collect / start root checks
        (root-check-poll! n))
      (progress! n))))

;;; --- Header verification, on the verifier thread ------------------------------------
(defun verify-block! (n blk total-gas txs our-gas receipts)
  "Block N's header verification (receipts.lisp: gas, bloom, receiptsRoot, blobGasUsed,
   requestsHash, the body's roots) on the verifier thread (src/evm/): under full state
   THE per-block check, a miss fatal — reported, and the run stopped, on the replay thread
   at its next flush; nothing durable claims N. The receiptsRoot commits to every receipt;
   receipts only say WHICH tx differs (fetched for this block when an RPC is configured)."
  (let ((inputs (block-verify-inputs)) (full *full-state*) (v (make-verdict n)))
    (setf *last-verdict* v)
    (fw-push
     (list :verify v
           (lambda ()
             (let ((bad (apply #'verify-block-header blk total-gas inputs)))
               (when bad
                 (verifier-note!
                  (lambda ()
                    (incf (getf *stats* :mismatches))
                    (format t "~&MISMATCH blk=~D header: gasUsed ours ~D vs ~A~{ · ~A differs~}~%" n total-gas (blk-gas-used blk) bad)
                    (unless receipts
                      (let ((rs (ignore-errors (fetch-receipts n))))   ; a diagnosis only
                        (if rs
                            (receipt-table txs rs our-gas)
                            (format t "  (the block source has no receipts for this block: supply them to localise the tx)~%"))))
                    (when full
                      (error "block ~D does not reproduce its header (~{~A~^, ~} MISMATCH) — the state root would drift from here" n bad)))))
               (not (and bad full))))))))

;;; --- Reorgs ------------------------------------------------------------------------
;;; A source that follows the head signals REORG from run-block (via its FOLLOW loop) when a
;;; block does not extend ours, finds the fork point, and calls ROLLBACK-CHAIN!.
(define-condition reorg (error) ((block :initarg :block :reader reorg-block))
  (:report (lambda (c s) (format s "reorg at block ~D" (reorg-block c)))))

(defun rollback-chain! (world fork)
  "Forget everything above the newest layer boundary T <= FORK: layers, the running root
   check and a pending compacted base (`rollback-to!`), queued root checks, observers'
   records (the stream's :rollback), block hashes and the source's blocks. Returns T+1."
  (let ((top (rollback-to! world fork)))
    ;; an anchor above TOP belongs to the abandoned branch
    (setf *anchor-queue* (remove-if (lambda (a) (> (first a) top)) *anchor-queue*))
    (stream-rollback! top)
    (loop for b being the hash-keys of *block-hashes* when (> b top) do (remhash b *block-hashes*))
    (source-call #'block-source-forget-above top)
    (1+ top)))

;;; --- Starting state ----------------------------------------------------------------
(defun composition-sealed-p (comps)
  (every (lambda (c) (eita.state.snapshot:snap-sealed-p (eita.state.snapshot:component-path (snapshot-dir) c))) comps))

(defun resume-from-anchor! (world rn)
  "Anchored restart at RN (recovery.lisp's resume point, or an operator's bisect point):
   the world starts empty over the composition a passed root check recorded for RN. Its
   components' manifests must hash to the recorded hashes and their files have the sizes
   the manifests record; the bytes are not re-read (`open-composition` :trust) — the root
   check read exactly these files, a component is immutable once published, and the next
   anchor's root check reads every byte again. EITA_RESUME_VERIFY=1 re-hashes them first
   (206 GB of Ethereum base: half of a 28-minute resume). A point without a passed check (a
   layer kept for bisecting, a copied snapshot) is resolved to its chain, its bytes
   re-hashed, root-checked now, synchronously, and recorded before anything runs on it.
   Returns the first block."
  (let ((comps (find-if #'composition-sealed-p (anchor-compositions rn)))
        (verify (let ((v (sb-ext:posix-getenv "EITA_RESUME_VERIFY"))) (and v (plusp (length v)) (string/= v "0")))))
    (if comps
        (let ((t0 (get-internal-real-time)))
          (resume-stack! world comps :trust (not verify))
          (format t "~&resume: composition ~A is anchored at ~D (root checked)~:[; manifests match it, bytes not re-read (EITA_RESUME_VERIFY=1 re-hashes them)~;, bytes re-hashed~]; resume took ~,1F s~%"
                  (eita.state.snapshot:composition-string comps) rn verify
                  (/ (- (get-internal-real-time) t0) internal-time-units-per-second)))
        (multiple-value-bind (anchors dumps files) (eita.state.recovery:read-view (snapshot-dir))
          (declare (ignore dumps))
          (let ((chain (if (eita.state.snapshot:snap-sealed-p (eita.state.snapshot:snap-path (snapshot-dir) rn))
                           (list (list :base rn))
                           (eita.state.recovery:resolve anchors files rn))))
            (unless (and chain (composition-sealed-p chain))
              (error "resume: no sealed snapshot or layer chain at block ~D" rn))
            (format t "~&resume: block ~D is not anchored: checking the root of ~S now~%" rn chain)
            (force-output)
            (resume-stack! world (mapcar (lambda (c) (append c (list nil))) chain))
            (root-check! rn (blk-state-root (fetch-block rn)) (stack-composition rn)))))
    (force-output)
    (1+ rn)))

(defun start-from-genesis! (world start)
  "Load the genesis alloc, check it against block 0's root, and confirm it is still the
   state at START-1 (equal header roots: no rewards, empty blocks change nothing)."
  (let* ((gpath (or (env "GENESIS") *chain-genesis-path*))
         (count (load-genesis-alloc world (home-relative gpath)))
         (groot (blk-state-root (fetch-block 0))))
    (format t "~&genesis alloc: ~D accounts from ~A~%" count gpath)
    (root-check! 0 groot (genesis-base! world 0 groot))
    (when (> start 1)
      (let ((prev (blk-state-root (fetch-block (1- start)))))
        (unless (string-equal prev groot)
          (error "block ~D stateRoot ~A ≠ genesis root ~A: the alloc is not the state there" (1- start) prev groot))
        (format t "~&fast-forward: blocks 1..~D leave the genesis state (header roots equal)~%" (1- start))))))

;;; --- Entry -----------------------------------------------------------------------
(defun replay-main (args)
  "ARGS: <block> [end-block | tip]. The chain module has set the chain settings, the
   block source (input/) and its hooks. An input outage past its bound exits
   +exit-input-outage+ (the stream finalized on the way out): not a death to the supervisor."
  (handler-bind ((input-outage (lambda (c) (format t "~&~A~%" c) (force-output)
                                 (sb-ext:exit :code +exit-input-outage+))))
    (replay-run args)))

(defun replay-run (args)
  (when (null args)
    (format t "usage: replay <block> [end-block | tip]   (decimal or 0x; tip = follow the head)~%")
    (sb-ext:exit :code 1))
  (load-observer!)                     ; EITA_OBSERVER: an observer to install (the observation seam)
  (read-run-policy!)
  ;; Nursery: SBCL's default is 5 % of the heap; per-tx garbage is dead by the next tx, so a
  ;; larger nursery means fewer collections at the same cost each. A quarter of the heap,
  ;; between 1 GB and 8 GB. x300, 30k mainnet blocks, 16 GB heap (2026-11-06): 1.6 GB
  ;; (a tenth) 1,614.6 Mgas/s, GC 25.0 s, RSS 8.7 GB; 4 GB 1,628.4 (+0.9 %), GC 18.3 s,
  ;; RSS 11.9 GB; 8 GB 1,641.6 (+1.7 %), GC 12.7 s, RSS 15.4 GB -- too close to a 16 GB
  ;; heap to be a default there, so 8 GB comes with heaps of 32 GB and more.
  (setf (sb-ext:bytes-consed-between-gcs)
        (max (* 1024 1024 1024) (min (* 8 1024 1024 1024) (floor (sb-ext:dynamic-space-size) 4))))
  (let* ((start (parse-block-arg (first args)))
         (end (cond ((null (second args)) start)
                    ((string-equal (second args) "tip") :tip)
                    (t (parse-block-arg (second args))))))
    (unless *block-source* (setf *block-source* (default-block-source)))
    (block-source)                      ; none: say how to give one, before anything runs
    (source-call #'block-source-begin start)
    (format t "~&Eita × ~A — ~A replay ~D..~A  verify=~A~@[ (header ~{~A~^, ~}: the chain's own, not compared)~]~%  blocks=~A  ~A~%"
            *chain-name* (if *full-state* "full-state" "lazy-state") start (if (eq end :tip) "tip (follow)" end)
            (if (eq *receipts-mode* :always) "per-tx receipts" "header gas+bloom+receipts, root on schedule")
            *chain-header-foreign*
            (block-source-name (block-source)) *chain-banner-extra*)   ; a source's name never holds a key
    ;; Full state: the world is the genesis alloc or an anchored snapshot, no lazy hooks.
    ;; Lazy state: the source loads accounts and slots on first touch, if it can.
    (if *full-state*
        (setf *fault-account-hook* nil *fault-slot-hook* nil)
        (let ((src (block-source)))
          (unless (block-source-fault-account src)
            (error "lazy state needs a block source that serves state (~A serves blocks only): ~
                    run from genesis (<PREFIX>_FROM_GENESIS=1) or from a snapshot (<PREFIX>_RESUME_FROM)"
                   (block-source-name src)))
          (setf *fault-account-hook* (block-source-fault-account src)
                *fault-slot-hook* (block-source-fault-slot src))))
    (let* ((world (make-world)) (*current-world* world))
      (when *full-state*
        (let ((resume (env "RESUME_FROM")))
          (if resume
              (setf start (resume-from-anchor! world (parse-integer resume)))
              (start-from-genesis! world start)))
        (drop-stale-rootouts!)
        ;; what earlier lives left (retired and superseded layers) goes now, not at the
        ;; first anchor: the GC rule pins this run's stack
        (prune-dumps!)
        ;; this run re-runs from START: an observer pulls its frontier back to START-1 before
        ;; it records anything, so it never claims what a resumed run is about to redo
        (stream-commit! (1- start) :force t :durable t)
        (observe start start))
      (setf *run-t0* (get-internal-real-time))
      ;; End the stream even on an abnormal exit (a loud `error` in a not-yet-ported
      ;; path), so observers close what they wrote.
      (unwind-protect
           (if (eq end :tip)
               (let ((follow (block-source-follow (block-source))))
                 (unless follow
                   (error "tip: the block source ~A does not follow a chain head" (block-source-name (block-source))))
                 (funcall follow world start))
               (progn
                 (loop for n from start to end
                       ;; a hint to the source: the next 100 blocks (a source may batch them)
                       do (when (zerop (mod (- n start) 100)) (source-call #'block-source-prepare n (min end (+ n 99))))
                          (run-block world n))
                 ;; a bounded range ends on its blocks' verdicts and the last anchor's
                 (fw-drain)
                 (when *full-state* (finish-anchors! end))))
        (progn (stream-finalize!)
               (stop-background!)
               (when (and *mpt-armed* (fboundp 'mpt-stop-worker)) (mpt-stop-worker))))
      (format t "~&summary: txs=~D  gate-mismatches=~D  type4=~D  source-rpc-calls=~D  offline-misses=~D~%"
              (getf *stats* :txs) (getf *stats* :mismatches) (getf *stats* :type4)
              *rpc-calls* *offline-misses*))))

;;; The trie (state/mpt.lisp, Lean-mirrored) backs the receipts-root gate (receipts.lisp) and,
;;; with EITA_MPT_CHECK, the incremental state-root validator (state/mpt-live.lisp, #237): one
;;; persistent account trie on a worker thread fed per-block dirty sets. The worker is a
;;; live aux thread, so a run that also forks would hit SBCL's "cannot fork with multiple
;;; threads running" — the driver does not fork.
;;; The incremental validator (state/mpt-live.lisp, system eita/mpt-live) is kept but cannot
;;; be armed: its anchors were text dumps — written by the deleted dump-state-root, resumed by
;;; the deleted load-state-dump, re-seeded from a world that held every account — and a
;;; snapshot-backed world evicts cold accounts, so the worker can neither be seeded from
;;; it nor resumed into. Step F (the project's complexity ledger) gives mpt-live the
;;; snapshot: seed the worker from snap-N/, take the anchor verdict (n expected computed
;;; ok content-hash) from it in place of `eita check-root`. Until then this is the stub:
;;; EITA_MPT_CHECK is refused, not silently ignored.
(at-startup refuse-mpt-check
  (when (sb-ext:posix-getenv "EITA_MPT_CHECK")
    (error "EITA_MPT_CHECK: the incremental validator cannot be armed until it reads snapshots (step F); run with snapshot root checks instead")))
