;;;; factlog/writer.lisp — the fact-log writer: an observer on the engine's observation seam
;;;; (evm/observe.lisp) that records every verified block as rows of seven tables
;;;; (docs/fact-log.md). The format is factlog/format.lisp's (lean/Evm/FactLog/); this file is
;;;; the row shapes, the capture into the event stream's buffer, the shard encoder subscriber,
;;;; the shards, seals, resume prefixes, the `committed` marker and the code-version manifest.
;;;; A replay installs it when EITA_FACTLOG_DIR names a directory (`bin/eita replay --factlog
;;;; DIR`); unset, nothing of it runs.

(in-package #:eita.factlog.writer)
(defvar *factlog-on* t "The writer's switch (the tests turn it off and on).")

;;; --- The fact log ----------------------------------------
;;; While the verified EVM replays, the writer emits value-bearing, (block, tx)-stamped,
;;; append-only facts, block-range sharded so the directory is the index.
;;;
;;; The tables and their typed columns are lean/Evm/FactLog/Format.lean `tables`
;;; (emitted to src/generated/factlog-schema.lisp). Row shapes, per kind:
;;;   storage_diff  (block tx addr slot pre post)
;;;   account_diff  (block tx addr nonce-pre nonce-post bal-pre bal-post code-pre code-post)
;;;   transfer      (block tx kind depth from to value)  committed native value moves;
;;;                 kind 0 tx envelope, 1 CALL value, 2 CREATE endowment, 3 SELFDESTRUCT sweep,
;;;                 4 a chain's own move; depth = geth convention (0 = envelope/top frame,
;;;                 callee frame for 1/2)
;;;   log           (block tx log-index addr (topic0 ...) "data-hex")  log-index within the tx
;;;   tx            (block tx hash from to value type gas-used status egp)
;;;   block         (block timestamp coinbase base-fee gas-used gas-limit prev-randao
;;;                  blob-gas-used excess-blob-gas)   the last two NIL before Cancun
;;;   call          (block tx frame parent depth kind from to value selector input-len gas gas-used status)
;;;                 one row per EXECUTED frame, top frame included; frame = pre-order index in
;;;                 the fact tx (0 = the top frame), parent = the caller's frame (-1 for a top
;;;                 frame), so the call tree is the rows themselves. kind 0 CALL, 1 CALLCODE,
;;;                 2 DELEGATECALL, 3 STATICCALL, 4 CREATE, 5 CREATE2; from = the calling
;;;                 context, to = the code address (CREATE: the new address); value = the moved
;;;                 value (0 for DELEGATECALL/STATICCALL); selector = the first 4 input bytes
;;;                 as an integer, -1 when shorter; gas = the frame's budget (stipend
;;;                 included); status 0 return, 1 revert, 2 exceptional halt. Rows are written
;;;                 for every frame, also inside a failed tx or a reverted parent (they ran);
;;;                 a frame's effects survive iff it and every ancestor returned. Not
;;;                 recorded: a CALL/CREATE refused before a frame exists (depth, balance,
;;;                 collision, chain frame-init rule, parent out of gas).
;;; tx is the tx's index in the block, -1 for the system work before the user txs and 10^9
;;; for the work after them (chains/block-system.lisp). `log` rows come from the emitted
;;; LOG-N handler (AsmCore.logEmit), which hands each record to the log callback after its gas
;;; charge.
;;;
;;; Two rules keep the log exact without hooking the ~50 mutation sites:
;;;
;;; * storage_diff / account_diff are NET PER TX, derived from the fault seam.
;;;   Every account / slot access is preceded by fault-account! / fault-slot!
;;;   (the invariant the tiered state store also relies on), so the FIRST fault
;;;   of a key within a tx snapshots its pre-image — after the hook, so it is
;;;   the authoritative loaded value — and at tx end every touched key whose
;;;   current value differs is emitted. Writes inside frames that later revert
;;;   net out (pre == post). code-hash = keccak(code) via the memoized
;;;   code-hash-int, 0 when the account has no code (a diff-log datom, not the
;;;   EXTCODEHASH sentinel).
;;;
;;; * transfer is an EVENT, so it mirrors the journal's frame scoping instead:
;;;   pending moves go into a per-tx vector; a frame takes a mark where it
;;;   snapshots parent-jsnap and truncates back to it wherever it calls
;;;   revert-journal-to; tx end emits the survivors iff the tx succeeded —
;;;   exactly the moves whose balance effects committed.
;;;
;;; Shards: one append-only file per (kind, block range) under EITA_FACTLOG_DIR,
;;; EITA_FACTLOG_SHARD blocks each (default 1000):
;;;   <dir>/<kind>/<lo>-<hi>.fct      rows: columnar groups, then the history index
;;;   <dir>/<kind>/<lo>-<hi>.sealed   footer, written when the driver moves past
;;;                                   the range or at factlog-finalize!
;;; Shards open per BLOCK (factlog-block-begin!), not per emission, so a footer's
;;; :first-block/:last-block say exactly which blocks it covers and an empty
;;; sealed shard is the fact "no rows of this kind here". A range whose footer
;;; is complete (first-block = lo, last-block = hi) is skipped on a re-run — the
;;; skip-if-exists incremental model; a partial one is rewritten. The shards are
;;; written and READ (footers, digests, resume prefixes) through the one format library.

(defstartup *factlog-dir*
  (or (sb-ext:posix-getenv "EITA_FACTLOG_DIR") "/tmp/eita-factlog/"))
(defstartup *factlog-shard-blocks*
  (let ((v (sb-ext:posix-getenv "EITA_FACTLOG_SHARD"))) (if v (parse-integer v) 1000)))
(defparameter *factlog-kinds* '(:storage_diff :account_diff :transfer :log :tx :block :call)
  "The kinds this chain's log carries; install-chain-spec! sets it from the chain-spec.")

(defstruct factlog-shard stream builder lo hi (rows 0) first-block last-block min-block max-block
  versions                    ; ((first-block . code-version) ...): who wrote which rows
  (pending (make-array 256 :adjustable t :fill-pointer 0)))  ; rows to encode: (buffer start)…

;;; STREAM is the binary rows file (.fct); BUILDER (eita-factlog:group-builder) holds the rows
;;; not yet written as a group. Groups are flushed at commits (every ~0.5 s, so a group is
;;; about half a second of blocks: tens of thousands of rows during a catch-up, one block at
;;; the tip) and never straddle a block, so every group boundary is a consistent cut.
(defvar *factlog-shards* (make-hash-table :test 'eq)
  "kind -> the one live factlog-shard (blocks arrive in order).")
(defvar *factlog-skip* (make-hash-table :test 'equal)
  "(kind . lo) -> t when that range is complete on disk; skip re-emitting it.")

;;; Durability: one barrier, one policy. The barrier: on Linux one syncfs(2) of the log's
;;; filesystem (one journal commit and cache flush, where N fsyncs cost N: tens of ms each on
;;; a SATA SSD); else fsyncs of the live rows and of every path `factlog-wrote!` noted.
;;; A step that must follow durability (a footer's rename; a `.was` or `.at-N` deletion)
;;; waits in `factlog-after-barrier` and runs inside the next barrier, which returns once
;;; those steps are durable too: files are written and renamed in the same order, only when
;;; they become durable moves. The policy (`factlog-catching-up-p`): at the tip (`at-tip-p`,
;;; the distance to the head the source follows) and in a lazy-state run, a barrier and
;;; `committed` at every commit. Catching up, a crash restarts from the newest verified anchor
;;; and runs again: a barrier at every layer point (the checkpoint, before the layer is
;;; published) and when `committed` moves, at most every +catch-up-commit-s+ (for its
;;; readers); a barrier per commit there would keep the disk busy and the CPU idle.
;;; The address is this process's: libc maps elsewhere in every process (ASLR), so it is
;;; resolved at startup (a saved executable carries its build's addresses otherwise).
(defstartup *syncfs-address*
  (and (find :linux *features*) (sb-sys:find-foreign-symbol-address "syncfs")))
(defconstant +catch-up-commit-s+ 30 "Seconds between `committed` moves while catching up.")
(defvar *factlog-dirty* (make-hash-table :test 'equal :synchronized t) ; lanes seal in parallel
  "Without syncfs: paths to fsync at the barrier.")
(defvar *factlog-after-barrier* '() "Steps waiting for the next barrier, newest first.")
(defun factlog-catching-up-p (n) (and *full-state* (not (at-tip-p n))))
(defun factlog-after-barrier (fn) (push fn *factlog-after-barrier*))
(defun factlog-wrote! (&rest paths)
  "PATHS were written, created, renamed or deleted: durable, with their directory entries,
   at the next barrier."
  (unless *syncfs-address*
    (dolist (p paths)
      (setf (gethash (namestring p) *factlog-dirty*) t
            (gethash (directory-namestring (merge-pathnames p)) *factlog-dirty*) t))))
(defun %factlog-sync ()
  (if *syncfs-address*
      (let ((fd (sb-posix:open (namestring *factlog-dir*) sb-posix:o-rdonly)))
        (unwind-protect
             (let ((r (sb-alien:alien-funcall
                       (sb-alien:sap-alien (sb-sys:int-sap *syncfs-address*)
                                           (function sb-alien:int sb-alien:int))
                       fd)))
               (unless (zerop r) (error "syncfs of ~A failed (errno ~D)" *factlog-dir* (sb-alien:get-errno))))
          (sb-posix:close fd)))
      (progn
        (loop for sh being the hash-values of *factlog-shards*
              do (sb-posix:fsync (sb-sys:fd-stream-fd (factlog-shard-stream sh))))
        (loop for p being the hash-keys of *factlog-dirty*      ; a deleted file: its directory only
              do (let ((fd (ignore-errors (sb-posix:open p sb-posix:o-rdonly))))
                   (when fd (unwind-protect (sb-posix:fsync fd) (sb-posix:close fd)))))
        (clrhash *factlog-dirty*))))
(defun factlog-barrier ()
  "Everything the log wrote so far durable; then the steps that waited for it, until none is left."
  (loop (%factlog-sync)
        (unless *factlog-after-barrier* (return))
        (mapc #'funcall (reverse (shiftf *factlog-after-barrier* nil)))))

(defstartup *factlog-fi-skew-from*
  (let ((e (sb-ext:posix-getenv "EITA_FI_SKEW_FROM"))) (and e (parse-integer e :junk-allowed t)))
  "TEST ONLY: storage_diff rows of blocks at or above it are altered (pre and post swapped),
   standing in for a code change that alters facts, so a crash-and-resume harness can check
   rewrites. It is always paired with EITA_CODE_SALT, so the code version moves with it.")

;;; The encoder is parallel by table: the shards are independent, so the CPU work on them —
;;; encoding pending rows, compressing a group, building a sealed shard's index — runs on one
;;; lane per shard (fork-join) while the encoder thread alone orders events and does every
;;; cross-shard step (`committed`, barriers). A lane touches only its own shard.
(defstruct (lane (:constructor %make-lane)) (go (sb-thread:make-semaphore)) job)
(defvar *lanes* (make-array 0 :adjustable t :fill-pointer 0) "The lane threads, grown on demand.")

(defun lanes-map (fn items)
  "(FN item) for each of ITEMS in parallel, one lane each; the results in order. The first
   error is re-raised here, after every lane has finished."
  (if (null (cdr items))
      (mapcar fn items)
      (let* ((n (length items)) (done (sb-thread:make-semaphore))
             (results (make-array n)) (errors (make-array n :initial-element nil)))
        (loop while (< (fill-pointer *lanes*) n)
              do (let ((l (%make-lane)))
                   (sb-thread:make-thread (lambda () (loop (sb-thread:wait-on-semaphore (lane-go l)) (funcall (lane-job l))))
                                          :name "factlog lane")
                   (vector-push-extend l *lanes*)))
        (loop for x in items for k from 0 for l = (aref *lanes* k)
              do (let ((x x) (k k))
                   (setf (lane-job l) (lambda ()
                                        (handler-case (setf (svref results k) (funcall fn x))
                                          (error (e) (setf (svref errors k) e)))
                                        (sb-thread:signal-semaphore done))))
                 (sb-thread:signal-semaphore (lane-go l)))
        (sb-thread:wait-on-semaphore done :n n)
        (let ((e (find-if-not #'null errors))) (when e (error e)))
        (coerce results 'list))))

(defun factlog-push-pending! (sh)
  "Encode SH's pending rows (each a capture buffer and the start of its fields, block first)
   onto its builder."
  (let* ((gb (factlog-shard-builder sh)) (pending (factlog-shard-pending sh))
         (skew (and *factlog-fi-skew-from* (eq (eita-factlog::group-builder-kind gb) :storage_diff))))
    (loop for k from 0 below (fill-pointer pending) by 2
          for v = (aref pending k) for start = (aref pending (1+ k))
          for block = (svref v start)
          do (if (and skew (>= block *factlog-fi-skew-from*))
                 ;; the test-only skew: pre and post swapped (a fact change the harness expects)
                 (destructuring-bind (b tx a s pre post) (coerce (subseq v start (+ start 6)) 'list)
                   (eita-factlog:builder-push! gb (list b tx a s post pre)))
                 (eita-factlog:builder-push-fields! gb v start))
             ;; bound the memory held between commits (a block with millions of rows)
             (when (> (eita-factlog:group-builder-raw-bytes gb) (* 8 1024 1024))
               (eita-factlog:write-group! gb (factlog-shard-stream sh)))
             (incf (factlog-shard-rows sh))
             (let ((mn (factlog-shard-min-block sh)) (mx (factlog-shard-max-block sh)))
               (when (or (null mn) (< block mn)) (setf (factlog-shard-min-block sh) block))
               (when (or (null mx) (> block mx)) (setf (factlog-shard-max-block sh) block))))
    (setf (fill-pointer pending) 0)))

(defvar *factlog-pending-rows* 0 "Rows queued on the shards, not yet encoded (encoder thread).")
(defconstant +factlog-pending-max+ 262144
  "Pending rows that are encoded at the next commit even when its flush is not due: a pending
   row holds its block's whole capture buffer, read events included, and between 0.5-s flushes
   a catching-up encoder can hold hundreds of dense blocks. A backstop: the byte-bounded pipe already limits what one flush interval can drain, and
   encoding in small runs costs a lane fork-join each.")

(defun factlog-encode-pending! ()
  "Every shard's pending rows onto its builder, in parallel: before any step that reads a
   builder or a shard's row counts (a commit's flush, a seal, a rollback), and whenever
   more than +factlog-pending-max+ rows wait."
  (setf *factlog-pending-rows* 0)
  (lanes-map #'factlog-push-pending!
             (loop for sh being the hash-values of *factlog-shards*
                   when (plusp (fill-pointer (factlog-shard-pending sh))) collect sh)))

;;; --- The code version a shard's rows come from ---
;;; A sealed shard is reused (skipped) on a later run only if the code that wrote every
;;; one of its rows is the code running now (core/src/native/code-version.lisp). Otherwise the
;;; range is rewritten, and at seal the new rows are compared with the ones they replace
;;; (`rewrites.sexp`), so a consumer that already folded the old rows can tell whether
;;; it must re-fold. Rows at or below the resume point cannot be re-derived (no state
;;; before it), so a shard may hold rows of two versions: `:versions` lists the segments.

(defun factlog-publish-code-manifest! ()
  "<factlog>/code/<version>.txt: what the version hashes, for telling two versions apart."
  (let* ((v (engine-code-version))
         (text (code-version-manifest))
         (path (merge-pathnames (format nil "code/~A.txt" v) *factlog-dir*)))
    (when (and text (not (probe-file path)))
      (ensure-directories-exist path)
      (let ((tmp (concatenate 'string (namestring path) ".tmp")))
        (with-open-file (f tmp :direction :output :if-exists :supersede :if-does-not-exist :create)
          (write-string text f) (finish-output f) (sb-posix:fsync (sb-sys:fd-stream-fd f)))
        (sb-posix:rename tmp (namestring path))
        (eita.state::fsync-directory-of path)))
    (format t "~&[factlog] code version ~A~%" v) (force-output)))

(defun factlog-versions-current-p (versions)
  "Lean `Recovery.allCurrent`: every segment was written by the running code."
  (let ((cur (engine-code-version)))
    (and versions (not (equal cur "unknown"))
         (every (lambda (seg) (equal (cdr seg) cur)) versions))))

(defun factlog-versions-upto (versions n)
  "Lean `Recovery.clip`: the segments covering blocks <= N."
  (remove-if (lambda (seg) (> (car seg) n)) versions))

(defun factlog-versions-extend (versions block)
  "Lean `Recovery.extend`: rows from BLOCK on are written by the running code."
  (if (and versions (equal (cdr (car (last versions))) (engine-code-version)))
      versions
      (append versions (list (cons block (engine-code-version))))))

(defun factlog-record-rewrite! (kind lo hi was now)
  "Append to <factlog>/rewrites.sexp whether a rewritten range came out identical to the
   sealed rows it replaced (a consumer reads it to decide whether to re-fold; durable with
   the next barrier, before the `.was` it compares with is deleted)."
  (let* ((path (merge-pathnames "rewrites.sexp" *factlog-dir*))
         ;; a footer without a digest: nothing to compare, so :UNKNOWN — neither
         ;; "identical" nor "differs"
         (comparable (and (or (getf was :content) (getf was :fnv)) t))
         (same (and comparable
                    (if (and (getf was :content) (getf now :content))
                        (equal (getf was :content) (getf now :content))
                        (and (eql (getf was :bytes) (getf now :bytes)) (equal (getf was :fnv) (getf now :fnv)))))))
    (with-open-file (f path :direction :output :if-exists :append :if-does-not-exist :create)
      (let ((*print-pretty* nil))
        (fresh-line f)                  ; a torn tail never glues onto this record
        (prin1 (list :kind kind :lo lo :hi hi :identical (cond (same t) (comparable nil) (t :unknown))
                     :old-versions (getf was :versions) :new-versions (getf now :versions)
                     :old-fnv (getf was :fnv) :new-fnv (getf now :fnv))
               f)
        (terpri f))
      (finish-output f))
    (factlog-wrote! path)
    (cond
      (same)
      ((not comparable)
       (format t "~&[factlog] ~(~A~) ~D-~D: rewritten by ~A; the rows it replaced carry no digest (~A), so whether they differ is unknown~%"
               kind lo hi (engine-code-version) (getf was :versions))
       (force-output))
      (t
      (format t "~&[factlog] ~(~A~) ~D-~D: rewritten by ~A and DIFFERS from the sealed rows it replaced (~A, ~A) — consumers that folded them must re-fold~%"
              kind lo hi (engine-code-version) (getf was :versions) (getf was :fnv))
      (force-output)))))

(defun factlog-settle-was! (kind lo hi now)
  "A `.was` (the footer a rewrite replaced) next to the range's new footer NOW: record
   the comparison, and drop the `.was` once the record is durable (a lost record with no
   `.was` left would lose the comparison). Also run at open, for a crash between seal and
   record. True when there was one."
  (let ((wp (factlog-shard-file kind lo hi "was")))
    (when (probe-file wp)
      (let ((was (eita-factlog:read-footer wp)))
        (when (listp was) (factlog-record-rewrite! kind lo hi was now)))
      (factlog-after-barrier (lambda () (ignore-errors (delete-file wp)) (factlog-wrote! wp)))
      t)))

(defun factlog-range-lo (block)
  (* *factlog-shard-blocks* (floor block *factlog-shard-blocks*)))
(defun factlog-shard-file (kind lo hi type)
  (merge-pathnames (format nil "~(~A~)/~D-~D.~A" kind lo hi type) *factlog-dir*))

(defun factlog-seal-begin! (kind sh)
  "First half of sealing SH: close its rows and write its footer to a .tmp (both durable at
   the next barrier). Returns what `factlog-seal-end!` needs (not SH: its buffers go now)."
  (let* ((s (factlog-shard-stream sh))
         (lo (factlog-shard-lo sh)) (hi (factlog-shard-hi sh))
         (rows-path (factlog-shard-file kind lo hi "fct"))
         (footer (factlog-shard-file kind lo hi "sealed"))
         (tmp (concatenate 'string (namestring footer) ".tmp"))
         (index nil))
    (eita-factlog:write-group! (factlog-shard-builder sh) s)
    (finish-output s)
    ;; the history index (History.lean): the diff tables' rows by key, plus the key filter,
    ;; from the keys of every row the builder has seen — exactly the rows now in the file
    ;; (a kept prefix included: `fct-builder` read them when the range reopened)
    (when (member kind '(:storage_diff :account_diff))
      (multiple-value-bind (section bits distinct) (eita-factlog:index-section (factlog-shard-builder sh))
        (setf index (list :index (file-length s) :bloom-bits bits :bloom-k 7 :keys distinct))
        (write-sequence section s)
        (finish-output s)))
    (close s)
    (multiple-value-bind (bytes fnv) (eita-factlog:digest rows-path)
      (with-open-file (f tmp :direction :output :if-exists :supersede :if-does-not-exist :create)
        (let ((*print-pretty* nil))
          (prin1 (append (list :kind kind :lo lo :hi hi
                               :rows (factlog-shard-rows sh)
                               :first-block (factlog-shard-first-block sh)
                               :last-block (factlog-shard-last-block sh)
                               :min-block (factlog-shard-min-block sh)
                               :max-block (factlog-shard-max-block sh)
                               :bytes bytes :fnv fnv
                               :content (eita-factlog:builder-content (factlog-shard-builder sh)))
                         index
                         (list :version (engine-code-version)
                               :versions (factlog-shard-versions sh)))
                 f)
          (terpri f))
        (finish-output f))
      (factlog-wrote! rows-path tmp)
      (list kind lo hi (and (eql (factlog-shard-first-block sh) lo) (eql (factlog-shard-last-block sh) hi))
            (list :bytes bytes :fnv fnv :content (eita-factlog:builder-content (factlog-shard-builder sh))
                  :versions (factlog-shard-versions sh))
            tmp footer))))

(defun factlog-seal-end! (sealing)
  "Second half, in a barrier (rows and footer .tmp durable): publish the footer."
  (destructuring-bind (kind lo hi whole now tmp footer) sealing
    ;; durable when the barrier returns; a footer lost to a power loss only makes the range
    ;; look incomplete, and it is rewritten (its `.at` prefixes go only after it is durable)
    (rename-file tmp footer)
    (factlog-wrote! footer)
    ;; a rewrite: compare with the rows it replaced, now that the new ones are sealed —
    ;; only once they cover the whole range. A run that ends mid-range (an error, a fixed
    ;; end block) seals a partial range, which differs from the complete rows it replaced
    ;; even when the facts are identical. The `.was` stays until the range is complete; the
    ;; rewrite that completes it records the comparison.
    (when whole
      (factlog-settle-was! kind lo hi now)
      ;; the footer covers the whole range now; its checkpoint prefixes are spent. A
      ;; partial seal keeps them: a later run that resumes inside this range drops the
      ;; partial footer and needs `.at-N` to keep rows LO..N (an error exit that seals a
      ;; range mid-rewrite, then a restart that resumes inside it).
      (factlog-after-barrier (lambda () (dolist (p (directory (factlog-shard-file kind lo hi "at-*")))
                                          (ignore-errors (delete-file p)) (factlog-wrote! p)))))))

(defun factlog-seal-all! (pairs)
  "Close every (KIND . SHARD) of PAIRS and publish its footer at the next barrier; the range
   is complete on disk iff first-block = lo and last-block = hi, and its rows match the
   footer's :bytes/:fnv. Order: rows and footer .tmp durable, then the rename — a footer on
   disk always describes rows already on disk."
  (factlog-encode-pending!)
  (dolist (x (lanes-map (lambda (p) (factlog-seal-begin! (car p) (cdr p))) pairs))
    (let ((x x)) (factlog-after-barrier (lambda () (factlog-seal-end! x))))))

(defun factlog-range-complete-p (kind lo hi)
  "The footer (true) when a sealed footer on disk covers [lo, hi] entirely and the rows on disk
   (any form) match its :bytes/:fnv. A footer without a digest is taken at its word. A digest
   mismatch — rows torn by a crash, or altered — makes the range incomplete, so this run
   rewrites it."
  (let ((ft (eita-factlog:read-footer (factlog-shard-file kind lo hi "sealed"))))
    (and (eita-factlog:footer-complete-p ft lo hi)
         (if (null (getf ft :fnv))
             ft
             (let ((rows (eita-factlog:rows-file *factlog-dir* kind lo hi)))
               (multiple-value-bind (bytes fnv) (and rows (eita-factlog:digest rows))
                 (or (and (eql bytes (getf ft :bytes)) (equal fnv (getf ft :fnv)) ft)
                     (progn
                       (format t "~&[factlog] ~(~A~) ~D-~D: rows do not match the footer (~A bytes ~A, footer ~A ~A); rewriting the range~%"
                               kind lo hi bytes fnv (getf ft :bytes) (getf ft :fnv))
                       (force-output)
                       nil))))))))

(defun factlog-prefix-file (kind lo hi n)
  (factlog-shard-file kind lo hi (format nil "at-~D" n)))

(defun factlog-resume-prefix (kind lo hi n path)
  "A run resuming at N+1 inside KIND's range LO-HI: when the checkpoint at N left a
   prefix record and the rows file still starts with exactly those bytes, truncate the
   file to them and return the record (the rows of blocks LO..N are kept: no state
   before N is loaded, so they could not be re-derived). Else, when the footer a rewrite
   retired (`.was`) still describes the rows file byte for byte — a run that retired it
   and died before keeping the prefix — keep the prefix from it (`factlog-scan-prefix`).
   NIL otherwise."
  (let ((ft (eita-factlog:read-footer (factlog-prefix-file kind lo hi n)))
        (was (eita-factlog:read-footer (factlog-shard-file kind lo hi "was"))))
    (flet ((starts-with (record &optional (limit (getf record :bytes)))
             (multiple-value-bind (bytes fnv) (eita-factlog:digest path :limit limit)
               (and (eql bytes (getf record :bytes)) (equal fnv (getf record :fnv))))))
      (cond ((not (probe-file path)) nil)
            ((and ft (starts-with ft))
             (sb-posix:truncate (namestring path) (getf ft :bytes))
             ft)
            ((and (eita-factlog:footer-complete-p was lo hi) (starts-with was nil))
             (factlog-scan-prefix kind lo hi n path was))
            (ft
             (format t "~&[factlog] ~(~A~) ~D-~D: rows file does not start with the checkpoint prefix at ~D~%" kind lo hi n)
             (force-output)
             nil)))))

(defun factlog-refuse-loss (kind lo hi n path)
  "Opening KIND's range LO-HI at N+1 with no rows of LO..N kept: refuse when that drops
   rows — the rows file holds a row of a block <= N, or the range before LO is on disk (the
   log covers blocks before LO, so it must cover LO..N). Only the log's first range, begun
   by a run that started inside it, legitimately starts after LO."
  (let ((before (and (>= lo *factlog-shard-blocks*)
                     (let ((plo (- lo *factlog-shard-blocks*)))
                       (or (probe-file (factlog-shard-file kind plo (1- lo) "sealed"))
                           (eita-factlog:rows-file *factlog-dir* kind plo (1- lo))))))
        (rows (if (probe-file path) (nth-value 1 (eita-factlog:fct-prefix-end path kind n)) 0)))
    (when (or before (plusp rows))
      (error "~(~A~) ~D-~D: resuming at block ~D would drop the rows of blocks ~D..~D (~:[~D of them in the rows file~;~*the range before is in the log~]) and no checkpoint prefix (`.at-~D`) or retired footer (`.was`) matching the rows file keeps them; resume from a snapshot at or before block ~D, or restore the range's rows and footer"
             kind lo hi (1+ n) lo n before rows n (1- lo)))))

(defun %factlog-checkpoint! (n)
  "Checkpoint at block N, before its state dump is written. Checkpoints need not fall on
   shard boundaries (anchors every 262144 blocks, shards of 1000), so a run resuming from N
   restarts inside a range whose rows LO..N it cannot re-derive. For every live shard,
   publish `<lo>-<hi>.at-N` = the digest of its rows so far, which are exactly the rows
   of blocks LO..N; `factlog-resume-prefix` keeps them. Rows, `committed` and the footers
   sealed since the last barrier first, then the records, all durable before the dump — a
   durable dump implies durable rows and prefixes."
  (when *factlog-on*
    (%factlog-commit! n :force t)
    (factlog-publish-prefixes!
     (loop for kind being the hash-keys of *factlog-shards* using (hash-value sh)
           for lo = (factlog-shard-lo sh) for hi = (factlog-shard-hi sh)
           collect (multiple-value-bind (bytes fnv) (eita-factlog:digest (factlog-shard-file kind lo hi "fct"))
                     (list (factlog-prefix-file kind lo hi n)
                           (list :block n :first-block (factlog-shard-first-block sh)
                                 :rows (factlog-shard-rows sh)
                                 :min-block (factlog-shard-min-block sh)
                                 :max-block (factlog-shard-max-block sh)
                                 :versions (factlog-shard-versions sh)
                                 :bytes bytes :fnv fnv)))))))

(defun factlog-publish-prefixes! (sides)
  "Publish each (PATH RECORD) of SIDES, a `<lo>-<hi>.at-N`: every tmp, barrier, every
   rename, barrier. Durable on return: callers truncate rows after it."
  (when sides
    (loop for (side record) in sides
          for tmp = (concatenate 'string (namestring side) ".tmp")
          do (with-open-file (f tmp :direction :output :if-exists :supersede :if-does-not-exist :create)
               (let ((*print-pretty* nil)) (prin1 record f) (terpri f)))
             (factlog-wrote! tmp))
    (factlog-barrier)
    (loop for (side) in sides
          do (sb-posix:rename (concatenate 'string (namestring side) ".tmp") (namestring side))
             (factlog-wrote! side))
    (factlog-barrier)))

(defun factlog-retire-footer! (kind lo hi)
  "A sealed range is about to be rewritten (another code version wrote it): keep its
   footer as `.was`, so the rewrite can be compared with it at seal, and so a crash
   mid-rewrite never leaves a footer describing new partial rows. The caller makes the
   rename durable (a barrier) before the rows file is truncated."
  (let ((ft (factlog-shard-file kind lo hi "sealed"))
        (wp (factlog-shard-file kind lo hi "was")))
    (when (probe-file ft)
      (if (probe-file wp)
          (delete-file ft)
          (sb-posix:rename (namestring ft) (namestring wp)))
      (factlog-wrote! ft wp))))

(defun factlog-scan-prefix (kind lo hi n path footer)
  "The rows of blocks LO..N of a sealed, digest-verified range (its checkpoint prefixes
   were spent at seal): cut PATH to them and return the prefix record. Rows are in block
   order, so the prefix ends at the first row of a block above N. A group holding blocks on
   both sides of N (a converted shard's groups span blocks)
   keeps its rows <= N re-encoded as one group, in a copy that replaces PATH once the
   record describes it."
  (multiple-value-bind (off rows mn mx straddler) (eita-factlog:fct-prefix-end path kind n)
    (let ((cut (and straddler (concatenate 'string (namestring path) ".cut"))))
      (when cut
        (with-open-file (out cut :direction :output :element-type '(unsigned-byte 8) :if-exists :supersede)
          (write-sequence (eita-factlog::read-file-bytes path) out :end off)
          (let ((gb (eita-factlog:make-group-builder kind)))
            (dolist (row straddler) (eita-factlog:builder-push! gb row))
            (eita-factlog:write-group! gb out))
          (finish-output out)
          (factlog-wrote! cut)
          (setf off (file-length out))))
      (let ((record (list :block n :first-block lo :rows rows :min-block mn :max-block mx
                          :versions (factlog-versions-upto (or (getf footer :versions) (list (cons lo "unknown"))) n)
                          :bytes off :fnv (nth-value 1 (eita-factlog:digest (or cut path) :limit off)))))
        ;; Make the kept prefix a checkpoint prefix BEFORE cutting: the footer is retired
        ;; now, so a crash mid-rewrite finds no footer and resumes through the `.at-N`
        ;; record like any mid-shard resume — without it the rows LO..N would be lost. A
        ;; crash before the record or before the copy replaces PATH resumes through the
        ;; `.was` instead.
        (factlog-publish-prefixes! (list (list (factlog-prefix-file kind lo hi n) record)))
        (if cut
            (progn (sb-posix:rename cut (namestring path)) (factlog-wrote! path) (factlog-barrier))
            (sb-posix:truncate (namestring path) off))
        (format t "~&[factlog] ~(~A~) ~D-~D: rewriting from block ~D; rows ~D..~D kept from the sealed range (~D rows, ~D bytes)~%"
                kind lo hi (1+ n) lo n rows off)
        (force-output)
        record))))

(defun factlog-range-plan (kind lo hi)
  "(values SKIP FOOTER) for KIND's range LO-HI: SKIP when it is already complete on disk
   AND was written by the running code; FOOTER when it is complete but of another
   version — then it is rewritten, and its footer is retired to `.was` here (made durable
   by the caller's barrier before the rows are touched)."
  (let ((key (cons kind lo)) (footer nil))
    (multiple-value-bind (skip seen) (gethash key *factlog-skip*)
      (unless seen
        (setf footer (factlog-range-complete-p kind lo hi))
        ;; a rewrite sealed but its comparison was never recorded (crash between): the
        ;; `.was` gone before this footer is retired to it
        (when (and footer (factlog-settle-was! kind lo hi footer)) (factlog-barrier))
        (setf skip (and footer (factlog-versions-current-p (getf footer :versions)))
              (gethash key *factlog-skip*) skip)
        (when (and footer (not skip))
          (format t "~&[factlog] ~(~A~) ~D-~D: sealed by code ~A, running ~A — rewriting~%"
                  kind lo hi (or (getf footer :versions) "unrecorded") (engine-code-version))
          (force-output)
          ;; rewriting: retire the old footer first, so a crash mid-rewrite can never
          ;; leave it describing new partial rows
          (factlog-retire-footer! kind lo hi)))
      (values skip footer))))

(defun factlog-open-range! (kind block lo hi footer)
  "Open KIND's live shard for range LO-HI at BLOCK (its footer, if any, already retired)."
  (let ((path (factlog-shard-file kind lo hi "fct")))
    (ensure-directories-exist path)
    ;; one rows file per range, and one format: a text shard here means the log was not
    ;; converted to the binary form before this writer ran
    (dolist (type '("sexp" "sexp.gz"))
      (when (probe-file (factlog-shard-file kind lo hi type))
        (error "~(~A~) ~D-~D: text shard present; convert the log before running the writer (sbcl --script src/factlog/format.lisp <dir> convert)" kind lo hi)))
    (unless footer (ignore-errors (delete-file (factlog-shard-file kind lo hi "sealed"))))
    (let* ((prefix (and (> block lo)
                        (if footer
                            (factlog-scan-prefix kind lo hi (1- block) path footer)
                            (or (factlog-resume-prefix kind lo hi (1- block) path)
                                (factlog-refuse-loss kind lo hi (1- block) path)))))
           (stream (if prefix
                       (open path :direction :output :element-type '(unsigned-byte 8) :if-exists :append)
                       (open path :direction :output :element-type '(unsigned-byte 8) :if-exists :supersede
                                                     :if-does-not-exist :create)))
           ;; with kept rows, the shard's content hash and index keys continue over them
           (builder (if prefix (eita-factlog:fct-builder path kind) (eita-factlog:make-group-builder kind))))
      (when prefix
        (sb-posix:fsync (sb-sys:fd-stream-fd stream)))   ; the truncation
      ;; the new file's directory entry (and its kind's), durable with the barrier before
      ;; `committed` names its rows: else a power loss can drop the whole file while the
      ;; marker names them
      (factlog-wrote! path (string-right-trim "/" (directory-namestring path)))
      (setf (gethash kind *factlog-shards*)
            (make-factlog-shard
             :stream stream :builder builder :lo lo :hi hi :last-block block
             :first-block (if prefix (getf prefix :first-block) block)
             :rows (if prefix (getf prefix :rows) 0)
             :min-block (and prefix (getf prefix :min-block))
             :max-block (and prefix (getf prefix :max-block))
             :versions (factlog-versions-extend
                        (and prefix (or (getf prefix :versions)
                                        (list (cons (getf prefix :first-block) "unknown"))))
                        block))))))

(defun factlog-open-shard (kind block)
  "The live shard for KIND covering BLOCK, sealing a stale one first. NIL when the range
   is already complete on disk AND was written by the running code; a complete range
   of another version is rewritten, keeping only the rows this run cannot re-derive."
  (let* ((lo (factlog-range-lo block))
         (hi (+ lo *factlog-shard-blocks* -1))
         (sh (gethash kind *factlog-shards*)))
    (when (and sh (/= (factlog-shard-lo sh) lo))
      (factlog-seal-all! (list (cons kind sh)))
      (remhash kind *factlog-shards*)
      (setf sh nil))
    (or sh
        (multiple-value-bind (skip footer) (factlog-range-plan kind lo hi)
          (unless skip (factlog-open-range! kind block lo hi footer))))))

(defun factlog-roll! (block)
  "Every kind enters BLOCK's range together: the stale shards sealed (their footers published
   at the next barrier), the new ranges planned and opened. A barrier here only when a range is
   rewritten: its retired footer (`.was`) durable before its rows file is truncated."
  (let* ((lo (factlog-range-lo block))
         (hi (+ lo *factlog-shard-blocks* -1))
         (stale (loop for kind in *factlog-kinds*
                      for sh = (gethash kind *factlog-shards*)
                      when (and sh (/= (factlog-shard-lo sh) lo)) collect (cons kind sh))))
    (factlog-seal-all! stale)            ; the stale shards' pending rows encoded first
    (dolist (p stale) (remhash (car p) *factlog-shards*))
    (let ((plans (loop for kind in *factlog-kinds*
                       unless (gethash kind *factlog-shards*)
                         collect (cons kind (multiple-value-list (factlog-range-plan kind lo hi))))))
      (when (some (lambda (p) (and (third p) (not (second p)))) plans)
        (factlog-barrier))
      (loop for (kind skip footer) in plans
            unless skip do (factlog-open-range! kind block lo hi footer)))))

(defun %factlog-block-begin! (block)
  "Driver hook at each block start: open (or roll) every kind's shard so
   coverage is tracked per block, and flush the previous block's rows."
  (when *factlog-on*
    (let ((lo (factlog-range-lo block)))
      (when (some (lambda (kind)
                    (let ((sh (gethash kind *factlog-shards*)))
                      (if sh
                          (/= (factlog-shard-lo sh) lo)
                          (not (nth-value 1 (gethash (cons kind lo) *factlog-skip*))))))
                  *factlog-kinds*)
        (factlog-roll! block)))
    (dolist (kind *factlog-kinds*)
      (let ((sh (factlog-open-shard kind block)))
        (when sh
          (setf (factlog-shard-last-block sh) block)
          (finish-output (factlog-shard-stream sh)))))))

(defvar *factlog-last-committed* nil
  "Highest block this run has committed; the end-of-run seal publishes it unthrottled.")
(defvar *factlog-flushed-at* 0 "Internal real time the last commit's flush finished (throttle).")
(defvar *factlog-committed-at* 0 "Internal real time `committed` last moved.")

(defun factlog-write-marker! (n durable)
  "Publish `committed` = N: tmp, the barrier (the rows of every block <= N, flushed by the
   caller, and the tmp durable), rename; with DURABLE the rename made durable too."
  (let* ((path (merge-pathnames "committed" *factlog-dir*))
         (tmp (concatenate 'string (namestring path) ".tmp")))
    (ensure-directories-exist path)
    (with-open-file (f tmp :direction :output :if-exists :supersede :if-does-not-exist :create)
      (format f "~D~%" n))
    (factlog-wrote! tmp)
    (factlog-barrier)
    ;; sb-posix:rename, not RENAME-FILE: the latter would merge the missing type
    ;; back from "committed.tmp" and rename the file onto itself
    (sb-posix:rename tmp (namestring path))
    (factlog-wrote! path)
    ;; DURABLE: a marker moved backwards must not roll forward again on a power
    ;; loss — the rows it gave up are about to be truncated
    (when durable (factlog-barrier))))

(defun %factlog-commit! (n &key force durable)
  "Block N passed its header gate: flush its rows (a group per shard) and publish
   `<factlog>/committed` = N, the frontier consumers read up to, never naming a block
   whose rows are not durable. On the writer thread; unforced, a flush no sooner than 0.5 s
   after the last ENDED (a write slower than a start-to-start gap would leave the writer no
   time for rows), and `committed` with it — while catching up at most every
   +catch-up-commit-s+. A lagging marker is safe, a leading one not."
  (when *factlog-on*
    (if (or force (>= (- (get-internal-real-time) *factlog-flushed-at*)
                      (floor internal-time-units-per-second 2)))
      (progn
        ;; Rows and marker durable, not just flushed: after a power loss the marker must not
        ;; name a block whose rows did not survive, nor be an empty file (Evm/Persist/Recovery.lean,
        ;; `published_good`). A marker that rolls back to its previous, smaller value only lags.
        (factlog-encode-pending!)
        (lanes-map (lambda (sh)
                     (let ((s (factlog-shard-stream sh)))
                       ;; the pending rows become a group: block boundaries only (we are between
                       ;; blocks), so every group boundary is a consistent cut
                       (eita-factlog:write-group! (factlog-shard-builder sh) s)
                       (finish-output s)))
                   (loop for sh being the hash-values of *factlog-shards* collect sh))
        (when (or force (not (factlog-catching-up-p n))
                  (>= (- (get-internal-real-time) *factlog-committed-at*)
                      (* +catch-up-commit-s+ internal-time-units-per-second)))
          (factlog-write-marker! n durable)
          (setf *factlog-committed-at* (get-internal-real-time)))
        (setf *factlog-flushed-at* (get-internal-real-time)))
      ;; not due: only bound what waits (onto the builders; no group, no barrier, no marker)
      (when (> *factlog-pending-rows* +factlog-pending-max+) (factlog-encode-pending!)))
    (setf *factlog-last-committed* n)))

(defun %factlog-rollback! (n)
  "A reorg rolled the state back to block N, a layer point (whose `.at-N` prefixes the
   checkpoint published): forget every row above N. Live shards are closed unsealed (they
   reopen at N+1 through the prefix and truncate to it); a range sealed since, and
   containing N, keeps its rows up to N (`factlog-scan-prefix`, the code-change rewrite
   path); ranges wholly above N lose their footers and are rewritten; `committed` = N."
  (when *factlog-on*
    (factlog-encode-pending!)
    (factlog-barrier)                   ; the footers waiting for it published: retired below
    (let ((top (or *factlog-last-committed* n)))
      (maphash (lambda (kind sh) (declare (ignore kind)) (close (factlog-shard-stream sh))) *factlog-shards*)
      (clrhash *factlog-shards*)
      (clrhash *factlog-skip*)
      (dolist (kind *factlog-kinds*)
        (loop for lo from (factlog-range-lo n) to (factlog-range-lo top) by *factlog-shard-blocks*
              for hi = (+ lo *factlog-shard-blocks* -1)
              for footer = (eita-factlog:read-footer (factlog-shard-file kind lo hi "sealed"))
              when (and footer (> hi n))
                do (factlog-retire-footer! kind lo hi)
                   (when (<= lo n)
                     (factlog-scan-prefix kind lo hi n (factlog-shard-file kind lo hi "fct") footer))))
      (factlog-write-marker! n t)
      (setf *factlog-last-committed* n))))

(defun %factlog-finalize! ()
  "Seal every live shard (end of run), after publishing the last committed block."
  (when *factlog-on*
    (when *factlog-last-committed* (%factlog-commit! *factlog-last-committed* :force t))
    (factlog-seal-all! (loop for kind being the hash-keys of *factlog-shards*
                             using (hash-value sh) collect (cons kind sh)))
    (clrhash *factlog-shards*)
    (factlog-barrier)))


;;; --- Rows in the event stream's buffer ---
(eval-when (:compile-toplevel :load-toplevel :execute)   ; the capture macros expand with them
    (defconstant +fw-sort+ 8)
  (defparameter +fw-widths+
    (coerce (append (mapcar (lambda (k) (1+ (length (eita-factlog:table-cols k)))) eita-factlog:+kinds+)
                    (list 2 2))
            'simple-vector)
    "Record width by code: a row is its code and its columns; an event or sort header 2."))

(defmacro fw-row (kind &rest fields)
  "Capture one row of KIND (a literal table keyword); FIELDS are its columns, block first."
  (let ((code (position kind eita-factlog:+kinds+))
        (vars (loop repeat (length fields) collect (gensym "F"))))
    (unless (and code (= (length fields) (length (eita-factlog:table-cols kind))))
      (error "fw-row: ~S is not a fact table of ~D columns" kind (length fields)))
    `(let ,(mapcar #'list vars fields)
       (multiple-value-bind (v i) (eita.evm::fw-reserve ,(1+ (length fields)))
         (setf (svref v i) ,code
               ,@(loop for var in vars for k from 1 append `((svref v (+ i ,k)) ,var)))))))

(defmacro with-fw-sorted ((kind) &body body)
  "The rows of KIND (all BODY captures) are one run the encoder sorts: a +fw-sort+ header
   counts them; none, no header."
  (let ((w (svref +fw-widths+ (position kind eita-factlog:+kinds+))))
    `(let ((hdr (nth-value 1 (eita.evm::fw-reserve 2))))
       ,@body
       (let ((n (floor (- (eita.evm::fw-batch-fill eita.evm::*fw-batch*) hdr 2) ,w)))
         (if (zerop n)
             (setf (eita.evm::fw-batch-fill eita.evm::*fw-batch*) hdr)
             (let ((v (eita.evm::fw-batch-vec eita.evm::*fw-batch*)))
               (setf (svref v hdr) +fw-sort+ (svref v (1+ hdr)) n)))))))

(defun encoder-event (ev)
  "The shard encoder: the events, in capture order, onto the shards. Events of other
   subscribers (the verifier's, the hooks' records) pass by."
  (case (car ev)
    (:block-begin (%factlog-block-begin! (second ev)))
    (:commit (eita.evm::require-verified (fifth ev))
     (%factlog-commit! (second ev) :force (third ev) :durable (fourth ev)))
    (:checkpoint (%factlog-checkpoint! (second ev)))
    (:rollback (%factlog-rollback! (second ev)))
    (:finalize (%factlog-finalize!))))

(defun encoder-row (code v i n)
  "The encoder's rows: the row at I, or a +fw-sort+ run in key order (address, then slot:
   unique in a tx, so the order is total), queued on their shards. Returns the next index."
  (declare (type simple-vector v) (type fixnum i n) (ignore n))
  (if (eql code +fw-sort+)
      (let* ((k (svref v (1+ i))) (kc (svref v (+ i 2))) (w (svref +fw-widths+ kc))
             (run (coerce (loop for j below k collect (+ i 2 (* j w))) 'simple-vector)))
        (declare (type fixnum k w))
        ;; a record's fields after its code: block, tx, address, slot
        (flet ((key< (a b) (let ((x (svref v (+ a 3))) (y (svref v (+ b 3))))
                             (or (< x y) (and (= x y) (eql kc #.(position :storage_diff eita-factlog:+kinds+))
                                              (< (svref v (+ a 4)) (svref v (+ b 4))))))))
          (loop for r across (sort run #'key<) do (%factlog-queue-row! kc v (1+ r))))
        (+ i 2 (* k w)))
      (progn (%factlog-queue-row! code v (1+ i))
             (+ i (svref +fw-widths+ code)))))

(defmacro factlog-emit! (kind block &rest fields)
  "Capture one row (BLOCK . FIELDS) of KIND (a literal table keyword)."
  `(when *factlog-on* (fw-row ,kind ,block ,@fields)))
(defun %factlog-queue-row! (code v start)
  "Queue the row whose fields (block first) are V[START…] on the shard of its table (CODE)
   for its block; a lane encodes it at the next step that needs it (`factlog-encode-pending!`)."
  (when *factlog-on*
    (let ((sh (factlog-open-shard (nth code eita-factlog:+kinds+) (svref v start))))
      (when sh
        (vector-push-extend v (factlog-shard-pending sh))
        (vector-push-extend start (factlog-shard-pending sh))
        (incf *factlog-pending-rows*)))))


;;; --- The rows of a block, a tx, a tx's summary ---
(defun block-fact-row (blk fork-ord)
  "The `block` fact of BLK at FORK-ORD: its header's fields, consensus inputs — gas-used the
   header's, PREVRANDAO as the EVM saw it (block-prev-randao), blob gas NIL before Cancun.
   The one definition: the observer writes it and the blob backfill re-emits it."
  (list (blk-number blk) (blk-timestamp blk) (blk-miner blk) (or (blk-base-fee blk) 0) (blk-gas-used blk)
        (blk-gas-limit blk) (eita.chain::block-prev-randao blk fork-ord)
        (blk-blob-gas-used blk) (blk-excess-blob-gas blk)))

(defun factlog-tx-rows (block tx success)
  "A tx's rows from its touched-state summary: the net account and storage diffs (each a
   run the encoder puts in key order, so shards are byte-deterministic), the `call` rows,
   and — iff the tx succeeded — the committed transfers and logs, in order."
  (with-fw-sorted (:account_diff)
    (eita.evm::do-account-changes (a n0 n1 b0 b1 h0 h1)
      (factlog-emit! :account_diff block tx a n0 n1 b0 b1 h0 h1)))
  (with-fw-sorted (:storage_diff)
    (eita.evm::do-storage-changes (a s pre post)
      (factlog-emit! :storage_diff block tx a s pre post)))
  (when eita.evm::*observe-calls*
    (eita.evm::do-call-frames (f p d k from to value sel ilen gas used status)
      (factlog-emit! :call block tx f p d k from to value sel ilen gas used status)))
  (when success
    (eita.evm::do-tx-events (:transfer (kind depth from to value) :log (index addr topics data))
      (:transfer (factlog-emit! :transfer block tx kind depth from to value))
      (:log (factlog-emit! :log block tx index addr topics data)))))

;;; Installing it (the observation seam): the directory, the chain's kinds (a chain-spec's
;;; :observe-kinds: a chain whose log began without `call` rows keeps them out), the row
;;; widths, the observer. The driver calls it before the first block, after the chain is
;;; installed, when EITA_FACTLOG_DIR is set (evm/observe.lisp `load-observer!`).
(defun install-factlog-observer! (&optional (dir (nonempty-env "EITA_FACTLOG_DIR")))
  "Record the blocks of this run into the fact log at DIR (default EITA_FACTLOG_DIR, else
   *factlog-dir*)."
  (when dir (setf *factlog-dir* (namestring (eita-factlog::as-dir dir))))
  (setf eita.evm::*fw-widths* +fw-widths+)
  (setf *factlog-kinds* (or eita.chain::*chain-observe-kinds* '(:storage_diff :account_diff :transfer :log :tx :block :call))
        eita.evm::*observe-calls* (and (member :call *factlog-kinds*) t))

  (setf *observer*
        (make-observer
         :name "factlog"
         :attach (lambda () (attach-subscriber! "encoder" #'encoder-event :on-row #'encoder-row :rolls-back t))
         :start (lambda (start) (declare (ignore start)) (factlog-publish-code-manifest!))
         :block (lambda (blk fork-ord)
                  (destructuring-bind (bn bts bcb bfee bgas blimit randao blob-gas excess) (block-fact-row blk fork-ord)
                    (factlog-emit! :block bn bts bcb bfee bgas blimit randao blob-gas excess)))
         :retain (lambda (n dir)   ; a retained anchor (core anchors.lisp): the shard files at N, copied
                   ;; (a resume truncates a rows file to its prefix at N: never a link)
                   (dolist (kind *factlog-kinds*)
                     (let ((lo (factlog-range-lo n)))
                       (dolist (f (directory (merge-pathnames (format nil "~(~A~)/~D-~D.*" kind lo (+ lo *factlog-shard-blocks* -1)) *factlog-dir*)))
                         (let ((to (merge-pathnames (format nil "~(~A~)/~A" kind (file-namestring f)) dir)))
                           (ensure-directories-exist to)
                           (alexandria:copy-file f to))))))
         :tx-end #'factlog-tx-rows
         :tx-result (lambda (n idx tx gas status egp)
                      ;; OUR gas-used / status (-1 = skipped, unverified) and OUR effective gas price
                      (factlog-emit! :tx n idx (eita.evm::tx-hash tx)  ; 0: source has no tx hash
                                     (tx-sender tx) (tx-to tx) (tx-value tx) (tx-type tx)
                                     gas (if (eq status :skip) -1 status) egp)))))
