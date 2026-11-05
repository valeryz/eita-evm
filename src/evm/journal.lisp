;;;; evm/journal.lisp — per-tx state (EIP-2929 sets, transient storage, refunds, created set,
;;;; originals), the revert journal, the per-tx destroyed and touched sets.

(in-package #:eita.evm)

;;; Per-tx state — EIP-2929 accessed sets, EIP-1153 transient storage,
;;; EIP-3529 refund counter, EIP-6780 created set, EIP-2200 originals —
;;; lives natively in *tx-state* (c/tx_state.h). The wrappers below
;;; marshal integers into scratch u256 buffers and call into libeita.
;;; Every mutation journals into the current frame's TxArena, so a
;;; reverting frame restores all of it (EELS frame-scope semantics).

(defstartup *u256-scratch-a* (foreign-alloc :uint8 :count 32))
(defstartup *u256-scratch-k* (foreign-alloc :uint8 :count 32))
(defstartup *u256-scratch-v* (foreign-alloc :uint8 :count 32))
(defstartup *u256-scratch-o* (foreign-alloc :uint8 :count 32))

(declaim (inline current-arena))
(defun current-arena ()
  "The TxArena journal scope for the running frame — its cb_ctx (offset
   504) — or the root arena when no frame is active (reset-tx-state,
   apply-tx prologue)."
  (if (null-pointer-p *current-state*)
      *tx-arena-root*
      (mem-ref *current-state* :pointer 504)))

(defun access-addr! (addr)
  "Return T if cold (first access this tx), NIL if warm. Marks as warm.
   PRE-BERLIN FAST PATH: EIP-2929 warm/cold is gas-neutral before Berlin
   (ord 10) — every pre-Berlin gas plan ignores the cold bit, and access-cost's
   cold/warm table entries are equal. So skip the native set-insert + its
   journal entry entirely and report cold=T. This was ~13% of replay time on
   the (all pre-Berlin) 0–5M range; the work was pure waste there."
  (if (< *fork-ord* 10)
      t
      (progn (u256-write *u256-scratch-a* addr)
             (= 1 (%ts-access-addr *tx-state* (current-arena) *u256-scratch-a*)))))

(defun access-slot! (addr slot)
  (if (< *fork-ord* 10)
      t                                 ; pre-Berlin: see access-addr!
      (progn (u256-write *u256-scratch-a* addr)
             (u256-write *u256-scratch-k* slot)
             (= 1 (%ts-access-slot *tx-state* (current-arena)
                                   *u256-scratch-a* *u256-scratch-k*)))))

(defun created-insert! (addr)
  (u256-write *u256-scratch-a* addr)
  (%ts-created-insert *tx-state* (current-arena) *u256-scratch-a*))

(defun created-p! (addr)
  (u256-write *u256-scratch-a* addr)
  (= 1 (%ts-created-p *tx-state* *u256-scratch-a*)))

(defun orig-record! (addr slot cur)
  "First-touch snapshot of the original (tx-start) value. Not journaled."
  (u256-write *u256-scratch-a* addr)
  (u256-write *u256-scratch-k* slot)
  (u256-write *u256-scratch-v* cur)
  (%ts-orig-record *tx-state* *u256-scratch-a* *u256-scratch-k* *u256-scratch-v*))

(defun orig-get! (addr slot cur)
  "The original (tx-start) value of (addr, slot); CUR when untouched."
  (u256-write *u256-scratch-a* addr)
  (u256-write *u256-scratch-k* slot)
  (u256-write *u256-scratch-v* cur)
  (%ts-orig-get *tx-state* *u256-scratch-a* *u256-scratch-k*
                *u256-scratch-v* *u256-scratch-o*)
  (u256-read *u256-scratch-o*))

(defun refund-add! (delta)
  (%ts-refund-add *tx-state* (current-arena) delta))

(defun ts-refund ()
  (mem-ref *tx-state* :int64 0))

;;; Incremental state-root dirty hook (#237). mpt-live.lisp (loaded only under
;;; EITA_MPT_CHECK) redefines *mpt-tracking* / mpt-touch! to union the addr into
;;; the per-block dirty set on a worker thread. These stubs make a normal replay
;;; pay nothing (the inlined `when` folds away) and let replay-cl call the hook
;;; unconditionally.
(defvar *mpt-tracking* nil)
;; NOT inline: mpt-live.lisp REDEFINES mpt-touch! after replay-cl is compiled.
;; An inline stub would bake the no-op body into journal-push! et al., so the
;; redefinition would never take effect. A plain funcall through the symbol's
;; fdefinition picks up the live definition. The call sites already gate on
;; *mpt-tracking*, so a normal run only pays a special-var read.
;; SLOT (optional): for a STORAGE change pass the changed slot so the worker
;; can update that contract's storage trie incrementally; NIL = an
;; account-level change (balance/nonce/code/created).
(defun mpt-touch! (addr &optional slot) (declare (ignore addr slot)) nil)
;; Storage cleared WHOLESALE (no per-slot journal entry), so slot-level dirty
;; tracking cannot see it. mpt-live.lisp redefines this to force a full re-read.
(defun mpt-touch-all! (addr) (declare (ignore addr)) nil)

(defun journal-push! (arena type addr key old-val)
  "Append a host-replayed JournalEntry (type 0 sstore / 2 balance) to
   ARENA. Layout per c/tx_arena.h: type@0, addr@8, key@40, old_val@72.
   Also records ADDR into the incremental state-root dirty set (no-op unless
   EITA_MPT_CHECK armed it): every journaled write (storage 0, balance 2,
   nonce 9, created 4/10) carries the addr of an account whose leaf changed."
  ;; type 0 = SSTORE: KEY is the storage slot, so record (addr . slot) for
  ;; slot-level dirty tracking. All other types are account-level (slot NIL).
  (when *mpt-tracking* (mpt-touch! addr (when (zerop type) key)))
  (let* ((count (mem-ref arena :uint64 0))
         (e (inc-pointer (mem-ref arena :pointer 16)
                         (* count +journal-entry-bytes+))))
    (setf (mem-ref e :uint64 0) type)
    (u256-write (inc-pointer e 8) addr)
    (u256-write (inc-pointer e 40) key)
    (u256-write (inc-pointer e 72) old-val)
    (setf (mem-ref arena :uint64 0) (1+ count))))

;; The two per-tx address sets, as a bit on the account's id plus the list of the ids that
;; carry it (the end-of-tx walks; reset-tx-state clears both):
;;   accounts_to_delete — originators selfdestructed this tx (pre-Cancun semantics: deleted
;;     at end of tx; pre-London: 24000 refund on first selfdestruct of each address).
;;     Journaled as host type 3 so a reverting frame's selfdestructs are forgotten.
;;   touched — EIP-161 (Spurious Dragon+), swept of empty accounts at end of tx (#252); the
;;     touch!/sweep helpers are with the other account helpers below.
(defconstant +acct-destroyed+ 8 "In this tx's accounts_to_delete (per tx; never persisted).")
(defconstant +acct-touched+ 16 "In this tx's EIP-161 touched set (per tx; never persisted).")
(defparameter *selfdestructed* '() "This tx's accounts_to_delete: their ids, newest first.")
(defparameter *touched* '() "This tx's touched set: their ids, newest first.")
(defvar *tx-sets-table* nil "The account table the per-tx sets' ids are in.")

(defun forget-tx-sets! ()
  "Empty both per-tx sets (reset-tx-state; a freeze, so no frozen table carries them)."
  (let ((tb *tx-sets-table*))
    (when tb
      (dolist (a *selfdestructed*) (acct-clear-flag! tb a +acct-destroyed+))
      (dolist (a *touched*) (acct-clear-flag! tb a +acct-touched+))))
  (setf *selfdestructed* '() *touched* '() *tx-sets-table* nil))
(defun tx-sets-push (tb a set)
  (setf *tx-sets-table* tb)
  (cons a set))
(defun tx-set-addrs (set)
  "The addresses of the per-tx set SET (a list of ids), oldest first."
  (let ((tb *tx-sets-table*)) (mapcar (lambda (a) (acct-addr tb a)) (reverse set))))
(defun destroyed-p (addr) (with-acct (tb a) *current-world* addr (acct-flag-p tb a +acct-destroyed+)))
(defun touched-p (addr) (with-acct (tb a) *current-world* addr (acct-flag-p tb a +acct-touched+)))
(defun mark-destroyed! (addr)
  "EffectIR `markDestroyed`: ADDR joins accounts_to_delete (journaled, type 3)."
  (with-acct (tb a) *current-world* addr
    (unless (acct-flag-p tb a +acct-destroyed+)
      (acct-set-flag! tb a +acct-destroyed+)
      (setf *selfdestructed* (tx-sets-push tb a *selfdestructed*))
      (journal-push! (current-arena) 3 addr 0 0))))
(defun unmark-destroyed! (addr)
  (with-acct (tb a) *current-world* addr
    (when (acct-flag-p tb a +acct-destroyed+)
      (acct-clear-flag! tb a +acct-destroyed+)
      (setf *selfdestructed* (delete a *selfdestructed* :count 1)))))
(defun untouch! (addr)
  (with-acct (tb a) *current-world* addr
    (when (acct-flag-p tb a +acct-touched+)
      (acct-clear-flag! tb a +acct-touched+)
      (setf *touched* (delete a *touched* :count 1)))))

;; Host-only journal entry type for an EIP-161 touch (beyond the native enum
;; 0..8; the native `eita_ts_revert` skips it via its `default:` arm, and the
;; CL revert loop maps it to `untouch!`). Lets a frame revert un-touch
;; accounts touched inside it (#271 revert-scoping).
(defconstant +j-touch+ 12)

(defun revert-journal-to (arena target)
  "Roll back every journal entry in ARENA above TARGET, in reverse:
   host-replays world-state types (0 sstore, 2 balance, 3 selfdestruct
   mark) here, then %ts-revert undoes the native types (warm-ups,
   tstores, refund, created) and rewinds journal_count to TARGET."
  (let ((count (mem-ref arena :uint64 0))
        (jdata (mem-ref arena :pointer 16)))
    (loop for n downfrom count above target do
      (let ((e (inc-pointer jdata (* (1- n) +journal-entry-bytes+))))
        ;; Entry type 10 (`created`) is restored by dropping the account's WHOLE
        ;; storage table, with no per-slot entry — so a reverted CREATE onto an
        ;; address that already held storage would leave the incremental
        ;; validator holding slots the world no longer has. Slots written inside
        ;; the create are individually journaled (type 0) and would be covered,
        ;; but pre-existing ones are not, so force a full re-read.
        (when (and *mpt-tracking* (= 10 (mem-ref e :uint64 0)))
          (mpt-touch-all! (u256-read (inc-pointer e 8))))
        ;; CL-side restore dispatch is emitted from the Lean spec
        ;; (Evm.CL.HostEmit.revertDispatch → spec-restore-journal-entry):
        ;; 0 sstore, 2 balance, 3 selfdestruct-mark, 9 nonce, 10 created,
        ;; 11 existence-insert, 12 EIP-161 touch-undo (#271 revert-scoping).
        ;; Native types (tstore/warm/refund/created) are undone by %ts-revert.
        (spec-restore-journal-entry
         (mem-ref e :uint64 0)                  ; entry_type
         (u256-read (inc-pointer e 8))          ; addr
         (u256-read (inc-pointer e 40))         ; slot/key
         (u256-read (inc-pointer e 72))))))     ; old value
  (%ts-revert *tx-state* arena target))

(defun journal-balance! (arena addr)
  "Journal ADDR's current balance (type 2) so a revert restores it."
  (journal-push! arena 2 addr 0
                 (balance-of *current-world* addr)))

(defun journal-nonce! (arena addr)
  "Journal ADDR's current nonce (type 9) so a revert restores it."
  (journal-push! arena 9 addr 0
                 (nonce-of *current-world* addr)))

(defun journal-created! (arena addr)
  "Journal that ADDR was CREATE'd in this frame (type 10) so a revert un-creates it
   (code/nonce/storage, and existence unless it existed before: the entry's old value is
   1 when ADDR was already marked present). Balance is restored by its own type-2 entry."
  (journal-push! arena 10 addr 0 (if (account-marked-p *current-world* addr) 1 0)))

(defun ts-table-mask (gas-limit min-gas cap)
  "The probe mask of a per-tx table for a tx of GAS-LIMIT whose every entry costs at least
   MIN-GAS (+256 free entries: the seeded precompiles, sender, target, coinbase, a chain's
   prewarm), at most half full; never above the table's CAP (sized from +block-gas-limit+)."
  (1- (min cap (max 1024 (next-pow2 (* 2 (+ 256 (ceiling gas-limit min-gas))))))))

(defun reset-tx-state (&optional gas-limit)
  "Reset per-tx native state — O(1) epoch bump (eita_ts_reset): the journal, the EIP-2929
   accessed sets, EIP-1153's transient storage, the refund counter, the created set, the
   accounts_to_delete and EIP-161's touched set. The tx's warm-ups are the derived effect's
   (warm-tx-seed!, in spec-tx-effect).
   GAS-LIMIT (a user tx, Berlin+): the tables are probed over the part the tx's gas can fill
   (an access costs >= 1900 gas — a cold access 2100/2600 or an access-list entry 1900/2400 —
   a TSTORE >= 100, a CREATE >= 32000) instead of the whole 200M-gas table: a tx's random
   probes then stay in a few cache-resident pages, not 0.5 GB. Without it (system calls,
   deposits, pre-Berlin where originals are recorded at 50-gas SLOADs): the whole tables.
   The native inserts still abort on an over-full table."
  (ensure-arenas)
  (setf *current-state* (null-pointer))
  (setf (mem-ref *tx-arena-root* :uint64 0) 0)   ; journal_count = 0
  (let ((ts *tx-state*) (g (and gas-limit (>= *fork-ord* 10) gas-limit)))
    (flet ((mask (min-gas cap) (if g (ts-table-mask g min-gas cap) (1- cap))))
      (setf (mem-ref ts :uint64 16) (mask 1900 +ts-addr-cap+)
            (mem-ref ts :uint64 24) (mask 1900 +ts-slot-cap+)
            (mem-ref ts :uint64 32) (mask 100 +ts-tstore-cap+)
            (mem-ref ts :uint64 40) (mask 32000 +ts-created-cap+)
            (mem-ref ts :uint64 48) (mask 1900 +ts-orig-cap+))))
  (%ts-reset *tx-state*)
  (forget-tx-sets!))                    ; EIP-161 touched set is per-tx (#252)
