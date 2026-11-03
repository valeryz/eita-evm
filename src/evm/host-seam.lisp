;;;; evm/host-seam.lisp — the world-query seam the Lean-emitted host effects call (generated/host.lisp
;;;; loads next), dead accounts, EIP-161 touches.

(in-package #:eita.evm)

;; Scratch output buffer for `_eita_call_gas`. A single static buffer is
;; safe despite cb-call's reentrancy: the three plan words are read into
;; Lisp integers immediately after the FFI call, before any sub-frame
;; (and hence any nested cb-call) can run.
(defstartup *call-gas-plan* (foreign-alloc :uint64 :count 3))

(defun account-dead-p (addr)
  "EELS `is_account_dead`: absent OR empty (balance 0, nonce 0, no code).
   Our world hashes don't distinguish absent from present-but-empty —
   both legs collapse to all-empty, exactly like Lean `isDead`."
  (fault-account! addr)
  (and (zerop (balance-of *current-world* addr))
       (zerop (nonce-of *current-world* addr))
       (zerop (length (code-of *current-world* addr)))))

;;; --- EIP-161 (Spurious Dragon+) touched set (#252) ---------------------------
;;; Mainnet deletes every *touched* account that is empty at the END of a tx: the
;;; Lean-emitted spec-sweep-effect (Evm.CL.EffectEndTx, = SpuriousDragon.finishTx's
;;; sweep). `*touched*` is per-tx (reset in reset-tx-state), populated at the EELS
;;; touchAddr points — sender+recipient seed (apply-tx), a CALL-family child's target
;;; when it succeeds and leaves it existing and empty, and 0x03 when a failed child
;;; qualifies for EELS's RIPEMD-160 exemption (cb-call: spec-call-effect), CREATE new
;;; address (cb-create), SELFDESTRUCT beneficiary
;;; (cb-selfdestruct) — fork-gated ≥ Spurious Dragon (ord 4), revert-scoped (#271).
;;; (`*touched*` is declared up near `*selfdestructed*` so reset-tx-state sees it.)

(declaim (inline touch!))
(defun touch! (addr)
  "Record ADDR as touched this tx (EIP-161; Spurious Dragon+ only) and journal
   a type-12 entry into the active frame's scope so a frame revert un-touches
   it (#271 revert-scoping): a touch inside a sub-frame that later reverts must
   NOT reach the end-of-tx empty-account sweep — mirrors the Lean spec, where
   the touch lives in the frame's `env` and is discarded with it on revert.
   Only NEW touches journal: a re-touch of an already-touched addr adds no
   un-touch entry, so a later revert of the re-touching frame can't drop a
   touch that an enclosing committed frame still owns."
  (when (>= *fork-ord* 4)
    (with-acct (tb a) *current-world* addr
      (unless (acct-flag-p tb a +acct-touched+)
        (acct-set-flag! tb a +acct-touched+)
        (setf *touched* (tx-sets-push tb a *touched*))
        (journal-push! (current-arena) +j-touch+ addr 0 0)))))


;;; --- World-query seam for the Lean-emitted host predicates ----------
;;;
;;; The generated effect terms (src/generated/host.lisp: EffectIR's `present` /
;;; `dead`) call these; their contract (docs/effect-layer-derivation.md §3.2):
;;;   world-account-present-p  ==  Frontier.State.accountExists  (in state at all)
;;;   world-account-empty-p    ==  Account.isEmpty               (0 bal / 0 nonce / no code)
;;; Keeping these hand-written (not emitted) is deliberate: this is the
;;; pluggable backend seam — key-existence over the in-memory world today,
;;; the lazy-RPC fault hook for the Base track.

(defun mark-account-present! (arena addr)
  "Record that ADDR now exists in state (an empty-but-present account),
   journaling the insertion (entry type 4) so a frame revert un-creates it.
   No-op if ADDR is already known to exist (in the set, or non-dead)."
  (let ((w *current-world*))
    (unless (or (account-marked-p w addr) (not (account-dead-p addr)))
      (account-mark! w addr)
      ;; Type 11 (existence-insert), NOT 4: the native journal uses type 4
      ;; for EITA_J_ACCESS_ADDR (EIP-2929 warm-set), and the CL revert
      ;; dispatch must not confuse a warm-up with an account creation. A
      ;; reverting tx that merely WARMS an empty-but-present account (e.g.
      ;; a pre-Spurious 0-value CALL to it) would otherwise have its
      ;; world-accounts entry wrongly remhash'd on revert. (Block 637758:
      ;; an invalid-jump tx that touches 0xf5ed057f, created back at 637752,
      ;; silently deleted it → +25000 new-account overcharge thereafter.)
      (journal-push! arena 11 addr 0 0))))

(defun world-account-present-p (addr)
  "`accountExists`: is ADDR present in state (even as an empty account)?
   Non-empty accounts are witnessed by ¬isDead; empty-but-present ones (a
   CALL to a formerly-absent account, including a precompile, or an empty
   CREATE) are witnessed by the explicit `accounts` set."
  (fault-account! addr)
  (or (account-marked-p *current-world* addr)
      (not (account-dead-p addr))))

(defun world-account-empty-p (addr)
  "`Account.isEmpty`: balance 0, nonce 0, no code (EIP-161 emptiness).
   Independent of presence — an empty-but-present account is empty."
  (account-dead-p addr))
