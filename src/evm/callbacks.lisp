;;;; evm/callbacks.lisp — the host callbacks the native handlers call: storage, balances, code, BLOCKHASH.

(in-package #:eita.evm)

(defun read-addr (ptr)
  "Read a u256 from PTR and mask to the low 160 bits — every opcode that takes
   an address off the stack (BALANCE/EXTCODE*/SELFDESTRUCT/SLOAD-owner) masks to
   an address. Keeps a divergent path from handing the lazy-RPC fault a 256-bit
   value (which crashes eth_getBalance with 'Invalid params')."
  (if *current-world*
      (acct-table-intern-words (world-accts *current-world*) (mem-aref ptr :uint64 0) (mem-aref ptr :uint64 1)
                               (logand (mem-aref ptr :uint64 2) #xFFFFFFFF))
      (logand (u256-read ptr) #.(1- (ash 1 160)))))

;;; SLOAD and SSTORE (c/storage_host.h; docs/native-storage.md): the vtable's SLOAD and SSTORE
;;; slots are eita_cb_sload / eita_cb_sstore, their one execution path, the C printing of the
;;; Lean terms (c/generated/storage_effect.c, Evm.CL.EffectC) against the native slot tables.
;;; Lisp is called for data and observation only: cb-storage-learn (an account's id),
;;; cb-storage-fault (a lazy world's absent key) and cb-storage-hook (after the effect: the
;;; read stream, the watched accounts, the incremental root checker's dirty slots).
(defstartup *storage-host* (foreign-symbol-pointer "eita_sh_g"))

(declaim (inline storage-host-sync!))
(defun storage-host-sync! ()
  "At a frame's entry: the world's slot tables, the per-tx state, the fork, the flags
   (c/storage_host.h EITA_SH_*) and the zero-slot rule."
  (let ((h *storage-host*) (w *current-world*))
    (setf (mem-ref h :pointer 0) (if w (eita.state::acct-table-ws! (world-accts w)) (null-pointer))
          (mem-ref h :pointer 8) *tx-state*
          (mem-ref h :uint64 16) *fork-ord*
          (mem-ref h :uint64 24) (logior (if *observer* 4 0) (if eita.state::*fault-slot-hook* 8 0)
                                         (if *view-log* 16 0) (if *mpt-tracking* 32 0))
          (mem-ref h :uint64 80) (if eita.state::*keep-zero-slots* 1 0))))

(defvar *storage-watch* '()
  "The watched accounts (tier (b)): each SLOAD/SSTORE of one calls *storage-access-hook*. Set
   with storage-watch!; empty in normal runs.")
(defvar *storage-access-hook* nil
  "(lambda (op addr slot value)) for each SLOAD (:sload, the value read) or SSTORE (:sstore,
   the value written) of a watched account, synchronously, in execution order.")
(defun storage-watch! (addr)
  "Watch ADDR: each of its accesses calls the hook, which calls *storage-access-hook*."
  (unless (member addr *storage-watch*)
    (when (zerop (%sh-watch (eita.state::u256-word addr 0) (eita.state::u256-word addr 1) (eita.state::u256-word addr 2)))
      (error "storage-watch!: the watch filter is full"))
    (push addr *storage-watch*)))
(defun storage-watch-clear! () (%sh-watch-clear) (setf *storage-watch* '()))

(defcallback cb-storage-learn :uint64 ((addr :pointer))
  "The id of the frame account at ADDR in the current world (added when it has none)."
  (eita.state::acct-table-intern (world-accts *current-world*) (read-addr addr)))

(defcallback cb-storage-fault :void ((addr :pointer) (key :pointer))
  "Load KEY of the account at ADDR, absent from its table, through the world's fault hook
   (fault-slot!'s, outside the read stream)."
  (let ((*view-log* nil)) (funcall eita.state::*fault-slot-hook* (read-addr addr) (u256-read key))))

(defcallback cb-storage-hook :void ((op :uint64) (addr :pointer) (key :pointer) (val :pointer) (cur :pointer))
  "After an SLOAD (OP 0: VAL the value read) or SSTORE (OP 1: VAL the value written over CUR)
   of the account at ADDR: the read stream sees what the effect read and wrote (an SSTORE
   that changes its slot reads it again for the journal entry, then writes), the root checker
   the changed slot, the watch hook the access."
  (let ((a (read-addr addr)) (v (u256-read val)))
    (if (zerop op)
        (when *view-log* (eita.state::view-log-read :storage a key v))
        (let ((c (u256-read cur)))
          (when *view-log*
            (eita.state::view-log-read :storage a key c)
            (unless (= v c) (eita.state::view-log-read :storage a key c) (eita.state::view-log-write :storage a key c v)))
          (when (and *mpt-tracking* (/= v c)) (mpt-touch! a (word-int key)))))
    (when (and *storage-watch* *storage-access-hook* (member a *storage-watch*))
      (funcall *storage-access-hook* (if (zerop op) :sload :sstore) a (word-int key) v))))

;; TLOAD/TSTORE are fully native: the emitted handlers call
;; eita_ts_tload/eita_ts_tstore via arena->tx_state directly (keyed
;; (address, slot) per EIP-1153). cb vtable slots 2/3 stay null.

(defun addr-access-gas (addr kind)
  "Fork-correct account-access cost from the emitted table; marks ADDR
   warm. KIND: 1 balance, 2 extcode{size,copy}, 3 extcodehash."
  (access-cost kind (access-addr! addr)))

(defcallback cb-balance :uint64
    ((ctx :pointer) (addr :pointer) (out :pointer))
  (declare (ignore ctx))
  (let ((a (read-addr addr)))
    (fault-account! a)
    (u256-write out (balance-of *current-world* a))
    (cb-gas-check "balance" (addr-access-gas a 1) :addr a)))

(defcallback cb-ext-code-size :uint64
    ((ctx :pointer) (addr :pointer) (out :pointer))
  (declare (ignore ctx))
  (let* ((a (read-addr addr))
         (code (progn (fault-account! a)
                      (code-of *current-world* a))))
    (setf (mem-ref out :uint64) (length code))
    (cb-gas-check "extcodesize" (addr-access-gas a 2) :addr a)))

(defconstant +empty-code-hash+
  ;; keccak256("") per EIP-1052; returned for accounts that exist but have
  ;; no code.
  #xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470)

(defcallback cb-ext-code-hash :uint64
    ((ctx :pointer) (addr :pointer) (out :pointer))
  (declare (ignore ctx))
  ;; EELS extcodehash (EIP-1052): 0 iff the account is the EMPTY_ACCOUNT
  ;; sentinel (dead = absent or all-zero), else keccak256(code). The "is zero"
  ;; decision is now DERIVED: `spec-extcodehash-zero-p` is emitted from
  ;; Evm.CL.HostEmit.extcodehashZero (= the `empty` world-seam query), so the
  ;; EIP-161 dead-account test can't drift from the one the new-account charge
  ;; uses. A LIVE account with no code returns keccak256("")=+empty-code-hash+
  ;; (EELS computes it; we shortcut the hash of empty input). The hash is the
  ;; code's one owner, `code-hash-int`: seeded from the snapshot's codehash when
  ;; the code is faulted, hashed once per code object otherwise — never per access.
  (let* ((a (read-addr addr))
         (code (progn (fault-account! a)
                      (code-of *current-world* a))))
    (cond
      ((spec-extcodehash-zero-p a)
       (u256-write out 0))              ; dead account → 0
      ((plusp (length code))            ; live with code → keccak256(code)
       (u256-write out (code-hash-int code)))
      (t                                ; live, no code → keccak256("")
       (u256-write out +empty-code-hash+)))
    (cb-gas-check "extcodehash" (addr-access-gas a 3) :addr a)))

(defcallback cb-block-hash :void
    ((ctx :pointer) (blk :pointer) (out :pointer))
  (declare (ignore ctx))
  ;; BLOCKHASH gas is fixed 20; charged via exitWithGas in the handler.
  ;; The validity window is now DERIVED: `spec-blockhash-valid` is emitted from
  ;; Evm.CL.HostEmit.blockhashValid (src/generated/host.lisp), the EELS
  ;; predicate `n < cur AND cur <= n+256` (oldest valid = cur-256, inclusive),
  ;; with kernel-checked boundary examples — so the #265 off-by-one (the old
  ;; hand-written `(> n (- cur 256))` excluded cur-256) is unrepresentable. The
  ;; hash LOOKUP (*block-hashes*) stays the runtime-pluggable world seam.
  (let* ((n (u256-read blk))
         (cur *current-block-number*))
    (u256-write out
                (if (spec-blockhash-valid n cur)
                    (gethash n *block-hashes* 0)
                    0))))

(defcallback cb-ext-code-copy :uint64
    ((ctx :pointer) (addr :pointer) (dst :pointer)
     (src-off :uint64) (len :uint64))
  (declare (ignore ctx))
  (let* ((a (read-addr addr))
         (code (progn (fault-account! a)
                      (code-of *current-world* a))))
    (let* ((clen (length code))
           (avail (if (< src-off clen) (min len (- clen src-off)) 0)))
      ;; src-off may be 2^64-1 (the native side saturates a u256 source past any code),
      ;; which is no fixnum: copy only when there is something to copy.
      (when (plusp avail) (bytes->foreign dst code avail src-off))
      (when (< avail len) (%memset (inc-pointer dst avail) 0 (- len avail))))
    ;; Access cost + 3 per word copied (memexp added natively).
    (cb-gas-check "extcodecopy" (+ (addr-access-gas a 2) (* 3 (ceiling len 32)))
                  :addr a :src-off src-off :len len)))
