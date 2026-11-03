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

(defcallback cb-sload :uint64
    ((ctx :pointer) (addr :pointer) (slot :pointer) (out :pointer))
  "The native handler popped the key; the effect — read, EIP-2929 warm-up, original value at
   first touch, the fork's price — is the Lean-emitted spec-sload-effect (Evm.CL.EffectSload,
   proved equal to every fork's SLOAD). Every slot read is on the read stream."
  (declare (ignore ctx))
  (let ((a (read-addr addr)) (s (u256-read slot)))
    (multiple-value-bind (g v) (spec-sload-effect a s)
      (u256-write out v)
      (cb-gas-check "sload" g :addr a :slot s))))

(defcallback cb-sstore :uint64
    ((ctx :pointer) (addr :pointer) (slot :pointer) (val :pointer))
  "The native handler popped the key and value and passed EIP-214 and the EIP-2200/1706
   sentry; the effect — read, EIP-2929 warm-up, original value, the fork's schedule, the
   refund, the journaled write — is the Lean-emitted spec-sstore-effect
   (Evm.CL.EffectSstore, proved equal to every fork's SSTORE)."
  (declare (ignore ctx))
  (let ((a (read-addr addr)) (s (u256-read slot)) (v (u256-read val)))
    (cb-gas-check "sstore" (spec-sstore-effect a s v) :addr a :slot s :val v)))

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
