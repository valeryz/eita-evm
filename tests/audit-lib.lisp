;;;; audit-lib.lisp — shared harness for the native-handler audits.
;;;;
;;;; Loaded (via LOAD, into the caller's package) by audit-native.lisp
;;;; and audit-jit.lisp. Defines the EvmState field offsets, the audit
;;;; callback vtable, U256 limb I/O, and the fixture-plist → EvmState
;;;; builder + snapshot/compare helpers. Expects CFFI to be loaded and
;;;; the caller's package to :use #:cl #:cffi.

;; Field offsets pinned by c/evm_state.h. If anything drifts here, the
;; static_assert in evm_state.h would have caught it at compile time.
(defconstant +pc-offset+               0)
(defconstant +gas-left-offset+         8)
(defconstant +sp-offset+              16)
(defconstant +mp-offset+              24)
(defconstant +stack-offset+           32)
(defconstant +memory-offset+          40)
(defconstant +memory-size-offset+     48)
(defconstant +memory-cap-offset+      56)
(defconstant +code-offset+            64)
(defconstant +code-size-offset+       72)
(defconstant +calldata-offset+        80)
(defconstant +calldata-size-offset+   88)
(defconstant +returndata-offset+      96)
(defconstant +returndata-size-offset+ 104)
(defconstant +output-offset+         112)
(defconstant +output-size-offset+    120)
(defconstant +halted-offset+         128)
(defconstant +reverted-offset+       129)
(defconstant +staticp-offset+        130)
(defconstant +jumpdests-offset+      136)   ; valid-JUMPDEST map of the code (eita_jumpdest_map)
(defconstant +address-offset+        144)
(defconstant +cb-offset+             496)
(defconstant +cb-ctx-offset+         504)
(defconstant +evm-state-size+        600)   ; sizeof(EvmState), c/evm_state.h

(defconstant +u256-bytes+ 32)
(defconstant +stack-capacity+ 1024)

;; TxArena offsets (from c/tx_arena.h).
(defconstant +arena-journal-count-offset+ 0)
(defconstant +arena-log-count-offset+     8)
(defconstant +arena-journal-data-offset+ 16)
(defconstant +arena-log-data-offset+     24)
(defconstant +arena-tx-state-offset+     64)
(defconstant +arena-size+                72)
(defconstant +journal-entry-size+       104)
(defconstant +journal-capacity+         1024)

;; Unified entry point: run a single opcode through the threaded dispatch.
(defcfun ("eita_run_one" eita-run-one) :void
  (state :pointer)
  (opcode :uint8))
;; Valid-JUMPDEST map of LEN code bytes into OUT (EELS get_valid_jump_destinations).
(defcfun ("eita_jumpdest_map" %jumpdest-map) :void
  (code :pointer) (len :uint64) (out :pointer))

;; --- Callback context (per fixture) ---
;; Each fixture's :cache, :tstorage, :world-balance-by-val, etc. lives here.
;; Callbacks are defined as defcallbacks that read from these dynamic vars.

(defparameter *fixture-cache*           nil)  ; ((addr slot val) ...)
(defparameter *fixture-world-balance*   nil)  ; ((addr-val val) ...)
(defparameter *fixture-world-codesize*  nil)  ; ((addr-val n) ...)
(defparameter *fixture-world-codehash*  nil)  ; ((addr-val val) ...)
(defparameter *fixture-world-blockhash* nil)  ; ((addr-val val) ...)
(defparameter *fixture-world-code*      nil)  ; ((addr-val hex-string) ...)

;; All access callbacks return uint64 gas. Audit callbacks return the same
;; flat values the spec/fixture expects (100 for SLOAD/SSTORE/etc.); fixtures
;; aren't testing EIP-2929 cold/warm tracking so the audit doesn't care.

(defcallback cb-sload :uint64
    ((ctx :pointer) (addr :pointer) (slot :pointer) (out :pointer))
  (declare (ignore ctx))
  (let* ((a (u256-read addr))
         (s (u256-read slot))
         (e (find-if (lambda (e) (and (= (first e) a) (= (second e) s))) *fixture-cache*))
         (v (if e (third e) 0)))
    (u256-write out v)
    100))

(defcallback cb-sstore :uint64
    ((ctx :pointer) (addr :pointer) (slot :pointer) (val :pointer))
  (declare (ignore ctx addr slot val))
  100)

;; TLOAD/TSTORE are fully native: the handlers reach the TxState tables
;; through arena->tx_state (offset 64), so the audit allocates a real
;; TxState and preloads fixture tstorage into it (see ensure-tx-state /
;; build-native-state). cb vtable slots 2/3 stay null.

(defcallback cb-balance :uint64
    ((ctx :pointer) (addr :pointer) (out :pointer))
  (declare (ignore ctx))
  (let* ((a (u256-read addr))
         (e (find-if (lambda (e) (= (first e) a)) *fixture-world-balance*))
         (v (if e (second e) 0)))
    (u256-write out v)
    100))

(defcallback cb-ext-code-size :uint64
    ((ctx :pointer) (addr :pointer) (out :pointer))
  (declare (ignore ctx))
  (let* ((a (u256-read addr))
         (e (find-if (lambda (e) (= (first e) a)) *fixture-world-codesize*))
         (v (if e (second e) 0)))
    (setf (mem-ref out :uint64) v)
    100))

(defcallback cb-ext-code-hash :uint64
    ((ctx :pointer) (addr :pointer) (out :pointer))
  (declare (ignore ctx))
  (let* ((a (u256-read addr))
         (e (find-if (lambda (e) (= (first e) a)) *fixture-world-codehash*))
         (v (if e (second e) 0)))
    (u256-write out v)
    100))

(defcallback cb-ext-code-copy :uint64
    ((ctx :pointer) (addr :pointer) (dst :pointer)
     (src-off :uint64) (len :uint64))
  (declare (ignore ctx))
  (let* ((a (u256-read addr))
         (e (find-if (lambda (e) (= (first e) a)) *fixture-world-code*))
         (hex (if e (second e) "")))
    (loop for i from 0 below len do
      (let ((src-idx (+ src-off i)))
        (setf (mem-aref dst :uint8 i)
              (if (< (* 2 (1+ src-idx)) (length hex))
                  (parse-integer hex :radix 16
                                 :start (* 2 src-idx) :end (* 2 (1+ src-idx)))
                  0))))
    ;; Mirror replay's cb split: access (flat 100 here) + 3 per word
    ;; copied; the native handler adds memory expansion on top.
    (+ 100 (* 3 (ceiling len 32)))))

(defcallback cb-block-hash :void
    ((ctx :pointer) (blk :pointer) (out :pointer))
  (declare (ignore ctx))
  (let* ((b (u256-read blk))
         (e (find-if (lambda (e) (= (first e) b)) *fixture-world-blockhash*))
         (v (if e (second e) 0)))
    (u256-write out v)))

;; Stub callbacks for ops we don't implement (LOG, CALL, CREATE, SELFDESTRUCT).
(defcallback cb-noop :void ((ctx :pointer)) (declare (ignore ctx)) nil)

(defun alloc-callbacks ()
  "Allocate a callbacks vtable struct, populate function pointers."
  (let ((cb (foreign-alloc :pointer :count 16 :initial-element (null-pointer))))
    (setf (mem-aref cb :pointer 0)  (callback cb-sload))
    (setf (mem-aref cb :pointer 1)  (callback cb-sstore))
    ;; slots 2/3 (tload/tstore) are null — handlers are fully native
    (setf (mem-aref cb :pointer 4)  (callback cb-balance))
    (setf (mem-aref cb :pointer 5)  (callback cb-ext-code-size))
    (setf (mem-aref cb :pointer 6)  (callback cb-ext-code-hash))
    (setf (mem-aref cb :pointer 7)  (callback cb-ext-code-copy))
    (setf (mem-aref cb :pointer 8)  (callback cb-block-hash))
    cb))

;; Opcode bytes per EVM convention.
(defparameter *opcode-bytes*
  '(("STOP" . #x00) ("ADD" . #x01) ("MUL" . #x02) ("SUB" . #x03)
    ("DIV" . #x04) ("SDIV" . #x05) ("MOD" . #x06) ("SMOD" . #x07)
    ("ADDMOD" . #x08) ("MULMOD" . #x09) ("EXP" . #x0a) ("SIGNEXTEND" . #x0b)
    ("LT" . #x10) ("GT" . #x11) ("SLT" . #x12) ("SGT" . #x13)
    ("EQ" . #x14) ("ISZERO" . #x15)
    ("AND" . #x16) ("OR" . #x17) ("XOR" . #x18) ("NOT" . #x19)
    ("BYTE" . #x1a) ("SHL" . #x1b) ("SHR" . #x1c) ("SAR" . #x1d)
    ("KECCAK256" . #x20)
    ("ADDRESS" . #x30) ("BALANCE" . #x31) ("ORIGIN" . #x32) ("CALLER" . #x33)
    ("CALLVALUE" . #x34) ("CALLDATALOAD" . #x35) ("CALLDATASIZE" . #x36)
    ("CALLDATACOPY" . #x37) ("CODESIZE" . #x38) ("CODECOPY" . #x39)
    ("GASPRICE" . #x3a) ("EXTCODESIZE" . #x3b) ("EXTCODECOPY" . #x3c)
    ("RETURNDATASIZE" . #x3d) ("RETURNDATACOPY" . #x3e) ("EXTCODEHASH" . #x3f)
    ("BLOCKHASH" . #x40) ("COINBASE" . #x41) ("TIMESTAMP" . #x42)
    ("NUMBER" . #x43) ("GASLIMIT" . #x45)
    ("CHAINID" . #x46) ("SELFBALANCE" . #x47) ("BASEFEE" . #x48)
    ("POP" . #x50) ("MLOAD" . #x51) ("MSTORE" . #x52) ("MSTORE8" . #x53)
    ("SLOAD" . #x54) ("SSTORE" . #x55) ("JUMP" . #x56) ("JUMPI" . #x57)
    ("PC" . #x58) ("MSIZE" . #x59) ("GAS" . #x5a)
    ("JUMPDEST" . #x5b) ("TLOAD" . #x5c) ("TSTORE" . #x5d)
    ("MCOPY" . #x5e) ("PUSH0" . #x5f)
    ("PUSH1" . #x60) ("PUSH2" . #x61) ("PUSH3" . #x62) ("PUSH4" . #x63)
    ("PUSH5" . #x64) ("PUSH8" . #x67) ("PUSH9" . #x68) ("PUSH16" . #x6f)
    ("PUSH17" . #x70) ("PUSH24" . #x77) ("PUSH25" . #x78) ("PUSH32" . #x7f)
    ("DUP1" . #x80) ("DUP3" . #x82)
    ("SWAP1" . #x90) ("SWAP3" . #x92)
    ("LOG0" . #xa0) ("LOG1" . #xa1) ("LOG2" . #xa2) ("LOG3" . #xa3) ("LOG4" . #xa4)
    ("RETURN" . #xf3) ("REVERT" . #xfd) ("INVALID" . #xfe)))

;; --- U256 little-endian limb I/O on a pointer ---

(defun u256-write (ptr value)
  "Write VALUE as 4 little-endian uint64 limbs at PTR."
  (loop for i from 0 below 4 do
    (setf (mem-aref ptr :uint64 i)
          (logand (ash value (- (* i 64))) #xFFFFFFFFFFFFFFFF))))

(defun u256-read (ptr)
  "Read 4 little-endian uint64 limbs from PTR into one bignum."
  (let ((acc 0))
    (loop for i from 3 downto 0 do
      (setf acc (logior (ash acc 64) (mem-aref ptr :uint64 i))))
    acc))

;; --- Allocate + populate an EvmState struct from a fixture pre-state plist ---

;; Native per-tx state tables (c/tx_state.h). The TLOAD/TSTORE handlers
;; bypass the cb vtable and drive these directly through arena->tx_state,
;; so the audit needs a real TxState: one shared instance, epoch-reset
;; per fixture, fixture tstorage preloaded via eita_ts_tstore.
(defcfun ("eita_ts_reset" %ts-reset) :void (ts :pointer))
(defcfun ("eita_ts_tstore" %ts-tstore) :void
  (ts :pointer) (ar :pointer) (addr :pointer) (slot :pointer) (val :pointer))

(defconstant +ts-audit-cap+ 1024)
(defparameter *audit-tx-state* nil)
(defparameter *ts-scratch-addr* nil)
(defparameter *ts-scratch-slot* nil)
(defparameter *ts-scratch-val*  nil)

(defun ensure-tx-state ()
  "Allocate the shared audit TxState (136 bytes, c/tx_state.h):
   masks at 16..48, table pointers at 56..88. Caps of 1024 dwarf any
   single-op fixture's needs."
  (unless *audit-tx-state*
    (let ((ts (foreign-alloc :uint8 :count 136 :initial-element 0)))
      (loop for off in '(16 24 32 40 48) do
        (setf (mem-ref ts :uint64 off) (1- +ts-audit-cap+)))
      (setf (mem-ref ts :pointer 56) (foreign-alloc :uint8 :count (* +ts-audit-cap+ 40) :initial-element 0))
      (setf (mem-ref ts :pointer 64) (foreign-alloc :uint8 :count (* +ts-audit-cap+ 72) :initial-element 0))
      (setf (mem-ref ts :pointer 72) (foreign-alloc :uint8 :count (* +ts-audit-cap+ 104) :initial-element 0))
      (setf (mem-ref ts :pointer 80) (foreign-alloc :uint8 :count (* +ts-audit-cap+ 40) :initial-element 0))
      (setf (mem-ref ts :pointer 88) (foreign-alloc :uint8 :count (* +ts-audit-cap+ 104) :initial-element 0))
      (setf *audit-tx-state* ts)
      (setf *ts-scratch-addr* (foreign-alloc :uint8 :count 32 :initial-element 0))
      (setf *ts-scratch-slot* (foreign-alloc :uint8 :count 32 :initial-element 0))
      (setf *ts-scratch-val*  (foreign-alloc :uint8 :count 32 :initial-element 0))))
  *audit-tx-state*)

(defun alloc-arena ()
  "Allocate a TxArena + journal-data region. Returns (values arena journal-data)."
  (let ((arena (foreign-alloc :uint8 :count +arena-size+ :initial-element 0))
        (journal (foreign-alloc :uint8
                                :count (* +journal-capacity+ +journal-entry-size+)
                                :initial-element 0)))
    (setf (mem-ref arena :uint64 +arena-journal-count-offset+) 0)
    (setf (mem-ref arena :pointer +arena-journal-data-offset+) journal)
    (setf (mem-ref arena :pointer +arena-tx-state-offset+) (ensure-tx-state))
    (values arena journal)))

(defun hex-bytes-to-foreign (hex)
  "Allocate a foreign byte buffer + copy hex string contents."
  (let* ((n (floor (length hex) 2))
         (buf (foreign-alloc :uint8 :count (max n 1) :initial-element 0)))
    (loop for i from 0 below n do
      (setf (mem-aref buf :uint8 i)
            (parse-integer hex :radix 16 :start (* 2 i) :end (* 2 (+ i 1)))))
    (values buf n)))

(defparameter *aux-buffers* nil)
(defun track-aux (buf) (push buf *aux-buffers*) buf)

;; A guard tail after every EvmState the audits allocate: the native tiers must never write
;; past the struct. A harness that allocates fewer bytes than the handlers use (it once
;; allocated 600 after EvmState grew to 608: x86-64 eita_run/eita_execute_program store
;; cont_table at offset 600) corrupts the malloc heap, which faulted later suites only
;; intermittently; the guard turns that into a deterministic failure of the program that wrote it.
(defconstant +state-guard-bytes+ 64)
(defconstant +state-guard-byte+ #xA5)

(defun state-guard-intact-p (state)
  "True when the guard tail after STATE's +evm-state-size+ bytes is untouched."
  (loop for i from +evm-state-size+ below (+ +evm-state-size+ +state-guard-bytes+)
        always (= (mem-aref state :uint8 i) +state-guard-byte+)))

(defun build-native-state (pre)
  "Allocate an EvmState* and a backing stack array; populate from PRE.
   Returns (values state stack arena journal)."
  (let ((state (foreign-alloc :uint8 :count (+ +evm-state-size+ +state-guard-bytes+) :initial-element 0))
        (stack (foreign-alloc :uint8
                              :count (* +stack-capacity+ +u256-bytes+)
                              :initial-element 0))
        ;; Always allocate a large memory buffer (preallocated per-frame).
        (mem  (foreign-alloc :uint8 :count (* 64 1024) :initial-element 0)))
    (loop for i from +evm-state-size+ below (+ +evm-state-size+ +state-guard-bytes+)
          do (setf (mem-aref state :uint8 i) +state-guard-byte+))
    (setf (mem-ref state :pointer +memory-offset+) mem)
    (setf (mem-ref state :uint64 +memory-cap-offset+) (* 64 1024))
    (track-aux mem)
    ;; Set scalar fields.
    (setf (mem-ref state :uint64 +pc-offset+)       (or (getf pre :pc) 0))
    (setf (mem-ref state :uint64 +gas-left-offset+) (or (getf pre :gas-left) 0))
    (setf (mem-ref state :uint64 +mp-offset+)       (or (getf pre :mp) 0))
    (setf (mem-ref state :pointer +stack-offset+)   stack)
    ;; Populate stack (top of fixture list at index sp-1).
    (let* ((stk (getf pre :stack))
           (sp (length stk)))
      (setf (mem-ref state :uint64 +sp-offset+) sp)
      (loop for v in (reverse stk)
            for i from 0 do
        (u256-write (inc-pointer stack (* i +u256-bytes+)) v)))
    ;; Populate U256 env fields where present in the fixture.
    (when (getf pre :address)
      (u256-write (inc-pointer state +address-offset+) (getf pre :address)))
    (when (getf pre :origin)
      (u256-write (inc-pointer state 176) (getf pre :origin)))
    (when (getf pre :caller)
      (u256-write (inc-pointer state 208) (getf pre :caller)))
    (when (getf pre :coinbase)
      (u256-write (inc-pointer state 336) (getf pre :coinbase)))
    (when (getf pre :callvalue)
      (u256-write (inc-pointer state 240) (getf pre :callvalue)))
    (when (getf pre :gasprice)
      (u256-write (inc-pointer state 272) (getf pre :gasprice)))
    (when (getf pre :chainid)
      (u256-write (inc-pointer state 304) (getf pre :chainid)))
    (when (getf pre :timestamp)
      (u256-write (inc-pointer state 368) (getf pre :timestamp)))
    (when (getf pre :block-number)
      (u256-write (inc-pointer state 400) (getf pre :block-number)))
    (when (getf pre :gaslimit)
      (u256-write (inc-pointer state 432) (getf pre :gaslimit)))
    (when (getf pre :basefee)
      (u256-write (inc-pointer state 464) (getf pre :basefee)))
    ;; mp (memory high-water mark); size scalars for size-pushers.
    (when (getf pre :mp)
      (setf (mem-ref state :uint64 +mp-offset+) (getf pre :mp)))
    ;; Code: allocate + populate, then 64 zero bytes — the handlers' code-pad
    ;; contract (src/evm/ +code-tail-pad-bytes+): a PUSH-N immediate past
    ;; code_size and the fetch after it read these zeros, unchecked.
    (when (getf pre :code-hex)
      (multiple-value-bind (buf n) (hex-bytes-to-foreign
                                    (concatenate 'string
                                                 (getf pre :code-hex)
                                                 (make-string 128 :initial-element #\0)))
        (declare (ignore n))
        (track-aux buf)
        (setf (mem-ref state :pointer +code-offset+) buf)
        (setf (mem-ref state :uint64 +code-size-offset+)
              (/ (length (getf pre :code-hex)) 2))
        ;; The valid-JUMPDEST map the JUMP/JUMPI handlers consult (#136).
        (let* ((n (/ (length (getf pre :code-hex)) 2))
               (map (foreign-alloc :uint8 :count (max n 1) :initial-element 0)))
          (track-aux map)
          (%jumpdest-map buf n map)
          (setf (mem-ref state :pointer +jumpdests-offset+) map))))
    (when (getf pre :calldata-hex)
      (multiple-value-bind (buf n) (hex-bytes-to-foreign (getf pre :calldata-hex))
        (track-aux buf)
        (setf (mem-ref state :pointer +calldata-offset+) buf)
        (setf (mem-ref state :uint64 +calldata-size-offset+) n)))
    (when (getf pre :returndata-hex)
      (multiple-value-bind (buf n) (hex-bytes-to-foreign (getf pre :returndata-hex))
        (track-aux buf)
        (setf (mem-ref state :pointer +returndata-offset+) buf)
        (setf (mem-ref state :uint64 +returndata-size-offset+) n)))
    ;; Memory: if pre has :memory-hex, copy into our preallocated buffer.
    (when (getf pre :memory-hex)
      (let* ((hex (getf pre :memory-hex))
             (n (floor (length hex) 2))
             (mptr (mem-ref state :pointer +memory-offset+)))
        (loop for i from 0 below n do
          (setf (mem-aref mptr :uint8 i)
                (parse-integer hex :radix 16 :start (* 2 i) :end (* 2 (+ i 1)))))
        (setf (mem-ref state :uint64 +memory-size-offset+) n)))
    ;; Populate fixture-callback data from pre.
    (setf *fixture-cache*           (getf pre :cache))
    (setf *fixture-world-balance*   (getf pre :world-balance-by-val))
    (setf *fixture-world-codesize*  (getf pre :world-code-size-by-val))
    (setf *fixture-world-codehash*  (getf pre :world-code-hash-by-val))
    (setf *fixture-world-blockhash* (getf pre :world-block-hash-by-val))
    (setf *fixture-world-code*      (getf pre :world-code-by-val))
    ;; Set up callbacks table.
    (let ((cb (alloc-callbacks)))
      (track-aux cb)
      (setf (mem-ref state :pointer 496) cb))
    ;; Set up arena and point cb_ctx at it. Epoch-reset the shared
    ;; TxState, then preload fixture tstorage keyed (address, slot)
    ;; per EIP-1153 — the fixture address defaults to 0, matching the
    ;; zeroed state.address above.
    (multiple-value-bind (arena journal) (alloc-arena)
      (setf (mem-ref state :pointer 504) arena)
      (%ts-reset *audit-tx-state*)
      (loop for (slot val) in (getf pre :tstorage) do
        (u256-write *ts-scratch-addr* (or (getf pre :address) 0))
        (u256-write *ts-scratch-slot* slot)
        (u256-write *ts-scratch-val*  val)
        (%ts-tstore *audit-tx-state* arena
                    *ts-scratch-addr* *ts-scratch-slot* *ts-scratch-val*))
      ;; Preload journaling is bookkeeping, not fixture activity.
      (setf (mem-ref arena :uint64 +arena-journal-count-offset+) 0)
      (values state stack arena journal))))

(defun snapshot-native-state (state)
  "Read post-state into a plist comparable to the fixture format."
  (let* ((pc       (mem-ref state :uint64 +pc-offset+))
         (gas-left (mem-ref state :uint64 +gas-left-offset+))
         (sp       (mem-ref state :uint64 +sp-offset+))
         (stack-ptr (mem-ref state :pointer +stack-offset+))
         (stack (loop for i from 0 below sp
                      collect (u256-read (inc-pointer stack-ptr (* i +u256-bytes+)))))
         (arena (mem-ref state :pointer 504))
         ;; The spec's journal models only the host-replayed entry types
         ;; (0 sstore / 2 balance / 3 selfdestruct). Native TxState types
         ;; (1, 4-8: tstore/access/refund/created) are revert bookkeeping
         ;; for eita_ts_revert, invisible to the Form spec — exclude them.
         (journal-len
           (if (null-pointer-p arena)
               0
               (loop with data = (mem-ref arena :pointer +arena-journal-data-offset+)
                     for i from 0 below (mem-ref arena :uint64 +arena-journal-count-offset+)
                     count (member (mem-ref data :uint64 (* i +journal-entry-size+))
                                   '(0 2 3))))))
    (list :pc pc :gas-left gas-left :stack (reverse stack)
          :journal-len journal-len)))

(defun state-matches-fixture (state expected)
  (let ((got (snapshot-native-state state)))
    (and (= (getf got :pc) (or (getf expected :pc) 0))
         (= (getf got :gas-left) (or (getf expected :gas-left) 0))
         (= (getf got :journal-len) (or (getf expected :journal-len) 0))
         (let* ((es (getf expected :stack))
                (gs (getf got :stack)))
           (and (= (length es) (length gs))
                (every #'= es gs))))))

;; --- Fixture loader (subset of what audit-macros.lisp does) ---

(defun load-fixtures (path)
  (with-open-file (f path)
    (getf (read f) :opcodes)))
