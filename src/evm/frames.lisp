;;;; evm/frames.lisp — frames: the current world and address, per-tx buffers and arenas sized from the
;;;; block gas limit, frame code images, the tx and block environment.

(in-package #:eita.evm)

;;; --- Native callbacks bridged to *current-world* ---

(defparameter *current-world*    nil)
(defparameter *current-address*  0)
;; EIP-150: max call/create depth = 1024. cb-call and cb-create bump this on
;; entry, restore on exit, and return failure without invoking a sub-frame
;; once the limit is hit.
(defparameter *call-depth* 0)
(defconstant +max-call-depth+ 1024)

;;; =============================================================
;;; Per-tx buffer sizing, derived backwards from the block gas limit.
;;;
;;; Every per-frame buffer (EVM memory, EVM stack, deployed/init code,
;;; revert journal) has a worst-case size that's gas-bounded. We size
;;; once, at load time, from a single +block-gas-limit+ knob so the
;;; rationale is visible in source and the buffers don't need to grow
;;; at run time.
;;;
;;; Reference: post-Fusaka mainnet limit is 60M; planned Glamsterdam
;;; target is ~200M. We size for the high end so the same buffers work
;;; across upgrades. L2s with materially higher per-tx ceilings (e.g.
;;; BNB Chain at ~140M, some op-stack chains permitting larger) would
;;; need this knob bumped.

(defconstant +block-gas-limit+ 200000000
  "Gas budget the buffers below are sized to absorb. Pick the chain's
   highest single-tx gas ceiling (mainnet block limit ≈ Glamsterdam 200M).")

;; ---- EVM memory ----------------------------------------------
;;
;; Memexp gas cost: cost(words) = 3w + w²/512.  Solve cost = G for w:
;;   w² + 1536w - 512·G = 0
;;   w = ⌊(√(1536² + 2048·G) − 1536) / 2⌋
;; bytes = 32 · w (+ 32 byte tail so a 32-byte read past the high
;; water mark stays in-bounds).
;;
;; The arena is SHARED across all frames in a tx. Total memexp gas
;; across the call tree is bounded by tx.gasLimit, so a single
;; max-frame allocation handles any single-frame ceiling.

(defun memory-bytes-for-gas (gas)
  "Max EVM-memory bytes a frame can grow to spending exactly GAS on
   memexp. Inverts the EELS memory cost formula."
  (let* ((disc (+ (* 1536 1536) (* 2048 gas)))
         (w    (floor (- (isqrt disc) 1536) 2)))
    (+ (* 32 w) 32)))

(defparameter +memory-bytes-per-frame+ (memory-bytes-for-gas +block-gas-limit+)
  "Upper bound on a single EVM frame's memory usage at the block gas
   limit.  9.74 MiB at G=200M, 6.88 MiB at G=100M, 5.33 MiB at G=60M,
   3.76 MiB at G=30M.")

;; ---- EVM stack ----------------------------------------------
;;
;; Hard-bounded by the EVM spec: 1024 slots × 32 bytes per slot.
;; Independent of gas. Each frame has its own; depth bound is EIP-150.

(defconstant +stack-slot-bytes+ 32)
(defconstant +stack-slots-per-frame+ 1024)
(defparameter +stack-bytes-per-frame+
  (* +stack-slots-per-frame+ +stack-slot-bytes+))   ; 32 KiB

;; Head pad below the stack arena (#272). The emitted threaded interpreter caches
;; the second-from-top operand in registers: after a stack-shrinking op it
;; speculatively pre-loads stack[depth-2] for the next handler (e.g. eita_handler_eq
;; `ldp [stack_base + (depth-2)*32]`). Every binary op guards depth>=2, so the
;; minimum index is -1 — one u256 slot BELOW the live stack. The value is
;; discarded (the next op underflow-checks or overwrites), so it is a benign
;; speculative under-read — but for the depth-0 frame stack_base == arena base,
;; so it touches one slot below the arena. We reserve that slot as valid zeroed
;; slack (symmetric to +code-tail-pad-bytes+ for PUSH's forward over-read); two
;; slots for margin. Lets the PROT_NONE guard stay on for ALL platforms.
(defconstant +stack-head-pad-bytes+ (* 2 +stack-slot-bytes+))   ; 64 B (>= 1 slot)

;; ---- Bytecode ----------------------------------------------
;;
;; EIP-170 caps deployed code at 24576 bytes; EIP-3860 caps init code
;; (the data passed to CREATE/CREATE2) at 49152 bytes. After the code comes a
;; zero pad of 64 bytes (one cache line), then the frame's valid-JUMPDEST map (one
;; byte per code byte, eita_jumpdest_map), which JUMP/JUMPI consult instead of the
;; code byte (EvmState #136): the code's frame image [code | pad | map], built once
;; per code object (frame-code-image) — the ONE place the native handlers' code
;; buffer is made.
;;
;; The pad is a contract with the handlers, which have no bounds check on code reads:
;;  - PUSH-N reads its immediate as whole 8-byte limbs from pc (lean/Evm/CL/PushWide.lean,
;;    `PadContract`): every byte in [code_size, code_size + 32) must be 0, which is
;;    exactly EELS's zero-fill of an immediate that runs off the end;
;;  - the fetch reads code[pc] unchecked, so after a PUSH32 in the last code byte
;;    (pc = code_size + 32) it must read 0 = STOP, EELS's implicit halt
;;    (lean/Evm/CL/Fetch.lean, `slack_suffices`): 33 zero bytes.

(defconstant +code-tail-pad-bytes+      64)
(assert (>= +code-tail-pad-bytes+ 33) () "the code pad must cover a PUSH32 immediate and the fetch after it")

;; ---- Revert journal ----------------------------------------
;;
;; The journal records every state mutation a frame can revert: storage
;; writes (SSTORE), balance transfers (CALL with value, SELFDESTRUCT),
;; EIP-2929 warm-ups, EIP-1153 transient stores, refund-counter changes,
;; created-this-tx inserts. 104 bytes/entry (c/tx_arena.h JournalEntry).
;;
;; Bounding the entry count: every journaled mutation costs gas. The
;; cheapest journaling ops are 100 gas (warm SSTORE value-change →
;; sstore + refund entries; TSTORE → one entry), so we budget one entry
;; per 50 gas. Allocated once, lazily zero-paged via calloc — at G=200M
;; the 416 MiB worst case stays virtual unless a tx really journals
;; 4M entries.

(defconstant +journal-entry-bytes+        104)
(defconstant +min-gas-per-journal-entry+   50)      ; 100-gas op, 2 entries
(defparameter +journal-entries-per-tx+
  (ceiling +block-gas-limit+ +min-gas-per-journal-entry+))
(defparameter +journal-bytes-per-tx+
  (* +journal-entry-bytes+ +journal-entries-per-tx+))

;; ---- Arena totals --------------------------------------------
;;
;; Arenas are pre-allocated once (lazy on first tx) and reused across
;; every tx and every frame. The sub-frame's slice into each arena is
;; computed from the parent frame's runtime state at the time of CALL/
;; CREATE, then rolled back on return.
;;
;; Memory: shared. EVM gas semantics allow up to N · memory(G/N) total
;; bytes across N frames in a tx; this is maximized as N → max-depth,
;; but EIP-150 (63/64 forwarded) damps deep chains exponentially. A
;; 4× single-frame ceiling covers any realistic shape. If a pathological
;; deep chain trips the cap, frames OOG instead of crashing.

(defconstant +memory-arena-overcommit+ 4)
(defparameter +memory-arena-bytes+
  (max (* +memory-arena-overcommit+ +memory-bytes-per-frame+)
       (* 2 1024 1024 1024))
  "~40 MiB at G=200M, floored at 2 GiB: legacy-corpus randomStatetests
   carry ~2^63 tx gas limits and legitimately expand memory to ~1.5 GiB
   (e.g. SHA3 with size=timestamp). calloc reserves lazily — untouched
   pages cost nothing, and the post-tx scrub only memsets the used
   high-water mark.")

;; Stack: spec-bounded × depth. One slot per frame, no over-commit.
;; Frames live at depths 0..+max-call-depth+ inclusive: the tx-level frame
;; is depth 0, and a CALL/CREATE is rejected only once the *calling* frame
;; is already at depth +max-call-depth+ (EELS `depth + 1 > STACK_DEPTH_LIMIT`),
;; so the deepest frame that actually runs sits at depth +max-call-depth+ and
;; slices at base (+max-call-depth+ · frame). That's 1+max-call-depth slots —
;; sizing for exactly +max-call-depth+ leaves the deepest frame writing one
;; slot past the arena (a guard-page memory fault). Pre-EIP-150 (before
;; Tangerine, block 2463000) gas is forwarded un-retained, so a contract can
;; cheaply recurse to the full limit and hit this every time.
(defparameter +stack-arena-bytes+
  (* (1+ +max-call-depth+) +stack-bytes-per-frame+))   ; ~32 MiB

;; A frame runs its code in place: EvmState points at the code's frame image, an octet
;; vector [code | pad | map] built once per code OBJECT (world code vectors are stable
;; and immutable; init code is fresh per CREATE and its image is GC'd with it) and pinned
;; while the frame runs. Rebuilding the JUMPDEST map on every frame was 25 % of the 2020
;; replay (9M frames x 11 us); copying code + map into a per-depth arena slot on every
;; frame was 3.8 % of the x86-64 near-tip replay (2026-11-01). One image per code also
;; means no slot to overflow: pre-Shanghai init code over 49152 bytes needs no
;; separate placement.
(defparameter *code-image-cache* (make-hash-table :test 'eq :weakness :key)
  "code vector -> its frame image (octets: code, +code-tail-pad-bytes+ zeros, JUMPDEST map).")

(defun frame-code-image (code len)
  "CODE's frame image (LEN = its length), from the cache or built now."
  (or (gethash code *code-image-cache*)
      ;; :initial-element 0 makes the pad zero: the PUSH/fetch contract above.
      (let ((img (make-array (+ len +code-tail-pad-bytes+ len) :element-type '(unsigned-byte 8)
                                                                 :initial-element 0)))
        (replace img code :end2 len)
        (sb-sys:with-pinned-objects (img)
          (let ((sap (sb-sys:vector-sap img)))
            (%jumpdest-map sap len (sb-sys:sap+ sap (+ len +code-tail-pad-bytes+)))))
        (setf (gethash code *code-image-cache*) img))))

(defmacro with-frame-code ((state code len) &body body)
  "Run BODY with STATE's code (#64/#72) and JUMPDEST map (#136) pointing into CODE's frame
   image, pinned for BODY's extent. The one place a frame's code is installed — tx, CALL
   family and CREATE."
  (let ((img (gensym "IMG")) (n (gensym "LEN")) (st (gensym "STATE")))
    `(let* ((,n ,len) (,img (frame-code-image ,code ,n)) (,st ,state))
       (sb-sys:with-pinned-objects (,img)
         (let ((sap (sb-sys:vector-sap ,img)))
           (setf (mem-ref ,st :pointer 64)  sap
                 (mem-ref ,st :uint64 72)   ,n
                 (mem-ref ,st :pointer 136) (sb-sys:sap+ sap (+ ,n +code-tail-pad-bytes+))))
         ,@body))))

;; Journal: per-tx arena, frame-relative slices via a parallel "journal
;; base" dynvar. Sized for the tx-level total.
(defparameter +journal-arena-bytes+ +journal-bytes-per-tx+)

;; ---- Native per-tx state tables (c/tx_state.h) ----------------
;;
;; Open-addressed linear-probe tables with epoch-tag occupancy. Sized
;; from the gas bound: every insert costs gas, so capacity =
;; next-pow2(2 × G / cheapest-insert-gas) keeps load factor ≤ 1/2.
;; calloc keeps the big ones virtual until touched.

(defun next-pow2 (n) (ash 1 (integer-length (1- n))))

(defconstant +ts-addr-entry-bytes+  40)   ; TsAddrEntry
(defconstant +ts-slot-entry-bytes+  72)   ; TsSlotEntry
(defconstant +ts-kv-entry-bytes+   104)   ; TsKvEntry

(defparameter +ts-addr-cap+                          ; cold addr = 2600
  (next-pow2 (ceiling (* 2 +block-gas-limit+) 2600)))
(defparameter +ts-slot-cap+                          ; cold slot = 2100
  (next-pow2 (ceiling (* 2 +block-gas-limit+) 2100)))
(defparameter +ts-tstore-cap+                        ; TSTORE = 100
  (next-pow2 (ceiling (* 2 +block-gas-limit+) 100)))
(defparameter +ts-created-cap+                       ; CREATE = 32000
  (next-pow2 (ceiling (* 2 +block-gas-limit+) 32000)))
(defparameter +ts-orig-cap+ +ts-slot-cap+)           ; first-touch ≤ slot accesses

;; ---- Arena state (lazy-init) ---------------------------------

(defparameter *memory-arena*       nil)
(defparameter *stack-arena*        nil)
(defparameter *journal-arena*      nil)

;; Native TxState (136 bytes, c/tx_state.h) + the root TxArena the
;; top-level frame and pre-frame code (reset-tx-state, apply-tx
;; prologue) journal into. Sub-frame arenas slice the same journal
;; buffer, so the whole tx is one contiguous log.
(defparameter *tx-state*        nil)
(defparameter *tx-arena-root*   nil)

;; The current frame's start offset into each arena. Dynvars so cb-call/
;; cb-create can save+rebind across recursive eita-run calls. (Code has no arena:
;; a frame runs its code's image in place, with-frame-code.)
(defparameter *memory-arena-base*  0)
(defparameter *stack-arena-base*   0)
(defparameter *journal-arena-base* 0)

;; The active frame's EvmState pointer. cb-call reads its memory_size
;; (offset 48) to know how much of the memory arena the parent has used,
;; so the sub-frame can start in the unused remainder.
(defparameter *current-state* (cffi:null-pointer))

;; libc memset for fast bulk zeroing — Lisp-level loops over 10s of MiB
;; take seconds; memset clears at memory-bandwidth speed.
(defcfun ("memset" %memset) :pointer
  (s :pointer) (c :int) (n :size))

;; libc memcpy + the two copy helpers across the foreign boundary. The code,
;; output and input copies used to be per-byte Lisp loops; with the vector's
;; type unknown at the call site each byte went through
;; HAIRY-DATA-VECTOR-REF/CHECK-BOUNDS — 26 % of the Arc replay's CPU
;; (sb-sprof, x86-64 Linux 2026-10-17: every CALL copied the whole callee code that way).
(defcfun ("memcpy" %memcpy) :pointer
  (dst :pointer) (src :pointer) (n :size))
(deftype octets () '(simple-array (unsigned-byte 8) (*)))
(defun bytes->foreign (dst v n &optional (start 0))
  "Copy N bytes of V, from START, to foreign DST. memcpy for simple octet
   vectors (world code, frame outputs); a byte loop for anything else."
  (declare (type fixnum n start))
  (when (plusp n)
    (if (typep v 'octets)
        (sb-sys:with-pinned-objects (v)
          (%memcpy dst (sb-sys:sap+ (sb-sys:vector-sap v) start) n))
        (loop for i below n do (setf (mem-aref dst :uint8 i) (aref v (+ start i))))))
  dst)
(defun foreign->bytes (src n)
  "A fresh simple octet vector holding N bytes from foreign SRC."
  (declare (type fixnum n))
  (let ((v (make-array n :element-type '(unsigned-byte 8))))
    (when (plusp n)
      (sb-sys:with-pinned-objects (v) (%memcpy (sb-sys:vector-sap v) src n)))
    v))
;; libc calloc: zeroed AND lazily paged — the OS maps zero pages until
;; first touch, so the worst-case-sized journal/tstorage buffers cost
;; nothing unless a tx actually fills them. (foreign-alloc with
;; :initial-element loops in Lisp at ~5 MiB/s; never use it for these.)
(defcfun ("calloc" %calloc) :pointer
  (n :size) (size :size))

;; ---- Guard-paged arena allocation ----------------------------
;; mmap each frame arena with a trailing PROT_NONE guard page so the FIRST
;; out-of-bounds write faults exactly at the arena boundary (clean SIGSEGV
;; with the PC in the offending handler) instead of silently scribbling into
;; an adjacent arena / the Lisp heap and only blowing up later in GC
;; ("CORRUPTION WARNING"). The per-frame capacity check (EvmState.memory_cap,
;; offset 56) OOGs before any *legitimate* access reaches the guard page, so a
;; fault here is always a real bounds bug — surfaced immediately and visibly
;; rather than as silent drift.
(defstartup *guard-arenas*
  (not (sb-ext:posix-getenv "EITA_NO_GUARD_ARENAS"))
  "PROT_NONE-guard the frame arenas. Unconditionally ON — this is a correctness
   tripwire, not a tuning knob: a guard fault is always a real bounds bug, caught
   at the offending access instead of as silent state drift. The cost is one
   mmap+mprotect per arena at first-tx setup; there is no per-access cost, so
   there is no performance reason to disable it.

   EITA_NO_GUARD_ARENAS is a DEBUG-ONLY escape hatch, NOT deployment config: when
   a guard *does* fire, run once with it set to A/B whether results still match
   (benign over-read) or diverge (real corruption) — the bisect that pinned #272.
   Never set it merely to push a faulting run to completion; fix the bounds bug.
   (#272: the Linux/aarch64 speculative stack[depth-2] under-read that used to
   fault here is fixed by the stack arena's +stack-head-pad-bytes+ head pad.)")
(defconstant +guard-page-bytes+ 16384)   ; Apple Silicon / common arm64 page

(defun %calloc-guarded (nbytes)
  "Zeroed, page-aligned region of NBYTES followed by a PROT_NONE guard page.
   mmap MAP_ANON memory is zero-filled and lazily paged, like calloc.
   Falls back to plain calloc when *guard-arenas* is nil."
  (if (not *guard-arenas*)
      (%calloc nbytes 1)
      (let* ((page  +guard-page-bytes+)
             (body  (* page (ceiling nbytes page)))
             (total (+ body page))
             ;; PROT_READ|PROT_WRITE = 3; MAP_PRIVATE|MAP_ANON (OS-dependent bit)
             (p (%mmap (null-pointer) total +prot-rw+ +map-priv-anon+ -1 0)))
        (when (= (pointer-address p) (ldb (byte 64 0) -1)) ; MAP_FAILED
          (error "mmap failed for ~D bytes" total))
        (when (minusp (%mprotect (inc-pointer p body) page 0)) ; PROT_NONE
          (error "mprotect guard page failed for arena of ~D bytes" nbytes))
        (when (sb-ext:posix-getenv "EITA_TRACE_ARENAS")
          (format *error-output* "ARENA base=~X body=~X(~D) guard=~X nbytes=~D~%"
                  (pointer-address p) body body
                  (pointer-address (inc-pointer p body)) nbytes)
          (finish-output *error-output*))
        p)))

;; #248/#250: the per-sub-call EvmState (600 B, c/evm_state.h) and TxArena header (72 B) are
;; pure scratch — freed by frame pop = slot reuse, never escaping (only the
;; RETURN output escapes, and that is still copied to a fresh disjoint buffer,
;; matching the proved discipline in Evm.CL.Arena.arena_refines_spec). So they
;; live in depth-indexed arena slots instead of a foreign-alloc per call, which
;; in the DoS region was ~70% of execution (CFFI parse-type + malloc + zeroing,
;; #248). Slot = frame depth: the tx-level frame is slot 0, a sub-frame is slot
;; (1+*call-depth*) which the depth guard keeps <= +max-call-depth+.
(defconstant +subarena-bytes+ 72)
(defparameter *substate-arena* nil)
(defparameter *subarena-arena* nil)

(defun ensure-arenas ()
  "Allocate the arenas + native TxState once, on first tx. Idempotent."
  (unless *memory-arena*
    (setf *memory-arena*  (%calloc-guarded +memory-arena-bytes+))
    ;; #272: reserve +stack-head-pad-bytes+ of valid slack BELOW the usable stack
    ;; region (the interp's speculative stack[depth-2] pre-load reads one slot
    ;; below the depth-0 frame's base). Frame bases = *stack-arena* + depth*frame
    ;; are unchanged; the guard still follows the (now slightly larger) body.
    (setf *stack-arena*   (inc-pointer (%calloc-guarded (+ +stack-head-pad-bytes+
                                                           +stack-arena-bytes+))
                                       +stack-head-pad-bytes+))
    (setf *journal-arena* (%calloc-guarded +journal-arena-bytes+))
    ;; Per-depth sub-frame state/arena slots (depths 0..+max-call-depth+).
    (setf *substate-arena* (%calloc-guarded (* (1+ +max-call-depth+) +substate-bytes+)))
    (setf *subarena-arena* (%calloc-guarded (* (1+ +max-call-depth+) +subarena-bytes+)))
    ;; TxState: masks at offsets 16..48, table pointers at 56..88
    ;; (c/tx_state.h layout, static-asserted there).
    (let ((ts (%calloc 136 1)))
      (setf (mem-ref ts :uint64 16) (1- +ts-addr-cap+))
      (setf (mem-ref ts :uint64 24) (1- +ts-slot-cap+))
      (setf (mem-ref ts :uint64 32) (1- +ts-tstore-cap+))
      (setf (mem-ref ts :uint64 40) (1- +ts-created-cap+))
      (setf (mem-ref ts :uint64 48) (1- +ts-orig-cap+))
      (setf (mem-ref ts :pointer 56) (%calloc +ts-addr-cap+    +ts-addr-entry-bytes+))
      (setf (mem-ref ts :pointer 64) (%calloc +ts-slot-cap+    +ts-slot-entry-bytes+))
      (setf (mem-ref ts :pointer 72) (%calloc +ts-tstore-cap+  +ts-kv-entry-bytes+))
      (setf (mem-ref ts :pointer 80) (%calloc +ts-created-cap+ +ts-addr-entry-bytes+))
      (setf (mem-ref ts :pointer 88) (%calloc +ts-orig-cap+    +ts-kv-entry-bytes+))
      (setf *tx-state* ts))
    ;; Root TxArena (72 bytes, c/tx_arena.h): journal_data at 16,
    ;; journal_cap at 40, tx_state at 64. Sub-frame arenas carry cap = 0
    ;; (unchecked); the gas-derived bound is enforced here at the root.
    (let ((ar (%calloc 72 1)))
      (setf (mem-ref ar :pointer 16) *journal-arena*)
      (setf (mem-ref ar :uint64 40) +journal-entries-per-tx+)
      (setf (mem-ref ar :pointer 64) *tx-state*)
      (setf *tx-arena-root* ar))))

(declaim (inline zero-fixed))
(defun zero-fixed (ptr nbytes)
  "Zero NBYTES at PTR via u64 stores (literal types inline — no CFFI
   parse-type, no malloc). Replaces foreign-alloc's :initial-element 0 loop."
  (let ((w (ash nbytes -3)))
    (dotimes (i w) (setf (mem-aref ptr :uint64 i) 0))
    (loop for i from (ash w 3) below nbytes do (setf (mem-aref ptr :uint8 i) 0))))

(declaim (inline alloc-zeroed))
(defun alloc-zeroed (nbytes)
  "Raw malloc of NBYTES, zeroed — no CFFI type-parse (the #248 hot cost).
   For variable-size scratch (calldata) and the escaping RETURN out-copy."
  (let ((p (cffi-sys:%foreign-alloc nbytes)))
    (zero-fixed p nbytes)
    p))

(declaim (inline substate-slot subarena-slot))
(defun substate-slot (depth)
  "Zeroed EvmState scratch for frame DEPTH (arena slice, not malloc)."
  (let ((p (inc-pointer *substate-arena* (* depth +substate-bytes+))))
    (zero-fixed p +substate-bytes+) p))
(defun subarena-slot (depth)
  "Zeroed TxArena header for frame DEPTH (arena slice, not malloc)."
  (let ((p (inc-pointer *subarena-arena* (* depth +subarena-bytes+))))
    (zero-fixed p +subarena-bytes+) p))

(defun zero-bytes (ptr off count)
  "Zero COUNT bytes at PTR+OFF. Used to scrub a sub-frame's memory slice
   so the parent (or a later sibling) sees zeros when memexp grows into
   that region, as EVM memory semantics require."
  (when (plusp count)
    ;; Bounds-guard the memory-arena scrubs: a frame's memory_size (the
    ;; COUNT here) must never exceed the arena body, or the memset walks
    ;; into the guard page and SIGSEGVs in foreign code (uncatchable). If
    ;; it does, some opcode set memory_size past memory_cap — raise a
    ;; catchable Lisp error so the driver names the block/tx instead.
    (when (and (pointer-eq ptr *memory-arena*)
               (> (+ off count) +memory-arena-bytes+))
      (error "memory-arena scrub overrun: off=~D count=~D (arena=~D) — a frame's memory_size exceeded memory_cap"
             off count +memory-arena-bytes+))
    (%memset (inc-pointer ptr off) 0 count)))
;; Transaction-level env, propagated to every CALL/CREATE sub-frame so the
;; ARM64 ORIGIN/COINBASE/etc. handlers read the right values.
(defparameter *tx-origin*     0)
(defparameter *tx-gasprice*   0)
(defparameter *tx-coinbase*   0)
(defparameter *tx-timestamp*  0)
(defparameter *tx-number*     0)
(defparameter *tx-gaslimit*   0)
(defparameter *tx-basefee*    0)
(defparameter *tx-chainid*    1)
(defparameter *tx-prev-randao* 0)

;; EIP-4844 blob env, EvmState #552/#560/#568 (c/evm_state.h; the contract is
;; Evm.CL.BlobEnv.HostTable / HostFee): the tx's versioned hashes as a native u256
;; table BLOBHASH indexes, and the block's blob base fee BLOBBASEFEE pushes. One table
;; per process, rewritten per tx; a tx has at most the block's blob cap of hashes (6 at
;; Cancun, 9 at Prague), so 128 entries is far above any schedule — more is an error,
;; never a silent truncation.
(defconstant +blob-hash-table-cap+ 128)
(defstartup *blob-hash-table* nil)   ; foreign, allocated on first use in each process
(defparameter *tx-blob-count* 0)
(defparameter *tx-blob-base-fee* 0)

(defun set-tx-blob-env! (hashes blob-base-fee)
  "Per tx: write the versioned HASHES (integers, EELS tx_env.blob_versioned_hashes; nil
   for a non-blob tx) into the native table and keep the block's BLOB-BASE-FEE;
   install-blob-env! then points every frame of the tx at them."
  (unless *blob-hash-table*
    (setf *blob-hash-table* (foreign-alloc :uint8 :count (* 32 +blob-hash-table-cap+))))
  (when (> (length hashes) +blob-hash-table-cap+)
    (error "tx carries ~D blob hashes; the native table holds ~D" (length hashes) +blob-hash-table-cap+))
  (loop for h in hashes for i from 0
        do (u256-write (inc-pointer *blob-hash-table* (* 32 i)) h))
  (setf *tx-blob-count* (length hashes)
        *tx-blob-base-fee* blob-base-fee))

(defun install-blob-env! (state)
  "Point STATE (any frame of the current tx) at the tx's blob-hash table and count
   (#552/#560) and give it the block's blob base fee (#568)."
  (setf (mem-ref state :pointer 552) (or *blob-hash-table* (null-pointer))
        (mem-ref state :uint64 560)  *tx-blob-count*)
  (u256-write (inc-pointer state 568) *tx-blob-base-fee*))

(defun populate-sub-env (sub-state &optional (parent (null-pointer)))
  "Write tx-level env (origin, gasprice, chainid, coinbase, timestamp,
number, gaslimit, basefee, prev_randao, the blob env) into a freshly-allocated
sub-frame state so opcodes like ORIGIN/COINBASE/etc. work in sub-calls. A sub-frame's
PARENT (any frame of the tx) holds exactly that env: it is copied over word by word
instead of rewritten field by field (EvmState: origin 176, gasprice..basefee 272..496,
prev_randao 512, blob_hashes..blob_base_fee 552..600)."
  (unless (null-pointer-p parent)
    (macrolet ((copy (from to)
                 `(loop for o of-type fixnum from ,from below ,to by 8
                        do (setf (sb-sys:sap-ref-64 sub-state o) (sb-sys:sap-ref-64 parent o)))))
      (copy 176 208) (copy 272 496) (copy 512 544) (copy 552 600))
    (return-from populate-sub-env sub-state))
  (u256-write (inc-pointer sub-state 176) *tx-origin*)
  (u256-write (inc-pointer sub-state 272) *tx-gasprice*)
  (u256-write (inc-pointer sub-state 304) *tx-chainid*)
  (u256-write (inc-pointer sub-state 336) *tx-coinbase*)
  (u256-write (inc-pointer sub-state 368) *tx-timestamp*)
  (u256-write (inc-pointer sub-state 400) *tx-number*)
  (u256-write (inc-pointer sub-state 432) *tx-gaslimit*)
  (u256-write (inc-pointer sub-state 464) *tx-basefee*)
  (u256-write (inc-pointer sub-state 512) *tx-prev-randao*)
  (install-blob-env! sub-state))
;; BLOCKHASH(n) lookup: maps block_number → hash. Populated by run-test
;; from the test JSON's genesis + block headers.
(defparameter *block-hashes* (make-hash-table :test 'eql))
;; Current block number — BLOCKHASH(n) returns 0 unless current-256 < n < current.
(defparameter *current-block-number* 0)
