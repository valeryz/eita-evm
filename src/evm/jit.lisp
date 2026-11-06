;;;; evm/jit.lisp — the JIT tier: the in-process loader, the code arena, the emitJIT daemon, the cache.

(in-package #:eita.evm)

;; Defined further down (the JIT cache and its statistics, the emit daemon's path) and in
;; evm/frames.lisp (the call depth).
(declaim (special *jit-cache* *jit-stats* *emit-jit* *call-depth*))

;; Fork.ord of the network under replay (Evm.Fork: frontier=0 ...
;; berlin=10 ... cancun=16). Selects the native dispatch table and the
;; call-gas plan symbol cb-call binds.
(defparameter *fork-ord* 16)

;;; --- Hotness-gated JIT tier (Phase 6d) -----------------------------
;;;
;;; Frames whose code has run *jit-threshold* times get compiled
;;; through `lake exe emitJIT` (per-chunk subroutine-threaded native
;;; code with chunk-head gas pre-charge + constant folding; see
;;; lean/Evm/CL/ARM64/JIT.lean) and dispatched chunk-by-chunk via
;;; eita_run_chunk. Programs the IR compiler rejects (opcodes whose
;;; forks aren't staged yet: SHL/SHR/SAR, RETURNDATA*, PUSH0, ... —
;;; see Evm/IR/Execute.lean) are cached :no-jit and stay on the
;;; interp tier. Both tiers share the EvmState ABI and callbacks, so
;;; nothing else in this file changes behavior.
;;;
;;; Per-program dylibs define the same symbols (_eita_run_chunk,
;;; _eita_jit_entries, _eita_chunk_N), so they are dlopen'd
;;; RTLD_LOCAL and resolved per-handle — CFFI's global symbol
;;; resolution can't express that.

(defcfun ("dlopen" %dlopen) :pointer (path :string) (mode :int))
(defcfun ("dlsym" %dlsym) :pointer (handle :pointer) (name :string))
(defconstant +rtld-now+   2)
(defconstant +rtld-local+ 4)

;;; --- In-process binary loader (#235): no clang, no dlopen ------------
;;;
;;; `emitJIT bin` writes a serialized image blob (machine bytes + movabs
;;; relocs + (pc,off) entries; see Evm.CL.ARM64.JIT.emitProgramImage). We
;;; mmap it RW, patch each movabs reloc with the runtime address of the
;;; named libeita symbol (the same handlers/helpers/stubs the clang dylib
;;; linked against), flip the page to RX + invalidate icache, and hand the
;;; resulting run_chunk pointer + entries manifest to the SAME
;;; `_eita_execute_program` dispatcher. This SBCL is unhardened, so plain
;;; RW->RX mprotect is permitted (no MAP_JIT entitlement needed).
;; mmap / mprotect: native/ffi.lisp.
;; Portable I-cache flush for a freshly-written JIT chunk (libeita's
;; eita_clear_icache → __builtin___clear_cache); works on arm64 macOS AND Linux,
;; replacing the macOS-only sys_icache_invalidate.
(defcfun ("eita_clear_icache" %icache-flush) :void
  (addr :pointer) (len :uint64))
(defconstant +prot-rw+ 3)            ; PROT_READ|PROT_WRITE
(defconstant +prot-rx+ 5)            ; PROT_READ|PROT_EXEC
;; MAP_PRIVATE|MAP_ANON: the MAP_ANON bit differs by OS — Darwin 0x1000, Linux
;; 0x20. (MAP_PRIVATE is 0x2 on both; MAP_SHARED is 0x1 on both.)
(defconstant +map-priv-anon+ #+darwin #x1002 #+linux #x22 #-(or darwin linux) #x1002)

(defun %read-file-bytes (path)
  (with-open-file (s path :element-type '(unsigned-byte 8))
    (let ((v (make-array (file-length s) :element-type '(unsigned-byte 8))))
      (read-sequence v s) v)))

(declaim (inline %rd64 %roundup))
(defun %rd64 (v o) (loop for i below 8 sum (ash (aref v (+ o i)) (* 8 i))))
(defun %roundup (n k) (* k (ceiling n k)))

;;; --- Bounded executable code arena (#259) ----------------------------------
;;; One RWX mmap holds ALL JIT chunks; load-jit-image bump-allocates into it
;;; instead of mmap'ing a fresh page per chunk (which made macOS dyld re-serialize
;;; its process-image atlas per chunk — the O(n²) DoS-peak storm, #248). Chunks are
;;; position-independent (only libeita symbols are reloc'd; inter-block flow goes
;;; through the dispatcher via the manifest's fn-abs, recomputed from the placement
;;; base), so any chunk can live anywhere in the arena. On wrap, evict non-pinned
;;; chunks and drop their *jit-cache* entry (re-touch reloads from the disk blob).
;;; SAFETY (Evm.CL.CodeArena.place_safe, proved): never overwrite a chunk on the
;;; live call stack — *code-exec-pinned* holds the executing frames' ranges, and
;;; alloc picks a range disjoint from all of them. Trust surface = the arena mach
;;; calls below + the page-index eviction refining the proved `place`.
;;; macOS/Apple-Silicon will NOT mmap a region RWX (W∧X is denied without MAP_JIT),
;;; and MAP_JIT's per-thread `pthread_jit_write_protect_np` toggle flips W^X for the
;;; WHOLE thread — which on SBCL 2.5.8/arm64 (its own code space is MAP_JIT) makes
;;; Lisp itself non-executable and faults the next instruction.  So we get one fixed
;;; executable region the portable JIT way: a RW/RX DOUBLE MAP.  `vm_allocate` an RX
;;; region, `vm_remap` a RW alias of the SAME physical pages, then `vm_protect` the
;;; two views.  We WRITE chunks through the RW view and EXECUTE them through the RX
;;; view — never W∧X on one mapping, no MAP_JIT, no toggle, and only TWO mappings for
;;; the whole run, so dyld serializes its image atlas once instead of per chunk (the
;;; #248 storm).  Trust surface = these three mach calls + the view-offset arithmetic.
;; macOS double-map primitives (mach VM): vm_allocate an RX region, vm_remap a
;; RW alias of the SAME physical pages, vm_protect the two views.
#+darwin
(progn
  (defcfun ("vm_allocate" %vm-allocate) :int
    (task :uint32) (addr :pointer) (size :uint64) (flags :int))
  (defcfun ("vm_protect" %vm-protect) :int
    (task :uint32) (addr :uint64) (size :uint64) (setmax :int) (prot :int))
  (defcfun ("vm_remap" %vm-remap) :int
    (target :uint32) (taddr :pointer) (size :uint64) (mask :uint64) (flags :int)
    (src :uint32) (saddr :uint64) (copy :int) (cur :pointer) (max :pointer) (inherit :int))
  (defun %mach-task-self () (mem-ref (foreign-symbol-pointer "mach_task_self_") :uint32))
  (defconstant +vm-flags-anywhere+ 1)
  (defconstant +vm-inherit-none+ 2)
  (defconstant +vm-prot-rw+ 3)           ; VM_PROT_READ|WRITE
  (defconstant +vm-prot-rx+ 5))          ; VM_PROT_READ|EXECUTE

;; Linux double-map primitives: memfd_create an anonymous file, size it, then
;; mmap it TWICE (MAP_SHARED) — once RW, once RX — over the same physical pages.
;; Same W^X-clean RW/RX aliasing as the macOS mach path; no MAP_JIT, no per-thread
;; toggle. memfd_create is a libc wrapper on glibc >= 2.27 (AL2023 = 2.34).
#+linux
(progn
  (defcfun ("memfd_create" %memfd-create) :int (name :string) (flags :uint32))
  (defcfun ("ftruncate" %ftruncate) :int (fd :int) (len :int64))
  (defcfun ("close" %close) :int (fd :int))
  (defconstant +map-shared+ #x1)         ; MAP_SHARED
  (defconstant +mfd-cloexec+ #x1))       ; MFD_CLOEXEC
(defstartup +code-exec-arena-bytes+
  (let ((kb (sb-ext:posix-getenv "EITA_CODE_ARENA_KB"))
        (mb (sb-ext:posix-getenv "EITA_CODE_ARENA_MB")))
    (cond (kb (* (parse-integer kb) 1024))          ; KB knob: forces wrap in stress tests
          (mb (* (parse-integer mb) 1024 1024))
          (t  (* 512 1024 1024)))))                 ; default 512 MiB
(defparameter *code-exec-base*   nil)    ; RX (execute) view base pointer
(defparameter *code-write-base*  nil)    ; RW (write) view: same physical pages as RX
(defparameter *code-exec-head*   0)      ; bump offset
;; Live chunks indexed by the arena PAGE(s) they occupy (a spatial hash): a
;; placement examines only chunks sharing a page with its byte range, so eviction
;; is O(amortized-1) instead of the old whole-list `remove-if` scan that was O(n²)
;; over a JIT batch (#259).  Overlap is decided by exact offset arithmetic — there
;; is NO assumption about allocation/FIFO order, which a bump-with-wrap-and-pins
;; allocator routinely violates (the FIFO-oldest chunk can sit at a high offset
;; after a wrap, so a FIFO front-walk would stop before reaching a low-offset
;; overlap and leave a stale chunk mapped onto overwritten bytes).
(defconstant +code-page-shift+ 12)       ; 4 KiB pages
(defparameter *code-page-index* nil)     ; simple-vector: page -> list of #(off len key man)
(defparameter *code-live-count* 0)       ; live chunk count (diagnostics)
(defparameter *code-exec-pinned* nil)    ; on-stack ranges: list of (off . len)

#+darwin
(defun %arena-double-map (sz)
  "macOS: vm_allocate RX + vm_remap a RW alias of the same physical pages.
   Returns (values rx-pointer rw-pointer)."
  (let ((task (%mach-task-self)))
    (with-foreign-objects ((rx :uint64) (rw :uint64) (cur :int) (max :int))
      (setf (mem-ref rx :uint64) 0 (mem-ref rw :uint64) 0)
      (unless (zerop (%vm-allocate task rx sz +vm-flags-anywhere+))
        (error "code-arena vm_allocate failed"))
      (let ((rxa (mem-ref rx :uint64)))
        (unless (zerop (%vm-remap task rw sz 0 +vm-flags-anywhere+
                                  task rxa 0 cur max +vm-inherit-none+))
          (error "code-arena vm_remap failed"))
        (let ((rwa (mem-ref rw :uint64)))
          (unless (zerop (%vm-protect task rwa sz 0 +vm-prot-rw+))
            (error "code-arena vm_protect(rw) failed"))
          (unless (zerop (%vm-protect task rxa sz 0 +vm-prot-rx+))
            (error "code-arena vm_protect(rx) failed"))
          (values (make-pointer rxa) (make-pointer rwa)))))))

#+linux
(defun %arena-double-map (sz)
  "Linux: memfd_create a sized anonymous file, mmap it twice (MAP_SHARED) as RW
   and RX over the same physical pages. Returns (values rx-pointer rw-pointer).
   The fd is closed after mapping — the two mappings keep the pages alive."
  (let ((fd (%memfd-create "eita-jit" +mfd-cloexec+)))
    (when (minusp fd) (error "code-arena memfd_create failed"))
    (unwind-protect
         (progn
           (unless (zerop (%ftruncate fd sz)) (error "code-arena ftruncate failed"))
           (let ((rw (%mmap (null-pointer) sz +prot-rw+ +map-shared+ fd 0))
                 (rx (%mmap (null-pointer) sz +prot-rx+ +map-shared+ fd 0)))
             (when (or (eql (pointer-address rw) #.(1- (ash 1 64)))  ; MAP_FAILED
                       (eql (pointer-address rx) #.(1- (ash 1 64))))
               (error "code-arena mmap failed"))
             (values rx rw)))
      (%close fd))))

(defun ensure-code-arena ()
  (unless *code-exec-base*
    (let ((sz +code-exec-arena-bytes+))
      (multiple-value-bind (rxp rwp) (%arena-double-map sz)
        (setf *code-exec-base*  rxp
              *code-write-base* rwp
              *code-exec-head* 0 *code-live-count* 0
              *code-page-index* (make-array (ceiling sz (ash 1 +code-page-shift+))
                                            :initial-element nil))))))

(declaim (inline %overlap %page-lo %page-hi))
(defun %overlap (o1 l1 o2 l2)
  "Ranges [o1,o1+l1) and [o2,o2+l2) overlap (¬Disjoint)."
  (and (< o1 (+ o2 l2)) (< o2 (+ o1 l1))))
(defun %page-lo (off)     (ash off (- +code-page-shift+)))
(defun %page-hi (off len) (ash (+ off len -1) (- +code-page-shift+)))   ; len>0

(defun code-arena-evict-overlapping (off len)
  "Evict every live chunk overlapping [off,off+len): drop it from *jit-cache*, free
   its manifest, and unlink it from the page index.  Only chunks sharing a page with
   the range are examined (the placement spans ⌈len/4K⌉+1 pages).  PINNED chunks (on
   the live call stack) never overlap — code-arena-place chose `off` disjoint from
   every pin — so they are naturally excluded; we assert it defensively.  This is the
   O(amortized-1) refinement of CodeArena.place's eviction (Evm.CL.CodeArena.place)."
  (let ((idx *code-page-index*) (victims nil))
    (loop for p from (%page-lo off) to (%page-hi off len) do
      (dolist (c (svref idx p))
        (when (and (%overlap off len (svref c 0) (svref c 1))
                   (not (member c victims :test #'eq)))
          (push c victims))))
    (dolist (c victims)
      (remhash (svref c 2) *jit-cache*)
      (foreign-free (svref c 3))                    ; manifest
      (incf (getf *jit-stats* :chunk-evictions 0))
      (decf *code-live-count*)
      (loop for p from (%page-lo (svref c 0)) to (%page-hi (svref c 0) (svref c 1)) do
        (setf (svref idx p) (delete c (svref idx p) :test #'eq))))))

(defun code-arena-place (len)
  "Find a non-pinned slot of LEN bytes (CodeArena.place): skip past any PINNED
   (on-stack) chunk, then evict the overlapping non-pinned chunks — dropping each
   from *jit-cache* and freeing its manifest. Return the byte offset; NIL only if
   every slot is pinned (never for pinned ⊆ call-stack ≪ arena → caller interps)."
  (ensure-code-arena)
  (let ((cap +code-exec-arena-bytes+) (scanned 0))
    (loop
      (when (> (+ *code-exec-head* len) cap) (setf *code-exec-head* 0))
      (let* ((off *code-exec-head*)
             (blocker (let ((m 0))
                        (dolist (p *code-exec-pinned*)
                          (when (%overlap off len (car p) (cdr p))
                            (setf m (max m (+ (car p) (cdr p))))))
                        (and (plusp m) m))))
        (cond
          (blocker
           (incf scanned (- blocker off))
           (setf *code-exec-head* blocker)
           (when (> scanned (+ cap len)) (return nil)))
          (t
           (code-arena-evict-overlapping off len)
           (setf *code-exec-head* (+ off len))
           (return off)))))))

(defun code-arena-register (off len key man)
  "Index a placed chunk #(off len cache-key manifest) under every page it occupies,
   so a later wrap-around allocation that reuses those bytes finds and evicts it."
  (let ((c (vector off len key man)) (idx *code-page-index*))
    (loop for p from (%page-lo off) to (%page-hi off len) do
      (push c (svref idx p)))
    (incf *code-live-count*)))

(defstartup *foreign-sym-cache* (make-hash-table :test 'equal)
  "Symbol name -> resolved libeita address. dlsym (foreign-symbol-pointer) is a dyld
   export-trie walk; the DoS region JITs thousands of chunks all referencing the same
   handful of libeita symbols, so resolving per-reloc made dlsym ~90% of the region
   (sampled). libeita symbols are fixed for the process lifetime → resolve each ONCE.")
(defun %sym-addr (cname)
  "Cached dlsym: the absolute address of libeita symbol CNAME."
  (or (gethash cname *foreign-sym-cache*)
      (let ((p (foreign-symbol-pointer cname)))
        (unless p (error "unresolved symbol ~A" cname))
        (setf (gethash cname *foreign-sym-cache*) (pointer-address p)))))

(defun load-jit-image (b key)
  "Bump-allocate the emitJIT blob B into the shared double-mapped code arena (#259)
   under cache KEY, returning (values run-chunk-ptr manifest off imgsz). Bytes and
   relocs are written through the RW view (*code-write-base*); the run-chunk pointer,
   manifest fn-abs and icache flush use the RX view (*code-exec-base*) — the address
   the chunk actually executes from. One arena, no per-chunk mmap/mprotect → dyld
   serializes once. Chunks are position-independent (only libeita symbols reloc'd).
   Evicted on wrap (code-arena-place); registered here for that. Signals on a bad
   blob or an unresolved symbol (only ever a libeita symbol)."
  (let* ((imgsz (%rd64 b 8)) (rcoff (%rd64 b 16))
         (nent (%rd64 b 24)) (nrel (%rd64 b 32))
         (aoff (code-arena-place imgsz)))
    (unless aoff (return-from load-jit-image (values nil "code arena full (all pinned)")))
    (let* ((wbase (inc-pointer *code-write-base* aoff))  ; write view
           (xbase (inc-pointer *code-exec-base*  aoff))  ; execute view (same pages)
           (baseaddr (pointer-address xbase)))
      ;; image bytes (RW view): memcpy (a byte loop here was ~1.3 s per 134 MB of images)
      (bytes->foreign wbase b imgsz 40)
      ;; patch relocs: kind 4 = ARM64 movabs (4 movz/movk words: OR the addr halfwords
      ;; into imm16), kind 5 = x86-64 abs64 slot (8 bytes)
      (let ((off (+ 40 (%roundup imgsz 8) (* 16 nent))))
        (dotimes (k nrel)
          (let* ((kind (%rd64 b off)) (roff (%rd64 b (+ off 8))) (slen (%rd64 b (+ off 16)))
                 (sym (map 'string #'code-char (subseq b (+ off 24) (+ off 24 slen)))))
            (setf off (+ off 24 (%roundup slen 8)))
            (unless (or (= kind 4) (= kind 5))
              (error "unexpected reloc kind ~A (~A)" kind sym))
            (let* ((cname (if (and (plusp (length sym)) (char= (char sym 0) #\_))
                              (subseq sym 1) sym))
                   (addr (%sym-addr cname)))
              (if (= kind 5)
                  ;; x86-64 (X86JIT): an abs64 slot, `.quad sym` — write the address
                  (setf (mem-ref wbase :uint64 roff) addr)
                  (let ((w (truncate roff 4)))
                    (dotimes (i 4)
                      (setf (mem-aref wbase :uint32 (+ w i))
                            (logior (mem-aref wbase :uint32 (+ w i))
                                    (ash (ldb (byte 16 (* 16 i)) addr) 5))))))))))
      (%icache-flush xbase imgsz)
      (when (sb-posix:getenv "EITA_TRACE_JIT_EXEC")
        (format *error-output* "JITLOAD base=~X off=~D imgsz=~D~%" baseaddr aoff imgsz)
        (finish-output *error-output*))
      ;; the (pc, fn-abs) manifest as a dispatch table; fn-abs from the EXECUTE base
      (let* ((eoff (+ 40 (%roundup imgsz 8)))
             (man (spec-dispatch-table
                   (loop for k below nent
                         collect (cons (%rd64 b (+ eoff (* 16 k)))
                                       (+ baseaddr (%rd64 b (+ eoff (* 16 k) 8))))))))
        (code-arena-register aoff imgsz key man)
        (values (inc-pointer xbase rcoff) man aoff imgsz)))))

(defun load-jit-blob (path key)
  "Load the disk-cached emitJIT blob at PATH into the code arena under KEY."
  (load-jit-image (%read-file-bytes path) key))

;;; --- Persistent emit server client (#235) ---------------------------
;;;
;;; One `emitJIT serve <sock>` daemon serves the whole run over a Unix
;;; domain socket: the replay streams (fork, code) and gets back the loader
;;; blob, so a cold contract costs a socket round-trip, not a process spawn.
;;; Warm contracts never reach here — the disk blob cache short-circuits.

(defstartup *emit-sock*
  (format nil "/tmp/eita-emit-~D.sock" (sb-posix:getpid)))
(defparameter *emit-proc* nil)
(defparameter *emit-stream* nil)

(defun %u32-bytes (n)
  (let ((v (make-array 4 :element-type '(unsigned-byte 8))))
    (dotimes (i 4 v) (setf (aref v i) (ldb (byte 8 (* 8 i)) n)))))

(defun %rd64-4 (v o) (loop for i below 4 sum (ash (aref v (+ o i)) (* 8 i))))

(defun emit-server-environment ()
  "The Lean-built daemon's environment: libmcl on macOS; on Linux the toolchain's own
   libc++/libc++abi/libunwind (lean --print-prefix)/lib, which no system path has."
  (let ((env (sb-ext:posix-environ)))
    (if (find :darwin *features*)
        (cons "DYLD_LIBRARY_PATH=/opt/homebrew/lib" env)
        (let* ((elan (format nil "~A/.elan/bin/lean" (sb-posix:getenv "HOME")))
               (prefix (ignore-errors
                        (string-trim '(#\Newline #\Space)
                                     (with-output-to-string (o)
                                       (sb-ext:run-program (if (probe-file elan) elan "lean")
                                                           '("--print-prefix") :search t :output o
                                                           :directory (namestring (eita-file "lean/"))))))))
          (if (plusp (length prefix))
              (cons (format nil "LD_LIBRARY_PATH=~A/lib~@[:~A~]" prefix (sb-posix:getenv "LD_LIBRARY_PATH"))
                    (remove-if (lambda (e) (eql 0 (search "LD_LIBRARY_PATH=" e))) env))
              env)))))

(defun ensure-emit-server ()
  "Start the emit daemon (once) and connect; return the byte stream."
  (unless *emit-stream*
    (setf *emit-proc*
          (sb-ext:run-program *emit-jit* (list "serve" *emit-sock*) :wait nil
                              :environment (emit-server-environment)))
    (push (lambda () (ignore-errors (sb-ext:process-kill *emit-proc* 15))
                     (ignore-errors (delete-file *emit-sock*)))
          sb-ext:*exit-hooks*)
    (loop repeat 500 until (probe-file *emit-sock*) do (sleep 0.01))
    (unless (probe-file *emit-sock*)
      (error "emitJIT (~A) did not open its socket within 5 s (~:[exited, code ~A~;still running~]); EITA_NO_JIT=1 runs without it"
             *emit-jit* (sb-ext:process-alive-p *emit-proc*) (sb-ext:process-exit-code *emit-proc*)))
    (let ((s (make-instance 'sb-bsd-sockets:local-socket :type :stream)))
      (sb-bsd-sockets:socket-connect s *emit-sock*)
      (setf *emit-stream*
            (sb-bsd-sockets:socket-make-stream s :input t :output t
                                               :element-type '(unsigned-byte 8)))))
  *emit-stream*)

(defun emit-request (code)
  "Ask the daemon to emit CODE at the active fork. Returns the blob byte vector,
   or (values nil reason) on a compile error."
  (let ((st (ensure-emit-server))
        (code (coerce code '(simple-array (unsigned-byte 8) (*)))))
    (write-sequence (%u32-bytes *fork-ord*) st)
    (write-sequence (%u32-bytes (length code)) st)
    (write-sequence code st)
    (finish-output st)
    (let ((hdr (make-array 8 :element-type '(unsigned-byte 8))))
      (unless (= 8 (read-sequence hdr st)) (error "emit server closed"))
      (let* ((status (%rd64-4 hdr 0)) (blen (%rd64-4 hdr 4))
             (body (make-array blen :element-type '(unsigned-byte 8))))
        (read-sequence body st)
        (if (zerop status) body
            (values nil (map 'string #'code-char body)))))))

;; Lean emit-server binary (native/libraries.lisp emit-jit-path: EITA_EMITJIT, else next
;; to the executable, else <home>/lean/.lake/build/bin). A deploy ships this binary (built by
;; `lake build emitJIT`) — the JIT emits via this daemon over a Unix socket (see
;; ensure-emit-server), so it is required at runtime on every target, alongside its libmcl
;; dependency.
(defstartup *emit-jit* (emit-jit-path))
(defstartup *jit-threshold*
  (let ((v (sb-ext:posix-getenv "EITA_JIT_THRESHOLD")))
    (if v (parse-integer v) 1))
  "Frames executed with the same code before we attempt to JIT it.
   Default 1 — JIT on first touch: replay is a validation workload,
   so maximal JIT coverage is the point. Raise via env to gate by
   hotness; huge value = interp-only.")
;; --- JIT cache keying: memoized keccak codehash (not per-lookup bytecode hash) ---
;; The cache key is (fork-ord . code). An EQUALP table would `psxhash` the WHOLE
;; bytecode on every lookup AND `equalp`-compare it on every hit — O(code-size)
;; per frame. In the 2016 DoS blocks (millions of CALL/EXTCODESIZE frames) that is
;; the dominant cost (a 2.35M-block batch: 43min -> 12.5min once removed, 0 state
;; divergence). Instead key by a custom test that goes through a memoized keccak:
;;   - code-hash-int: keccak256(code) as a 256-bit int, memoized per code OBJECT
;;     (code is the stable world-code vector) so keccak runs ONCE per contract;
;;     O(1) thereafter. Weak keys: a self-destructed code's entry is GC'd.
;;   - jitk-hash: O(1) — sxhash(fork) mixed with sxhash(memoized codehash bignum).
;;     (A raw EQ/address hash can't be used in a user test: SBCL's moving GC would
;;     leave it stale; only built-in :test 'eq tables get auto-rehashed.)
;;   - jitk=: eq fast-path (repeated same-contract frame — the hot case) -> O(1);
;;     else compare memoized codehashes (clones with identical bytecode share).
;; Same (fork . code) key + single table as before, so the #259 arena eviction
;; (`remhash (svref c 2) *jit-cache*`) is unchanged. Content identity is preserved
;; (codehash == the disk cache's identity), so the SAME chunk is selected — no
;; consensus change.
(defparameter *code-hash-memo* (make-hash-table :test 'eq :weakness :key)
  "code vector -> keccak256(code) as a 256-bit int. keccak once per contract.")
(defun code-hash-int (code)
  (or (gethash code *code-hash-memo*)
      (setf (gethash code *code-hash-memo*)
            (let ((h 0))
              (loop for b across (keccak256-bytes code)   ; defined below; runtime-resolved
                    do (setf h (logior (ash h 8) b)))
              h))))
(defun jitk-hash (key)
  (logand (logxor (* (sxhash (car key)) 31) (sxhash (code-hash-int (cdr key))))
          most-positive-fixnum))
(defun jitk= (a b)
  (and (eql (car a) (car b))
       (or (eq (cdr a) (cdr b))
           (eql (code-hash-int (cdr a)) (code-hash-int (cdr b))))))
(sb-ext:define-hash-table-test jitk= jitk-hash)
(defparameter *jit-cache* (make-hash-table :test 'jitk=)
  "(fork-ord . code bytes) -> count | (:jit run-chunk entries) | :no-jit.
   Keyed by fork because the emitted chunks bake in fork routing
   (opcode admission, sstore sentry, exp byte cost, selfdestruct). The table's
   hash/equality go through a memoized keccak codehash (see above) so the hot-path
   lookup is O(1), not O(code-size).")
(defparameter *jit-counter* 0)
(defvar *frames-jit* 0)        ; per-frame counters, kept out of the plist (GETF/%PUTF per frame)
(defvar *frames-interp* 0)
(declaim (type fixnum *frames-jit* *frames-interp*))
(defparameter *jit-stats*
  (list :codes-jit 0 :codes-no-jit 0
        :frames-jit 0 :frames-interp 0 :manifest-misses 0)
  "Replay-wide tier accounting, reported in the end summary. Every
   interp fallback is visible here (no-silent-gaps rule).")

(defun code-tag (code)
  (format nil "~D bytes ~{~2,'0X~}~:[~;…~]"
          (length code)
          (coerce (subseq code 0 (min 8 (length code))) 'list)
          (> (length code) 8)))

(defun first-line (s)
  (let ((nl (position #\Newline s)))
    (string-trim '(#\Space #\Newline) (subseq s 0 (or nl (length s))))))

(defstartup *jit-cache-dir*
  (let ((d (or (sb-posix:getenv "EITA_JIT_CACHE_DIR")
               (format nil "~A/.cache/eita-jit" (sb-posix:getenv "HOME")))))
    (ensure-directories-exist (concatenate 'string d "/"))
    d)
  "DISK cache of compiled JIT chunks, keyed by (fork, keccak(code)). Within one
   run *jit-cache* (in-memory) already prevents recompiles; the disk cache means
   a RE-RUN or a RESUMED image (whose in-memory cache was wiped) dlopen's the
   already-built chunk directly, skipping emitJIT + clang. Set EITA_JIT_CACHE_DIR
   to relocate; rm -rf it to invalidate (e.g. after changing the chunk emitter).")

(defstartup *inproc-jit*
  (let ((v (sb-posix:getenv "EITA_INPROC_JIT"))) (if v (string/= v "0") t))
  "DEFAULT ON. Build JITs by loading the emit-daemon's chunk BYTES in-process
   (mmap -> relocation patch -> RX in the #259 double-mapped arena), instead of
   the clang+dlopen path. The dlopen path leaks one resident dylib mapping per
   chunk (fee5b5f unlinks the file but not the mapping) -> ~43G 'dyld private
   memory' over a long replay -> DoS-region swap death, and is ~50x slower. The
   arena loader is bounded (page-index eviction) and checkpoint-safe (9d25a27).
   Opt OUT with EITA_INPROC_JIT=0 to fall back to clang+dlopen (a deprecated
   cross-check kept only until inproc clears a full 0->5M). NOTE: this is the
   in-process LOADER; the Lean->ARM64 emission is still the out-of-process
   emitJIT daemon (true in-process emission is #235, not yet done).")

(defstartup *lastframe-from*
  (let ((v (sb-posix:getenv "EITA_LASTFRAME_FROM"))) (and v (parse-integer v)))
  "Hang probe: from this block on, overwrite /tmp/eita_lastframe.hex with each
   JIT frame's code before running it, so a wedged frame leaves its culprit.")

(defun jit-cache-path (code)
  "Cache dylib path for CODE at the active fork. keccak(code) is collision-
   resistant and matches the in-memory cache's content identity; the fork prefix
   keeps per-fork chunk variants (opcode admission, sstore/exp/selfdestruct)
   apart; the emitJIT binary's mtime versions the key so rebuilding the chunk
   GENERATOR auto-invalidates the cache. (libeita changes need no invalidation —
   the cached dylib dynamically links it, so a rebuilt handler is picked up at
   dlopen; only the code GENERATED into the chunk depends on emitJIT.)"
  (jit-cache-file code "dylib"))

(defun jit-cache-file (code ext)
  (format nil "~A/v~A-f~D-~64,'0X.~A" *jit-cache-dir* (or (ignore-errors (file-write-date *emit-jit*)) 0)
          *fork-ord* (code-hash-int code) ext))

(defun blob-cache-path (code)
  "In-process loader blob path for CODE (same keying as jit-cache-path, .blob)."
  (jit-cache-file code "blob"))

(defun try-build-jit-inproc (code)
  "In-process twin of try-build-jit: a cache-keyed blob is mmap'd + patched in
   this process (no clang, no dlopen). Cache HIT mmaps the disk blob directly;
   MISS asks the persistent emit daemon for the bytes, persists them, then maps.
   Returns (values run-chunk entries) or (values nil reason)."
  (let ((blob (blob-cache-path code))
        (key (cons *fork-ord* code)))
    (handler-case
        (if (probe-file blob)
            (load-jit-blob (namestring blob) key)
            (multiple-value-bind (bytes reason) (emit-request code)
              (if (null bytes)
                  (values nil reason)            ; compile error (not-yet-staged op)
                  (let ((tmp (format nil "~A.tmp~D" blob (incf *jit-counter*))))
                    (with-open-file (s tmp :direction :output
                                       :element-type '(unsigned-byte 8)
                                       :if-exists :supersede)
                      (write-sequence bytes s))
                    (rename-file tmp blob)        ; atomic install for resume
                    (load-jit-image bytes key)))))
      (error (e)
        (ignore-errors (delete-file blob))
        (values nil (format nil "inproc: ~A" e))))))

(defun try-build-jit (code)
  "Return (values run-chunk entries) for CODE, or (values nil reason). DISK-CACHED:
   if the keyed chunk dylib already exists, dlopen it directly; otherwise emitJIT
   + clang into a temp in the cache dir and atomically rename it in. Compile
   failures (CompileError.unknownOpcode for not-yet-staged ops) return nil."
  (let* ((dylib  (jit-cache-path code))
         (cached (probe-file dylib))
         (n (incf *jit-counter*))
         (hex (with-output-to-string (s)
                (loop for b across code do (format s "~2,'0x" b))))
         (s-path (format nil "/tmp/eita-jit-rt-~D.S" n))
         (tmp    (format nil "~A/.build-~D.dylib" *jit-cache-dir* n))
         (err (make-string-output-stream)))
    (unwind-protect
        (progn
          (unless cached
            ;; emitJIT → .S, clang → tmp dylib (same fs as cache, so the rename
            ;; below is atomic — a crashed compile never leaves a half-written
            ;; cache entry).
            (let ((p (sb-ext:run-program
                      *emit-jit* (list hex (format nil "~D" *fork-ord*))
                      :output s-path :if-output-exists :supersede :error err
                      :environment (cons "DYLD_LIBRARY_PATH=/opt/homebrew/lib"
                                         (sb-ext:posix-environ)))))
              (unless (zerop (sb-ext:process-exit-code p))
                (return-from try-build-jit
                  (values nil (format nil "emitJIT: ~A"
                                      (first-line (get-output-stream-string err)))))))
            (let ((p (sb-ext:run-program
                      "/usr/bin/clang"
                      (list "-arch" "arm64" "-shared" "-o" tmp s-path
                            (format nil "-L~A" (namestring (dir-of (native-path "libeita")))) "-leita")
                      :error err)))
              (unless (zerop (sb-ext:process-exit-code p))
                (return-from try-build-jit
                  (values nil (format nil "clang: ~A"
                                      (first-line (get-output-stream-string err)))))))
            (rename-file tmp dylib))
          (let ((handle (%dlopen (namestring dylib) (logior +rtld-now+ +rtld-local+))))
            (when (null-pointer-p handle)
              ;; A corrupt cache entry: drop it so the next touch rebuilds.
              (ignore-errors (delete-file dylib))
              (return-from try-build-jit (values nil "dlopen failed")))
            ;; `_eita_execute_program` indexes a dispatch table, not the manifest
            (values (%dlsym handle "eita_run_chunk")
                    (spec-dispatch-table (spec-manifest-pairs (%dlsym handle "eita_jit_entries"))))))
      (ignore-errors (delete-file s-path))
      (ignore-errors (delete-file tmp)))))   ; keep the CACHE dylib; only temps go

(defstartup *jit-max-pc*
  (let ((v (sb-ext:posix-getenv "EITA_JIT_MAX_PC"))) (and v (parse-integer v)))
  "Diagnosis: blind the compiled chunk manifest for every entry whose pc is >= this,
   so dispatch there is a manifest miss and the INTERP finishes the frame. Binary
   searching this value localises a JIT/interp divergence to one chunk entry — the
   smallest value at which the divergence still appears.")

(defstartup *jit-max-pc-codelen*
  (let ((v (sb-ext:posix-getenv "EITA_JIT_MAX_PC_CODELEN"))) (and v (parse-integer v)))
  "Restrict *jit-max-pc* to codes of exactly this byte length — i.e. one contract.")

(defun manifest-blinded (table max-pc)
  "The dispatch TABLE with no entry at any pc >= MAX-PC (in place: the table is
   ours, built by spec-dispatch-table)."
  (loop for pc from max-pc below (mem-aref table :uint64 0)
        do (setf (mem-aref table :uint64 (1+ pc)) 0))
  table)

(defstartup *jit-deny*
  (let ((f (sb-posix:getenv "EITA_JIT_DENY_FILE")))
    (when f
      (let ((s (make-hash-table :test 'equalp)))
        (with-open-file (in f :if-does-not-exist nil)
          (when in
            (loop for line = (read-line in nil nil) while line
                  for h = (string-trim '(#\Space #\Newline #\Return #\Tab) line)
                  when (plusp (length h))
                  do (setf (gethash
                            (coerce (loop for i below (floor (length h) 2)
                                          collect (parse-integer h :start (* 2 i)
                                                                  :end (+ 2 (* 2 i)) :radix 16))
                                    '(vector (unsigned-byte 8))) s) t))))
        s)))
  "Codes (byte-vector keys) forced to the interp tier — diagnosis: pin a JIT
   divergence by running the suspect contract on the verified interpreter while
   everything else still JITs. Set EITA_JIT_DENY_FILE to a file of hex codes.")

(defstartup *force-interp*
  (let ((v (sb-posix:getenv "EITA_NO_JIT"))) (and v (string/= v "0")))
  "When true, every frame runs the threaded interp — jit-for-code returns NIL
   before any emit, so the Lean `emitJIT` daemon is never spawned. EITA_NO_JIT=1
   selects this at startup: a Leanless interp-only deploy needs no Lean at
   runtime (just libeita + the committed host.lisp). Also bound true per-frame
   for the differential mode's tier-B pass (diff-run-tiers / #241).")

(defun jit-for-code (code)
  "Count an execution of CODE; (values run-chunk entries) once hot
   and compiled, NIL otherwise. A code that fails to compile is
   cached :no-jit and LOGGED once — interp fallbacks must stay
   visible, never silent."
  (when *force-interp* (return-from jit-for-code nil))
  (let* ((key (cons *fork-ord* code))
         (entry (gethash key *jit-cache*)))
    (when (and *jit-deny* (gethash code *jit-deny*))
      (unless (eq entry :no-jit)
        (format *error-output* "jit-DENY ~A -> interp~%" (code-tag code))
        (setf (gethash key *jit-cache*) :no-jit))
      (return-from jit-for-code nil))
    (cond
      ((eq entry :no-jit) nil)
      ((and (consp entry) (eq (car entry) :jit))
       (values (second entry) (third entry) (fourth entry) (fifth entry)))
      (t
       (let ((n (1+ (or entry 0))))
         (setf (gethash key *jit-cache*) n)
         (when (>= n *jit-threshold*)
           (multiple-value-bind (run-chunk extra aoff alen)
               (if *inproc-jit* (try-build-jit-inproc code) (try-build-jit code))
             (cond
               (run-chunk
                (incf (getf *jit-stats* :codes-jit))
                ;; aoff/alen present only on the inproc/arena path (#259); they
                ;; pin this chunk while it runs so a nested JIT can't evict it.
                (when (and *jit-max-pc*
                           (or (null *jit-max-pc-codelen*)
                               (= (length code) *jit-max-pc-codelen*)))
                  (flet ((live () (loop for pc below (mem-aref extra :uint64 0)
                                        count (/= 0 (mem-aref extra :uint64 (1+ pc))))))
                    (let ((n (live)))
                      (setf extra (manifest-blinded extra *jit-max-pc*))
                      (format *error-output* "~&[jit-blind] code=~D bytes entries=~D blinded>=~D kept=~D~%"
                              (length code) n *jit-max-pc* (live)))))
                (setf (gethash key *jit-cache*)
                      (list :jit run-chunk extra aoff alen))
                (values run-chunk extra aoff alen))
               (t
                (incf (getf *jit-stats* :codes-no-jit))
                (format *error-output* "jit-fallback ~A | ~A~%"
                        (code-tag code) extra)
                (setf (gethash key *jit-cache*) :no-jit)
                nil)))))))))

(defstartup *jit-fuel*
  (let ((v (sb-ext:posix-getenv "EITA_JIT_FUEL"))) (and v (parse-integer v)))
  "Diagnosis: cap the chunk-dispatch fuel so only the first N chunk transitions run
   in the JIT; the host then finishes the frame on the interp. Binary searching N
   localises a JIT/interp divergence to one chunk IN EXECUTION ORDER (the pc is
   logged when the fuel runs out), which pc-space blinding cannot do.")

(defstartup *jit-fuel-codelen*
  (let ((v (sb-ext:posix-getenv "EITA_JIT_FUEL_CODELEN"))) (and v (parse-integer v)))
  "Restrict *jit-fuel* to frames running a code of exactly this byte length.")

(defun run-jit-frame (state run-chunk entries &optional (codelen 0))
  "Chunk dispatch via the emitted `_eita_execute_program` (the native
   binding of IR.executeProgram — no Lisp re-encoding of the loop).
   rc=1 is a manifest miss: every host-visible pc (chunk 0, JUMPDESTs,
   post-JUMPI/post-CALL fallthroughs) has an entry, so a miss means an
   interp-only path — finish the frame there (counted; nonzero misses
   in the summary mean a dispatch gap to chase). rc=2 is the spec's
   transition-fuel .outOfGas: unreachable for fuel = gas_left + 1
   (every chunk transition charges >= 1 gas), so it is logged loudly."
  (let ((rc (%run-program state entries run-chunk
                          (if (and *jit-fuel*
                                   (or (null *jit-fuel-codelen*)
                                       (= codelen *jit-fuel-codelen*)))
                              (min *jit-fuel* (1+ (mem-ref state :uint64 8)))
                              (1+ (mem-ref state :uint64 8))))))
    ;; Gas is a u64 everywhere below this seam, so an unchecked subtraction in a
    ;; handler or in the JIT's chunk pre-charge bookkeeping does not halt the
    ;; frame — it wraps gas_left just under 2^64 and the frame runs on. The only
    ;; symptom used to be a bare CFFI TYPE-ERROR from a callback trampoline,
    ;; naming neither the frame nor the op (the second JIT bug, retakeRem). One
    ;; compare per JIT frame names the frame instead.
    (let ((g (mem-ref state :uint64 8)))
      (when (>= g (ash 1 63))
        (error "JIT chunk left gas_left=~D (= ~D - 2^64) exit-pc=~D codelen=~D depth=~A rc=~A"
               g (- g (ash 1 64)) (mem-ref state :uint64 0) codelen *call-depth* rc)))
    (unless (zerop rc)
      (when (= rc 2)
        (format *error-output* "jit-fuel-exhausted pc=~D~%"
                (mem-ref state :uint64 0)))
      (when (and *jit-fuel* (= rc 2))
        (format *error-output* "[jit-fuel] code=~D stopped at pc=~D gas=~D~%"
                codelen (mem-ref state :uint64 0) (mem-ref state :uint64 8)))
      (when (= rc 1)
        ;; a dispatch gap to chase: the pc the chunk handed back has no entry
        (format *error-output* "jit-manifest-miss pc=~D codelen=~D gas=~D depth=~A~%"
                (mem-ref state :uint64 0) codelen (mem-ref state :uint64 8) *call-depth*))
      (incf (getf *jit-stats* :manifest-misses))
      (eita-run state))))
