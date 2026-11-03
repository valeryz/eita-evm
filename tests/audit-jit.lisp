;;;; audit-jit.lisp — differential audit of the per-chunk JIT tier (Phase 6a).
;;;;
;;;; For each corpus program: emit the per-chunk image with `emitJIT bin` (ARM64 or
;;;; x86-64, the host's), load it into the code arena with the engine's own in-process
;;;; loader (eita.evm::load-jit-blob, the path the replay's JIT tier runs), then run
;;;; the JIT chunk-dispatch loop and the interp tier (`eita_run`) on identical
;;;; EvmStates and compare the full post-states (pc, gas, stack, memory,
;;;; output, halt/revert flags, journal length).
;;;;
;;;; The interp tier is already audited against the Form.interp fixtures
;;;; (audit-native.lisp), so agreement here transfers that audit to the
;;;; JIT tier. Programs that fault (OOG, invalid jump, underflow) are
;;;; corpus members too: both tiers must fault identically.
;;;;
;;;; Run: (eita.test:run-all :only '("audit-jit")), or (asdf:test-system "eita") for all suites.
;;;; Prereqs: lake build emitJIT; libeita up to date.

(defpackage #:eita.test.audit-jit (:use #:cl #:cffi))
(in-package :eita.test.audit-jit)

(load (merge-pathnames "audit-lib.lisp" *load-truename*))

;; The replay's dispatch-table builder (Lean-emitted spec-dispatch-table): host.lisp alone,
;; its references into the replay unresolved and never run. Tables are leaked: audit only.
(defcfun ("eita_run" eita-run) :void (state :pointer))
(defcfun ("eita_execute_program" %run-program) :uint64
  (state :pointer) (entries :pointer) (run-chunk :pointer) (fuel :uint64))

(defparameter *emit-jit* (eita.native:emit-jit-path))

(defun build-jit-image (name hex)
  "Emit the per-chunk image blob for HEX (Cancun, fork ord 16) and load it into the code
   arena; return (values run-chunk dispatch-table)."
  (let ((blob (format nil "/tmp/eita-jit-~A-~D.blob" name (sb-posix:getpid))))
    (let ((p (sb-ext:run-program *emit-jit* (list "bin" hex "16" blob)
                                 :output *standard-output* :error *standard-output*
                                 :environment (eita.evm::emit-server-environment))))
      (unless (zerop (sb-ext:process-exit-code p))
        (error "emitJIT failed for ~A" name)))
    (unwind-protect
         (multiple-value-bind (run-chunk table) (eita.evm::load-jit-blob blob (cons :audit-jit name))
           (unless run-chunk (error "loading the JIT image for ~A: ~A" name table))
           (values run-chunk table))
      (ignore-errors (delete-file blob)))))

(defun run-jit (state run-chunk table &optional (max-chunks 100000))
  "Dispatch via the emitted _eita_execute_program loop (the native binding of
   IR.executeProgram). rc=1 (manifest miss) and rc=2 (fuel) are hard errors here — the
   audit corpus must be fully covered."
  (let ((rc (%run-program state table run-chunk max-chunks)))
    (case rc
      (0 nil)
      (1 (error "no JIT chunk at pc=~D" (mem-ref state :uint64 +pc-offset+)))
      (2 (error "JIT fuel exhausted at pc=~D" (mem-ref state :uint64 +pc-offset+)))
      (t (error "eita_execute_program returned ~D" rc)))))

(defun full-snapshot (state)
  "Everything observable: lib snapshot (pc/gas/stack/journal-len) plus
   mp, memory bytes, halt/revert flags, and the output slice."
  (let* ((msize    (mem-ref state :uint64 +memory-size-offset+))
         (mptr     (mem-ref state :pointer +memory-offset+))
         (out-ptr  (mem-ref state :pointer +output-offset+))
         (out-size (mem-ref state :uint64 +output-size-offset+)))
    (append (snapshot-native-state state)
            (list :mp (mem-ref state :uint64 +mp-offset+)
                  :memory-size msize
                  :halted (mem-ref state :uint8 +halted-offset+)
                  :reverted (mem-ref state :uint8 +reverted-offset+)
                  :memory (loop for i from 0 below msize
                                collect (mem-aref mptr :uint8 i))
                  :output-size out-size
                  :output (unless (null-pointer-p out-ptr)
                            (loop for i from 0 below out-size
                                  collect (mem-aref out-ptr :uint8 i)))))))

(defparameter *failures* 0)

(defun exceptional-halt-p (snap)
  (and (= 1 (getf snap :halted))
       (= 1 (getf snap :reverted))
       (zerop (getf snap :gas-left))))

(defun snapshots-match (a b)
  "Full post-state equality, EXCEPT when both tiers halted
   exceptionally (halted=1, reverted=1, gas=0): the JIT's chunk-head
   pre-charge moves mid-chunk OOG to the head, so pc/stack/journal at
   death legitimately differ. Per-opcode gas accounting is explicitly
   out of scope; the flattened observables (the three flags + empty
   output, which is all the host acts on) must still agree."
  (if (and (exceptional-halt-p a) (exceptional-halt-p b))
      (and (zerop (getf a :output-size))
           (zerop (getf b :output-size)))
      (equal a b)))

(defun audit-jit-program (name hex gas &key calldata cache)
  (multiple-value-bind (run-chunk table) (build-jit-image name hex)
    (let ((pre (list :code-hex hex :gas-left gas
                     :calldata-hex calldata :cache cache)))
      (let ((s-interp (build-native-state pre))
            (s-jit    (build-native-state pre)))
        (eita-run s-interp)
        (run-jit s-jit run-chunk table)
        (let ((a (full-snapshot s-interp))
              (b (full-snapshot s-jit)))
          (if (snapshots-match a b)
              (format t "  PASS  ~A~%" name)
              (progn
                (incf *failures*)
                (format t "  FAIL  ~A~%" name)
                (format t "        interp: ~A~%" a)
                (format t "        jit:    ~A~%" b))))))
    (setf *aux-buffers* nil)))

;; --- Program corpus ---
;; Only ops the IR compiler decodes (compileLoop's Frontier+staged set)
;; AND that have native handlers. Post-Frontier ops the IR doesn't
;; stage yet (SHL/SHR/SAR, RETURNDATA*, CHAINID/BASEFEE, TLOAD/TSTORE/
;; MCOPY/PUSH0, REVERT/DELEGATECALL/STATICCALL/CREATE2) are excluded —
;; see Evm/IR/Execute.lean: "stay errors until their forks land".
;; Semantics need not be predicted — both tiers run the same program;
;; validity (no unintended underflow) keeps the paths interesting.

(defparameter *corpus*
  ;; (name hex gas &rest keys)
  `(("arith"
     ;; PUSH1 5; PUSH1 7; ADD; PUSH1 3; MUL; PUSH1 2; SWAP1; SUB; STOP
     "60056007016003026002900300" 100000)
    ("push-widths"
     ;; PUSH2/3/4/5/8/32 then STOP — exercises per-site pc advance by 1+n
     "61ffff6201020363deadbeef6401020304ff67ffeeddccbbaa99887f112233445566778899aabbccddeeff00112233445566778899aabbccddeeff0000" 100000)
    ("dup-swap"
     ;; PUSH 1..4; DUP1; DUP3; SWAP1; SWAP3; ADD x3; STOP
     "60016002600360048082909201010100" 100000)
    ("memory"
     ;; PUSH32 pat; MSTORE@0; MLOAD@0; MSTORE8@1; MSIZE; POP; RETURN 32B
     "7f00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff600052600051600153595060206000f3" 100000)
    ("keccak"
     ;; PUSH32 pat; MSTORE@0; KECCAK256(0,32); STOP
     "7f00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff600052602060002000" 100000)
    ("storage"
     ;; SLOAD(5); SSTORE(5,0x42); STOP
     "600554604260055500" 100000
     :cache ((0 5 1234)))
    ("loop"
     ;; counter=3; JUMPDEST; counter-1; DUP; JUMPI back — repeated dispatch
     "60035b600190038060025700" 100000)
    ("env"
     ;; ADDRESS ORIGIN CALLER COINBASE CALLVALUE GASPRICE TIMESTAMP
     ;; NUMBER GASLIMIT PC GAS MSIZE CALLDATASIZE CODESIZE STOP
     "30323341343a424345585a59363800" 100000)
    ("calldata"
     ;; CALLDATALOAD(0); CALLDATACOPY(0,4,16); STOP
     "6000356010600460003700" 100000
     :calldata "112233445566778899aabbccddeeff00112233")
    ("codecopy"
     ;; CODECOPY(0,0,16); STOP
     "6010600060003900" 100000)
    ("cmp-bitwise"
     ;; LT GT EQ AND OR XOR SLT SGT ISZERO NOT chain; STOP
     "6005600710600311600114600216600317600118600012600513151900" 100000)
    ("exp-byte"
     ;; EXP(5,3); BYTE(31); SIGNEXTEND(0); NOT; ISZERO; STOP
     "600360050a601f1a60000b191500" 100000)
    ("log"
     ;; PUSH32 pat; MSTORE@0; LOG1(topic 0xaa, mem[0..32]); STOP
     "7f00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff60005260aa60206000a100" 100000)
    ("invalid-op"
     ;; PUSH 1..3; INVALID: exceptional halt, both tiers consume all gas
     "600160026003fe" 100000)
    ("end-of-code"
     ;; PUSH1 5; PUSH1 7; ADD — no STOP byte: implicit endOfCode
     "6005600701" 100000)
    ("invalid-jump"
     ;; JUMP to a non-JUMPDEST byte: both tiers must fault identically
     "60035600" 100000)
    ("oog"
     ;; arith program with a 10-gas budget: dies mid-chunk
     "60056007016003026002900300" 10)
    ("underflow"
     ;; ADD on an empty stack
     "0100" 100000)
    ("fold-gas"
     ;; PUSH1 1; PUSH1 2; ADD; GAS; PUSH1 3; PUSH1 2; EXP; GAS; STOP —
     ;; first GAS's rem must include the later FOLDED exp's dynamic
     ;; gas (the JIT pre-charges it at the chunk head)
     "60016002015a600360020a5a00" 100000)
    ("fold-overflow"
     ;; 1025 PUSH1s: the interp faults on the push that crosses 1024;
     ;; the folder must fault via the flush peak-depth check
     ,(format nil "~v@{~A~:*~}00" 1025 "6001") 1000000)
    ;; --- Stage 6d: symbolic regions (dynamic values, issue #11 st. 2) ---
    ("sym-arith"
     ;; a=CDL(0); b=CDL(32); DUP2 DUP2 ADD SWAP2 MUL SUB; STOP —
     ;; symbolic dup/swap (incl. manufactured pops), inline add/sub,
     ;; helper mul, all materialized at one flush
     "60003560203581810191020300" 100000
     :calldata "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff0000000000000000000000000000000000000000000000000000000000000007")
    ("sym-divmod"
     ;; a=CDL(0); DUP1 DUP1 DUP1; PUSH1 7; SWAP1; DIV; MOD; ADDMOD —
     ;; DAG sharing (a referenced 4x = one slot), div/mod helpers,
     ;; ternary addmod helper with a manufactured third operand
     "60003580808060079004060800" 100000
     :calldata "00000000000000000000000000000000000000000000000000000000deadbeef")
    ("sym-shift"
     ;; a=CDL(0); DUP1; PUSH1 2; SHL; SWAP1; PUSH1 3; SHR; XOR;
     ;; PUSH1 0; BYTE; ISZERO; STOP — shl/shr/byte helpers with
     ;; constant operands folded into the symbolic DAG
     "6000358060021b9060031c1860001a1500" 100000
     :calldata "8000000000000000000000000000000000000000000000000000000000000001")
    ("sym-cmp-adversarial"
     ;; SLT SGT LT GT EQ over calldata words that differ only in the
     ;; lowest limb, sign bits set: only borrow/signed condition codes
     ;; survive the chained sbcs — Z-dependent codes would pass random
     ;; fixtures and fail exactly this shape
     "6000356020351260003560203513016000356020351001600035602035110160003560203514011500" 100000
     :calldata "80000000000000000000000000000000000000000000000000000000000000018000000000000000000000000000000000000000000000000000000000000002")
    ("sym-mixed-fold"
     ;; a=CDL(0); PUSH1 5; PUSH1 7; ADD; MUL; PUSH1 3; ADD — the const
     ;; prefix (5+7) folds via execOp atop the symbolic suffix, then
     ;; feeds the symbolic mul/add
     "60003560056007010260030100" 100000
     :calldata "0000000000000000000000000000000000000000000000000000000000000123")
    ("sym-swap-deep"
     ;; a=CDL(0); DUP1 x5; SWAP4; SUB x5; STOP — popN across the
     ;; explicit prefix boundary
     "600035808080808093030303030300" 100000
     :calldata "00000000000000000000000000000000000000000000000000000000000000ff")
    ("sym-underflow"
     ;; CDL leaves depth 1; DUP3 needs 3 — the interp faults in the
     ;; dup handler, the region via its entry `need` check
     "6000358200" 100000
     :calldata "0000000000000000000000000000000000000000000000000000000000000001")
    ("sym-overflow"
     ;; CDL then 1024 DUP1s: depth crosses 1024 mid-region; the
     ;; region's peak-net check must fault like the interp's dup
     ;; overflow guard
     ,(format nil "600035~v@{~A~:*~}00" 1024 "80") 1000000
     :calldata "0000000000000000000000000000000000000000000000000000000000000001")
    ;; --- Stage 6e: constant-offset memory promotion (issue #11 st. 3) ---
    ("mem-promote-roundtrip"
     ;; v=CDL(0); MSTORE@0 (absorbed, symbolic value); MLOAD@0 is the
     ;; barrier: the dirty word must hit memory before the mload
     ;; handler reads it back
     "60003560005260005100" 100000
     :calldata "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff")
    ("mem-promote-idiom"
     ;; the Solidity mapping-slot shape: key=CDL(0)→0x00, slot 7→0x20,
     ;; KECCAK256(0,64) — both stores buffer in ONE region; the keccak
     ;; barrier commits them (merged memexp + mp) before hashing
     "6000356000526007602052604060002000" 100000
     :calldata "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff")
    ("mem-promote-mstore8"
     ;; v=CDL(0); MSTORE8@5 (low byte of v); MLOAD@0 reads it back —
     ;; the byte-write path and its 1-byte expansion end
     "60003560055360005100" 100000
     :calldata "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff")
    ("mem-promote-alias"
     ;; MSTORE@0 of a const, MSTORE@0x10 of CDL(0) overlapping the
     ;; first word, then MLOAD@0 + MLOAD@0x10: program-order replay
     ;; at the flush IS the alias handling
     "60aa60005260003560105260005160105100" 100000
     :calldata "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff")
    ("mem-promote-msize"
     ;; MSTORE@0x21 then MSIZE: the barrier flush must land the
     ;; merged memexp (aligned memory_size) and raw-end mp before
     ;; the msize handler reads them
     "60016021525900" 100000)
    ("mem-promote-dynamic"
     ;; value+offset pushed, then JUMP: the jumpdest chunk's MSTORE
     ;; sees a stackAt offset (entry stack, not a const) — it must
     ;; degrade to the handler site, no promotion
     "60003560206008565b5200" 100000
     :calldata "00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff")
    ("mem-promote-oog"
     ;; MSTORE@0x10000: past the 64 KiB host buffer cap — the interp
     ;; OOGs in the handler's memExpandInto, the region at its flush
     ;; memexp cap check; the flattened halts must agree
     "6001620100005200" 100000)
    ("invalid-undefined-byte"
     ;; PUSH1 1; ADD-junk 0x0c (undefined in every fork): compiles to
     ;; the .invalid terminator instead of a whole-code CompileError —
     ;; exceptional halt, all gas consumed, must match the interp
     "60010c00" 100000)
    ("invalid-undefined-after-effects"
     ;; MSTORE runs (memory + gas effects) before the undefined byte
     ;; 0xba halts the frame — flattened-halt contract: gas=0, halted,
     ;; reverted agree even though prefix effects are unobservable
     "6001600052ba00" 100000)))

(format t "~%=== JIT (per-chunk) differential audit ===~%")
(dolist (entry *corpus*)
  (apply #'audit-jit-program entry))
(if (zerop *failures*)
    (format t "JIT audit complete: all ~D programs match.~%" (length *corpus*))
    (progn
      (format t "JIT audit: ~D/~D programs MISMATCHED.~%"
              *failures* (length *corpus*))
      (eita.test:finish :code 1)))
