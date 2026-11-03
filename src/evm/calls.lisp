;;;; evm/calls.lisp — the CALL / CREATE / SELFDESTRUCT / LOG callbacks around the derived effects,
;;;; tracing, the callback vtable.

(in-package #:eita.evm)

(defstartup *trace-frames*
  (and (sb-ext:posix-getenv "EITA_TRACE_FRAMES") t)
  "When non-nil, cb-call logs each sub-frame's (depth, kind, to, forwarded
   gas, gasUsed) so the per-frame gas can be diffed against a geth callTracer.")

;; #250: a sub-call's RETURN output is copied into a malloc'd `out-copy` buffer
;; (cb-call's `result.output_ptr`), which the native CALL handler installs as the
;; caller frame's state->returndata (EvmState offset 96, set in AsmCore.lean:642).
;; That buffer is the ONLY thing written to offset 96, so a non-null returndata is
;; ALWAYS a malloc'd out-copy — safe to free. Nothing freed it, so every CALL that
;; returns leaked one buffer; harmless at normal call density but catastrophic in
;; the 2.28M–2.46M DoS region (millions of nested cheap calls → ~28G → swap death).
;; Lifetime: returndata is valid only until the frame's NEXT call, so we free a
;; frame's old returndata when it makes another call (cb-call entry) and when the
;; frame ends (sub-frame return in cb-call/cb-create; top frame in apply-tx). The
;; field is nulled on free and at frame setup, so a reused arena slot never holds a
;; stale (freed) pointer — no double free.
;; Debug toggle (read once): EITA_NO_RD_FREE=1 disables the #250 returndata free
;; to A/B the leak. Default: enabled.
(defstartup *rd-free-enabled* (not (sb-posix:getenv "EITA_NO_RD_FREE")))
(declaim (inline free-frame-returndata))
(defun free-frame-returndata (state)
  "Free STATE's returndata buffer (offset 96; malloc'd out-copy or null) and clear
   the (ptr,size) fields. No-op on a null state or null returndata."
  (when (and *rd-free-enabled* (not (null-pointer-p state)))
    (let ((rd (mem-ref state :pointer 96)))
      (unless (null-pointer-p rd)
        (foreign-free rd)
        (setf (mem-ref state :pointer 96) (null-pointer))
        (setf (mem-ref state :uint64 104) 0)))))

;;; --- EIP-7702 delegation (Prague / OP-Isthmus) ------------------------------
;; A delegated EOA stores the 23-byte designator 0xEF0100 || <20-byte addr> as
;; its account code. Code-INTROSPECTION opcodes (EXTCODESIZE/HASH/COPY) see the
;; designator bytes verbatim — no special-casing needed, since we store the
;; designator as the account's code. Only EXECUTION (CALL family + the top
;; frame) follows the pointer to the delegate's code, at an extra access cost.
;; *prague-delegation* is bound per-block by the OP driver when fork >= Isthmus
;; (kept independent of *fork-ord*, which stays at the Cancun native dispatch
;; ord since Prague adds no new/changed opcodes).
(defparameter *prague-delegation* nil)

(declaim (inline delegation-target))
(defun delegation-target (code)
  "EIP-7702: if CODE is a delegation designator 0xEF0100||addr (23 bytes),
   return the 20-byte delegate address; else NIL."
  (when (and (typep code 'octets) (= (length code) 23)
             (= (aref code 0) #xef) (= (aref code 1) #x01) (= (aref code 2) #x00))
    (let ((a 0))
      (declare (type octets code))
      (loop for i from 3 below 23 do (setf a (logior (ash a 8) (aref code i))))
      a)))

;;; CALL / CALLCODE / DELEGATECALL / STATICCALL — the effect is DERIVED: spec-call-effect
;;; (src/generated/host.lisp, Evm.CL.EffectCall, proved equal to every fork's call family
;;; in Evm.CL.EffectCallProof). Hand-written here: the seams it runs a child through
;;; (run-call-frame! — EffectIR `runCall` —, precompile-run! — `runPre` —, the gas plan's
;;; natives — `callPlan` —, and Arc's chain precompile, outside the theorem) and the wrapper.

(defun call-gas-plan (cold vf na deleg gas-arg avail)
  "EffectIR `callPlan`: the fork's CALL-family plan (Evm.Frontier.Vm.Call.plan) through the
   emitted natives (`_eita_call_gas*`, proved equal to the three spec plans in
   Evm.CL.ARM64.CallGasSem). Returns (values charge forward stipend)."
  (funcall (cond ((>= *fork-ord* 10) #'%call-gas)
                 ((>= *fork-ord* 3) #'%call-gas-tangerine)
                 (t #'%call-gas-frontier))
           *call-gas-plan* (logior (if cold 1 0) (if vf 2 0) (if na 4 0)) deleg gas-arg avail)
  (values (mem-aref *call-gas-plan* :uint64 0) (mem-aref *call-gas-plan* :uint64 1)
          (mem-aref *call-gas-plan* :uint64 2)))

(defun precompile-run! (addr input-ptr input-len gas)
  "EffectIR `runPre`: the fork's precompile at ADDR on the input with GAS (run-precompile, the
   seam = the spec's table). Child record: (:return gas-left output) or (:halt 0 nil)."
  (multiple-value-bind (used output) (run-precompile addr input-ptr input-len gas)
    (setf *last-sub-outcome* (if output :return :halt))
    (if output (list :return (- gas used) output) (list :halt 0 nil))))

(defun chain-precompile-call! (to kind self input-ptr input-len gas static value snap snap-facts)
  "A chain-native stateful precompile (Arc 0x1800…; EffectIR `chainCall`, outside the Ethereum
   theorem): run the chain's handler with GAS; a failure (revert/OOG) unwinds the journal to
   SNAP — including any balance moves the precompile itself journaled. Returns (values ok
   sub-used output)."
  (multiple-value-bind (sub-used output success)
      (funcall *chain-precompile-hook* to kind self input-ptr input-len gas static value)
    (unless success
      (revert-journal-to (current-arena) snap)
      (observe-revert! snap-facts))
    (setf *last-sub-outcome* (cond (success :return) ((= sub-used gas) :halt) (t :revert)))
    (values success sub-used output)))

(defun run-call-frame! (kind self to value input-ptr input-len code-addr gas)
  "EffectIR `runCall`: run CODE-ADDR's code (the target's, or EIP-7702's delegate's) as the
   CALL-family child of the current frame with GAS on the native interpreter, and absorb
   its journal into the current frame's (a later rollback, or a revert of this frame,
   unwinds it). The child's address, caller, value and static flag follow KIND (DELEGATECALL
   inherits the frame's caller and value, STATICCALL is static and value-free). Returns the
   child record (status gas-left output): :return, :revert (REVERT: its output is the revert
   data) or :halt (an exceptional halt: no output pointer); the output is a (pointer .
   length) foreign copy made before the child's memory slice is scrubbed. Empty code halts
   at once with all its gas (the interpreter is not entered). Contract: = the spec's runSub
   on Evm.Frontier.Vm.Call.child, the world as the view holds it."
  (let ((code (code-of *current-world* code-addr)))
    (when (zerop (length code))
      (setf *last-sub-outcome* :return)
      (return-from run-call-frame! (list :return gas nil)))
    (let* ((sub-code-len (length code))
           (parent-state *current-state*)
           (parent-arena (current-arena))
           (parent-mem-used (if (null-pointer-p parent-state) 0
                                (mem-ref parent-state :uint64 48)))
           (parent-cb-ctx (if (null-pointer-p parent-state) (null-pointer)
                              (mem-ref parent-state :pointer 504)))
           (parent-jcount (if (null-pointer-p parent-cb-ctx) 0
                              (mem-ref parent-cb-ctx :uint64 0)))
           (parent-jdata  (if (null-pointer-p parent-cb-ctx) *journal-arena*
                              (mem-ref parent-cb-ctx :pointer 16)))
           (sub-journal-data (inc-pointer parent-jdata (* parent-jcount 104)))
           (sub-stack-base   (* (1+ *call-depth*) +stack-bytes-per-frame+))
           (sub-memory-base  (+ *memory-arena-base* parent-mem-used)))
      (let* ((*stack-arena-base*  sub-stack-base)
             (*memory-arena-base* sub-memory-base))
        (let* ((sub-depth (1+ *call-depth*))
               (sub-state (substate-slot sub-depth))    ; arena slot, not malloc (#248)
               (sub-stack (inc-pointer *stack-arena*  *stack-arena-base*))
               (sub-mem   (inc-pointer *memory-arena* *memory-arena-base*))
               (sub-mem-cap (- +memory-arena-bytes+ *memory-arena-base*))
               (sub-arena (subarena-slot sub-depth))    ; arena slot, not malloc (#248)
               (sub-input (if (plusp input-len) (alloc-zeroed input-len) (null-pointer)))
               (saved-addr *current-address*))
          (with-frame-code (sub-state code sub-code-len)
          (when (plusp input-len)
            (%memcpy sub-input input-ptr input-len))
          (setf (mem-ref sub-state :uint64 8)   gas)
          (setf (mem-ref sub-state :pointer 32) sub-stack)
          (setf (mem-ref sub-state :pointer 40) sub-mem)
          (setf (mem-ref sub-state :uint64 56)  sub-mem-cap)
          ;; #250: fresh frame starts with no returndata (this arena slot may hold a stale
          ;; freed ptr from a prior frame at this depth).
          (setf (mem-ref sub-state :pointer 96) (null-pointer))
          (setf (mem-ref sub-state :uint64 104) 0)
          (when (plusp input-len)
            (setf (mem-ref sub-state :pointer 80) sub-input)
            (setf (mem-ref sub-state :uint64 88) input-len))
          (let* ((sub-address (if (or (= kind 1) (= kind 2)) self to))
                 (parent-staticp (if (null-pointer-p parent-state) 0
                                     (mem-ref parent-state :uint8 130)))
                 (sub-staticp (if (or (= kind 3) (plusp parent-staticp)) 1 0))
                 (sub-caller (if (and (= kind 2) (not (null-pointer-p parent-state)))
                                 (u256-read (inc-pointer parent-state 208))
                                 self))
                 (sub-value (cond ((= kind 3) 0)
                                  ((= kind 2)
                                   (if (null-pointer-p parent-state) 0
                                       (u256-read (inc-pointer parent-state 240))))
                                  (t value))))
            (setf (mem-ref sub-state :uint8 130) sub-staticp)
            (u256-write (inc-pointer sub-state 144) sub-address)
            (u256-write (inc-pointer sub-state 208) sub-caller)
            (u256-write (inc-pointer sub-state 240) sub-value)
            (populate-sub-env sub-state)
            (setf (mem-ref sub-arena :pointer 16) sub-journal-data)
            (setf (mem-ref sub-arena :pointer 64) *tx-state*)
            (setf (mem-ref sub-state :pointer 496) (callbacks-vtable))
            (setf (mem-ref sub-state :pointer 504) sub-arena)
            (setf *current-address* sub-address)
            (setf *current-state*   sub-state)
            (incf *call-depth*)
            (unwind-protect (run-frame sub-state code)
              (decf *call-depth*)
              (setf *current-state*   parent-state)
              (setf *current-address* saved-addr)))
          ;; Copy the child's output BEFORE scrubbing its memory slice (output_ptr points
          ;; into it). The interpreter raises `reverted` for REVERT and for every
          ;; exceptional halt; only REVERT writes the output pointer (offset 112, zeroed per
          ;; frame), so a NULL pointer is an exceptional halt (stop #16: calling those
          ;; :revert made Arc CallFrom refund its retained 1/64 after an OOG child).
          (let* ((halted   (not (zerop (mem-ref sub-state :uint8 128))))
                 (reverted (not (zerop (mem-ref sub-state :uint8 129))))
                 (output-ptr (mem-ref sub-state :pointer 112))
                 (output-len (mem-ref sub-state :uint64 120))
                 (gas-left (mem-ref sub-state :uint64 8))
                 (status (cond ((and halted (not reverted)) :return)
                               ((and reverted (not (null-pointer-p output-ptr))) :revert)
                               (t :halt)))
                 (output (when (and (not (eq status :halt)) (plusp output-len))
                           (let ((out-copy (alloc-zeroed output-len)))   ; escapes -> disjoint buffer
                             (%memcpy out-copy output-ptr output-len)
                             (cons out-copy output-len)))))
            (setf *last-sub-outcome* status)
            ;; Absorb the child's journal into this frame's scope: its entries sit
            ;; contiguously after ours, so bumping our count claims them (the term's
            ;; rollback, or a revert of this frame, unwinds them).
            (incf (mem-ref parent-arena :uint64 0) (mem-ref sub-arena :uint64 0))
            (let ((used (mem-ref sub-state :uint64 48)))
              (when (plusp used)
                (zero-bytes *memory-arena* *memory-arena-base* used)))
            (unless (null-pointer-p sub-input) (foreign-free sub-input))
            ;; #250: the child ended — free the returndata left by the LAST call it made.
            (free-frame-returndata sub-state)
            (list status (if (eq status :halt) 0 gas-left) output))))))))

(defcallback cb-call :int
    ((ctx :pointer) (params :pointer) (result :pointer))
  "The native handler popped the operands, raised EIP-214, charged the memory expansion of
   both ranges and handed over the target, value, input and requested gas (saturated at
   2^64-1); the gas left is the frame's. The wrapper resolves EIP-7702's designator; the
   rest — warm-ups, the plan, out of gas, the fail-fast, the child's world, the precompile
   or child frame, its end, EIP-161's touch and the RIPEMD-160 exemption — is the
   Lean-emitted spec-call-effect. Its return data becomes the frame's returndata (the
   handler copies it into memory and pushes the flag)."
  (declare (ignore ctx))
  ;; #250: this CALL replaces the caller frame's returndata — free the previous one.
  (free-frame-returndata *current-state*)
  (let* ((kind (mem-ref params :int 0))
         ;; CALL masks its target to the low 160 bits; mask defensively so a divergent path
         ;; can never hand the lazy-RPC fault a 256-bit "address".
         (to (read-addr (inc-pointer params 8)))
         (value (u256-read (inc-pointer params 40)))
         (input-ptr (mem-ref params :pointer 72))
         (input-len (mem-ref params :uint64 80))
         (gas-arg (mem-ref params :uint64 88))
         (deleg (and *prague-delegation*
                     (progn (fault-account! to) (delegation-target (code-of *current-world* to)))))
         (avail (if (null-pointer-p *current-state*)
                    gas-arg
                    ;; A wrapped parent pool would otherwise be laundered into a
                    ;; plausible-looking forward.
                    (let ((g (mem-ref *current-state* :uint64 8)))
                      (when (>= g (ash 1 63))
                        (error "cb-call: PARENT gas already wrapped ~D (= ~D - 2^64) depth=~A kind=~D to=~40,'0x requested=~D"
                               g (- g (ash 1 64)) *call-depth* kind to gas-arg))
                      g)))
         (static (or (= kind 3)
                     (and (not (null-pointer-p *current-state*))
                          (plusp (mem-ref *current-state* :uint8 130))))))
    (multiple-value-bind (used out rd)
        (spec-call-effect kind *current-address* to deleg (and deleg t) value gas-arg avail
                          (>= *call-depth* +max-call-depth+) input-ptr input-len static)
      (setf (mem-ref result :int 0) (if (zerop out) 0 1)
            ;; out of gas: charge + an uncapped pre-EIP-150 forward can exceed u64; any value
            ;; above the pool faults the native deduction equally.
            (mem-ref result :uint64 24) (min used #xFFFFFFFFFFFFFFFF))
      (cond ((consp rd)                                  ; a child frame's foreign copy
             (setf (mem-ref result :pointer 8) (car rd)
                   (mem-ref result :uint64 16) (cdr rd)))
            ((and rd (plusp (length rd)))                ; a precompile's or a chain's bytes
             (let ((buf (foreign-alloc :uint8 :count (length rd))))
               (bytes->foreign buf rd (length rd))
               (setf (mem-ref result :pointer 8) buf
                     (mem-ref result :uint64 16) (length rd))))
            (t (setf (mem-ref result :pointer 8) (null-pointer)
                     (mem-ref result :uint64 16) 0)))
      0)))

(defun derive-create2-address (sender salt init-code-hash)
  "EIP-1014: keccak256(0xff || sender_20 || salt_32 || keccak256(init))[12..32]."
  (let* ((bytes (make-array 85 :element-type '(unsigned-byte 8))))
    (setf (aref bytes 0) #xff)
    (let ((sb (addr-to-bytes sender)))
      (loop for i from 0 below 20 do (setf (aref bytes (1+ i)) (elt sb i))))
    (loop for i from 0 below 32 do
      (setf (aref bytes (+ 21 i)) (logand #xff (ash salt (* -8 (- 31 i))))))
    (loop for i from 0 below 32 do
      (setf (aref bytes (+ 53 i)) (aref init-code-hash i)))
    (let ((h (keccak256-bytes bytes)) (a 0))
      (loop for i from 12 to 31 do (setf a (logior (ash a 8) (aref h i))))
      a)))

;;; EELS destroy_storage at a creation (EIP-7610 is not applied: execution-specs #3417 dropped
;;; the storage leg of the collision rule, #3508 made every fork's tracker honour the wipe).
(defun storage-wipe-journaled! (addr)
  "EffectIR `wipeStorage`: every nonzero slot of ADDR, in RAM or in the cold tier, set to 0
   through the storage view with one journal entry each (type 0), so a failed creation
   restores them and observers and the read stream see each write. Contract: = the
   spec's `State.destroyStorage` on the view."
  (let ((w *current-world*) (keys '()))
    (let ((tbl (with-acct (tb a) w addr (acct-storage tb a))))
      (when tbl (slots-map (lambda (k v) (unless (zerop v) (push k keys))) tbl)))
    (when *cold-storage-map-hook*
      (funcall *cold-storage-map-hook* addr (lambda (k v) (unless (zerop v) (push k keys)))))
    (dolist (k keys)
      (fault-slot! addr k)
      (let ((v (storage-of w addr k)))
        (unless (zerop v)
          (journal-push! (current-arena) 0 addr k v)
          (setf (storage-of w addr k) 0))))))

;;; CREATE / CREATE2 — the effect is DERIVED: spec-create-effect (src/generated/host.lisp,
;;; Evm.CL.EffectCreate, proved equal to every fork's CREATE in Evm.CL.EffectCreateProof).
;;; Hand-written here: the seam it runs a child through (run-init-frame!, EffectIR `runChild`)
;;; and the child record's accessors.

(defun run-init-frame! (sender new-addr value init-code fwd)
  "EffectIR `runChild`: run INIT-CODE as NEW-ADDR's init frame (caller SENDER, value VALUE,
   FWD gas) on the native interpreter, one frame below the current one, and absorb its
   journal into the current frame's (so a later rollback, or a revert of this frame,
   unwinds it). Returns the child record (status gas-left output): status :return,
   :revert (the REVERT opcode: its output is the REVERT data) or :halt (an exceptional
   halt: the interpreter raises `reverted` and writes no output pointer); output is copied
   out of the child's memory slice before the slice is scrubbed. Contract: = the spec's
   runSub on the child the spec builds (Evm.Frontier.Vm.Create.child), the world as the
   view holds it."
  (let* ((input-len (length init-code))
         (parent-state *current-state*)
         (parent-arena (current-arena))
         (parent-mem-used (if (null-pointer-p parent-state) 0
                              (mem-ref parent-state :uint64 48)))
         (parent-cb-ctx (if (null-pointer-p parent-state) (null-pointer)
                            (mem-ref parent-state :pointer 504)))
         (parent-jcount (if (null-pointer-p parent-cb-ctx) 0
                            (mem-ref parent-cb-ctx :uint64 0)))
         (parent-jdata  (if (null-pointer-p parent-cb-ctx) *journal-arena*
                            (mem-ref parent-cb-ctx :pointer 16)))
         (sub-journal-data (inc-pointer parent-jdata (* parent-jcount 104)))
         (sub-stack-base  (* (1+ *call-depth*) +stack-bytes-per-frame+))
         (sub-memory-base (+ *memory-arena-base* parent-mem-used)))
    (let* ((*stack-arena-base*  sub-stack-base)
           (*memory-arena-base* sub-memory-base))
      (let* ((sub-depth (1+ *call-depth*))
             (sub-state (substate-slot sub-depth))    ; arena slot, not malloc (#248)
             (sub-stack (inc-pointer *stack-arena*  *stack-arena-base*))
             (sub-mem   (inc-pointer *memory-arena* *memory-arena-base*))
             (sub-mem-cap (- +memory-arena-bytes+ *memory-arena-base*))
             (sub-arena (subarena-slot sub-depth))    ; arena slot, not malloc (#248)
             (saved-addr *current-address*))
        (with-frame-code (sub-state init-code input-len)
        (setf (mem-ref sub-state :uint64 8)   fwd)
        (setf (mem-ref sub-state :pointer 32) sub-stack)
        (setf (mem-ref sub-state :pointer 40) sub-mem)
        (setf (mem-ref sub-state :uint64 56)  sub-mem-cap)
        ;; #250: fresh init frame — clear any stale returndata in this arena slot.
        (setf (mem-ref sub-state :pointer 96) (null-pointer))
        (setf (mem-ref sub-state :uint64 104) 0)
        (u256-write (inc-pointer sub-state 144) new-addr)
        (u256-write (inc-pointer sub-state 208) sender)
        (u256-write (inc-pointer sub-state 240) value)
        (populate-sub-env sub-state)
        (setf (mem-ref sub-arena :pointer 16) sub-journal-data)
        (setf (mem-ref sub-arena :pointer 64) *tx-state*)
        (setf (mem-ref sub-state :pointer 496) (callbacks-vtable))
        (setf (mem-ref sub-state :pointer 504) sub-arena)
        (setf *current-address* new-addr)
        (setf *current-state*   sub-state)
        (incf *call-depth*)
        ;; Initcode runs once per deployment — never hot, stays interp.
        (unwind-protect (eita-run sub-state)
          (decf *call-depth*)
          (setf *current-state*   parent-state)
          (setf *current-address* saved-addr))
        ;; Copy the output BEFORE scrubbing the sub-frame's memory slice: it points into it.
        (let* ((reverted (not (zerop (mem-ref sub-state :uint8 129))))
               (out-ptr  (mem-ref sub-state :pointer 112))
               (out-size (mem-ref sub-state :uint64 120))
               (gas-left (mem-ref sub-state :uint64 8))
               (status (cond ((not reverted) :return)
                             ((null-pointer-p out-ptr) :halt)
                             (t :revert)))
               (output (if (and (not (eq status :halt)) (plusp out-size))
                           (let ((bytes (make-array out-size :element-type '(unsigned-byte 8))))
                             (loop for i below out-size do
                               (setf (aref bytes i) (mem-aref out-ptr :uint8 i)))
                             bytes)
                           #())))
          ;; Absorb the init frame's journal into the parent scope (the sub's entries sit
          ;; contiguously after the parent's), so a rollback — or a later revert of the
          ;; PARENT frame — unwinds the init code's effects too.
          (incf (mem-ref parent-arena :uint64 0) (mem-ref sub-arena :uint64 0))
          (let ((used (mem-ref sub-state :uint64 48)))
            (when (plusp used)
              (zero-bytes *memory-arena* *memory-arena-base* used)))
          ;; #250: the init frame ended — free the returndata left by the last call its
          ;; constructor made (intermediate ones were freed at each cb-call entry).
          (free-frame-returndata sub-state)
          (list status gas-left output)))))))

(declaim (inline child-status child-gas child-output))
(defun child-status (c) (first c))
(defun child-gas (c) (second c))
(defun child-output (c) (third c))
(defun child-output-ef-p (c)
  "EIP-3541: the child's output starts with 0xEF."
  (let ((o (third c))) (and (plusp (length o)) (= #xef (aref o 0)))))
(defun child-frame-status (c out)
  "The observed frame status of a CREATE's init frame: :return when the creation
   succeeded, :revert for a REVERTed init frame, :halt otherwise (an exceptional halt, or a
   code deposit that failed the creation)."
  (cond ((/= out 0) :return)
        ((and c (eq (child-status c) :revert)) :revert)
        (t :halt)))

(defcallback cb-create :int
    ((ctx :pointer) (params :pointer) (result :pointer))
  "The native handler popped the operands, raised EIP-214, charged the init range's memory
   expansion and handed over the init code and the gas left. The wrapper derives the
   address (from the creator's nonce, or EIP-1014's salt and init-code hash), the opcode's
   charge (spec-create-gas) and EIP-3860's cap (spec-create-initcode-oversize); the rest —
   fail-fast, warm-up, collision, nonce bump, the child's world, the init frame, the code
   deposit, every rollback — is the Lean-emitted spec-create-effect. Its return data (a
   REVERTing init frame's output) becomes the frame's returndata; EELS generic_create
   clears it otherwise."
  (declare (ignore ctx))
  (free-frame-returndata *current-state*)
  (let* ((kind      (mem-ref params :int 0))
         (value     (u256-read (inc-pointer params 40)))
         (input-ptr (mem-ref params :pointer 72))
         (input-len (mem-ref params :uint64 80))
         (gas       (mem-ref params :uint64 88))
         (salt      (u256-read (inc-pointer params 96)))
         (sender    *current-address*)
         (init-code (foreign->bytes input-ptr input-len))
         (new-addr  (if (= kind 5)   ; CREATE2
                        (derive-create2-address sender salt (keccak256-bytes init-code))
                        (derive-create-address sender (nonce-of *current-world* sender)))))
    (multiple-value-bind (used out rd)
        (spec-create-effect sender new-addr value gas
                            (spec-create-gas *fork-ord* (if (= kind 5) 1 0) input-len)
                            (>= *call-depth* +max-call-depth+)
                            (< 0 (spec-create-initcode-oversize *fork-ord* input-len))
                            kind init-code)
      (setf (mem-ref result :int 0) (if (zerop out) 0 1)
            (mem-ref result :uint64 24) used)
      (u256-write (inc-pointer result 32) out)
      (if (and rd (plusp (length rd)))
          (let ((buf (foreign-alloc :uint8 :count (length rd))))
            (bytes->foreign buf rd (length rd))
            (setf (mem-ref result :pointer 8) buf
                  (mem-ref result :uint64 16) (length rd)))
          (setf (mem-ref result :pointer 8) (null-pointer)
                (mem-ref result :uint64 16) 0))
      0)))

(defvar *chain-selfdestruct-hook* nil
  "Chain override consulted by cb-selfdestruct BEFORE any state effect:
   (lambda (originator beneficiary balance)) → NIL to proceed, or
   (values :revert output-bytes) to make the frame REVERT with that output and
   its remaining gas (Arc's arc_network_selfdestruct: zero-address / self-target /
   blocklist / destructed-target rules, evm.rs opcode.rs). The base SELFDESTRUCT
   gas is already charged by the native body; nothing else is charged.")

(defparameter *frame-revert-buffers* (make-hash-table :test 'equalp)
  "Revert-output bytes → foreign buffer (allocated once per distinct message; the
   frame's output pointer must stay valid until the parent copies it).")

(defun frame-revert-with! (bytes)
  "Mark the live frame (*current-state*) as REVERTED with output BYTES. The native
   body still runs its own halt+sync, so the frame exits exactly like a REVERT."
  (let ((buf (or (gethash bytes *frame-revert-buffers*)
                 (setf (gethash bytes *frame-revert-buffers*)
                       (let ((p (foreign-alloc :uint8 :count (max 1 (length bytes)))))
                         (loop for i below (length bytes) do (setf (mem-aref p :uint8 i) (aref bytes i)))
                         p)))))
    (setf (mem-ref *current-state* :pointer 112) buf
          (mem-ref *current-state* :uint64 120) (length bytes)
          (mem-ref *current-state* :uint8 129) 1)))

(defcallback cb-selfdestruct :uint64
    ((ctx :pointer) (self :pointer) (beneficiary :pointer))
  (declare (ignore ctx))
  ;; The effect is DERIVED: spec-selfdestruct-effect (src/generated/host.lisp) is
  ;; Evm.CL.EffectSelfdestruct.term, proved in Evm.CL.EffectSelfdestructProof to be every
  ;; fork's SELFDESTRUCT as the spec binds it (Frontier..Amsterdam): EIP-161 touch, EIP-2929
  ;; warm-up, the fork-staged new-account charge, the accounts_to_delete mark and its refund
  ;; (EIP-6780: only a same-tx creation from Cancun; deletion itself at tx end,
  ;; spec-destroy-effect), the balance move (a self-beneficiary burns before Cancun and
  ;; keeps it after unless created this tx), pre-Spurious existence of the beneficiary. It
  ;; returns the gas beyond the native base. The native handler did the static check
  ;; (EIP-214), the base charge and the pop. What stays here: the chain override (Arc), which
  ;; may turn this SELFDESTRUCT into a REVERT before anything is touched, warmed or paid.
  (let ((a (read-addr self))
        (b (read-addr beneficiary)))
    (when *chain-selfdestruct-hook*
      (multiple-value-bind (verdict out)
          (funcall *chain-selfdestruct-hook* a b (balance-of *current-world* a))
        (when (eq verdict :revert)
          (frame-revert-with! out)
          (return-from cb-selfdestruct 0))))
    (cb-gas-check "selfdestruct" (spec-selfdestruct-effect a b) :addr a :beneficiary b)))

(defcallback cb-log :void
    ((ctx :pointer) (self :pointer) (n :uint8)
     (topics :pointer) (data :pointer) (len :uint64))
  (declare (ignore ctx))
  ;; Vtable slot 9, delivered by the emitted LOG-N handler (AsmCore.logEmit)
  ;; AFTER its gas charge. TOPICS points at topic_{n-1} with
  ;; topic_0 at +(n-1)*32 (the popped stack slots, ascending). Installed only
  ;; when observed (alloc-callbacks); a null slot is skipped
  ;; natively, so log-less replays are byte-identical. The record is revert-
  ;; scoped like transfers (same marks) and emitted at tx end.
  (let ((addr (read-addr self))
        (tps (loop for i below n
                   collect (u256-read (inc-pointer topics (* 32 (- n 1 i))))))
        (bytes (foreign->bytes data len)))
    (observe-log! addr tps bytes)))

(declaim (special *cur-block* *cur-tx*))
;; Default bindings so any driver loading this as a library (replay-base,
;; the lazy-RPC tip driver) has them.
(unless (boundp '*cur-block*) (defvar *cur-block* -1))
(unless (boundp '*cur-tx*)    (defvar *cur-tx* -1))

(defstartup *trace-step*
  (and (sb-ext:posix-getenv "EITA_TRACE_STEP") t)
  "When non-nil, install cb-trace-step at vtable offset 112 so the ARM64
   `_eita_next` continuation logs every opcode dispatch.")

(defstartup *trace-block*
  (let ((v (sb-ext:posix-getenv "EITA_TRACE_BLOCK"))) (and v (parse-integer v)))
  "When set, only install cb-trace-step for frames whose *cur-block* matches —
   lets a full 0→N replay trace just one block without per-opcode overhead
   elsewhere.")

(defstartup *trace-tx*
  (let ((v (sb-ext:posix-getenv "EITA_TRACE_TX"))) (and v (parse-integer v)))
  "When set (with EITA_TRACE_BLOCK), restrict tracing to this tx-index.")

(defparameter *opcode-names*
  ;; sparse vector indexed by byte value; nil means unknown
  (let ((v (make-array 256 :initial-element nil)))
    (dolist (e '((#x00 "STOP") (#x01 "ADD") (#x02 "MUL") (#x03 "SUB") (#x04 "DIV")
                 (#x05 "SDIV") (#x06 "MOD") (#x07 "SMOD") (#x08 "ADDMOD") (#x09 "MULMOD")
                 (#x0a "EXP") (#x0b "SIGNEXTEND")
                 (#x10 "LT") (#x11 "GT") (#x12 "SLT") (#x13 "SGT") (#x14 "EQ")
                 (#x15 "ISZERO") (#x16 "AND") (#x17 "OR") (#x18 "XOR") (#x19 "NOT")
                 (#x1a "BYTE") (#x1b "SHL") (#x1c "SHR") (#x1d "SAR") (#x20 "KECCAK256")
                 (#x30 "ADDRESS") (#x31 "BALANCE") (#x32 "ORIGIN") (#x33 "CALLER")
                 (#x34 "CALLVALUE") (#x35 "CALLDATALOAD") (#x36 "CALLDATASIZE")
                 (#x37 "CALLDATACOPY") (#x38 "CODESIZE") (#x39 "CODECOPY")
                 (#x3a "GASPRICE") (#x3b "EXTCODESIZE") (#x3c "EXTCODECOPY")
                 (#x3d "RETURNDATASIZE") (#x3e "RETURNDATACOPY") (#x3f "EXTCODEHASH")
                 (#x40 "BLOCKHASH") (#x41 "COINBASE") (#x42 "TIMESTAMP") (#x43 "NUMBER")
                 (#x44 "DIFFICULTY") (#x45 "GASLIMIT") (#x46 "CHAINID") (#x47 "SELFBALANCE")
                 (#x48 "BASEFEE")
                 (#x50 "POP") (#x51 "MLOAD") (#x52 "MSTORE") (#x53 "MSTORE8")
                 (#x54 "SLOAD") (#x55 "SSTORE") (#x56 "JUMP") (#x57 "JUMPI")
                 (#x58 "PC") (#x59 "MSIZE") (#x5a "GAS") (#x5b "JUMPDEST")
                 (#x5c "TLOAD") (#x5d "TSTORE") (#x5e "MCOPY") (#x5f "PUSH0")
                 (#xf0 "CREATE") (#xf1 "CALL") (#xf2 "CALLCODE") (#xf3 "RETURN")
                 (#xf4 "DELEGATECALL") (#xf5 "CREATE2") (#xfa "STATICCALL")
                 (#xfd "REVERT") (#xfe "INVALID") (#xff "SELFDESTRUCT")))
      (setf (aref v (first e)) (second e)))
    (loop for i from #x60 to #x7f do
      (setf (aref v i) (format nil "PUSH~D" (- i #x5f))))
    (loop for i from #x80 to #x8f do
      (setf (aref v i) (format nil "DUP~D" (1+ (- i #x80)))))
    (loop for i from #x90 to #x9f do
      (setf (aref v i) (format nil "SWAP~D" (1+ (- i #x90)))))
    (loop for i from #xa0 to #xa4 do
      (setf (aref v i) (format nil "LOG~D" (- i #xa0))))
    v))

(defcallback cb-trace-step :void
    ((state :pointer) (pc :uint64) (gas :uint64) (sp :uint64) (opcode :uint8))
  (declare (ignore state))
  (format t "~&[step] pc=~4,'0x op=~A(~2,'0x) gas=~A sp=~A~%"
          pc (or (aref *opcode-names* opcode) "?") opcode gas sp))

(defun alloc-callbacks ()
  "Allocate a fresh callbacks vtable. (Sub-frames get their own copy so we
   don't have to worry about per-frame state in the callbacks themselves —
   they all use the *current-world* dynvar.)"
  (let ((cb (foreign-alloc :pointer :count 16 :initial-element (null-pointer))))
    (setf (mem-aref cb :pointer 0)  (callback cb-sload))
    (setf (mem-aref cb :pointer 1)  (callback cb-sstore))
    ;; slots 2/3 (tload/tstore) are null — handlers are fully native
    (setf (mem-aref cb :pointer 4)  (callback cb-balance))
    (setf (mem-aref cb :pointer 5)  (callback cb-ext-code-size))
    (setf (mem-aref cb :pointer 6)  (callback cb-ext-code-hash))
    (setf (mem-aref cb :pointer 7)  (callback cb-ext-code-copy))
    (setf (mem-aref cb :pointer 8)  (callback cb-block-hash))
    ;; slot 9 (cb->log): logs are always collected — the header gates (bloom,
    ;; receiptsRoot) need them whether or not an observer is installed.
    (setf (mem-aref cb :pointer 9) (callback cb-log))
    ;; slot 10 (keccak256) is null — KECCAK256 hashes natively (eita_helper_keccak256)
    (setf (mem-aref cb :pointer 11) (callback cb-call))
    (setf (mem-aref cb :pointer 12) (callback cb-create))
    (setf (mem-aref cb :pointer 13) (callback cb-selfdestruct))
    (when (and *trace-step*
               (or (null *trace-block*) (eql *cur-block* *trace-block*))
               (or (null *trace-tx*)    (eql *cur-tx*    *trace-tx*)))
      (setf (mem-aref cb :pointer 14) (callback cb-trace-step)))
    cb))

(defstartup *shared-callbacks* nil
  "Process-wide callbacks vtable. The table is CONSTANT — the same CFFI callback
   pointers every frame — so all frames share ONE instead of foreign-alloc'ing
   (and, in the sub-frame path, leaking) a fresh 16-pointer table per call
   (#248/#250). Only the rare per-block/tx step-trace path needs a private copy.")

(defun callbacks-vtable ()
  "Return the shared callbacks vtable (built once). Falls back to a fresh
   per-frame table only when step-tracing is active for THIS block/tx, since
   that one carries a context-dependent trace-cb in slot 14 (debug path)."
  (if (and *trace-step*
           (or (null *trace-block*) (eql *cur-block* *trace-block*))
           (or (null *trace-tx*)    (eql *cur-tx*    *trace-tx*)))
      (alloc-callbacks)
      (or *shared-callbacks* (setf *shared-callbacks* (alloc-callbacks)))))
