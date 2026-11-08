;;;; evm/tx.lisp — a transaction: the TX record, apply-tx around the derived tx effect, intrinsic gas,
;;;; EIP-7702 authorizations.

(in-package #:eita.evm)

;;; --- JSON test parsing ---

(defun jval (obj key)
  "KEY's value in the jsown object OBJ, NIL when absent (jsown:val-safe signals per absent key).
   Block input does not come through here: input/ decodes it from its bytes."
  (and (consp obj) (cdr (find key (cdr obj) :key (lambda (kv) (and (consp kv) (car kv))) :test #'equal))))

;;; --- A transaction ---
;;; Every block source (chain-io's decoder, the fixtures, the OP deposits) builds one TX;
;;; MAKE-TX takes the fields as keywords. The data's zero / nonzero byte counts (intrinsic
;;; gas, the calldata floor, settlement) are counted once. HASH, CHAIN-ID, V (a typed tx's
;;; y parity), R, S and an OP deposit's SOURCE-HASH / SYSTEM-P are not executed: with the
;;; executed fields they are what the envelope (receipts.lisp tx-envelope) encodes, so the
;;; transactionsRoot ties the very values that run to the header.
(defstruct (tx (:constructor make-tx
                   (&key type sender to nonce gas-limit gas-price max-fee max-priority value
                         (data #()) access-list blob-hashes max-blob-fee mint (auth-count 0)
                         auth-list (hash 0) chain-id v r s source-hash system-p)))
  (type 0) sender to (nonce 0) (gas-limit 0) (gas-price 0) max-fee max-priority (value 0)
  (data #()) access-list blob-hashes max-blob-fee mint (auth-count 0) auth-list
  (hash 0) chain-id v r s source-hash system-p
  (zero-bytes nil))                     ; #(zero nonzero al-addrs al-keys), counted on first use

(defun calldata-byte-counts (tx)
  "Seam: (values zero-bytes nonzero-bytes access-list-addresses access-list-keys) of TX,
   counted once: a block decoder asks as it decodes (off the replay thread)."
  (let ((c (tx-zero-bytes tx)))
    (unless c
      (let ((zero 0) (data (tx-data tx)) (al-addrs 0) (al-keys 0))
        (declare (type fixnum zero al-addrs al-keys))
        (if (typep data '(simple-array (unsigned-byte 8) (*)))
            (locally (declare (type (simple-array (unsigned-byte 8) (*)) data) (optimize speed))
              (dotimes (i (length data)) (when (zerop (aref data i)) (incf zero))))
            (loop for b across data when (zerop b) do (incf zero)))
        (dolist (entry (tx-access-list tx))
          (incf al-addrs)
          (incf al-keys (length (cdr entry))))
        (setf c (setf (tx-zero-bytes tx) (vector zero (- (length data) zero) al-addrs al-keys)))))
    (values (svref c 0) (svref c 1) (svref c 2) (svref c 3))))

;;; --- Execute one tx ---
;;; The effect is DERIVED: spec-tx-effect (src/generated/host.lisp, Evm.CL.EffectTx,
;;; proved against every fork's processTransaction — Evm.Frontier.Vm.Tx — in
;;; Evm.CL.EffectTxProof): the validation, the upfront charge, the accessed sets, EIP-7702's
;;; authorizations and delegation, the message (collision, the child's world, the frame or
;;; the precompile, the code deposit, EIP-161's touch), the rollback. Hand-written here: the
;;; seams it calls (warm-tx-seed!, run-tx-frame!, precompile-run-bytes!, chain-tx-precompile!,
;;; tx-frame-status) and apply-tx, which computes its inputs.

(defvar *last-tx-output* #()
  "Return data of the most recent tx's top frame (a system call's output, e.g. a request
   predeploy's payload or ProtocolConfig.feeParams(); system-call returns it).")

(defvar *precompile-seeds* '() "((max p256 list . u256-buffer) ...): one entry per precompile set seen.")

(defun precompile-seed (&aux (max (precompile-max-for-fork)) (p256 (precompile-address-p 256)))
  "This fork's precompile seed: (max p256 list . buffer), the list and its u256s in foreign
   memory, built once per set (a tx used to cons the list and warm it one crossing at a time:
   6 % of the x86 replay thread's allocation, 2026-11-05)."
  (or (find-if (lambda (e) (and (eql (first e) max) (eq (second e) p256))) *precompile-seeds*)
      (let* ((l (append (loop for i from 1 to max collect i) (when p256 (list 256))))
             (buf (foreign-alloc :uint64 :count (* 4 (length l)))))
        (loop for a in l for i from 0 do (u256-write (inc-pointer buf (* 32 i)) a))
        (car (push (list* max p256 l buf) *precompile-seeds*)))))

(defun precompile-seed-addrs ()
  "The fork's precompile addresses EIP-2929 warms (precompile-max-for-fork, and 0x100 when it
   is one — Osaka, OP Fjord). Contract: = the spec's Tx.precompileAddrs."
  (third (precompile-seed)))

(defun warm-tx-seed! (sender target coinbase access-list)
  "EffectIR `warmTx`: EIP-2929's precompiles, the sender, the target, from Shanghai the
   coinbase (EIP-3651), EIP-2930's access-list addresses and slots, in that order. Journaled
   natively, below the tx's snapshot. Contract: = the spec's Tx.seedAddrs / Tx.seedSlots
   inserted in order."
  (when (>= *fork-ord* 10)               ; = (dolist (a (precompile-seed-addrs)) (access-addr! a)), one crossing
    (let ((s (precompile-seed)))
      (%ts-access-addrs *tx-state* (current-arena) (cdddr s) (length (third s)))))
  (access-addr! sender)
  (access-addr! target)
  (when (>= *fork-ord* 15) (access-addr! coinbase))
  (dolist (entry access-list) (access-addr! (car entry)))
  (dolist (entry access-list)
    (dolist (slot (cdr entry)) (access-slot! (car entry) slot))))

(defvar *system-seed* '()
  "The addresses a system call starts warm with — its chain's rule (system-call binds it).")

(defun warm-system-seed! ()
  "EffectIR `warmSys`: warm *system-seed* in order (EELS: none). Contract: = the rule's
   System.Rule.seed inserted in order (Ctx.sysSeed)."
  (dolist (a *system-seed*) (access-addr! a)))

(defun run-tx-frame! (create sender target code-addr value data block-ctx gas)
  "EffectIR `runTx`: run the tx's message frame with GAS on the native interpreter, at depth
   0 (arena slot 0, journaling into the root arena: the term's rollback unwinds it) — a
   creation's init code (DATA) at TARGET, or CODE-ADDR's code (the target's, or EIP-7702's
   delegate's) on DATA — with the block's environment from BLOCK-CTX (its
   :effective-gas-price is GASPRICE). Returns the child record (status gas-left output):
   :return, :revert (REVERT: the interpreter writes the output pointer) or :halt (an
   exceptional halt: no output pointer, no gas left); the output is copied out before the
   memory is scrubbed, and is also *last-tx-output*. Empty code returns at once with all
   its gas. Contract: = the spec's runSub on the frame Tx.create / Tx.call build."
  (let ((code (if create data (code-of *current-world* code-addr))))
    (when (zerop (length code))
      (setf *last-tx-output* #())
      (return-from run-tx-frame! (list :return gas #())))
    (ensure-arenas)
    (setf *memory-arena-base* 0 *stack-arena-base* 0 *journal-arena-base* 0)
    (let* ((state    (substate-slot 0))   ; tx-level frame = arena slot 0 (#248)
           (stack    (inc-pointer *stack-arena*  *stack-arena-base*))
           (mem      (inc-pointer *memory-arena* *memory-arena-base*))
           (mem-cap  (- +memory-arena-bytes+ *memory-arena-base*))
           (code-len (length code))
           (calldata-bytes (if create #() data))
           (calldata-len (length calldata-bytes))
           (egp (or (getf block-ctx :effective-gas-price) 0)))
      ;; The frame reads its calldata in place: the tx data vector, pinned for the frame
      ;; (a copy only for a vector that is not a simple octet vector).
      (sb-sys:with-pinned-objects (calldata-bytes)
      (let ((calldata (cond ((zerop calldata-len) (null-pointer))
                            ((typep calldata-bytes 'octets) (sb-sys:vector-sap calldata-bytes))
                            (t (bytes->foreign (alloc-bytes calldata-len) calldata-bytes calldata-len)))))
      (with-frame-code (state code code-len)
      (setf (mem-ref state :uint64 8)   gas)
      (setf (mem-ref state :pointer 32) stack)
      (setf (mem-ref state :pointer 40) mem)
      (setf (mem-ref state :uint64 56)  mem-cap)
      ;; #250: the top frame starts with no returndata.
      (setf (mem-ref state :pointer 96) (null-pointer))
      (setf (mem-ref state :uint64 104) 0)
      (when (plusp calldata-len)
        (setf (mem-ref state :pointer 80) calldata)
        (setf (mem-ref state :uint64 88) calldata-len))
      (u256-write (inc-pointer state 144) target)
      (u256-write (inc-pointer state 176) sender)  ; origin
      (u256-write (inc-pointer state 208) sender)  ; caller
      (u256-write (inc-pointer state 240) value)
      ;; The tx environment every sub-frame copies (populate-sub-env).
      (setf *tx-origin*    sender
            *tx-gasprice*  egp
            *tx-chainid*   (or (getf block-ctx :chain-id) 1)
            *tx-coinbase*  (or (getf block-ctx :coinbase) 0)
            *tx-timestamp* (or (getf block-ctx :timestamp) 0)
            *tx-number*    (or (getf block-ctx :number) 0)
            *tx-gaslimit*  (or (getf block-ctx :gas-limit) 0)
            *tx-basefee*   (or (getf block-ctx :base-fee) 0)
            *tx-prev-randao* (or (getf block-ctx :prev-randao) 0))
      ;; EIP-4844: the tx's versioned hashes (BLOBHASH) and the block's blob base fee
      ;; (BLOBBASEFEE), for this frame and every sub-frame (populate-sub-env).
      (set-tx-blob-env! (getf block-ctx :blob-hashes) (or (getf block-ctx :blob-base-fee) 0))
      (populate-sub-env state)
      (setf (mem-ref state :pointer 496) (callbacks-vtable))
      (setf (mem-ref state :pointer 504) *tx-arena-root*)
      (setf *current-address* target
            *current-state*   state)
      ;; Init code runs once per deployment — never hot: straight to the interp, as
      ;; cb-create's init frames.
      (cond (create (storage-host-sync!) (eita-run state))
            (*diff-tiers* (diff-run-tiers state code))
            (t (run-frame state code)))
      (let* ((status (frame-status state))
             (gas-left (if (eq status :halt) 0 (mem-ref state :uint64 8)))
             ;; copy BEFORE scrubbing the memory: the output pointer points into it
             (output (if (eq status :halt) #() (%frame-output state))))
        (setf *last-tx-output* output)
        (zero-bytes *memory-arena* 0 (mem-ref state :uint64 48))
        (setf *current-state* (null-pointer))
        (when (and (plusp calldata-len) (not (typep calldata-bytes 'octets))) (foreign-free calldata))
        ;; #250: the top frame ended — free the returndata of its last call.
        (free-frame-returndata state)
        (list status gas-left output))))))))

(defun precompile-run-bytes! (addr data gas)
  "EffectIR `runPreTx`: the fork's precompile at ADDR on the tx's DATA with GAS
   (precompile-run! over a foreign copy of the bytes)."
  (let* ((n (length data))
         (p (if (plusp n) (foreign-alloc :uint8 :count n) (null-pointer))))
    (when (plusp n) (bytes->foreign p data n))
    (unwind-protect (precompile-run! addr p n gas)
      (when (plusp n) (foreign-free p)))))

(defun chain-tx-precompile! (to sender data gas value snap snap-facts)
  "EffectIR `chainTxCall` (outside the Ethereum theorem): a tx straight to a chain-native
   precompile (Arc 0x1800…; cb-call's leg is chain-precompile-call!) — the chain's handler
   as a top-level CALL (kind 0, not static, the value already moved) with GAS; a failure
   unwinds to SNAP, the value transfer with it. OBLIGATION: a chain precompile is a
   precompile at EVERY call site; both legs follow *chain-precompile-p*. Returns (values ok
   used) — on an out-of-gas failure `used` is the whole GAS (the hook returns it)."
  (let* ((n (length data))
         (p (if (plusp n) (foreign-alloc :uint8 :count n) (null-pointer))))
    (when (plusp n) (bytes->foreign p data n))
    (multiple-value-bind (used output success)
        (unwind-protect (funcall *chain-precompile-hook* to 0 sender p n gas nil value)
          (when (plusp n) (foreign-free p)))
      (declare (ignore output))
      (unless success
        (revert-journal-to (current-arena) snap)
        (observe-revert! snap-facts))
      (values success used))))

(defun tx-frame-status (child out)
  "The observed status of a tx's top frame: :return when the message succeeded, :revert
   for a REVERTed frame (a chain's veto, a chain precompile that returned gas), :halt
   otherwise (an exceptional halt, a collision, a failed code deposit)."
  (cond ((/= out 0) :return)
        ((and child (eq (child-status child) :revert)) :revert)
        (t :halt)))

(defparameter +tx-invalid-reasons+
  #("tx type" "intrinsic gas" "init code size" "nonce overflow" "gas above TX_MAX_GAS_LIMIT"
    "priority fee above max fee" "max fee below base fee" "gas price below base fee"
    "no blobs" "too many blobs" "blob versioned hash version" "max blob fee below blob base fee"
    "type cannot create" "empty authorization list" "nonce mismatch" "insufficient balance"
    "sender not an EOA")
  "The rules spec-tx-effect rejects by (its rejection n is rule n), in Tx.invalid's order.")

(define-condition block-invalid (simple-error)
  ((kind :initarg :kind :reader invalid-kind))
  (:documentation "A block the spec rejects. KIND names the rule: a +tx-invalid-reasons+ entry,
   \"gas allowance\", \"blob gas allowance\", \"system contract empty\", \"system call
   failed\", \"deposit layout\". The replay stops on it (a canonical block cannot carry
   one); the fixture runner (src/fixtures/runner.lisp) requires it of an invalid block."))

(defun invalid! (kind fmt &rest args)
  (error 'block-invalid :kind kind :format-control fmt :format-arguments args))

(defun apply-tx (tx coinbase block-ctx &key (egp (or (tx-gas-price tx) 0)) (checked t) (extra 0))
  "One tx up to the end of its message: the Lean-emitted spec-tx-effect, with the inputs it
   reads — the creation's address (derive-create-address: the seam = computeContractAddress),
   the data's byte counts and the access list's sizes (the seam the emitted
   spec-intrinsic-gas / spec-calldata-floor-gas read), the blob hashes' version byte. EGP is
   the effective gas price (effective-gas-price); CHECKED nil skips the validation (an OP
   deposit); EXTRA a chain's upfront
   extra (OP's L1 fee). The caller has reset the per-tx state (reset-tx-state). Returns
   (values success gas-used-by-the-message rejection), the rejection 0 for a valid tx."
  (let* ((from (tx-sender tx))
         (to (tx-to tx))
         (create (null to))
         (data (tx-data tx))
         (hashes (tx-blob-hashes tx))
         (target (or to (progn (fault-account! from)
                               (derive-create-address from (nonce-of *current-world* from))))))
    (multiple-value-bind (zero nz) (calldata-byte-counts tx)
      (multiple-value-bind (used out rej)
          (spec-tx-effect from target coinbase create checked *prague-delegation*
                          (every (lambda (h) (= (ash h -248) 1)) hashes)
                          (tx-value tx) (tx-gas-limit tx) (intrinsic-gas tx)
                          (spec-calldata-floor-gas zero nz (el-fork)) egp extra
                          (or (tx-type tx) 0) (tx-nonce tx)
                          (or (tx-max-fee tx) 0) (or (tx-max-priority tx) 0)
                          (or (tx-gas-price tx) 0) (or (getf block-ctx :base-fee) 0)
                          (length hashes) (or (tx-max-blob-fee tx) 0)
                          (or (getf block-ctx :blob-base-fee) 0) (or (tx-auth-count tx) 0)
                          (length data) (or (getf block-ctx :chain-id) 1)
                          (tx-access-list tx) (tx-auth-list tx) data
                          (list* :effective-gas-price egp :blob-hashes hashes block-ctx))
        (values (= out 1) used rej)))))

;;; --- Intrinsic gas + tx fees (formulas: Evm.CL.GasEmit via src/generated/host.lisp) ---

(defun block-blob-base-fee (excess-blob-gas fork-ord)
  "The block's blob base fee: EELS calculate_blob_gas_price(excess_blob_gas) at the block's
   fork — the emitted spec-blob-base-fee (Evm.CL.GasEmit.blobBaseFee, proved equal to
   Evm.Osaka.Spec.calculateBlobGasPriceAt in Evm.CL.GasEmitCancun: the fork's blob
   schedule entry's fraction — Cancun, Prague/Osaka (EIP-7691), BPO1, BPO2 (EIP-7892)).
   Computed ONCE per block (the block-ctx's
   :blob-base-fee); it prices every type-3 tx (spec-tx-effect) and is what BLOBBASEFEE
   pushes (install-blob-env!). EELS pushes U256(fee), so a fee past 2^256 is an error."
  (let ((fee (spec-blob-base-fee excess-blob-gas fork-ord)))
    (when (>= fee (ash 1 256))
      (error "blob base fee ~D does not fit u256 (excess_blob_gas ~D)" fee excess-blob-gas))
    fee))

(defvar *el-fork-ord* nil
  "The Ethereum fork whose TRANSACTION and BLOCK rules apply (refund cap, calldata floor,
   system calls), when it differs from the opcode table in *fork-ord*: OP-Stack Isthmus
   follows Prague (17) at the tx level but runs the Cancun (16) opcode table. NIL = same.")
(defun el-fork () (or *el-fork-ord* *fork-ord*))

(defun intrinsic-gas (tx)
  "Tx intrinsic gas. The byte counting + access-list sizing is the hand-written CL
   SEAM; the cost FORMULA is the Lean-emitted spec-intrinsic-gas (Evm.CL.GasEmit,
   src/generated/host.lisp). #261: derived, not hand-written."
  (let* ((data (tx-data tx))
         (is-create (if (null (tx-to tx)) 1 0)))
    (multiple-value-bind (zero nonzero al-addrs al-keys) (calldata-byte-counts tx)
      (+ (spec-intrinsic-gas is-create (length data) zero nonzero al-addrs al-keys *fork-ord*)
         ;; EIP-7702 (Prague+): PER_EMPTY_ACCOUNT_COST per authorization tuple.
         (* (or (tx-auth-count tx) 0) (spec-auth-intrinsic-per-auth))))))

;;; --- EIP-7702 authorization processing (Prague+) ---------------------------
;;; EELS prague vm/eoa_delegation.py set_delegation / recover_authority; the
;;; relation is Evm.Prague.Spec.SetCodeStep.IsApplyAuthorization(s). Runs at tx
;;; level after the sender's nonce bump and before the message is prepared, and is
;;; NOT journaled: a reverting call does not undo delegations (same as the bump).

(defconstant +secp256k1-n+ #xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141)
(defconstant +set-code-tx-magic+ #x05)

(defun designator-bytes (addr)
  "0xef0100 || addr (EIP-7702 delegation designator)."
  (let ((v (make-array 23 :element-type '(unsigned-byte 8))))
    (setf (aref v 0) #xef (aref v 1) #x01 (aref v 2) #x00)
    (loop for i from 0 below 20 do (setf (aref v (+ 3 i)) (logand #xff (ash addr (* -8 (- 19 i))))))
    v))

(defun ecrecover-address (msg v r s)
  "The address that signed the 32-byte hash MSG with (V ∈ {27, 28}, R, S) — the ECRECOVER
   precompile's eita_ecrecover (lean/c/ecrecover.c) — or NIL when it does not recover."
  (when (and (member v '(27 28)) (< (max r s) (ash 1 256)))
    (with-foreign-object (in-buf :uint8 128)
      (loop for i below 128 do (setf (mem-aref in-buf :uint8 i) 0))
      (loop for i below 32 do (setf (mem-aref in-buf :uint8 i) (aref msg i)))
      (setf (mem-aref in-buf :uint8 63) v)
      (loop for i below 32 do
        (setf (mem-aref in-buf :uint8 (+ 64 i)) (logand #xff (ash r (* -8 (- 31 i))))
              (mem-aref in-buf :uint8 (+ 96 i)) (logand #xff (ash s (* -8 (- 31 i))))))
      (with-foreign-object (out-buf :uint8 32)
        (when (plusp (%eita-ecrecover in-buf 128 out-buf))
          (let ((a 0))
            (loop for i from 12 below 32 do (setf a (logior (ash a 8) (mem-aref out-buf :uint8 i))))
            a))))))

(defvar *authorities-ahead* (make-hash-table :test 'equal :synchronized t)
  "(chain-id addr nonce y-parity r s) -> the authority (or :none), recovered by the block
   decoder ahead of execution (`recover-authority-ahead!`); taken by `recover-authority`.")

(defun recover-authority-ahead! (chain-id addr nonce y-parity r s)
  "On the decoder thread: recover a tuple's authority now, so the replay thread does not run
   the ecrecover (EELS's checks around it stay where the effect makes them). A table grown
   past its bound (tuples whose tx never ran) is dropped: a miss only recovers again."
  (when (and (integerp chain-id) (integerp addr) (integerp nonce) (integerp y-parity) (< y-parity 2)
             (integerp r) (integerp s) (< 0 r +secp256k1-n+) (< 0 s +secp256k1-n+))
    (let ((tab *authorities-ahead*))
      (when (> (hash-table-count tab) 100000) (clrhash tab))
      (setf (gethash (list chain-id addr nonce y-parity r s) tab)
            (or (%recover-authority chain-id addr nonce y-parity r s) :none)))))

(defun recover-authority (chain-id addr nonce y-parity r s)
  "EELS recover_authority: keccak(MAGIC || rlp([chain_id, address, nonce])) signed by
   (y_parity, r, s) → the authority address, or NIL when recovery fails. Scalar bounds
   (r, s ∈ (0, n); s ≤ n/2; y_parity ∈ {0,1}) are the caller's. The decoder has usually
   recovered it already (`recover-authority-ahead!`): the same function, earlier."
  (let* ((key (list chain-id addr nonce y-parity r s))
         (hit (gethash key *authorities-ahead*)))
    (cond (hit (remhash key *authorities-ahead*) (if (eq hit :none) nil hit))
          (t (%recover-authority chain-id addr nonce y-parity r s)))))

(defun %recover-authority (chain-id addr nonce y-parity r s)
  (let ((rlp (rlp-encode-list (list (rlp-encode-bytes (int-to-be-bytes chain-id))
                                    (rlp-encode-bytes (addr-to-bytes addr))
                                    (rlp-encode-bytes (int-to-be-bytes nonce))))))
    (ecrecover-address (keccak256-bytes (coerce (cons +set-code-tx-magic+ rlp) 'vector)) (+ 27 y-parity) r s)))
