;;;; evm/seams.lisp — chain hooks into the EVM (chain precompiles, frame init), the precompile
;;;; range, the Lean-emitted SSTORE gas and access-cost natives.

(in-package #:eita.evm)

;;; Chain-native precompiles (e.g. Circle Arc 0x1800…: src/chains/arc-precompiles.lisp).
;;; A driver installs a predicate + handler; cb-call consults them BEFORE the
;;; standard 0x01..0x0a range. Handler: (addr kind caller input-ptr input-len gas
;;; is-static) → (values gas-used output success); OOG = (gas #() nil).
(defvar *chain-precompile-p* nil "When set: (lambda (addr)) → chain-native precompile?")
(defvar *chain-precompile-hook* nil "When set: the chain-native precompile handler.")
(defvar *last-sub-outcome* nil
  "How the most recent sub-frame run by cb-call ended: :return, :revert or :halt
   (OOG/exception). A frame-spawning chain precompile (Arc CallFrom) reads it to
   apply the client\'s halt rule after re-entering cb-call for the child.")
(defvar *chain-value-transfer-log-hook* nil
  "When set: emits the chain's frame-init value-transfer log (Arc EIP-7708) at the
   point the transfer actually happens. Separate from the check hook because the
   check runs BEFORE the depth/balance fail-fast and the log must not.")
(defvar *chain-value-transfer-hook* nil
  "When set: (lambda (from to value &optional (emit-log t))) — a chain's frame-init
   check for a value-bearing frame (Arc: zero-address / blocklist / destructed-target
   reverts plus unmetered blocklist-slot warming, evm.rs check_blocklist_and_create_log).
   Returns NIL to proceed or (values :revert output). Call it ONLY through
   `chain-frame-init`.")

(defun chain-frame-init (from to value &key (emit-log t))
  "THE entry point for a chain's frame-init check on a value-bearing frame: the
   top-level tx (apply-tx), CALL (cb-call) and CREATE (cb-create) all come through
   here, so a chain rule cannot be honoured at some frame kinds and missed at others —
   which is exactly how stop #15 happened (the tx level dropped the verdict). Returns
   NIL (proceed) or (values :revert output); on :revert the CALLER must revert the
   frame before any value moves or code runs, with no gas spent inside it. No hook
   (plain Ethereum) or zero value: NIL."
  (when (and *chain-value-transfer-hook* (plusp value))
    (funcall *chain-value-transfer-hook* from to value emit-log)))

(defparameter *p256verify* nil
  "P256VERIFY at 0x100 beyond the fork's own (Osaka+): T = EIP-7951 (Arc from genesis, OP
   Azul), :RIP7212 = the same verifier at RIP-7212's gas (OP Fjord..Isthmus — the spec's
   Evm.Optimism.Fjord.Spec.p256VerifyGas). Not in the contiguous 0x01..0x0a range, so it
   is a separate leg of `precompile-address-p`.")

(defun precompile-address-p (addr)
  "Is ADDR a precompile at the active fork? The contiguous range 0x01..max plus,
   when enabled, EIP-7951's 0x100 (Evm.Osaka.Spec.P256VerifyStep)."
  (or (and (>= addr 1) (<= addr (precompile-max-for-fork)))
      (and (or *p256verify* (>= *fork-ord* 18)) (= addr 256))))

(defun precompile-max-for-fork ()
  "Highest precompile address (inclusive) that exists at the active fork.
   Frontier..Spurious: 0x01-0x04. Byzantium+: +modexp/bn256 (0x05-0x08).
   Istanbul+: +blake2f (0x09). Cancun+: +point-eval (0x0a). Addresses above
   this are ordinary (empty) accounts, NOT precompiles."
  (cond ((>= *fork-ord* 17) 17)        ; Prague: +EIP-2537 BLS12-381 (0x0b..0x11)
        ((>= *fork-ord* 16) 10)
        ((>= *fork-ord* 8)  9)
        ((>= *fork-ord* 5)  8)
        (t 4)))

(defparameter +precompile-impls+ '(1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 256)
  "Addresses `run-precompile` actually dispatches. NOT a copy of the fork range:
   the two are compared, and an in-range address missing from this list is a loud
   error rather than a silent answer.

   This gate exists because the absence of 0x0b..0x11 did NOT fail: an address past
   the fork range is an ordinary empty account, so a CALL to the BLS12-381 pairing
   check succeeded, returned nothing and cost only the call base. Arc block
   21 142 242 undercharged 131 592 gas that way and its logs bloom diverged.")

(defun precompile-coverage-gaps ()
  "In-range precompile addresses with no implementation, at the active fork."
  (loop for a from 1 to (precompile-max-for-fork)
        unless (member a +precompile-impls+) collect a))

;; The cold-account surcharge for SELFDESTRUCT (EIP-2929, Berlin+; warm adds 0, not 100,
;; so it can't come from the access table) is the Lean-emitted spec-selfdestruct-cold-gas.

;;; SSTORE gas/refunds and account/slot access costs come from the
;;; natives emitted out of the Lean spec (Evm.CL.ARM64.SstoreGas) —
;;; no Lisp re-encoding of the per-fork schedules.

;; Scratch for the sstore plans: out[2] at 0, orig at byte 16,
;; cur at 48, new at 80.
(defstartup *sstore-gas-buf*
  (foreign-alloc :uint64 :count 14 :initial-element 0))

(defun sstore-gas-native (refund original current new-val cold?)
  "The fork's SSTORE plan (cost, new refund) through the emitted dispatch
   (spec-sstore-gas-dispatch, Evm.CL.EffectIR.SstoreSched). Returns (values cost new-refund)."
  (let ((out  *sstore-gas-buf*)
        (orig (inc-pointer *sstore-gas-buf* 16))
        (cur  (inc-pointer *sstore-gas-buf* 48))
        (new  (inc-pointer *sstore-gas-buf* 80))
        (cold (if cold? 1 0)))
    (u256-write orig original)
    (u256-write cur  current)
    (u256-write new  new-val)
    (spec-sstore-gas-dispatch out refund orig cur new cold)
    (values (mem-aref out :uint64 0) (mem-aref out :uint64 1))))

;; _eita_access_costs[ord][kind]{cold,warm}, emitted from the IR
;; metadata ladder + Berlin EIP-2929 constants.
(defstartup *access-costs*
  (foreign-symbol-pointer "eita_access_costs"))

(defun check-cached-foreign-pointers! (where)
  "Loud check that libeita has not been remapped under the pointers we cached.

   Every libeita address resolved at load time — this table, the handler addresses
   in *foreign-sym-cache* that JIT relocations are patched with, the callback
   vtable — is only valid for the image that was open then. dlopen'ing libeita a
   SECOND time (e.g. by absolute path when it was first loaded by name) maps
   another image at a new base, and dyld may then place the old mapping's pages
   elsewhere: the cached pointers read another image's memory, with no error.

   That is not hypothetical. Loading src/state/mpt.lisp used to re-dlopen libeita,
   and a cold SLOAD read 4 341 146 380 from this table instead of 2100 — Arc's
   ProtocolConfig proxy OOG'd, feeParams() failed, and block 1 silently took the
   chainspec-default base fee. In other runs the stale read was 0, which
   UNDERCHARGES and does not fail at all. Call this after anything that may load
   a foreign library mid-run."
  (let ((now (foreign-symbol-pointer "eita_access_costs")))
    (unless (pointer-eq *access-costs* now)
      (error "libeita was remapped after ~A: eita_access_costs cached at ~A, dlsym now says ~A.~%~
              Every cached libeita pointer is stale (gas tables, handler addresses for JIT relocs).~%~
              Something dlopen'd libeita a second time — load it once, by one path."
             where *access-costs* now))))

(defun cb-gas-fail (who g ctx)
  (error "host cb ~A returned out-of-range gas ~A~@[ (= ~A − 2^64)~]~%  inputs: ~{~A~^ ~}~%  fork=~A depth=~A"
         who g (and (integerp g) (minusp g) (+ g (ash 1 64))) ctx *fork-ord* *call-depth*))
(defmacro cb-gas-check (who g &rest ctx)
  "A host callback must return gas as an (UNSIGNED-BYTE 64). Returning anything
   else used to surface as a bare CFFI TYPE-ERROR from the trampoline, naming
   neither the callback nor its inputs — the second JIT bug cost a session to
   that. Fail loudly with both instead (CTX is built only then)."
  (let ((v (gensym "G")))
    `(let ((,v ,g)) (if (typep ,v '(unsigned-byte 64)) ,v (cb-gas-fail ,who ,v (list ,@ctx))))))

(defun access-cost (kind cold?)
  "Account/slot access cost for the current fork. KIND: 0 sload,
   1 balance, 2 extcode{size,copy}, 3 extcodehash."
  ;; 21 = amsterdam, the last row of the Fork.ord-indexed table (ARM64.SstoreGas.tableForks).
  (mem-aref *access-costs* :uint64
            (+ (* (min *fork-ord* 21) 8) (* kind 2) (if cold? 0 1))))
