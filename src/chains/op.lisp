;;;; chains/op.lisp — Base mainnet (OP-Stack) replay with lazy
;;;; RPC-backed state.
;;;;
;;;; Uses the engine (system eita) and
;;;; drives its world/apply-tx machinery from Base mainnet RPC data.
;;;; Unlike the fixture/mainnet replays the world starts EMPTY: the
;;;; fault hooks (fault-account!/fault-slot! choke points in
;;;; src/state/world.lisp) fetch balance/nonce/code/storage on first touch
;;;; via eth_getBalance / eth_getTransactionCount / eth_getCode /
;;;; eth_getStorageAt, pinned at the block before the replay range
;;;; (anything not yet locally known was untouched by the replayed
;;;; blocks, so its value at range-start-1 is still current).
;;;;
;;;; Data sources, in priority order:
;;;;   1. per-block prestateTracer overlay (lean/external/base-cache/
;;;;      prestate_<hex>.json, written by the Lean Base replay) —
;;;;      first-touch-wins merge gives the exact pre-block value of
;;;;      every account/slot the canonical execution touched;
;;;;   2. disk cache (same dir, balance_/nonce_/code_/storage_ keys,
;;;;      shared format with lean/Evm/Optimism/Replay/Fetch.lean);
;;;;   3. live RPC via curl ($BASE_RPC_URL).
;;;; A fault that misses all three is counted + warned (a touched-set
;;;; divergence from the canonical execution, or an offline run of an
;;;; untraced block) — the run is suspect if offline-misses > 0.
;;;;
;;;; OP-Stack tx semantics (mirrors the validated Lean track,
;;;; lean/Evm/Optimism/Bedrock/Fork.lean):
;;;;   * deposited txs (type 0x7E): nonce bump + mint credit survive
;;;;     failure; no fee accounting at all (gas paid on L1); receipt
;;;;     gasUsed = intrinsic + execution, NO refund.
;;;;   * user txs: sender pays gas*egp + l1Fee upfront; refund per
;;;;     EIP-3529 (cap raw/5 — every Base fork is London+); fees are
;;;;     routed, not burned: priority*gasUsed -> SequencerFeeVault,
;;;;     baseFee*gasUsed -> BaseFeeVault, l1Fee (from the receipt,
;;;;     same shortcut as the Lean track) -> L1FeeVault.
;;;;   * no beacon-roots / EIP-2935 system calls, no withdrawals
;;;;     (mirrors the Lean OP drivers, validated Isthmus 500/500).
;;;;
;;;; Validation per tx: gasUsed vs receipt, status vs receipt, sender
;;;; nonce vs tx.nonce (lazy-state check), depositNonce vs world.
;;;; Per block: cumulative gas vs header.gasUsed.
;;;;
;;;; Native fork mapping (OpFork.ethereumAnalog): bedrock->london(11),
;;;; canyon->shanghai(15), ecotone..holocene->cancun(16). Isthmus+
;;;; (prague: EIP-7702 delegation) is NOT yet supported by the native
;;;; tier — blocks past the Isthmus timestamp error out loudly.
;;;; Known gaps vs op-geth, surfaced by gates rather than hidden:
;;;; RIP-7212 P256VERIFY (0x100) executes as empty code (warm-seeded
;;;; Fjord+ but not implemented); Granite's bn256 pairing input cap
;;;; is not enforced.
;;;;
;;;; Run: eita replay --chain base|opt|world --from N [--to M] (lazy state: a block source that
;;;;   serves state, --source FILE; needs $BASE_RPC_URL unless fully cached)



(in-package #:eita.chain.op)

;;; --- OP fork schedule (Base mainnet timestamps) ---

(defun base-op-fork (ts)
  "OP fork active at TS on Base mainnet (chain 8453) + the Ethereum
   fork ord its EL semantics tracks (Evm.Optimism.OpFork.ethereumAnalog)."
  (cond ((>= ts 1779991200) (values :azul     18))   ; ~Osaka
        ((>= ts 1746806401) (values :isthmus  17))   ; ~Prague
        ((>= ts 1740484801) (values :holocene 16))
        ((>= ts 1726070401) (values :granite  16))
        ((>= ts 1720627201) (values :fjord    16))
        ((>= ts 1710374401) (values :ecotone  16))   ; ~Cancun
        ((>= ts 1704992401) (values :canyon   15))   ; ~Shanghai
        (t                  (values :bedrock  11)))) ; ~London

;;; --- Chain selection (#269: OP-Stack lazy-RPC at tip) ---
;; EITA_CHAIN picks the OP-Stack chain: base (default) | opt | world.
;; They share OP-Stack semantics (fee vaults, deposit txs, and the
;; coordinated Superchain fork schedule — Ecotone/Fjord/Granite/Holocene/
;; Isthmus all activate network-wide at the SAME timestamp across the
;; Superchain, so base-op-fork's thresholds are correct for all three);
;; they differ only in chain-id, the Alchemy endpoint, and the cache dir.
(defstartup *chain* (or (sb-ext:posix-getenv "EITA_CHAIN") "base"))
(defparameter +chains+
  '(("base"  8453 "base-mainnet")
    ("opt"   10   "opt-mainnet")
    ("world" 480  "worldchain-mainnet")))

;;; --- OP fee vault predeploys (Bedrock/Spec/FeeVaults.lean) ---

(defconstant +sequencer-fee-vault+ #x4200000000000000000000000000000000000011)
(defconstant +base-fee-vault+      #x4200000000000000000000000000000000000019)
(defconstant +l1-fee-vault+        #x420000000000000000000000000000000000001a)
(defconstant +operator-fee-vault+  #x420000000000000000000000000000000000001b)  ; Isthmus

;; Bound per-block: T iff the block is OP-Isthmus (>= Prague EL). Gates the
;; EIP-7623 calldata floor + operator-fee routing in run-user-tx.
(defparameter *isthmus* nil)

;;; --- OP-Stack as a chain-spec on the generic driver ---------------------------

(defvar *op-fork* :bedrock "The OP fork of the current block (set by op-block-setup).")

(defun op-block-setup (n blk ts)
  "OP fork by timestamp; the native opcode table tracks the Ethereum analog capped at
   Cancun (Prague/Isthmus adds no opcodes), while tx-level rules follow the full analog
   (*el-fork-ord*: EIP-7623 floor from Isthmus) — Evm.Optimism.OpFork.ethereumAnalog."
  (declare (ignore blk))
  (multiple-value-bind (op-fork eth-ord) (base-op-fork ts)
    (let ((dispatch-ord (min eth-ord 16)))
      (unless (= dispatch-ord *fork-ord*)
        (format t "~&block ~D: ~A -> native fork ord ~D~%" n op-fork dispatch-ord)
        (setf *fork-ord* dispatch-ord)
        (%set-fork dispatch-ord)))
    (setf *op-fork* op-fork
          *el-fork-ord* eth-ord                   ; run-block derives *prague-delegation* from it
          *isthmus* (>= eth-ord 17)
          ;; 0x100 (Evm.Optimism.Fjord.Spec.p256VerifyGasAt): a precompile — so warmed by
          ;; every tx's seed, deposits included (op-geth ActivePrecompiles) — from Fjord,
          ;; at RIP-7212's gas until Azul (the native table is capped at Cancun, so the
          ;; Osaka leg of precompile-address-p never fires on OP)
          *p256verify* (case op-fork
                         ((:fjord :granite :holocene :isthmus) :rip7212)
                         (:azul t)))))

(defun run-deposit-tx (world tx receipt block-ctx coinbase blk idx)
  "Type-0x7E deposited tx (Bedrock/Fork.lean processDepositedTx): nonce bump + mint
   credit survive failure; gas-free at L2; receipt gasUsed = intrinsic + execution, no
   refund. Returns (values gas-used status egp=0)."
  (let ((from (tx-sender tx))
        (mint (tx-mint tx)))
    (fault-account! from)
    ;; depositNonce gate: receipt carries the sender nonce the deposit consumed.
    (let ((dn (getf receipt :deposit-nonce)))
      (when dn
        (gate blk idx "depositNonce" dn (nonce-of world from))))
    (when (plusp mint)
      (incf (balance-of world from) mint))
    ;; Warm-seed like op-geth (Prepare runs for deposits too): the derived effect warms
    ;; the sender, the target, the precompiles and the coinbase; no validation, no charge
    ;; (the gas price is 0).
    (reset-tx-state)
    (multiple-value-bind (success exec-used)
        (apply-tx tx coinbase block-ctx :egp 0 :checked nil)
      (spec-destroy-effect)                 ; end of tx, as for a user tx
      (spec-sweep-effect)
      (values (+ (intrinsic-gas tx) exec-used) (if success 1 0) 0))))

(defun op-run-tx (world tx receipt block-ctx coinbase blk idx)
  "OP tx kinds: deposits (0x7E) have their own rules; type 4 is still skipped here (see
   below); everything else is the generic user-tx pipeline with the OP hooks."
  (cond
    ((= (tx-type tx) #x7e)
     (incf (getf *stats* :deposits))
     ;; Deposit receipts carry depositNonce/depositReceiptVersion: not encoded yet, so
     ;; this block's receiptsRoot is not checked (honestly marked, never "passed").
     (setf *receipts-unverifiable* t)
     (run-deposit-tx world tx receipt block-ctx coinbase blk idx))
    ((= (tx-type tx) 4)
     ;; Kept from the pre-generic driver: OP type-4 txs are SKIPPED (nonce bumped, receipt
     ;; gas charged) and counted unverified. The generic pipeline does execute EIP-7702
     ;; (spec-tx-effect, validated on Arc) — switching OP over is a separate, gated change.
     (incf (getf *stats* :type4))
     (format *error-output*
             "~&NOTE blk=~D tx=~D: type-4 (EIP-7702) ~D auth(s) SKIPPED (unverified) — receipt gas used~%"
             blk idx (tx-auth-count tx))
     (incf (nonce-of world (tx-sender tx)))
     (values (getf receipt :gas-used) :skip (effective-gas-price tx (getf block-ctx :base-fee))))
    (t (run-evm-tx world tx block-ctx coinbase blk idx :receipt receipt))))

(defun op-upfront-extra (tx receipt)
  "The L1 data fee is charged upfront with the gas (apply-tx moves `value` itself)."
  (declare (ignore tx))
  (getf receipt :l1-fee))

(defun op-fee-settlement (from coinbase egp base-fee gas-used tx receipt)
  "OP fee routing (Bedrock/Spec/FeeVaults.lean): priority fee → SequencerFeeVault, base
   fee → BaseFeeVault, L1 fee → L1FeeVault, Isthmus operator fee → OperatorFeeVault. The
   vault credits are deltas (balance-delta!), like the coinbase's on Ethereum."
  (declare (ignore coinbase tx))
  (let ((w *current-world*))
    (fault-account! +sequencer-fee-vault+)
    (fault-account! +base-fee-vault+)
    (fault-account! +l1-fee-vault+)
    (balance-delta! w +sequencer-fee-vault+ (* (- egp base-fee) gas-used))
    (balance-delta! w +base-fee-vault+ (* base-fee gas-used))
    (balance-delta! w +l1-fee-vault+ (getf receipt :l1-fee))
    ;; Isthmus operator fee: scalar*gasUsed/1e6 + constant (net debit from the sender).
    (when *isthmus*
      (let ((opfee (+ (floor (* (getf receipt :operator-fee-scalar) gas-used) 1000000)
                      (getf receipt :operator-fee-constant))))
        (when (plusp opfee)
          (fault-account! +operator-fee-vault+)
          (decf (balance-of w from) opfee)
          (balance-delta! w +operator-fee-vault+ opfee))))))

(defun op-chain-spec (&optional (chain *chain*))
  "An OP-Stack chain (base | opt | world) as a chain-spec."
  (let ((row (or (assoc chain +chains+ :test #'string=) (error "unknown OP chain ~S" chain))))
    (make-chain-spec
     :name (format nil "OP-Stack ~A" chain) :id (second row)
     :banner "OP fork by timestamp (Superchain schedule)"
     :rpc-url (or (sb-ext:posix-getenv "BASE_RPC_URL")
                  (let ((k (sb-ext:posix-getenv "ALCHEMY_KEY")))
                    (and k (format nil "https://~A.g.alchemy.com/v2/~A" (third row) k))))
     :cache-dir (pathname (format nil "lean/external/~A-cache/" chain))
     :prestate-overlay t
     :block-setup #'op-block-setup
     ;; Kept from the pre-generic driver: no pre-block system calls in lazy OP runs
     ;; (op-geth does run EIP-4788/2935; adding them is a separate, gated change). No
     ;; post-block work either: OP has no withdrawals and Isthmus disables the EIP-7002/7251
     ;; request calls (requestsHash = sha256("")).
     :pre-block (lambda (world n blk coinbase block-ctx) (declare (ignore world n blk coinbase block-ctx)) nil)
     :post-block (lambda (world n blk gas-used coinbase block-ctx) (declare (ignore world n blk gas-used coinbase block-ctx)) nil)
     :header-foreign '("withdrawalsRoot" "blobGasUsed")    ; message-passer root (Isthmus), DA footprint (Jovian)
     :run-tx #'op-run-tx
     :upfront-extra #'op-upfront-extra
     :fee #'op-fee-settlement)))

(dolist (c '("base" "opt" "world"))
  (let ((c c)) (register-chain-spec c (lambda () (op-chain-spec c)))))

;;; --- Entry ---

(defun main-base (args &optional (chain *chain*))
  "Install the OP-Stack CHAIN (base | opt | world), run the generic driver, report, and exit
   0 only when no gate mismatched and no state was missing offline."
  (install-chain-spec! (op-chain-spec chain))
  (replay-main args)
  (format t "source: rpc-calls=~D offline-misses=~D~%" *rpc-calls* *offline-misses*)
  (format t "jit: codes=~D no-jit=~D frames-jit=~D frames-interp=~D manifest-misses=~D~%"
          (getf *jit-stats* :codes-jit) (getf *jit-stats* :codes-no-jit)
          eita.evm::*frames-jit* eita.evm::*frames-interp*
          (getf *jit-stats* :manifest-misses))
  (sb-ext:exit :code (if (and (zerop (getf *stats* :mismatches)) (zerop *offline-misses*)) 0 1)))
