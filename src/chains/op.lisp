;;;; chains/op.lisp — OP-Stack chains (Base, OP Mainnet, World Chain) on the generic driver,
;;;; in full state (from the chain's genesis alloc or an anchored snapshot) or lazily (a block
;;;; source that serves state). Everything the OP Stack changes about an Ethereum block is a
;;;; chain-spec hook here; every rule in it is the Lean spec's (lean/Evm/Optimism/):
;;;;
;;;;   fork          the OP fork by timestamp and the Ethereum fork it tracks: the emitted
;;;;                 spec-op-base-fork-ord / spec-op-eth-analog-ord (Replay.Emit, proved =
;;;;                 OpFork.baseMainnetAt / ethereumAnalog). Base's schedule; OP Mainnet and
;;;;                 World Chain share the Superchain times from Ecotone (their Canyon is
;;;;                 the same timestamp too), Azul is Base's alone (not run on the others).
;;;;   deposits      type 0x7E (Bedrock/Spec/DepositReceipt.lean, specs deposits.md): the mint
;;;;                 first (it survives anything), no validation, no fee; metered as a type-2
;;;;                 tx (refund capped at a fifth, the EIP-7623 floor from Isthmus); a deposit
;;;;                 whose message fails a consensus check (spec-op-deposit-fails) is a failed
;;;;                 deposit: nonce bumped, status 0, its whole gas limit used.
;;;;   user txs      the generic pipeline with an upfront extra (the L1 data fee and, from
;;;;                 Isthmus, the operator fee at the gas limit) and OP's fee routing: the
;;;;                 priority fee to the coinbase, the base fee to BaseFeeVault, the L1 fee to
;;;;                 L1FeeVault, the operator fee (at the gas used) to OperatorFeeVault and the
;;;;                 rest of it back to the sender (op-geth state_transition.go 690-735).
;;;;   L1 data fee   spec-op-l1-fee (Replay.Emit.l1FeeExpr = Replay.l1FeeWei: Bedrock,
;;;;                 Ecotone, Fjord) over the tx's EIP-2718 bytes (zero / non-zero counts and,
;;;;                 Fjord+, spec-flz-compress-len) and the L1Block predeploy's storage as the
;;;;                 block's deposits left it (op-geth NewL1CostFunc reads it after them).
;;;;   receipts      a deposit's receipt hashes depositNonce and version 1 from Canyon
;;;;                 (DepositReceipt.lean): the receipt extension the generic encoder appends.
;;;;   block         pre-block system calls by the Ethereum analog (EIP-4788 from Ecotone,
;;;;                 when the header has a beacon root; EIP-2935 from Isthmus); the Canyon
;;;;                 block installs the create2Deployer (op-geth EnsureCreate2Deployer); no
;;;;                 post-block calls (Isthmus: requestsHash = sha256("")); from Jovian the
;;;;                 header's blobGasUsed is the DA footprint (op-geth CalcDAFootprint).
;;;;   header        withdrawalsRoot from Isthmus is the L2ToL1MessagePasser storage root:
;;;;                 not computed here, so not compared then (named in the banner; stated in
;;;;                 Isthmus/Spec/PragueInheritance.lean). Before Isthmus it is the empty root
;;;;                 of the empty withdrawals list and is compared.
;;;;
;;;; Run: eita replay --chain base|opt|world --from N [--to M] (full state: --full-state with
;;;; the chain's genesis.json, EITA_GENESIS; lazy: a block source that serves state, --source)

(in-package #:eita.chain.op)

;;; --- Fork schedule ---------------------------------------------------------------------

(defparameter +op-forks+ #(:bedrock :canyon :ecotone :fjord :granite :holocene :isthmus :jovian :azul)
  "OpFork constructors by OpFork.ord (lean/Evm/Optimism/Forks.lean).")
(defconstant +op-canyon+ 1) (defconstant +op-ecotone+ 2) (defconstant +op-fjord+ 3)
(defconstant +op-isthmus+ 6) (defconstant +op-jovian+ 7)

(defun base-op-fork (ts)
  "The OP fork ordinal at TS and the Ethereum fork ordinal its EL rules track."
  (let ((ord (spec-op-base-fork-ord ts)))
    (values ord (spec-op-eth-analog-ord ord))))

;;; --- Chains ------------------------------------------------------------------------------
(defstartup *chain* (or (sb-ext:posix-getenv "EITA_CHAIN") "base"))
(defparameter +chains+
  '(("base"  8453 "base-mainnet")
    ("opt"   10   "opt-mainnet")
    ("world" 480  "worldchain-mainnet")))

;;; --- Predeploys (Bedrock/Spec/FeeVaults.lean, L1Block.lean) ------------------------------
(defconstant +base-fee-vault+      #x4200000000000000000000000000000000000019)
(defconstant +l1-fee-vault+        #x420000000000000000000000000000000000001a)
(defconstant +operator-fee-vault+  #x420000000000000000000000000000000000001b)  ; Isthmus
(defconstant +l1-block+            #x4200000000000000000000000000000000000015)
;; Canyon: op-geth consensus/misc/create2deployer.go (Canyon/Spec/Create2Deployer.lean)
(defconstant +create2deployer+     #x13b0D85CcB8bf860b6b79AF3029fCA081AE9beF2)
(defconstant +create2deployer-code-hash+ #xb0550b5b431e30d38000efb7107aaa0ade03d48a7198a140edda9d27134468b2)
(defconstant +canyon-time+ 1704992401 "Canyon on Base, OP Mainnet and World Chain alike.")

(defvar *op-fork* 0 "The OP fork ordinal of the current block (op-block-setup).")

(defun op-block-setup (n blk ts)
  "OP fork by timestamp; the EVM runs the Ethereum fork it tracks, opcodes, precompiles and
   tx rules alike: Isthmus/Jovian = Prague (EIP-2537, -2935, -7623, -7702), Azul = Osaka
   (CLZ, EIP-7823/7883 MODEXP, EIP-7825 tx gas cap, EIP-7951 P256VERIFY — base/base
   crates/execution/chainspec/src/upgrades.rs:14 'Osaka=Azul', evm/src/config.rs:357;
   CLZ measured live: eth_call of 60011e… on Base returns 255)."
  (declare (ignore blk))
  (multiple-value-bind (op-fork eth-ord) (base-op-fork ts)
    (unless (= eth-ord *fork-ord*)
      (format t "~&block ~D: ~(~A~) -> fork ord ~D~%" n (svref +op-forks+ op-fork) eth-ord)
      (setf *fork-ord* eth-ord)
      (%set-fork eth-ord))
    (setf *op-fork* op-fork
          *el-fork-ord* nil
          ;; 0x100 (Evm.Optimism.Fjord.Spec.p256VerifyGasAt): a precompile — warmed by every
          ;; tx's seed, deposits included (op-geth ActivePrecompiles) — from Fjord, at
          ;; RIP-7212's gas until Azul, Osaka's EIP-7951 from then
          *p256verify* (cond ((>= eth-ord 18) t) ((>= op-fork +op-fjord+) :rip7212))
          ;; Isthmus: withdrawalsRoot is the L2ToL1MessagePasser storage root, not computed
          *chain-header-foreign* (if (>= op-fork +op-isthmus+) '("withdrawalsRoot") '()))))

;;; --- The L1 data fee and the operator fee -------------------------------------------------

(defun l1-block-word (slot)
  "The L1Block predeploy's storage SLOT as the block's deposits left it."
  (fault-account! +l1-block+)
  (fault-slot! +l1-block+ slot)
  (storage-of *current-world* +l1-block+ slot))

(defun tx-l1-fee (tx)
  "spec-op-l1-fee of TX (a user tx): its EIP-2718 bytes and the L1Block slots 1 (L1 base
   fee), 3 (the Ecotone scalars: base-fee at bytes [16:20), blob at [20:24)), 7 (blob base
   fee) and, while those are unset (before Ecotone and in its first block), 5 (overhead) and
   6 (scalar) — op-geth rollup_cost.go 32-98, 151-185. Only the slots the formula reads are
   read."
  (let* ((bytes (tx-envelope tx))
         (zeroes (count 0 bytes))
         (s3 (if (>= *op-fork* +op-ecotone+) (l1-block-word 3) 0))
         (blob (if (>= *op-fork* +op-ecotone+) (l1-block-word 7) 0))
         (bfs (ldb (byte 32 96) s3)) (bbfs (ldb (byte 32 64) s3))
         (bedrock (zerop (+ blob bfs bbfs))))
    (spec-op-l1-fee *op-fork* zeroes (- (length bytes) zeroes)
                    (if (and (>= *op-fork* +op-fjord+) (not bedrock)) (spec-flz-compress-len bytes) 0)
                    (l1-block-word 1)
                    (if bedrock (l1-block-word 5) 0) (if bedrock (l1-block-word 6) 0)
                    blob bfs bbfs)))

(defun tx-operator-fee (gas)
  "spec-op-operator-fee at GAS: L1Block slot 8, scalar at bytes [20:24), constant [24:32)."
  (if (< *op-fork* +op-isthmus+)
      0
      (let ((s8 (l1-block-word 8)))
        (spec-op-operator-fee *op-fork* gas (ldb (byte 32 64) s8) (ldb (byte 64 0) s8)))))

(defvar *tx-l1-fee* 0 "The current user tx's L1 data fee (op-upfront-extra), for the vault.")

(defun op-upfront-extra (tx receipt)
  "Charged upfront with the gas: the L1 data fee and the operator fee at the gas limit
   (op-geth buyGas)."
  (declare (ignore receipt))
  (setf *tx-l1-fee* (tx-l1-fee tx))
  (+ *tx-l1-fee* (tx-operator-fee (tx-gas-limit tx))))

(defun op-fee-settlement (from coinbase egp base-fee gas-used tx receipt)
  "OP fee routing after the unused-gas refund: the priority fee to the coinbase (the derived
   settlement's coinbase half, as on Ethereum), the base fee to BaseFeeVault, the L1 fee to
   L1FeeVault, from Isthmus the operator fee at the gas used to OperatorFeeVault and its
   excess over that at the gas limit back to the sender. Vault credits are deltas."
  (declare (ignore receipt))
  (let ((w *current-world*))
    (spec-coinbase-fee-effect coinbase gas-used egp base-fee)
    (fault-account! +base-fee-vault+)
    (fault-account! +l1-fee-vault+)
    (balance-delta! w +base-fee-vault+ (* base-fee gas-used))
    (balance-delta! w +l1-fee-vault+ *tx-l1-fee*)
    (when (>= *op-fork* +op-isthmus+)
      (let ((at-limit (tx-operator-fee (tx-gas-limit tx))) (at-used (tx-operator-fee gas-used)))
        (balance-delta! w from (- at-limit at-used))
        (fault-account! +operator-fee-vault+)
        (balance-delta! w +operator-fee-vault+ at-used)))))

;;; --- Deposits ----------------------------------------------------------------------------

(defun run-deposit-tx (world tx receipt block-ctx coinbase blk idx)
  "A type-0x7E deposit (Bedrock/Spec/DepositReceipt.lean; op-geth state_transition.go
   execute 474-509): the mint first, then the message without validation or fee — or, when
   one of the message's consensus checks fails, a failed deposit (nonce bumped, status 0, the
   whole gas limit). The receipt extension: the sender's nonce before it, version 1 (Canyon+).
   Returns (values gas-used status egp=0)."
  (let ((from (tx-sender tx)) (mint (or (tx-mint tx) 0)) (gas-limit (tx-gas-limit tx)))
    (observe-tx-begin!)
    (fault-account! from)
    (let ((nonce (nonce-of world from)))
      (when (and receipt (getf receipt :deposit-nonce))
        (gate blk idx "depositNonce" (getf receipt :deposit-nonce) nonce))
      (setf *tx-receipt-extension* (and (>= *op-fork* +op-canyon+) (list nonce 1)))
      (when (plusp mint) (incf (balance-of world from) mint))
      (reset-tx-state)
      (multiple-value-bind (zero nz) (calldata-byte-counts tx)
        (if (= 1 (spec-op-deposit-fails *op-fork* gas-limit (intrinsic-gas tx)
                                        (spec-calldata-floor-gas zero nz (el-fork))
                                        (tx-value tx) (balance-of world from) (length (tx-data tx))
                                        (if (tx-to tx) 0 1)))
            (progn (incf (nonce-of world from))
                   (observe-tx-end! blk idx nil)
                   (values gas-limit 0 0))
            (multiple-value-bind (success exec-used)
                (apply-tx tx coinbase block-ctx :egp 0 :checked nil)
              (let ((gas-used (spec-tx-gas-used (+ (intrinsic-gas tx) exec-used) (ts-refund) zero nz (el-fork))))
                (spec-destroy-effect)
                (spec-sweep-effect)
                (observe-tx-end! blk idx success)
                (values gas-used (if success 1 0) 0))))))))

(defun op-run-tx (world tx receipt block-ctx coinbase blk idx)
  "Deposits (0x7E) have their own rules; every other type is the generic user-tx pipeline
   with the OP hooks (EIP-7702 included, from Isthmus)."
  (if (= (tx-type tx) #x7e)
      (progn (incf (getf *stats* :deposits))
             (run-deposit-tx world tx receipt block-ctx coinbase blk idx))
      (run-evm-tx world tx block-ctx coinbase blk idx :receipt receipt)))

;;; --- Block work ----------------------------------------------------------------------------

(defun create2deployer-code ()
  "The create2Deployer's code (chains/op/create2deployer.hex, op-geth's
   consensus/misc/create2deployer.bin), checked against its code hash."
  (let* ((path (home-relative "chains/op/create2deployer.hex"))
         (code (hex->bytes (string-trim '(#\Space #\Newline #\Return) (alexandria:read-file-into-string path)))))
    (unless (= (octets-int (keccak256-bytes code)) +create2deployer-code-hash+)
      (error "~A does not hash to the create2Deployer code hash" path))
    code))

(defun op-pre-block (world n blk coinbase block-ctx)
  "Canyon's activation block installs the create2Deployer's code before anything runs
   (op-geth state_processor.go:81); then Ethereum's pre-block system calls by the analog
   fork (EIP-4788 when the header has a beacon root, EIP-2935 from Isthmus/Prague)."
  (when (= (blk-timestamp blk) +canyon-time+)
    (fault-account! +create2deployer+)
    (setf (code-of world +create2deployer+) (create2deployer-code)))
  (ethereum-pre-block! world n blk coinbase block-ctx))

(defun da-footprint (txs)
  "Jovian: the header's blobGasUsed (op-geth CalcDAFootprint, specs jovian/exec-engine.md):
   Σ over the user txs of ⌊spec-op-da-size-scaled(FastLZ length) / 1e6⌋ × the scalar from
   the L1-attributes calldata (bytes [176:178)); the activation block's Isthmus-format
   attributes (176 bytes) carry none: 0."
  (let ((data (tx-data (first txs))))
    (if (< (length data) 178)
        0
        (let ((scalar (logior (ash (aref data 176) 8) (aref data 177))))
          (loop for tx in txs
                unless (= (tx-type tx) #x7e)
                  sum (* scalar (floor (spec-op-da-size-scaled (spec-flz-compress-len (tx-envelope tx))) 1000000)))))))

(defun op-post-block (world n blk gas-used coinbase block-ctx)
  "No post-block calls (no rewards, withdrawals or requests); from Jovian the DA footprint is
   what the header's blobGasUsed commits to."
  (declare (ignore world n gas-used coinbase block-ctx))
  (when (>= *op-fork* +op-jovian+)
    (setf *block-blob-gas* (da-footprint (blk-txs blk)))))

;;; --- The chain spec ------------------------------------------------------------------------

(defun op-chain-spec (&optional (chain *chain*))
  "An OP-Stack chain (base | opt | world) as a chain-spec."
  (let ((row (or (assoc chain +chains+ :test #'string=) (error "unknown OP chain ~S" chain))))
    (make-chain-spec
     :name (format nil "OP-Stack ~A" chain) :id (second row)
     :banner "OP fork by timestamp (Superchain schedule)"
     :rpc-url (or (sb-ext:posix-getenv "BASE_RPC_URL")
                  (let ((k (sb-ext:posix-getenv "ALCHEMY_KEY")))
                    (and k (format nil "https://~A.g.alchemy.com/v2/~A" (third row) k))))
     :cache-dir (merge-pathnames (format nil "lean/external/~A-cache/" chain)) ; absolute: renames merge with it
     :prestate-overlay t
     :block-setup #'op-block-setup
     :pre-block #'op-pre-block
     :post-block #'op-post-block
     :header-foreign '("withdrawalsRoot")        ; from Isthmus (set per block by op-block-setup)
     :run-tx #'op-run-tx
     :upfront-extra #'op-upfront-extra
     :fee #'op-fee-settlement)))

(dolist (c '("base" "opt" "world"))
  (let ((c c)) (register-chain-spec c (lambda () (op-chain-spec c)))))

;;; --- Entry ---------------------------------------------------------------------------------

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
