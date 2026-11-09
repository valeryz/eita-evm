;;;; chains/arc.lisp — Circle Arc (testnet) replay with lazy RPC-backed state.
;;;;
;;;; Arc is Circle's EVM L1 (Malachite BFT, USDC-native-gas, EVM = Osaka +
;;;; EIP-7708). It is NOT OP-Stack, so this driver reuses chains/op.lisp's
;;;; tested RPC transport / fetchers / fault hooks / tx+receipt parsers (loaded
;;;; as a library) but drives a *vanilla-L1* per-tx fee model — no L1 data fee,
;;;; no fee vaults, no operator fee, no deposited txs.
;;;;
;;;; The point is a DIFFERENTIAL: Eita executes each real Arc tx and we compare
;;;; our gasUsed to the on-chain receipt. gasUsed depends only on execution
;;;; semantics (opcodes / gas schedule / precompiles), NOT on Arc's no-burn fee
;;;; routing — so matches prove we run Arc correctly, and any delta localizes an
;;;; Arc-specific semantic (candidate: EIP-7708 value-transfer logs, or a native
;;;; predeploy at a reserved address like 0x3600…00) rather than a fee artifact.
;;;;
;;;; Fork: Arc = Osaka; the native dispatch runs fork ordinal 18 (`%set-fork 18` in the
;;;; block loop). Transaction settlement (refund cap, EIP-7623 calldata floor) is the
;;;; generic src/evm/run-tx.lisp over the Lean-emitted spec-tx-gas-used.
;;;;
;;;; Run: eita replay --chain arc-mainnet|arc-testnet --from N [--to M | --to tip] …
;;;;   (Arc testnet RPC is public: default https://rpc.testnet.arc.io, override
;;;;    with ARC_RPC_URL. EITA_NO_JIT=1 for interp-only. EITA_OBSERVER=<file>
;;;;    installs an observer — see src/evm/ "Observation seam".)


;; Generic chain I/O (RPC/cache/block batches/lazy state/parsing) with the EVM host
;; (src/evm/) underneath — chain-neutral; nothing OP-Stack is loaded.
(in-package #:eita.chain.arc)

(defstartup *arc-net* (or (sb-ext:posix-getenv "ARC_CHAIN") "testnet")
  "testnet (5042002, rpc.testnet.arc.io) or mainnet (5042, rpc.mainnet.arc.io).")
(defun arc-net-chain-id (net) (if (string= net "mainnet") 5042 5042002))   ; native currency USDC
(defstartup +arc-chain-id+ (arc-net-chain-id *arc-net*))
;; ArcHardfork::Zero8 activation by timestamp (arc-node execution-config/src/hardforks.rs:410-411).
(defconstant +arc-zero6-ts-testnet+ 1779894517)   ; hardforks.rs:400 (mainnet: from genesis)
(defconstant +arc-zero8-ts-testnet+ 1788447600)
;; Zero7 (hardforks.rs:405-407): CallFrom (0x1800…0003) is only registered from Zero7
;; (evm.rs:1672 + its test "CallFrom should be registered when Zero7 is active"); before
;; it the address holds the genesis 1-byte placeholder 0x01, so a call there halts
;; exceptionally and burns the whole forwarded pool.
(defconstant +arc-zero7-ts-testnet+ 1781791200)
(defconstant +arc-zero7-ts-mainnet+ 1789052400)
(defconstant +arc-zero8-ts-mainnet+ 1789052400)

(defun arc-fee-settlement (from coinbase egp base-fee gas-used tx receipt)
  "Arc fee routing: the WHOLE fee to the coinbase — Arc does not burn the base fee, so the
   derived settlement runs with a zero base fee."
  (declare (ignore from base-fee tx receipt))
  (spec-coinbase-fee-effect coinbase gas-used egp 0))

(defun arc-pre-block! (world n blk coinbase block-ctx)
  "executor.rs apply_pre_execution_changes: Arc runs EIP-2935 only (no EIP-4788 beacon
   root), even though its EL fork is Osaka."
  (declare (ignore world coinbase))
  (eip2935-store-parent-hash! n (blk-parent-hash blk) block-ctx))

(defvar *arc-system-precompiles-warm* nil
  "True for a post-block system call after a block with transactions: revm's journal keeps
   the precompile addresses a tx's pre_execution warmed (Evm.Arc.Spec.BlockSystem).")

(defun arc-system-rule (target block-ctx)
  "arc-node's system call (Evm.Arc.Spec.BlockSystem.systemRule; revm-handler run_system_call,
   evm.rs:1557-1597): the target warm (the first frame loads it), NativeCoinControl from Zero7
   (evm.rs:1576-1583), the precompiles after a block's txs; GASPRICE 0 (the system TxEnv has
   no gas price); the end of tx runs (revm's commit destroys the selfdestructed and clears
   touched empty accounts)."
  (declare (ignore block-ctx))
  (values (append (list target)
                  (when *arc-zero7* (list +arc-native-coin-control+))
                  (when *arc-system-precompiles-warm* (precompile-seed-addrs)))
          t 0))

(defun arc-post-block! (world n blk gas-used coinbase block-ctx)
  "executor.rs apply_post_block_writes: feeParams() (system call; NIL on failure →
   chainspec defaults), compute_gas_values, storeGasValues(n, …). Gated against the
   header\'s extra_data (8-byte big-endian nextBaseFee), which the client itself
   validates (validate_extra_data_base_fee)."
  (declare (ignore coinbase))
  (unless (string= *arc-net* "mainnet")
    (error "post-block SystemAccounting model carries the MAINNET BaseFeeConfig only"))
  (observe-tx-begin!)
  (let* ((fp (multiple-value-bind (ok out)
                 (let ((*arc-system-precompiles-warm* (plusp gas-used)))   ; a tx ran (≥ 21000 gas)
                   (system-call +arc-protocol-config+
                                (coerce #(#x92 #x42 #x16 #x4f) '(simple-array (unsigned-byte 8) (*)))
                                block-ctx))
               (and ok (arc-decode-fee-params out))))
         (gas-limit (blk-gas-limit blk))
         (base-fee (or (blk-base-fee blk) 0))
         (parent-smoothed (nth-value 1 (arc-read-gas-values world (max 0 (1- n))))))
    (multiple-value-bind (smoothed next-base-fee)
        (arc-compute-gas-values n gas-used gas-limit base-fee parent-smoothed fp)
      (arc-store-gas-values! world n gas-used smoothed next-base-fee)
      (let ((extra (blk-extra-data blk)))
        (when (and extra (= (length extra) 8))
          (let ((hdr-next (octets-int extra)))
            (unless (= hdr-next next-base-fee)
              (error "block ~D: computed nextBaseFee ~D ≠ header extra_data ~D (feeParams ~A)"
                     n next-base-fee hdr-next (if fp "ok" "unavailable"))))))))
  (observe-tx-end! n +postblock-tx+ t))

(defun arc-block-setup (n blk ts)
  "Per block: Arc's EL fork (Osaka: +CLZ, +P256VERIFY, EIP-7702 delegation) and its
   hardfork flags by timestamp (arc-node execution-config hardforks.rs)."
  (declare (ignore blk))
  (unless (= *fork-ord* 18) (setf *fork-ord* 18) (%set-fork 18))   ; run-block: delegation on (≥ Prague)
  (let ((mainnet (= +arc-chain-id+ 5042)))
    (setf *arc-zero8* (>= ts (if mainnet +arc-zero8-ts-mainnet+ +arc-zero8-ts-testnet+))
          *arc-zero6* (or mainnet (>= ts +arc-zero6-ts-testnet+))
          *arc-zero7* (>= ts (if mainnet +arc-zero7-ts-mainnet+ +arc-zero7-ts-testnet+))))
  (unless *arc-zero6*
    (error "block ~D (ts ~D) is pre-Zero6: its precompile gas rules are not in arc-node HEAD — not reproducible from the spec (testnet Zero6 = ts ~D)" n ts +arc-zero6-ts-testnet+)))

(defun arc-chain-spec (&optional (net *arc-net*))
  "Arc as a chain-spec: everything Arc changes about the generic replay."
  (let ((mainnet (string= net "mainnet")))
    (make-chain-spec
     :name (format nil "Arc ~A" net) :id (arc-net-chain-id net)
     :genesis-path (format nil "lean/external/arc-cache/genesis-~A.json" (if mainnet "mainnet" "testnet"))
     :banner "fork=Osaka(18) + EIP-7623"
     :reorg-depth 0                               ; BFT finality: a block never reverts
     :rpc-url (or (sb-ext:posix-getenv "ARC_RPC_URL")
                  (if mainnet "https://rpc.mainnet.arc.io" "https://rpc.testnet.arc.io"))
     ;; ARC_CACHE_DIR: the supervisor's own $CACHE. Without it every supervisor on a box
     ;; shared lean/external's — the fault-injection twins read and wrote production's.
     :cache-dir (pathname (let ((d (sb-ext:posix-getenv "ARC_CACHE_DIR")))
                            (if (and d (plusp (length d)))
                                (if (char= (char d (1- (length d))) #\/) d (concatenate 'string d "/"))
                                (if mainnet "lean/external/arc-mainnet-cache/" "lean/external/arc-cache/"))))
     :block-setup #'arc-block-setup               ; Osaka table + Zero6/7/8 by timestamp
     :pre-block #'arc-pre-block!                  ; EIP-2935 only (no EIP-4788)
     :post-block #'arc-post-block!                ; SystemAccounting storeGasValues
     :system-rule #'arc-system-rule               ; revm run_system_call: target warm, GASPRICE 0
     :tx-prewarm #'arc-tx-prewarm!                ; handler.rs check_blocklist: unmetered warming
     :fee #'arc-fee-settlement                    ; whole fee to the coinbase, no burn
     :precompile-p #'arc-precompile-p             ; 0x1800… native USDC, PQ, CallFrom (Zero7+)
     :precompile-run #'arc-precompile-run
     :frame-init #'arc-value-transfer-prewarm!    ; zero-address / blocklist / destructed reverts
     :frame-init-log #'arc-value-transfer-log!    ; EIP-7708 transfer logs
     :selfdestruct #'arc-selfdestruct-check
     :p256verify t                                ; EIP-7951 at 0x100 (block 1888235 = first use)
     ;; Call frames on (owner, 2026-11-09: the execution-gas views). A deliberate migration: a
     ;; live replay records them from its switch block on; full history comes from a re-replay
     ;; from genesis in its own directory, swapped in at the tip (docs/eth-protocol-views.md §7.3).
     :observe-kinds '(:storage_diff :account_diff :transfer :log :tx :block :call))))

(register-chain-spec "arc-mainnet" (lambda () (arc-chain-spec "mainnet")))
(register-chain-spec "arc-testnet" (lambda () (arc-chain-spec "testnet")))

(defun main-arc (args &optional (net *arc-net*))
  "Install Arc (NET: testnet or mainnet), then run the generic driver (chains/driver.lisp)."
  (setf *arc-net* net +arc-chain-id+ (arc-net-chain-id net))
  (install-chain-spec! (arc-chain-spec net))
  (replay-main args))

