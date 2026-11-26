;;;; chains/op.lisp — OP-Stack chains (Base, OP Mainnet, World Chain) on the generic driver,
;;;; in full state (from the chain's genesis alloc or an anchored snapshot) or lazily (a block
;;;; source that serves state). Everything the OP Stack changes about an Ethereum block is a
;;;; chain-spec hook here; every rule in it is the Lean spec's (lean/Evm/Optimism/):
;;;;
;;;;   fork          the OP fork by timestamp and the Ethereum fork it tracks: the emitted
;;;;                 spec-op-base-fork-ord / spec-op-eth-analog-ord (Replay.Emit, proved =
;;;;                 OpFork.baseMainnetAt / ethereumAnalog). Base's schedule; OP Mainnet and
;;;;                 World Chain share the Superchain times from Ecotone (their Canyon is
;;;;                 the same timestamp too); Azul, Beryl, Cobalt and Denim are Base's alone
;;;;                 (refused on the others).
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
;;;;                 of the empty withdrawals list and is compared. From Denim the timestamp
;;;;                 is the schedule's (spec-op-denim-block-ms: 200 ms blocks, Denim/Spec/
;;;;                 BaseTime.lean) and tx[1] is the BaseTime metadata deposit carrying its
;;;;                 millisecond part.
;;;;   native        Base from Beryl: stateful native precompiles (the B-20 factory and
;;;;   precompiles   tokens, the policy and activation registries; from Cobalt the
;;;;                 transaction-context and nonce-manager precompiles), classified by
;;;;                 spec-op-native-kind (Beryl/Spec/NativePrecompiles.lean). Their logic is
;;;;                 base/base's, linked unchanged (rust/base → c/libeita_base); every world
;;;;                 operation it performs is the engine's, priced by the emitted
;;;;                 spec-op-native-*-gas. The installed ones are warm from each tx's start.
;;;;                 Denim's first block installs the BaseTime predeploy's implementation.
;;;;
;;;; Run: eita replay --chain base|opt|world --from N [--to M] --genesis FILE (full state, the
;;;; default; OP_CACHE_DIR = the block chunks) or --lazy with a block source that serves state.

(in-package #:eita.chain.op)

;;; --- Fork schedule ---------------------------------------------------------------------

(defparameter +op-forks+ #(:bedrock :canyon :ecotone :fjord :granite :holocene :isthmus :jovian :azul
                           :beryl :cobalt :denim)
  "OpFork constructors by OpFork.ord (lean/Evm/Optimism/Forks.lean).")
(defconstant +op-canyon+ 1) (defconstant +op-ecotone+ 2) (defconstant +op-fjord+ 3)
(defconstant +op-isthmus+ 6) (defconstant +op-jovian+ 7) (defconstant +op-azul+ 8)
(defconstant +op-beryl+ 9) (defconstant +op-cobalt+ 10) (defconstant +op-denim+ 11)

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
    ;; Azul and after are Base's own forks: on another OP chain these times mean nothing
    (when (and (>= op-fork +op-azul+) (string/= *chain* "base"))
      (error "block ~D (ts ~D): ~(~A~) is Base's fork, not ~A's (lean/Evm/Optimism/Forks.lean)"
             n ts (svref +op-forks+ op-fork) *chain*))
    ;; Denim: the header's seconds are the schedule's (consensus/src/lib.rs:206-218)
    (when (= 1 (spec-op-denim-p n))
      (gate n "header" "timestamp (Denim schedule)" (floor (spec-op-denim-block-ms n) 1000) ts))
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
      (op-tx-prewarm! from (tx-to tx) (tx-value tx))
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
  ;; the environment a native precompile reads (a tx straight to one runs no frame to set it)
  (setf eita.evm::*tx-origin* (tx-sender tx) eita.evm::*tx-coinbase* coinbase
        eita.evm::*tx-number* (getf block-ctx :number) eita.evm::*tx-timestamp* (getf block-ctx :timestamp))
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
  (ethereum-pre-block! world n blk coinbase block-ctx)
  (when (>= *op-fork* +op-denim+)
    (ensure-base-time! world n)
    (check-base-time-deposit n (second (blk-txs blk)))))

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

;;; --- Denim: BaseTime (Denim/Spec/BaseTime.lean) -------------------------------------------

(defconstant +base-time+ #x4200000000000000000000000000000000000030)
(defconstant +base-time-impl+ #xc0D3C0d3C0d3C0D3c0d3C0d3c0D3C0d3c0d30030)
(defconstant +base-time-impl-code-hash+ #x9c4c8a497a69d0b8f2ba67be0bee7a1373186055978c3be6ec3068e0ec27f32a)
(defconstant +eip1967-impl-slot+ #x360894a13ba1a3210667c828492db98dca3e2076cc3735a920a3ca505d382bbc)
(defconstant +eip1967-admin-slot+ #xb53127684a568b3173ae13b9f8a6016e243e63b6e8ee1178d6a717850b5d6103)
(defconstant +proxy-admin+ #x4200000000000000000000000000000000000018)
(defconstant +depositor+ #xDeaDDEaDDeAdDeAdDEAdDEaddeAddEAdDEAd0001)

(defun base-time-code ()
  "BaseTime's runtime (chains/op/base-time.hex, base/base evm/src/bytecode/base-time.hex),
   checked against its code hash."
  (let* ((path (home-relative "chains/op/base-time.hex"))
         (code (hex->bytes (string-trim '(#\Space #\Newline #\Return) (alexandria:read-file-into-string path)))))
    (unless (= (octets-int (keccak256-bytes code)) +base-time-impl-code-hash+)
      (error "~A does not hash to BaseTime's code hash" path))
    code))

(defun ensure-base-time! (world n)
  "BaseTime::ensure_predeploy (Spec.BaseTime.ensurePredeploy; evm/src/base_time.rs:96-150):
   while the proxy's implementation slot is zero, the proxy must have code and ProxyAdmin as
   its admin, and the implementation is installed and linked."
  (fault-slot! +base-time+ +eip1967-impl-slot+)
  (when (zerop (storage-of world +base-time+ +eip1967-impl-slot+))
    (fault-account! +base-time+)
    (fault-slot! +base-time+ +eip1967-admin-slot+)
    (cond ((zerop (length (code-of world +base-time+)))
           (invalid! "BaseTime" "block ~D: the BaseTime proxy has no code" n))
          ((/= (storage-of world +base-time+ +eip1967-admin-slot+) +proxy-admin+)
           (invalid! "BaseTime" "block ~D: the BaseTime proxy's admin is not ProxyAdmin" n)))
    (fault-account! +base-time-impl+)
    (setf (code-of world +base-time-impl+) (base-time-code)
          (storage-of world +base-time+ +eip1967-impl-slot+) +base-time-impl+)))

(defun base-time-source-hash (n)
  "source.rs:112-124: keccak256(3 as a 32-byte word ‖ keccak256(N as a 32-byte word))."
  (flet ((word (x) (let ((v (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)))
                     (loop for i below 32 do (setf (aref v (- 31 i)) (ldb (byte 8 (* 8 i)) x)))
                     v)))
    (octets-int (keccak256-bytes (concatenate '(vector (unsigned-byte 8))
                                              (word 3) (keccak256-bytes (word n)))))))

(defun base-time-millis (data)
  "Spec.BaseTime.decodeCalldata: setTimestampMillisPart(uint16) with 30 zero padding bytes
   and a 200 ms slot below 1000, or NIL."
  (when (and (= (length data) 36)
             (= (octets-int (subseq data 0 4)) #x86bdf394)
             (every #'zerop (subseq data 4 34)))
    (let ((ms (+ (* 256 (aref data 34)) (aref data 35))))
      (and (< ms 1000) (zerop (mod ms 200)) ms))))

(defun check-base-time-deposit (n tx)
  "Spec.BaseTime.metadataOk (base_time.rs:166-198, 148-164): tx[1] is the BaseTime deposit of
   block N — from the depositor to BaseTime, no mint or value, 1,000,000 gas, not a system
   tx, the domain-3 source hash of N — and its millisecond part is the schedule's."
  (let ((want (list #x7e +depositor+ +base-time+ 0 0 1000000 nil (base-time-source-hash n)
              (mod (spec-op-denim-block-ms n) 1000)))
        (got (and tx (list (tx-type tx) (tx-sender tx) (tx-to tx) (or (tx-mint tx) 0) (tx-value tx)
                      (tx-gas-limit tx) (and (tx-system-p tx) t) (tx-source-hash tx)
                      (base-time-millis (tx-data tx))))))
    (unless (equal want got) (gate n 1 "BaseTime deposit" want got))))

;;; --- Native precompiles (Beryl/Spec/NativePrecompiles.lean) -------------------------------
;;; The logic is base/base's own (rust/base, c/libeita_base: eita_base_precompile); this is
;;; its host. Each callback below performs one world operation the way the EVM opcode it
;;; stands for does (the same access sets, journal and originals) and returns that opcode's
;;; price from the emitted spec-op-native-*-gas.

(defcfun ("eita_base_precompile" %base-precompile) :int
  (host :pointer) (env :pointer) (op-fork :uint32) (addr :pointer) (caller :pointer)
  (value :pointer) (is-static :uint32) (direct :uint32) (input :pointer) (input-len :uint64)
  (gas :uint64) (outcome :pointer))
(defcfun ("eita_base_precompile_kind" %base-precompile-kind) :uint32 (addr :pointer) (op-fork :uint32))
(defcfun ("eita_base_free" %base-free) :void (p :pointer) (n :uint64))
(defcfun ("eita_ts_tload" %ts-tload) :void (ts :pointer) (addr :pointer) (slot :pointer) (out :pointer))
(defcfun ("eita_ts_tstore" %ts-tstore) :void (ts :pointer) (ar :pointer) (addr :pointer) (slot :pointer) (val :pointer))

(defparameter +native-warm+
  '((#xB20F000000000000000000000000000000000000 . 1) (#x8453000000000000000000000000000000000002 . 2)
    (#x8453000000000000000000000000000000000001 . 3) (#x813000000000000000000000000000000000aa02 . 6)
    (#x813000000000000000000000000000000000aa01 . 7))
  "The installed native precompiles (address . kind): Spec.warmAtTxStart's addresses.")

(defun op-tx-prewarm! (from to value)
  "From Beryl the installed native precompiles are in every tx's warm set (alloy-evm
   warm_addresses = the precompile map's keys), like Ethereum's; the tokens are not."
  (declare (ignore from to value))
  (when (>= *op-fork* +op-beryl+)
    (loop for (a . k) in +native-warm+
          when (= (spec-op-native-kind *op-fork* a) k) do (access-addr! a))))

(defun op-native-precompile-p (addr)
  (and (>= *op-fork* +op-beryl+) (plusp (spec-op-native-kind *op-fork* addr))))

(defstartup *base-lib* nil "T once libeita_base is open (in this process).")
(defstartup *native-buf* nil "Foreign scratch: the env (64), the outcome (56), addresses and words.")

(defun base-ensure-lib! ()
  "Open libeita_base on first use (native/libraries.lisp's search); loud when absent."
  (unless *base-lib*
    (load-foreign-library (native-path "libeita_base"))
    (check-cached-foreign-pointers! "loading c/libeita_base")
    (setf *base-lib* t
          *native-buf* (foreign-alloc :uint8 :count 512))))

(defun be-read (p n)
  (loop with v = 0 for i below n do (setf v (logior (ash v 8) (mem-aref p :uint8 i))) finally (return v)))
(defun be-write (p n x)
  (loop for i below n do (setf (mem-aref p :uint8 (- n 1 i)) (ldb (byte 8 (* 8 i)) x))))

(defvar *native-code* #() "The code OP 5's phase 0 looked up, for phase 1's copy.")

(defun native-word (p) (be-read p 32))

(defun native-u256 (scratch x) (u256-write scratch x) scratch)

(defcallback op-native-host :uint64
    ((op :uint32) (phase :uint32) (a :pointer) (b :pointer) (c :pointer) (n :uint64)
     (out :pointer) (aux :pointer))
  "rust/base's HostFn: one world operation per OP (lib.rs OP_*), returning its price."
  (let ((w *current-world*))
    (flet ((f (x) (if x 1 0)))
      (case op
        ;; SLOAD and SSTORE load the account first, warming it (alloy-evm traits.rs:317-326:
        ;; load_account_mut), at no charge of their own
        (0 (let ((ad (be-read a 20)) (k (native-word b)))                ; SLOAD
             (fault-account! ad) (access-addr! ad)
             (fault-slot! ad k)
             (let ((cold (access-slot! ad k)))
               (be-write out 32 (storage-of w ad k))
               (spec-op-native-sload-gas (f cold)))))
        (1 (if (<= n (spec-op-native-sstore-sentry))                     ; SSTORE (EIP-2200 sentry)
               (1- (ash 1 64))
               (let ((ad (be-read a 20)) (k (native-word b)) (new (native-word c)))
                 (fault-account! ad) (access-addr! ad)
                 (fault-slot! ad k)
                 (let* ((cold (access-slot! ad k))
                        (cur (storage-of w ad k))
                        (orig (progn (orig-record! ad k cur) (orig-get! ad k cur))))
                   (setf (mem-ref aux :int64)
                         (- (spec-op-native-sstore-refund-add (f (= new cur)) (f (= cur orig)) (f (zerop orig))
                                                              (f (zerop cur)) (f (zerop new)) (f (= new orig)))
                            (spec-op-native-sstore-refund-sub (f (= new cur)) (f (= cur orig)) (f (zerop orig))
                                                              (f (zerop cur)))))
                   (unless (= new cur)
                     (journal-push! (current-arena) 0 ad k cur)
                     (setf (storage-of w ad k) new))
                   (spec-op-native-sstore-gas (f cold) (f (= new cur)) (f (= cur orig)) (f (zerop orig)))))))
        (2 (let ((buf *native-buf*))                                     ; TLOAD
             (%ts-tload eita.evm::*tx-state* (native-u256 (inc-pointer buf 128) (be-read a 20))
                        (native-u256 (inc-pointer buf 160) (native-word b)) (inc-pointer buf 192))
             (be-write out 32 (u256-read (inc-pointer buf 192)))
             (if (= phase 0) (spec-op-native-transient-gas) 0)))
        (3 (if (= phase 0)                                               ; TSTORE
               (spec-op-native-transient-gas)
               (let ((buf *native-buf*))
                 (%ts-tstore eita.evm::*tx-state* (current-arena) (native-u256 (inc-pointer buf 128) (be-read a 20))
                             (native-u256 (inc-pointer buf 160) (native-word b))
                             (native-u256 (inc-pointer buf 192) (native-word c)))
                 0)))
        (4 (let ((ad (be-read a 20)))                                    ; account info
             (fault-account! ad)
             (let ((cold (access-addr! ad)) (code (code-of w ad)))
               (be-write out 32 (balance-of w ad))
               (be-write (inc-pointer out 32) 8 (nonce-of w ad))
               (be-write (inc-pointer out 40) 32 (if (plusp (length code)) (code-hash-int code) eita.evm::+empty-code-hash+))
               (spec-op-native-account-gas (f cold)))))
        (5 (let ((ad (be-read a 20)))                                    ; account code
             (if (= phase 0)
                 (progn (fault-account! ad)
                        (let ((cold (access-addr! ad)))
                          (setf *native-code* (code-of w ad)
                                (mem-ref aux :int64) (length *native-code*))
                          (spec-op-native-account-gas (f cold))))
                 (progn (loop for i below n do (setf (mem-aref out :uint8 i) (aref *native-code* i)))
                        0))))
        (6 (case phase                                                   ; install code
             (0 (spec-op-native-code-deposit-gas n))
             (1 (let ((ad (be-read a 20)))
                  (fault-account! ad)
                  (access-addr! ad)
                  (if (zerop (length (code-of w ad))) (spec-op-native-new-code-gas n) 0)))
             (t (let ((ad (be-read a 20))
                      (code (let ((v (make-array n :element-type '(unsigned-byte 8))))
                              (dotimes (i n v) (setf (aref v i) (mem-aref b :uint8 i))))))
                  ;; revm journals a code change; here (a fresh token account, the factory's
                  ;; collision rule) the creation entry undoes it, and the existence mark its own
                  (eita.evm::mark-account-present! (current-arena) ad)
                  (journal-push! (current-arena) 10 ad 0 1)
                  (setf (code-of w ad) code)
                  0))))
        (7 (spec-op-native-log-gas (mem-ref aux :int64) n))              ; log price
        (8 (spec-op-native-keccak-gas n))                                ; keccak price
        (9 (mem-ref (current-arena) :uint64 0))                          ; checkpoint
        (10 (eita.evm::revert-journal-to (current-arena) n) 0)                     ; revert to it
        (t (error "libeita_base asked for host op ~D" op))))))

(defun native-emit-logs! (p len)
  "The precompile's packed logs (lib.rs Outcome.logs), in order, as LOGs of the frame."
  (let ((i 0))
    (loop while (< i len)
          do (let* ((ad (be-read (inc-pointer p i) 20))
                    (nt (mem-aref p :uint8 (+ i 20)))
                    (topics (loop for k below nt collect (be-read (inc-pointer p (+ i 21 (* 32 k))) 32)))
                    (j (+ i 21 (* 32 nt)))
                    (dl (be-read (inc-pointer p j) 8))
                    (data (let ((v (make-array dl :element-type '(unsigned-byte 8))))
                            (dotimes (q dl v) (setf (aref v q) (mem-aref p :uint8 (+ j 8 q)))))))
               (observe-log! ad topics data)
               (setf i (+ j 8 dl))))))

(defun op-native-precompile-run (addr kind caller input-ptr input-len gas is-static value)
  "The chain-precompile hook (Spec.NativePrecompiles' boundary): base/base's precompile at
   ADDR for this OP fork; KIND 1/2 (CALLCODE, DELEGATECALL) is not a direct call. A success
   adds its refund and emits its logs; a revert keeps its unspent gas; a halt spends all.
   Returns (values gas-used output success)."
  (base-ensure-lib!)
  (incf (getf *stats* :native-calls 0))
  (let* ((buf *native-buf*) (env buf) (outcome (inc-pointer buf 64)) (a (inc-pointer buf 224))
         (cl (inc-pointer buf 256)) (v (inc-pointer buf 288)))
    (setf (mem-ref env :uint64 0) *chain-id* (mem-ref env :uint64 8) eita.evm::*tx-number*
          (mem-ref env :uint64 16) eita.evm::*tx-timestamp*)
    (be-write (inc-pointer env 24) 20 eita.evm::*tx-coinbase*)
    (be-write (inc-pointer env 44) 20 eita.evm::*tx-origin*)
    (be-write a 20 addr) (be-write cl 20 caller) (be-write v 32 value)
    (dotimes (i 56) (setf (mem-aref outcome :uint8 i) 0))
    (let ((rc (%base-precompile (callback op-native-host) env *op-fork* a cl v (if is-static 1 0)
                                (if (or (= kind 1) (= kind 2)) 0 1)
                                (if (plusp input-len) input-ptr (null-pointer)) input-len gas outcome)))
      (let* ((status (mem-ref outcome :uint32 0)) (used (mem-ref outcome :uint64 8))
             (refund (mem-ref outcome :int64 16))
             (op (mem-ref outcome :pointer 24)) (on (mem-ref outcome :uint64 32))
             (lp (mem-ref outcome :pointer 40)) (ln (mem-ref outcome :uint64 48))
             (bytes (let ((o (make-array on :element-type '(unsigned-byte 8))))
                      (dotimes (i on o) (setf (aref o i) (mem-aref op :uint8 i))))))
        (%base-free op on)
        (case rc
          (-1 (error "~40,'0x: the engine's classification (spec-op-native-kind ~D) and ~
                      libeita_base's (~D) disagree" addr (spec-op-native-kind *op-fork* addr)
                      (%base-precompile-kind a *op-fork*)))
          (-2 (error "native precompile ~40,'0x: fatal: ~A" addr (map 'string #'code-char bytes))))
        (when *trace-frames*
          (format *error-output* "~&[native] ~40,'0x status=~D used=~D refund=~D out=~D logs=~D~%"
                  addr status used refund on ln))
        (when (= status 0)
          (native-emit-logs! lp ln)
          (unless (zerop refund) (eita.evm::refund-add! refund)))
        (%base-free lp ln)
        (values used bytes (= status 0))))))

;;; --- The chain spec ------------------------------------------------------------------------

(defun op-chain-spec (&optional (chain *chain*))
  "An OP-Stack chain (base | opt | world) as a chain-spec."
  (let ((row (or (assoc chain +chains+ :test #'string=) (error "unknown OP chain ~S" chain))))
    (make-chain-spec
     :name (format nil "OP-Stack ~A" chain) :id (second row)
     ;; not in the repository (9 MB for Base): docs/block-input.md says where it comes from
     :genesis-path (format nil "chains/~A/genesis.json" chain)
     :banner "OP fork by timestamp (Superchain schedule)"
     :rpc-url (or (sb-ext:posix-getenv "BASE_RPC_URL")
                  (let ((k (sb-ext:posix-getenv "ALCHEMY_KEY")))
                    (and k (format nil "https://~A.g.alchemy.com/v2/~A" (third row) k))))
     ;; OP_CACHE_DIR: the supervisor's block chunks; absolute either way (a source's renames
     ;; merge with it)
     :cache-dir (merge-pathnames (let ((d (sb-ext:posix-getenv "OP_CACHE_DIR")))
                                   (cond ((or (null d) (zerop (length d))) (format nil "lean/external/~A-cache/" chain))
                                         ((char= (char d (1- (length d))) #\/) d)
                                         (t (concatenate 'string d "/")))))
     :prestate-overlay t
     :block-setup #'op-block-setup
     :pre-block #'op-pre-block
     :post-block #'op-post-block
     :header-foreign '("withdrawalsRoot")        ; from Isthmus (set per block by op-block-setup)
     :run-tx #'op-run-tx
     :tx-prewarm #'op-tx-prewarm!
     :precompile-p #'op-native-precompile-p
     :precompile-run #'op-native-precompile-run
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
  (format t "source: rpc-calls=~D offline-misses=~D native-precompile-calls=~D~%"
          *rpc-calls* *offline-misses* (getf *stats* :native-calls 0))
  (sb-ext:exit :code (if (and (zerop (getf *stats* :mismatches)) (zerop *offline-misses*)) 0 1)))
