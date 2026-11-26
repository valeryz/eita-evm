;;;; tests/avalanche.lisp — unit tests for Avalanche C-Chain (Etna -> Fortuna -> Granite -> Helicon/SAE).
;;;;
;;;; Checks:
;;;;   1. Lean-emitted spec-avax-* fork schedules (Mainnet & Fuji) and pre-Etna refusal.
;;;;   2. Coreth disables EVM gas refunds and credits full fee to coinbase.
;;;;   3. Helicon / SAE minimum gas floor ceil(gasLimit / 2) via spec-avax-tx-gas-used.
;;;;   4. SAE executed base fee extraction from dynamic-fee receipts.
;;;;   5. Granite P-256 precompile (0x100) activation by timestamp.
;;;;   6. Avalanche atomic batch codec v0 (empty + gas formula via spec-avax-atomic-tx-gas).
;;;;   7. Warp Messenger precompile: getBlockchainID, sendWarpMessage, getVerifiedWarpMessage,
;;;;      getVerifiedWarpBlockHash, header.extraData BlockResults parsing, predicate gas withholding.
;;;;   8. SAE GasClock (gasclock-from-settled, before-block!, base-fee, after-block!).
;;;;   9. Coreth storage-trie key normalization (slot[0] &= 0xfe) and 5-field multiCoin account RLP.

(in-package #:eita.evm)

(let ((pass 0) (fail 0))
  (labels ((chk (label ok &optional detail)
             (if ok
                 (progn (incf pass) (format t "  PASS  ~A~%" label))
                 (progn (incf fail) (format t "  FAIL  ~A~@[: ~A~]~%" label detail))))
           (run-avax-tx (world tx &key (sae nil) (base-fee 25) (ts 1789110499) (warp-results nil))
             (let* ((coinbase #x0100000000000000000000000000000000000000)
                    (spec (eita.chain.avalanche:avalanche-chain-spec "mainnet"))
                    (af (if sae 4 3))
                    (eita.evm::*current-world* world)
                    (eita.evm::*cur-block* 96000000)
                    (eita.evm::*cur-tx* 0)
                    (eita.evm::*receipt-cumulative-gas* 0)
                    (eita.chain.avalanche::*avalanche-fork-ord* af)
                    (eita.chain.avalanche::*avalanche-sae-block* sae)
                    (eita.chain.avalanche::*avalanche-exec-base-fee* base-fee)
                    (eita.chain.avalanche::*avalanche-block-gas-limits* 0)
                    (eita.chain.avalanche::*avalanche-warp-results* warp-results)
                    (block-ctx (list :timestamp ts :number 96000000 :base-fee base-fee
                                     :gas-limit 30000000 :prev-randao 0 :coinbase coinbase
                                     :chain-id 43114 :excess-blob-gas 0 :blob-base-fee 1)))
               (eita.chain:install-chain-spec! spec)
               (unless (= *fork-ord* 16) (setf *fork-ord* 16) (%set-fork 16))
               (setf *p256verify* (>= ts 1763568000) *prague-delegation* nil)
               (funcall (eita.chain::chain-spec-run-tx spec) world tx nil block-ctx coinbase 96000000 0))))

    ;; 1. Lean-emitted fork schedule & pre-Etna refusal
    (chk "spec-avax-mainnet-fork-ord pre-Etna = 0" (= (spec-avax-mainnet-fork-ord 1734364799) 0))
    (chk "spec-avax-mainnet-fork-ord Etna = 1"     (= (spec-avax-mainnet-fork-ord 1734364800) 1))
    (chk "spec-avax-mainnet-fork-ord Fortuna = 2"  (= (spec-avax-mainnet-fork-ord 1744124400) 2))
    (chk "spec-avax-mainnet-fork-ord Granite = 3"  (= (spec-avax-mainnet-fork-ord 1763568000) 3))
    (chk "spec-avax-mainnet-fork-ord Helicon = 4"  (= (spec-avax-mainnet-fork-ord 1790089200) 4))
    (chk "spec-avax-fuji-fork-ord Helicon = 4"     (= (spec-avax-fuji-fork-ord 1788274800) 4))
    (chk "spec-avax-extradata-offset Etna=80 Fortuna=24 Helicon=0"
         (and (= (spec-avax-extradata-offset 1) 80)
              (= (spec-avax-extradata-offset 2) 24)
              (= (spec-avax-extradata-offset 3) 24)
              (= (spec-avax-extradata-offset 4) 0)))
    (let ((spec (eita.chain.avalanche:avalanche-chain-spec "mainnet"))
          (dummy-blk (eita.input::make-chain-block :number 1000 :base-fee 25 :gas-limit 30000000))
          (refused nil))
      (handler-case
          (funcall (eita.chain::chain-spec-block-setup spec) 1000 dummy-blk 1700000000)
        (error () (setf refused t)))
      (chk "pre-Etna block is refused loudly" refused))

    ;; 2. Coreth disables refunds + credits full fee to coinbase
    (let* ((w (make-world))
           (sender #xa11ce)
           (contract #x1000)
           (coinbase #x0100000000000000000000000000000000000000)
           (code (hex->bytes "600060005500"))
           (tx (make-tx :type 2 :sender sender :to contract :nonce 0 :gas-limit 100000
                        :max-fee 100 :max-priority 10 :value 0 :data #())))
      (setf (balance-of w sender) 1000000000
            (code-of w contract) code)
      (world-storage-set w contract 0 1)
      (multiple-value-bind (gas status egp) (run-avax-tx w tx :sae nil :base-fee 25)
        (chk "Coreth pre-SAE clear-slot tx succeeds" (= status 1) status)
        (chk "Coreth pre-SAE egp = baseFee + tip = 35" (= egp 35) egp)
        (chk "Coreth pre-SAE disables SSTORE refund (gas=26006, not 21206)" (= gas 26006) gas)
        (chk "Coreth sender paid full gas*egp" (= (balance-of w sender) (- 1000000000 (* gas egp))) (balance-of w sender))
        (chk "Coreth coinbase received full fee (base+tip)" (= (balance-of w coinbase) (* gas egp)) (balance-of w coinbase))))

    ;; 3. Helicon / SAE minimum gas floor ceil(limit / 2)
    (let* ((w (make-world))
           (sender #xa11ce)
           (recipient #xb0b)
           (coinbase #x0100000000000000000000000000000000000000)
           (tx (make-tx :type 2 :sender sender :to recipient :nonce 0 :gas-limit 100001
                        :max-fee 100 :max-priority 5 :value 1000 :data #())))
      (setf (balance-of w sender) 1000000000)
      (multiple-value-bind (gas status egp) (run-avax-tx w tx :sae t :base-fee 20 :ts 1790190722)
        (chk "SAE plain transfer succeeds" (= status 1) status)
        (chk "SAE charges ceil(100001/2) = 50001 gas" (= gas 50001) gas)
        (chk "SAE egp = executed baseFee + tip = 25" (= egp 25) egp)
        (chk "SAE sender paid 50001*25 + 1000" (= (balance-of w sender) (- 1000000000 (* 50001 25) 1000)) (balance-of w sender))
        (chk "SAE coinbase received 50001*25" (= (balance-of w coinbase) (* 50001 25)) (balance-of w coinbase))))

    ;; 4. SAE executed base fee from receipts
    (let* ((tx0 (make-tx :type 0 :sender #x1 :to #x2 :gas-price 100))
           (tx1 (make-tx :type 2 :sender #x1 :to #x2 :max-fee 100 :max-priority 5))
           (tx2 (make-tx :type 2 :sender #x1 :to #x2 :max-fee 50 :max-priority 10))
           (r0 (list :effective-gas-price 100))
           (r1 (list :effective-gas-price 42))
           (r2 (list :effective-gas-price 47)))
      (multiple-value-bind (bf found)
          (eita.chain.avalanche:sae-executed-base-fee (list tx0 tx1 tx2) (list r0 r1 r2) 45 96000000)
        (chk "SAE executed base fee extracted from receipts = 37" (and found (= bf 37)) (list bf found))))

    ;; 5. Granite P-256 activation by timestamp
    (let ((spec (eita.chain.avalanche:avalanche-chain-spec "mainnet"))
          (dummy-blk (eita.input::make-chain-block :number 95000000 :base-fee 25 :gas-limit 30000000)))
      (eita.chain:install-chain-spec! spec)
      (funcall (eita.chain::chain-spec-block-setup spec) 95000000 dummy-blk 1763567999)
      (chk "pre-Granite (Fortuna): *p256verify* is NIL" (null *p256verify*) *p256verify*)
      (funcall (eita.chain::chain-spec-block-setup spec) 95000000 dummy-blk 1763568000)
      (chk "Granite+: *p256verify* is T (6900 gas)" (eq *p256verify* t) *p256verify*))

    ;; 6. Atomic batch decoder & Lean-emitted gas
    (multiple-value-bind (effs gas) (eita.chain.avalanche:decode-atomic-batch #())
      (chk "empty atomic batch -> (nil, 0)" (and (null effs) (zerop gas)) (list effs gas)))
    (chk "spec-avax-atomic-tx-gas(100, 2) = 12102" (= (spec-avax-atomic-tx-gas 100 2) 12102))

    ;; 7. Warp precompile: getBlockchainID, sendWarpMessage, getVerifiedWarpMessage & BlockResults
    (let* ((w (make-world))
           (sender #xa11ce)
           (warp #x0200000000000000000000000000000000000005)
           (tx-id (make-tx :type 2 :sender sender :to warp :nonce 0 :gas-limit 100000
                           :max-fee 100 :max-priority 0 :value 0
                           :data (hex->bytes "4213cf78")))
           (send-data (hex->bytes (concatenate 'string
                                               "ee5b48eb"
                                               "0000000000000000000000000000000000000000000000000000000000000020"
                                               "0000000000000000000000000000000000000000000000000000000000000004"
                                               "deadbeef00000000000000000000000000000000000000000000000000000000")))
           (tx-send (make-tx :type 2 :sender sender :to warp :nonce 1 :gas-limit 100000
                             :max-fee 100 :max-priority 0 :value 0 :data send-data))
           ;; getVerifiedWarpMessage(0) with no Warp access-list -> succeeds returning (empty, valid=false) at 750 gas
           (read-data (hex->bytes "6f8253500000000000000000000000000000000000000000000000000000000000000000"))
           (tx-read-miss (make-tx :type 2 :sender sender :to warp :nonce 2 :gas-limit 100000
                                  :max-fee 100 :max-priority 0 :value 0 :data read-data)))
      (setf (balance-of w sender) 1000000000)
      (multiple-value-bind (gas status egp) (run-avax-tx w tx-id :sae nil :base-fee 25)
        (declare (ignore egp))
        (chk "Warp getBlockchainID succeeds" (= status 1) status)
        (chk "Warp getBlockchainID gas = 21264" (= gas 21264) gas))
      (multiple-value-bind (gas status egp) (run-avax-tx w tx-send :sae nil :base-fee 25)
        (declare (ignore egp))
        (chk "Warp sendWarpMessage succeeds" (= status 1) status)
        (chk "Warp sendWarpMessage gas = 63788" (= gas 63788) gas)
        (chk "Warp sendWarpMessage emitted 1 log" (= (length *last-tx-logs*) 1) (length *last-tx-logs*)))
      (multiple-value-bind (gas status egp) (run-avax-tx w tx-read-miss :sae nil :base-fee 25)
        (declare (ignore egp))
        ;; intrinsic: 21000 + 4*16 + 32*4 = 21192; read miss = 750 -> 21942
        (chk "Warp getVerifiedWarpMessage(0) missing succeeds (valid=false)" (= status 1) status)
        (chk "Warp getVerifiedWarpMessage(0) missing gas = 21942" (= gas 21942) gas)
        (chk "Warp getVerifiedWarpMessage(0) valid flag = 0"
             (and (>= (length *last-tx-output*) 64) (zerop (aref *last-tx-output* 63))))))

    ;; 7b. Warp BlockResults parser (real block 95,000,011 extraData bytes)
    (let* ((extra (hex->bytes
                   "00000000004782dc000000017e00a6200000000002c5c860000000000001c4ad0906a7105e2498da36d7b7eab6599645ed0dd83c99def5d93b2006332bd300000001020000000000000000000000000000000000000500000000"))
           (tbl (eita.chain.avalanche:warp-parse-block-results extra 24))
           (txh #xc4ad0906a7105e2498da36d7b7eab6599645ed0dd83c99def5d93b2006332bd3))
      (multiple-value-bind (bits found) (gethash txh tbl)
        (chk "BlockResults decodes real block 95,000,011 Warp entry (0 failed)"
             (and found (zerop (length bits))) (list found bits))))

    ;; 8. SAE GasClock (seeded from real mainnet block 96,000,000 settled marker)
    (let* ((gc (eita.chain.avalanche:gasclock-from-settled
                #x6ab4247d #x625341 #x171a7ed02 #x2c5c860 #x1ff37c048d1567bc))
           (bf0 (eita.chain.avalanche:gasclock-base-fee gc)))
      (chk "SAE GasClock initial baseFee > 0" (plusp bf0) bf0)
      (eita.chain.avalanche:gasclock-before-block! gc #x6ab42482 #x1a0cfae9f10)
      (let ((bf1 (eita.chain.avalanche:gasclock-base-fee gc)))
        (chk "SAE GasClock BeforeBlock decays excess (bf1 <= bf0)" (<= bf1 bf0) (list bf0 bf1)))
      (eita.chain.avalanche:gasclock-after-block! gc 4000000 #x2c5c860 #x1ff37c048d1567bc)
      (chk "SAE GasClock AfterBlock advances excess/time" (plusp (eita.chain.avalanche:gasclock-base-fee gc))))

    ;; 9. Coreth storage-trie key normalization (slot[0] &= 0xfe) & 5-field multiCoin RLP
    (let* ((slot-odd  #x4f11000000000000000000000000000000000000000000000000000000000000)
           (slot-even #x4e11000000000000000000000000000000000000000000000000000000000000)
           (r-eth-odd   (eita.mpt:storage-root (list (cons slot-odd 42))  :normalize-slot-key nil))
           (r-eth-even  (eita.mpt:storage-root (list (cons slot-even 42)) :normalize-slot-key nil))
           (r-avax-odd  (eita.mpt:storage-root (list (cons slot-odd 42))  :normalize-slot-key t))
           (r-avax-even (eita.mpt:storage-root (list (cons slot-even 42)) :normalize-slot-key t))
           (empty-r (eita.mpt:empty-root-bytes))
           (empty-c (eita.mpt:empty-code-hash))
           (leaf-eth   (eita.mpt:account-leaf-value 1 100 empty-r empty-c :five-field nil :multi-coin nil))
           (leaf-c-f   (eita.mpt:account-leaf-value 1 100 empty-r empty-c :five-field t   :multi-coin nil))
           (leaf-c-t   (eita.mpt:account-leaf-value 1 100 empty-r empty-c :five-field t   :multi-coin t))
           ;; On-chain WAVAX account leaf at Avalanche mainnet block 95,000,000 (eth_getProof):
           ;; nonce=1, balance=0x0f814e3cc309f4f5e3e86c, storageRoot=0x22789b45..., codeHash=0xbe0979d9..., multiCoin=false
           (wavax-leaf (eita.mpt:account-leaf-value
                        1
                        #x0f814e3cc309f4f5e3e86c
                        (hex->bytes "22789b451a6681387a6c5889206cfd0b5efb0c0d6f3fdca0a127e27af1530ec1")
                        (hex->bytes "be0979d9ff9e744b48d32e81fd67db0d32dfc74120989df9b7b1588e2aff8597")
                        :five-field t
                        :multi-coin nil))
           (wavax-exp  (hex->bytes
                        "f850018b0f814e3cc309f4f5e3e86ca022789b451a6681387a6c5889206cfd0b5efb0c0d6f3fdca0a127e27af1530ec1a0be0979d9ff9e744b48d32e81fd67db0d32dfc74120989df9b7b1588e2aff859780")))
      (chk "Ethereum trie: 0x4f11.. and 0x4e11.. have distinct storage roots"
           (not (equalp r-eth-odd r-eth-even)))
      (chk "Coreth trie: 0x4f11.. normalizes to 0x4e11.. (identical storage root)"
           (and (equalp r-avax-odd r-avax-even) (equalp r-avax-odd r-eth-even)))
      (chk "Coreth 5-field multiCoin=false appends 0x80 (+1 byte vs Ethereum)"
           (and (= (length leaf-c-f) (1+ (length leaf-eth)))
                (= (aref leaf-c-f (1- (length leaf-c-f))) #x80)))
      (chk "Coreth 5-field multiCoin=true appends 0x01 (+1 byte vs Ethereum)"
           (and (= (length leaf-c-t) (1+ (length leaf-eth)))
                (= (aref leaf-c-t (1- (length leaf-c-t))) #x01)))
      (chk "Coreth 5-field WAVAX block 95,000,000 eth_getProof leaf matches byte-for-byte"
           (equalp wavax-leaf wavax-exp))
      (chk "find-chain-spec-by-id resolves 43114 and 43113 with Coreth trie parameters"
           (let ((m (eita.chain:find-chain-spec-by-id 43114))
                 (f (eita.chain:find-chain-spec-by-id 43113)))
             (and m f
                  (eita.chain:chain-spec-normalize-slot-key m)
                  (eita.chain:chain-spec-five-field-account m)
                  (eq (eita.chain:chain-spec-header-rlp m) :coreth)
                  (eita.chain:chain-spec-deferred-anchor-p m)
                  (eita.chain:chain-spec-five-field-account f)))))

    ;; 10. SAE deferred anchor persistence, resolution, expiry, rollback & restart
    (let* ((tmp-dir (format nil "/tmp/eita-avax-deferred-~D/" (get-universal-time)))
           (prev-env (sb-ext:posix-getenv "EITA_STATE_DIR")))
      (ensure-directories-exist (merge-pathnames "x" tmp-dir))
      (unwind-protect
           (progn
             (sb-posix:setenv "EITA_STATE_DIR" tmp-dir 1)
             (let ((eita.state::*deferred-anchors* '())
                   (eita.state::*deferred-resolved* '())
                   (eita.state::*anchor-queue* '()))
               (eita.state::defer-anchor! 96000090)
               (eita.state::defer-anchor! 96000099)
               (eita.state::defer-anchor! 96000110)
               (chk "defer-anchor! persists entries to deferred-anchors.sexp"
                    (equal (eita.state::read-deferred-anchors)
                           '((96000090 nil) (96000099 nil) (96000110 nil))))
               ;; Simulate restart at 96000100: drops > 96000100, keeps 96000090 & 96000099
               (setf eita.state::*deferred-anchors* '()
                     eita.state::*deferred-resolved* '()
                     eita.state::*anchor-queue* '())
               (eita.state::restore-deferred-anchors! 96000100)
               (chk "restore-deferred-anchors! reloads <= resume block across restart"
                    (equal eita.state::*deferred-anchors* '(96000090 96000099)))
               ;; Multi-block settlement at 96000099 expires 96000090 and promotes 96000099
               (chk "resolve-deferred-anchor! expires < settledHeight and promotes exact match"
                    (and (eita.state::resolve-deferred-anchor! 96000099 "0x8b02e85f")
                         (null eita.state::*deferred-anchors*)
                         (equal eita.state::*anchor-queue* '((96000099 "0x8b02e85f")))
                         (equal (eita.state::read-deferred-anchors) '((96000099 "0x8b02e85f")))))
               ;; Simulate restart after resolution (before check-root finishes): re-queues 96000099
               (setf eita.state::*deferred-anchors* '()
                     eita.state::*deferred-resolved* '()
                     eita.state::*anchor-queue* '())
               (eita.state::restore-deferred-anchors! 96000105)
               (chk "restore-deferred-anchors! re-queues resolved deferred anchor across restart"
                    (and (null eita.state::*deferred-anchors*)
                         (equal eita.state::*anchor-queue* '((96000099 "0x8b02e85f")))))
               ;; Rollback drops deferred/resolved entries above fork point
               (eita.state::defer-anchor! 96000104)
               (eita.state::drop-deferred-above! 96000095)
               (chk "drop-deferred-above! removes entries above fork point from memory and disk"
                    (and (null eita.state::*deferred-anchors*)
                         (null eita.state::*deferred-resolved*)
                         (null (eita.state::read-deferred-anchors))))))
        (if prev-env
            (sb-posix:setenv "EITA_STATE_DIR" prev-env 1)
            (sb-posix:unsetenv "EITA_STATE_DIR"))
        (sb-ext:run-program "rm" (list "-rf" tmp-dir) :search t)))

    (let* ((settling-blk (eita.input::make-chain-block
                          :number 96000000 :settled-height 95999994
                          :settled-gas-unix #x6ab4247d :settled-gas-numerator #x625341
                          :settled-excess #x171a7ed02 :target-exponent #x2c5c860
                          :min-price-exponent #x1ff37c048d1567bc))
           (other-blk (eita.input::make-chain-block :number 95999995 :settled-height 95999989))
           (eita.input:*block-source*
            (eita.input:make-block-source
             :name "test-sae-lookahead"
             :block (lambda (k) (if (= k 96000000) settling-blk other-blk))))
           (eita.chain.avalanche::*avalanche-gas-clock* nil)
           (eita.chain.avalanche::*avalanche-clock-block* nil))
      (chk "SAE GasClock auto-seeds at 95999994 from lookahead header 96000000"
           (and (eita.chain.avalanche::avalanche-seed-gasclock-lookahead 95999994)
                (eql eita.chain.avalanche::*avalanche-clock-block* 95999994)
                (plusp (eita.chain.avalanche:gasclock-base-fee eita.chain.avalanche::*avalanche-gas-clock*)))))

    ;; 11. Coreth opcode 0x44 (DIFFICULTY/PREVRANDAO) returns header.difficulty (1), not mixHash (0)
    (let* ((w (make-world))
           (sender #xa11ce)
           (contract #x2000)
           ;; PREVRANDAO (0x44), PUSH1 0, MSTORE, PUSH1 32, PUSH1 0, RETURN
           (code (hex->bytes "4460005260206000f3"))
           (tx (make-tx :type 2 :sender sender :to contract :nonce 0 :gas-limit 100000
                        :max-fee 100 :max-priority 0 :value 0 :data #()))
           (eita.chain.avalanche::*avalanche-block-difficulty* 1))
      (setf (balance-of w sender) 1000000000
            (code-of w contract) code)
      (multiple-value-bind (gas status egp) (run-avax-tx w tx :sae nil :base-fee 25)
        (declare (ignore gas egp))
        (chk "Coreth opcode 0x44 returns difficulty=1 (not mixHash=0)"
             (and (= status 1)
                  (= (length *last-tx-output*) 32)
                  (= (aref *last-tx-output* 31) 1))
             *last-tx-output*)))

    ;; 12. Saturating fake_exponential & gasclock-excess-for must never hang at u64::MAX
    (let* ((max64 #xffffffffffffffff)
           (p-sat (eita.evm::spec-avax-gasclock-price-at max64 1000000))
           (t-sat (eita.evm::spec-avax-gasclock-target max64))
           (m-sat (eita.evm::spec-avax-gasclock-min-price max64))
           (exc (eita.chain.avalanche::gasclock-excess-for 4000000 1000000000))
           (p-at (eita.evm::spec-avax-gasclock-price-at exc 4000000))
           (p-next (eita.evm::spec-avax-gasclock-price-at (1+ exc) 4000000))
           (gc (eita.chain.avalanche::make-avax-gasclock
                :seconds 100 :fraction 0 :excess 0 :target 4000000 :min-price 1000000000)))
      (eita.chain.avalanche::gasclock-enforce-min-excess! gc)
      (chk "saturating spec-avax-gasclock-price-at(u64::MAX) returns u64::MAX"
           (= p-sat max64) p-sat)
      (chk "saturating spec-avax-gasclock-target(u64::MAX) returns i64::MAX"
           (= t-sat #x7fffffffffffffff) t-sat)
      (chk "saturating spec-avax-gasclock-min-price(u64::MAX) returns u64::MAX"
           (= m-sat max64) m-sat)
      (chk "gasclock-excess-for finds exact boundary for 1 gwei minPrice"
           (and (plusp exc) (<= p-at 1000000000) (>= p-next 1000000000))
           (list exc p-at p-next))
      (chk "gasclock-enforce-min-excess! lifts excess=0 to excessFor(minPrice)"
           (= (eita.chain.avalanche::gc-excess gc) exc)
           (eita.chain.avalanche::gc-excess gc))
      ;; Extreme comparison vectors against Lean GasClock.lean (kernel-proved in Lean)
      (chk "Lean vs Lisp extreme: targetOfExponent(0) = 1000000"
           (= (eita.evm::spec-avax-gasclock-target 0) 1000000))
      (chk "Lean vs Lisp extreme: targetOfExponent(5e9) = i64::MAX"
           (= (eita.evm::spec-avax-gasclock-target 5000000000) 9223372036854775807))
      (chk "Lean vs Lisp extreme: minPriceOfExponent(0) = 1"
           (= (eita.evm::spec-avax-gasclock-min-price 0) 1))
      (chk "Lean vs Lisp extreme: minPriceOfExponent(415828534307635077) = 2"
           (= (eita.evm::spec-avax-gasclock-min-price 415828534307635077) 2))
      (chk "Lean vs Lisp extreme: minPriceOfExponent(2*minPriceConversion) = 7"
           (= (eita.evm::spec-avax-gasclock-min-price (* 2 415828534307635077)) 7))
      (chk "Lean vs Lisp extreme: minPriceOfExponent(128*minPriceConversion) = u64::MAX"
           (= (eita.evm::spec-avax-gasclock-min-price (* 128 415828534307635077)) max64))
      (chk "Lean vs Lisp extreme: priceAt(0, minTarget) = 1"
           (= (eita.evm::spec-avax-gasclock-price-at 0 1000000) 1))
      (chk "Lean vs Lisp extreme: priceAt(12e9, minTarget) = u64::MAX"
           (= (eita.evm::spec-avax-gasclock-price-at 12000000000 1000000) max64)))

    ;; 13. Coreth 30-field header hashing is gated on *header-rlp-mode*, not extDataHash presence
    (let* ((z32 "0x0000000000000000000000000000000000000000000000000000000000000000")
           (z20 "0x0000000000000000000000000000000000000000")
           (z256 (concatenate 'string "0x" (make-string 512 :initial-element #\0)))
           (j-with-ext
            (jsown:new-js
              ("parentHash" z32) ("sha3Uncles" z32) ("miner" z20) ("stateRoot" z32)
              ("transactionsRoot" z32) ("receiptsRoot" z32) ("logsBloom" z256)
              ("difficulty" "0x1") ("number" "0x1") ("gasLimit" "0x100000") ("gasUsed" "0x0")
              ("timestamp" "0x60000000") ("extraData" "0x") ("mixHash" z32) ("nonce" "0x0000000000000000")
              ("baseFeePerGas" "0x1") ("extDataHash" z32) ("extDataGasUsed" "0x0") ("blockGasCost" "0x0")))
           (j-no-ext
            (jsown:new-js
              ("parentHash" z32) ("sha3Uncles" z32) ("miner" z20) ("stateRoot" z32)
              ("transactionsRoot" z32) ("receiptsRoot" z32) ("logsBloom" z256)
              ("difficulty" "0x1") ("number" "0x1") ("gasLimit" "0x100000") ("gasUsed" "0x0")
              ("timestamp" "0x60000000") ("extraData" "0x") ("mixHash" z32) ("nonce" "0x0000000000000000")
              ("baseFeePerGas" "0x1")))
           (h-eth (let ((eita.input:*header-rlp-mode* nil))
                    (eita.input::blk-header-hash (eita.input::decode-block-json j-with-ext))))
           (h-eth-plain (let ((eita.input:*header-rlp-mode* nil))
                          (eita.input::blk-header-hash (eita.input::decode-block-json j-no-ext))))
           (h-coreth (let ((eita.input:*header-rlp-mode* :coreth))
                       (eita.input::blk-header-hash (eita.input::decode-block-json j-with-ext))))
           (coreth-missing-err nil))
      (handler-case
          (let ((eita.input:*header-rlp-mode* :coreth))
            (eita.input::decode-block-json j-no-ext))
        (error () (setf coreth-missing-err t)))
      (chk "Ethereum *header-rlp-mode* ignores extDataHash"
           (= h-eth h-eth-plain))
      (chk "Coreth *header-rlp-mode* produces distinct 30-field header hash"
           (/= h-coreth h-eth))
      (chk "Coreth *header-rlp-mode* errors loudly when extDataHash is absent"
           coreth-missing-err)))

  (format t "~&avalanche: ~D passed, ~D failed~%" pass fail)
  (when (plusp fail) (eita.test:finish :code 1)))
