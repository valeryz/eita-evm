;;;; packages.lisp — every package of the engine, defined up front.
;;;;
;;;; One package per subsystem (src/<subsystem>/). A symbol lives in the package of the file that
;;;; defines it; a subsystem exports what other subsystems use and :uses the subsystems it calls
;;;; into (the engine's subsystems call each other both ways: the EVM reads block state the
;;;; driver sets, the driver runs the EVM), which is why they are all defined here, before any
;;;; file is read. The export lists are the cross-subsystem surface: an addition to one is an
;;;; addition to an interface. The user-facing API is the EITA package (src/eita.lisp).

;; The subsystems use each other in a cycle, so each exists (empty) before a DEFPACKAGE names it
;; in a :USE.
(eval-when (:compile-toplevel :load-toplevel :execute)
  (dolist (name (quote ("EITA.NATIVE" "EITA.CORE" "EITA.EVM" "EITA.STATE" "EITA.INPUT" "EITA.CHAIN")))
    (unless (find-package name) (make-package name :use (quote ())))))

(defpackage #:eita.native
  (:documentation "The native artifacts: where libeita / libkeccak_batch / libeita_pq / libz are found and
   opened (one place), their FFI bindings, the startup registry a saved image re-runs, the
   engine's code version.")
  (:use #:cl #:cffi)
  (:export
           #:%call-gas #:%call-gas-frontier #:%call-gas-tangerine #:%eita-blake2f
           #:%eita-bls-g1add #:%eita-bls-g1msm #:%eita-bls-g2add #:%eita-bls-g2msm
           #:%eita-bls-map-fp-to-g1 #:%eita-bls-map-fp2-to-g2 #:%eita-bls-pairing
           #:%eita-bn254-add #:%eita-bn254-mul #:%eita-bn254-pairing #:%eita-ecrecover
           #:%eita-modexp #:%eita-p256-verify #:%eita-point-evaluation #:%jumpdest-map #:%mmap
           #:%mprotect #:%ripemd160-hash #:%run-program #:%set-fork #:%sha256-hash
           #:%ts-access-addr #:%ts-access-slot #:%ts-created-insert #:%ts-created-p
           #:%ts-orig-get #:%ts-orig-record #:%ts-refund-add #:%ts-reset #:%ts-revert
           #:*image-p* #:at-startup #:code-version #:code-version-manifest #:defstartup
           #:dir-of #:eita-file #:eita-home #:eita-keccak256 #:eita-lib-ext #:eita-run
           #:emit-jit-path #:executable-dir #:forget-shared-objects! #:freeze-lisp-manifest!
           #:home-relative #:native-path #:nonempty-env #:open-native #:run-startup!
           #:source-file))

(defpackage #:eita.core
  (:documentation "Byte-level primitives: u256 limbs, hex, RLP, keccak.")
  (:use #:cl #:cffi #:eita.native)
  (:export
           #:addr-to-bytes #:derive-create-address #:hex->bytes #:hex->int #:int-to-be-bytes
           #:keccak256-bytes #:rlp-encode-bytes #:rlp-encode-list #:u256->octets #:u256-read
           #:u256-write #:word-int #:words-u256))

(defpackage #:eita.evm
  (:documentation "The EVM: interpreter and JIT tiers, frames and arenas, the journal, the host callbacks
   (CALL/CREATE family, precompiles), the Lean-emitted host effects (generated/host.lisp),
   transaction application, the observation seam and the event stream.")
  (:use #:cl #:cffi #:eita.native #:eita.core #:eita.state #:eita.input #:eita.chain)
  (:export
           #:*block-blob-gas* #:*block-hashes* #:*call-depth* #:*chain-fee-hook*
           #:*chain-precompile-hook* #:*chain-precompile-p* #:*chain-selfdestruct-hook*
           #:*chain-tx-prewarm-hook* #:*chain-upfront-extra-hook* #:*chain-value-transfer-hook*
           #:*chain-value-transfer-log-hook* #:*code-hash-memo* #:*cur-block* #:*cur-tx*
           #:*current-address* #:*current-block-number* #:*current-world* #:*el-fork-ord*
           #:*fork-ord* #:*jit-stats* #:*last-sub-outcome* #:*last-tx-logs* #:*last-tx-output*
           #:*last-verdict* #:*mpt-tracking* #:*network-fork-ords* #:*p256verify*
           #:*prague-delegation* #:*receipt-cumulative-gas* #:*system-seed* #:*trace-frames*
           #:*trace-step* #:*trace-tx* #:*tx-origin* #:+acct-destroyed+ #:+acct-touched+
           #:+fork-ord-prague+ #:access-addr! #:access-slot! #:account-dead-p #:apply-tx
           #:attach-subscriber! #:block-blob-base-fee #:block-invalid #:cb-call
           #:check-cached-foreign-pointers! #:child-gas #:code-hash-int #:current-arena
           #:destroyed-p #:ecrecover-address #:effective-gas-price #:el-fork
           #:calldata-byte-counts #:engine-code-version #:forget-tx-sets! #:fw-drain #:fw-push #:intrinsic-gas
           #:invalid! #:invalid-kind #:journal-balance! #:journal-push! #:jval #:load-observer!
           #:make-observer #:make-pipe #:make-tx #:make-verdict #:mpt-touch! #:mpt-touch-all!
           #:observe #:observe-acct-touch! #:observe-log! #:observe-slot-touch!
           #:observe-transfer! #:observe-tx-begin! #:observe-tx-end! #:octets #:orig-get!
           #:orig-record! #:pipe-count #:pipe-put #:pipe-take #:precompile-seed-addrs
           #:reset-tx-state #:run-evm-tx #:set-fork! #:spec-arc-abi-copy-gas
           #:spec-arc-account-load-gas #:spec-arc-blocklist-event-gas #:spec-arc-call-stipend
           #:spec-arc-early-revert-penalty #:spec-arc-empty-account-gas
           #:spec-arc-is-blocklisted-gas #:spec-arc-native-transfer-gas
           #:spec-arc-next-base-fee #:spec-arc-pq-base-gas #:spec-arc-pq-msg-word-gas
           #:spec-arc-pq-sig-len #:spec-arc-pq-verify-gas #:spec-arc-pq-vk-len
           #:spec-arc-precompile-sstore-gas #:spec-arc-slot-read-gas
           #:spec-arc-smoothed-gas-used #:spec-arc-subcall-dispatch-cost
           #:spec-arc-transfer-log-gas #:spec-arc-write-gas #:spec-arc-write-probe-gas
           #:spec-block-credits #:spec-coinbase-fee-effect #:spec-destroy-effect
           #:spec-header-violation #:spec-mainnet-fork-ord #:spec-sweep-effect
           #:spec-system-effect #:stream-block-begin! #:stream-checkpoint! #:stream-commit!
           #:stream-finalize! #:stream-rollback! #:touch! #:tx #:tx-access-list #:tx-auth-count
           #:tx-auth-list #:tx-blob-hashes #:tx-chain-id #:tx-data #:tx-gas-limit
           #:tx-gas-price #:tx-max-blob-fee #:tx-max-fee #:tx-max-priority #:tx-mint #:tx-nonce
           #:tx-r #:tx-s #:tx-sender #:tx-source-hash #:tx-system-p #:tx-to #:tx-type #:tx-v
           #:tx-value #:verdict #:verifier-note! #:world-account-present-p))

(defpackage #:eita.state
  (:documentation "World state: the account and storage tables, the storage view, lazy faulting, the
   layered snapshot world, anchors and state-root checks.")
  (:use #:cl #:cffi #:eita.native #:eita.core #:eita.evm #:eita.input #:eita.chain)
  (:export
           #:*anchor-queue* #:*cold-storage-map-hook* #:*fault-account-hook*
           #:*fault-slot-hook* #:*mpt-armed* #:*observe-capture* #:*observer* #:*pending-root*
           #:*tip-freeze* #:*view-log* #:+acct-marked+ #:account-delete! #:account-mark!
           #:account-marked-p #:account-uncreate! #:account-unmark! #:acct-addr #:acct-balance
           #:acct-bits #:acct-clear-flag! #:acct-code #:acct-code-entry #:acct-flag-p
           #:acct-nonce #:acct-set-flag! #:acct-storage #:acct-table-intern-words #:anchor!
           #:anchor-compositions #:anchor-due-p #:balance-clear! #:balance-delta! #:balance-of
           #:bytes->hex-string #:code-clear! #:code-of #:copy-slots #:copy-world*
           #:drop-stale-rootouts! #:fault-account! #:fault-slot! #:finish-anchors!
           #:genesis-base! #:hot-over-budget-p #:layer-due-p #:load-genesis-alloc #:make-world
           #:map-accts #:mpt-post-block-hook #:mpt-stop-worker #:nonce-clear! #:nonce-of
           #:populate-world #:prune-dumps! #:resume-stack! #:rollback-to! #:root-check!
           #:root-check-poll! #:slots #:slots-map #:slots-state #:slots-words #:snapshot-dir
           #:stack-composition #:stop-background! #:storage-of #:u256 #:with-acct #:world
           #:world-accts #:world-state-root #:world-storage-get #:world-storage-set))

(defpackage #:eita.state.snapshot
  (:documentation "Binary snapshots and delta layers (docs/state-snapshot-format.md, docs/layered-snapshots.md).")
  (:use #:cl)
  (:export
           #:*foreign-layer* #:+empty-code-hash+ #:component-of #:component-path
           #:compose-address #:composition-string #:hardware-threads #:int->octets
           #:layer-account #:layer-map-slots #:layer-path #:layer-slot #:layer-tmp-path
           #:lookup-account #:make-merge #:make-obuf #:map-touched-addresses #:mapping-sap
           #:merge-account #:merge-finish #:obuf-count #:obuf-free #:obuf-sap #:octets->int
           #:parse-composition #:read-manifest #:release-range #:s1-included-p #:sap-be #:snap
           #:snap-account #:snap-acct #:snap-block #:snap-close #:snap-code #:snap-content-hash
           #:snap-dir #:snap-has-storage-p #:snap-kind-p #:snap-layer-p #:snap-manifest
           #:snap-map-account-storage #:snap-map-accounts #:snap-map-codes #:snap-map-storage
           #:snap-n-accounts #:snap-n-codes #:snap-n-slots #:snap-open #:snap-p #:snap-parent
           #:snap-path #:snap-publish #:snap-sealed-p #:snap-slot #:snap-slot-map
           #:snap-tmp-path #:snap-verify #:view-account #:view-code #:view-has-storage-p
           #:view-map-account-storage #:view-slot #:write-composed #:zero-bytes-p))

(defpackage #:eita.state.recovery
  (:documentation "The resume point and garbage collection over snapshots (lean/Evm/Persist/Recovery.lean).")
  (:use #:cl)
  (:export
           #:dumps-of #:gc-files #:gc-set #:read-anchors #:read-files #:read-points #:read-view
           #:resolve #:resume-point #:run-gc #:run-resume))

(defpackage #:eita.mpt
  (:documentation "The Merkle-Patricia trie, mirrored from lean/Evm/Trie (receipts root, state-root oracles).")
  (:use #:cl #:cffi)
  (:export
           #:%keccak #:%keccak-batch-c #:*keccak* #:account-leaf-value #:account-state-root
           #:bytes->hex #:empty-code-hash #:empty-root-bytes #:hex-prefix #:int->be-bytes-fixed
           #:keccak256-bytes #:make-mtrie #:make-nibbles #:mtrie-delete #:mtrie-insert
           #:mtrie-member #:mtrie-root #:mtrie-top #:node-ref #:rlp-bytes #:rlp-encode
           #:rlp-list #:rlp-list* #:rlp-uint #:storage-root #:trie-root))

(defpackage #:eita.state.root
  (:documentation "The streaming state root of a snapshot stack (the anchors' root check; `eita check-root`).")
  (:use #:cl #:cffi)
  (:export
           #:main #:make-stack-trie #:snapshot-root #:st-finish #:st-push #:st-reset
           #:st-root-bytes))

(defpackage #:eita.input
  (:documentation "Block input: the JSON block decoder and the block-source seam (docs/block-input.md).")
  (:use #:cl #:cffi #:eita.native #:eita.core #:eita.evm #:eita.state)
  (:export
           #:*block-source* #:*cache-dir* #:*offline-misses* #:*rpc-calls* #:*rpc-url*
           #:*stats* #:+exit-input-outage+ #:addr-hex #:blk-base-fee #:blk-blob-gas-used
           #:blk-difficulty #:blk-excess-blob-gas #:blk-extra-data #:blk-gas-limit
           #:blk-gas-used #:blk-hash #:blk-header-hash #:blk-header-rlp #:blk-logs-bloom
           #:blk-miner #:blk-mix-hash #:blk-nonce #:blk-number #:blk-parent-beacon-root
           #:blk-parent-hash #:blk-receipts #:blk-receipts-root #:blk-requests-hash
           #:blk-sha3-uncles #:blk-state-root #:blk-timestamp #:blk-transactions-root #:blk-txs
           #:blk-uncle-count #:blk-uncles #:blk-withdrawals #:blk-withdrawals-root
           #:block-source #:block-source-begin #:block-source-fault-account
           #:block-source-fault-slot #:block-source-follow #:block-source-forget-above
           #:block-source-name #:block-source-prepare #:block-source-prestate
           #:decode-block-json #:default-block-source #:directory-block-source #:fetch-block
           #:fetch-block-hash #:fetch-receipts #:fetch-uncles #:fetch-verified-block #:gate
           #:input-outage #:jnonnull #:make-block-source #:octets-int #:parse-block-arg
           #:source-call))

(defpackage #:eita.chain
  (:documentation "The chain-neutral block pipeline: the chain-spec record, block system work, receipts and
   header gates, the replay driver.")
  (:use #:cl #:cffi #:eita.native #:eita.core #:eita.evm #:eita.state #:eita.input)
  (:export
           #:*chain-id* #:*chain-spec* #:*full-state* #:*receipts-unverifiable*
           #:*recent-headers* #:+postblock-tx+ #:+preblock-tx+ #:block-credit! #:block-ommers
           #:chain-spec-reorg-depth #:eip2935-store-parent-hash! #:ethereum-pre-block!
           #:find-chain-spec #:header-record #:header-violation #:install-chain-spec!
           #:make-chain-spec #:receipts-block-begin! #:receipts-push! #:recover-tx-sender
           #:register-chain-spec #:replay-main #:run-post-block! #:run-pre-block! #:system-call
           #:verify-block-header))

(defpackage #:eita.chain.ethereum
  (:documentation "Ethereum mainnet on the generic driver.")
  (:use #:cl #:cffi #:eita.native #:eita.evm #:eita.state #:eita.input #:eita.chain))

(defpackage #:eita.chain.arc
  (:documentation "Circle Arc: its chain spec and native-USDC / PQ precompiles.")
  (:use #:cl #:cffi #:eita.native #:eita.core #:eita.evm #:eita.state #:eita.input #:eita.chain))

(defpackage #:eita.chain.op
  (:documentation "OP-Stack chains (Base, OP Mainnet, World Chain) with lazy RPC-backed state.")
  (:use #:cl #:cffi #:eita.native #:eita.evm #:eita.state #:eita.input #:eita.chain))

(defpackage #:eita.fixtures
  (:documentation "The BlockchainTests runner (ethereum/tests, execution-spec-tests).")
  (:use #:cl #:cffi #:eita.native #:eita.core #:eita.evm #:eita.state #:eita.input #:eita.chain)
  (:export
           #:main #:parse-test))

(defpackage #:eita
  (:documentation "The user-facing API (src/eita.lisp): worlds, transactions and calls at a fork's
   rules, fixtures (system eita/fixtures), chain replays (system eita/chains), and the engine
   entry points a program building on Eita needs.")
  (:use #:cl)
  (:import-from #:eita.state #:make-world #:world-state-root #:*observer*)
  (:import-from #:eita.evm #:make-tx #:apply-tx #:run-evm-tx #:make-observer
                #:attach-subscriber! #:*current-world*)
  (:import-from #:eita.input #:make-block-source #:directory-block-source #:*block-source*)
  (:import-from #:eita.chain #:make-chain-spec #:install-chain-spec! #:register-chain-spec
                #:find-chain-spec)
  (:export
   ;; the REPL API (src/eita.lisp)
   #:new-world #:fund #:set-code #:set-storage
   #:balance #:nonce #:code #:storage #:state-root
   #:transact #:call #:deploy
   #:load-fixture #:run-fixture-file
   #:set-fork #:fork #:hex #:addr #:*block*
   ;; replaying a chain (src/chains/replay.lisp)
   #:replay
   ;; the engine, re-exported: worlds, transactions, the block-source and observation seams,
   ;; chain specs
   #:make-world #:world-state-root #:make-tx #:apply-tx #:run-evm-tx #:*current-world*
   #:make-block-source #:directory-block-source #:*block-source*
   #:*observer* #:make-observer #:attach-subscriber!
   #:make-chain-spec #:install-chain-spec! #:register-chain-spec #:find-chain-spec))

(defpackage #:eita.cli
  (:documentation "bin/eita: the command line (src/cli.lisp).")
  (:use #:cl)
  (:export #:main #:register-command))
