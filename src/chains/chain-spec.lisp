;;;; chains/chain-spec.lisp — everything a chain can change about the generic replay, in one
;;;; record. A chain module builds a chain-spec and calls install-chain-spec!, which sets
;;;; EVERY hook — unset fields restore the Ethereum default — so no configuration can leak
;;;; from one chain into another, and this struct is the complete list of chain
;;;; extension points (grep it before adding a new hook anywhere else).
;;;;
;;;;   identity      name id genesis-path banner rpc-url cache-dir
;;;;   tip           reorg-depth (blocks a reorg may undo; 0: final at once)  — snapshot-world.lisp
;;;   lazy state    prestate-overlay (pre-block state from debug traces, one fetch per block)
;;;;   per block     block-setup (fork table, chain hardfork flags)   — chains/driver.lisp
;;;;                 pre-block post-block (system calls)              — block-system.lisp
;;;;                 system-rule (a system call's warm-up, GASPRICE, end) — block-system.lisp
;;;;   per tx        run-tx (non-user tx kinds) tx-prewarm upfront-extra fee — evm/run-tx.lisp
;;;;   header        header-foreign (fields the chain defines otherwise: not compared,
;;;;                 named in the banner)                             — receipts.lisp
;;;;   observers     observe-kinds (NIL = everything, call frames included) — src/evm/
;;;;   EVM core      precompile-p precompile-run frame-init frame-init-log selfdestruct
;;;;                 p256verify (EIP-7951 at 0x100)                   — src/evm/

(in-package #:eita.chain)

;;; --- Chain settings (set by the chain module before replay-main) ---------------
(defvar *chain-name* "chain" "Human label for banners, e.g. \"Arc mainnet\".")
(defvar *chain-id* 1)
(defvar *chain-genesis-path* nil "geth genesis.json for full-state runs from genesis.")
(defvar *chain-banner-extra* "" "Extra banner text (fork, chain rules).")
(defvar *chain-block-setup-hook* nil
  "(lambda (n blk ts)) before anything else in a block: fork table, chain hardfork flags,
   and any refusal for blocks the spec cannot reproduce.")
(defvar *chain-run-tx-hook* nil
  "(lambda (world tx receipt block-ctx coinbase n idx)) → (values gas status egp); default
   run-evm-tx. A chain with non-user tx kinds (OP deposits) dispatches here.")


(defvar *chain-header-foreign* '())        ; owned by receipts.lisp; declared for install
(defvar *chain-observe-kinds* nil
  "What this chain's observers record (NIL: everything). Arc's records predate call frames.")

(defstruct chain-spec
  (name "Ethereum") (id 1) genesis-path (banner "") rpc-url cache-dir prestate-overlay
  (reorg-depth 64)
  block-setup run-tx tx-prewarm upfront-extra fee pre-block post-block system-rule
  header-foreign observe-kinds
  precompile-p precompile-run frame-init frame-init-log selfdestruct p256verify)

(defvar *chain-spec* nil "The installed chain-spec.")

(defun install-chain-spec! (spec)
  "Install SPEC: identity, endpoint/cache, and every hook (NIL = the Ethereum default)."
  (setf *chain-spec* spec
        *chain-name* (chain-spec-name spec)
        *chain-id* (chain-spec-id spec)
        *chain-genesis-path* (chain-spec-genesis-path spec)
        *chain-banner-extra* (chain-spec-banner spec)
        *rpc-url* (chain-spec-rpc-url spec)
        *cache-dir* (chain-spec-cache-dir spec)
        *chain-block-setup-hook* (chain-spec-block-setup spec)
        *chain-pre-block-hook* (chain-spec-pre-block spec)
        *chain-post-block-hook* (chain-spec-post-block spec)
        *chain-system-rule* (chain-spec-system-rule spec)
        *chain-run-tx-hook* (chain-spec-run-tx spec)
        *chain-tx-prewarm-hook* (chain-spec-tx-prewarm spec)
        *chain-upfront-extra-hook* (chain-spec-upfront-extra spec)
        *chain-fee-hook* (chain-spec-fee spec)
        *chain-header-foreign* (chain-spec-header-foreign spec)
        *chain-precompile-p* (chain-spec-precompile-p spec)
        *chain-precompile-hook* (chain-spec-precompile-run spec)
        *chain-value-transfer-hook* (chain-spec-frame-init spec)
        *chain-value-transfer-log-hook* (chain-spec-frame-init-log spec)
        *chain-selfdestruct-hook* (chain-spec-selfdestruct spec)
        *p256verify* (chain-spec-p256verify spec)
        *chain-observe-kinds* (chain-spec-observe-kinds spec))
  spec)

;;; Registry: chain name → constructor (a function, so environment-dependent fields such as
;;; the RPC endpoint are read when the chain is installed, not when the module loads).
(defvar *chain-registry* (make-hash-table :test 'equal))
(defun register-chain-spec (name constructor) (setf (gethash name *chain-registry*) constructor) name)
(defun find-chain-spec (name)
  (let ((c (gethash name *chain-registry*)))
    (unless c (error "unknown chain ~S (registered: ~{~A~^, ~})" name
                     (loop for k being the hash-keys of *chain-registry* collect k)))
    (funcall c)))
