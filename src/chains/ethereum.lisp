;;;; chains/ethereum.lisp — Ethereum mainnet on the generic driver (Ethereum track, E).
;;;;
;;;; Blocks, receipts and uncles are JSON-RPC results (eth_getBlockByNumber,
;;;; eth_getBlockReceipts, eth_getUncleByBlockNumberAndIndex), from the installed block
;;;; source (src/input/; docs/block-input.md). What Ethereum changes
;;;; about the generic replay:
;;;;   fork          spec-mainnet-fork-ord, emitted from Evm.Forks.ofBlock (Evm.CL.ForkEmit)
;;;;   pre-block     the DAO irregular state change at 1,920,000 (EELS apply_dao), then the
;;;;                 generic EIP-4788/2935 system calls by fork
;;;;   post-block    the generic Ethereum default (block-system.lisp): rewards from the
;;;;                 uncle headers (0 from Paris), withdrawals, request system calls
;;;; Receipts before Byzantium embed a per-tx state root, so receiptsRoot is checked from
;;;; Byzantium on; the logs bloom is checked on every block. Post-Merge chunks (era
;;;; archives) carry no receipts: the header gate alone.
;;;;
;;;; Run: eita replay --chain ethereum --blocks DIR --from N --to M   (full state from genesis)
;;;; ETH_CACHE_DIR = the chunk directory (default lean/external/eth-cache/); ETH_RPC_URL =
;;;; an archive endpoint, only for lazy (non-genesis) runs of single blocks.

(in-package #:eita.chain.ethereum)

(defconstant +fork-ord-byzantium+ 5)
(defconstant +dao-fork-block+ 1920000)
(defconstant +dao-recovery+ #xbf4ed7b27f1d666546e30d74d50d173d20bca754)

(defun ethereum-block-setup (n blk ts)
  "The fork of block N from the Lean schedule (by number to the Merge, by timestamp after);
   the native dispatch follows it."
  (declare (ignore blk))
  (let ((ord (spec-mainnet-fork-ord n ts)))
    (unless (= ord *fork-ord*)
      (format t "~&block ~D: fork ord ~D -> ~D~%" n *fork-ord* ord)
      (setf *fork-ord* ord)
      (%set-fork ord))))

(defparameter *dao-accounts*
  (with-open-file (in (source-file "chains/ethereum/dao-accounts.sexp"))
    (loop for addr = (read in nil) while addr collect addr))
  "The DAO and child accounts apply_dao drains (EELS dao_fork/dao.py), in its order; read
   when the engine is loaded, so an executable carries them.")

(defun apply-dao-fork! (world)
  "EELS apply_dao: every DAO and child account's ether to the recovery contract, before
   any tx of block 1,920,000. Observed as the pre-block system tx."
  (let ((moved 0))
    (dolist (addr *dao-accounts*)
      (fault-account! addr)
      (let ((bal (balance-of world addr)))
        (incf moved bal)
        (setf (balance-of world addr) 0)
        (when *mpt-tracking* (mpt-touch! addr))))
    (fault-account! +dao-recovery+)
    (incf (balance-of world +dao-recovery+) moved)
    (when *mpt-tracking* (mpt-touch! +dao-recovery+))
    (format t "~&DAO fork: moved ~D wei to the recovery contract~%" moved)))

(defun ensure-recent-headers! (n blk)
  "*recent-headers* as block N's header gate needs them: blocks N-1 down to N-7 (or 0),
   newest first, each hash-linked to the next. After the block before N ran (post-block
   pushes it) they are; at a run's first block, after a resume or a reorg, they are fetched
   (hash-checked; before Paris with the hashes of their ommers, tied to their sha3Uncles)."
  (let ((want (min n 7)))
    (flet ((linked-p (w)
             (and (>= (length w) want)
                  (eql (getf (first w) :number) (1- n))
                  (eql (getf (first w) :hash) (blk-parent-hash blk))
                  (loop for (a b) on (subseq w 0 want) while b
                        always (and (eql (getf a :parent-hash) (getf b :hash))
                                    (eql (getf a :number) (1+ (getf b :number))))))))
      (unless (linked-p *recent-headers*)
        (setf *recent-headers*
              (loop for k from (1- n) downto (- n want)
                    collect (let ((b (fetch-verified-block k)))
                              (header-record b (mapcar #'blk-header-hash (block-ommers b))))))
        (unless (linked-p *recent-headers*)
          (error "block ~D: blocks ~D..~D as fetched are not the chain it extends" n (- n want) (1- n)))))))

(defun ethereum-header-gate! (n blk)
  "Block N's header against its parent's: EELS validate_header (header-violation, the
   Lean-emitted spec-header-violation) — gas used, the gas-limit window, the base fee, the
   excess blob gas, timestamp, number, extra data, the difficulty (PoW: the formula; PoS: 0,
   nonce 0, no ommers). The header is hash-checked canonical input, so a miss means OUR
   rule (or an unmodelled fork rule) is wrong from this block on: a MISMATCH, fatal under
   full state like the other header gates. The ommers are validate-ommers!'s (post-block)."
  (when (plusp n)
    (ensure-recent-headers! n blk)
    (let ((bad (header-violation blk (first *recent-headers*) (el-fork))))
      (when bad
        (incf (getf *stats* :mismatches))
        (format t "~&MISMATCH blk=~D header: ~A (EELS validate_header) refuses it against block ~D~%" n bad (1- n))
        (when *full-state*
          (error "block ~D header fails validate_header (~A) — our header rule is wrong from here" n bad))))))

(defun ethereum-pre-block-hook! (world n blk coinbase block-ctx)
  (when (< *fork-ord* +fork-ord-byzantium+)
    ;; Pre-Byzantium receipts carry the post-tx state root, which needs a trie root
    ;; after every tx; the bloom and the gas still check the block.
    (setf *receipts-unverifiable* t))
  (ethereum-header-gate! n blk)
  (when (= n +dao-fork-block+)
    (observe-tx-begin!)
    (apply-dao-fork! world)
    (observe-tx-end! n +preblock-tx+ t))
  (ethereum-pre-block! world n blk coinbase block-ctx))

(defun ethereum-chain-spec ()
  (make-chain-spec
   :name "Ethereum mainnet" :id 1
   :genesis-path "chains/ethereum/genesis.json"
   :banner "fork by block to the Merge, by timestamp after (Evm.Forks.ofBlock)"
   :rpc-url (sb-ext:posix-getenv "ETH_RPC_URL")
   :cache-dir (pathname (let ((d (sb-ext:posix-getenv "ETH_CACHE_DIR")))
                          (if (and d (plusp (length d)))
                              (if (char= (char d (1- (length d))) #\/) d (concatenate 'string d "/"))
                              "lean/external/eth-cache/")))
   :block-setup #'ethereum-block-setup
   :pre-block #'ethereum-pre-block-hook!))     ; post-block: the Ethereum default

(register-chain-spec "ethereum" #'ethereum-chain-spec)

(defun main-ethereum (args)
  (install-chain-spec! (ethereum-chain-spec))
  (replay-main args))

