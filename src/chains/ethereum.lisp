;;;; chains/ethereum.lisp — Ethereum on the generic driver (Ethereum track, E): mainnet, the
;;;; Hoodi testnet and a devnet (mainnet's rules; their own data: `ethereum-chain-spec`).
;;;;
;;;; Blocks, receipts and uncles are JSON-RPC results (eth_getBlockByNumber,
;;;; eth_getBlockReceipts, eth_getUncleByBlockNumberAndIndex), from the installed block
;;;; source (src/input/; docs/block-input.md). What Ethereum changes
;;;; about the generic replay:
;;;;   fork          spec-mainnet-fork-ord, emitted from Evm.Forks.ofBlock (Evm.CL.ForkEmit);
;;;;                 Hoodi: spec-hoodi-fork-ord, from Evm.Fork.ofHoodi (Evm/Testnets.lean);
;;;;                 a devnet: spec-times-fork-ord (Evm.Fork.ofTimes) at its genesis.json times
;;;;   pre-block     the DAO irregular state change at 1,920,000 on mainnet (EELS apply_dao),
;;;;                 then the generic EIP-4788/2935 system calls by fork
;;;;   post-block    the generic Ethereum default (block-system.lisp): rewards from the
;;;;                 uncle headers (0 from Paris), withdrawals, request system calls
;;;; Receipts before Byzantium embed a per-tx state root, so receiptsRoot is checked from
;;;; Byzantium on; the logs bloom is checked on every block. Post-Merge chunks (era
;;;; archives) carry no receipts: the header gate alone.
;;;;
;;;; Run: eita replay --chain ethereum|hoodi --blocks DIR --from N --to M   (full state from genesis)
;;;; ETH_CACHE_DIR = the chunk directory (default lean/external/eth-cache/, …/hoodi-cache/);
;;;; ETH_RPC_URL = an endpoint, for lazy runs and a deployment's block source (Hoodi: default
;;;; the public rpc.hoodi.ethpandaops.io).

(in-package #:eita.chain.ethereum)

(defconstant +fork-ord-byzantium+ 5)
(defconstant +dao-fork-block+ 1920000)
(defconstant +dao-recovery+ #xbf4ed7b27f1d666546e30d74d50d173d20bca754)

(defun ethereum-block-setup (fork-ord)
  "The block-setup hook of a network whose Lean schedule is FORK-ORD (n ts) -> ord: the
   fork of each block from it; the native dispatch follows it."
  (lambda (n blk ts)
    (declare (ignore blk))
    (let ((ord (funcall fork-ord n ts)))
      (unless (= ord *fork-ord*)
        (format t "~&block ~D: fork ord ~D -> ~D~%" n *fork-ord* ord)
        (setf *fork-ord* ord)
        (%set-fork ord)))))

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

(defun ethereum-pre-block-hook (dao-block)
  "The pre-block hook of a network whose DAO irregular state change is at DAO-BLOCK (NIL:
   it has none)."
  (lambda (world n blk coinbase block-ctx)
    (when (< *fork-ord* +fork-ord-byzantium+)
      ;; Pre-Byzantium receipts carry the post-tx state root, which needs a trie root
      ;; after every tx; the bloom and the gas still check the block.
      (setf *receipts-unverifiable* t))
    (ethereum-header-gate! n blk)
    (when (eql n dao-block)
      (observe-tx-begin!)
      (apply-dao-fork! world)
      (observe-tx-end! n +preblock-tx+ t))
    (ethereum-pre-block! world n blk coinbase block-ctx)))

(defparameter +devnet-forks+
  '(("cancun" . 16) ("prague" . 17) ("osaka" . 18) ("bpo1" . 19) ("bpo2" . 20))
  "The blobSchedule entries a devnet may name, with their fork ords (Evm.Fork.ord).")

(defun devnet-schedule (path)
  "The devnet whose geth genesis.json is PATH: (values chain-id prague osaka bpo1 bpo2), the
   activation times spec-times-fork-ord reads (a fork it does not schedule: never). Refused:
   a network that is not mainnet's rules scheduled by Evm.Fork.ofTimes — every block-numbered
   fork, shanghaiTime, cancunTime and the TTD at 0; Prague ≤ Osaka ≤ BPO1 ≤ BPO2; nothing
   later (Amsterdam, BPO3+) — and a blobSchedule entry other than the Lean schedule's for its
   fork (spec-blob-schedule-*: the fork ords carry those parameters)."
  (let* ((config (jval (jsown:parse (alexandria:read-file-into-string path)) "config"))
         (never (expt 2 64)) (times '()))
    (flet ((refuse (fmt &rest args)
             (error "devnet ~A: ~? — not a network on Evm.Fork.ofTimes (mainnet's rules, Cancun at genesis, then Prague, Osaka, BPO1, BPO2 by time)"
                    path fmt args)))
      (dolist (k (jsown:keywords config))
        (let ((v (jsown:val config k)))
          (cond ((member k '("chainId" "depositContractAddress" "blobSchedule" "daoForkSupport" "terminalTotalDifficultyPassed")
                         :test #'string=))
                ((member k '("pragueTime" "osakaTime" "bpo1Time" "bpo2Time") :test #'string=)
                 (unless (typep v '(integer 0)) (refuse "~A = ~S" k v))
                 (push (cons k v) times))
                ((or (member k '("shanghaiTime" "cancunTime" "terminalTotalDifficulty") :test #'string=)
                     (and (> (length k) 5) (string= "Block" k :start2 (- (length k) 5))))
                 (unless (eql v 0) (refuse "~A = ~S, not 0" k v)))
                (t (refuse "config ~A = ~S" k v)))))
      (let ((sched (mapcar (lambda (k) (or (cdr (assoc k times :test #'string=)) never))
                           '("pragueTime" "osakaTime" "bpo1Time" "bpo2Time"))))
        (unless (apply #'<= sched) (refuse "fork times ~S out of order" sched))
        (let ((blobs (jsown:val-safe config "blobSchedule")))
          (dolist (k (and blobs (jsown:keywords blobs)))
            (let ((ord (cdr (assoc k +devnet-forks+ :test #'string=))) (e (jsown:val blobs k)))
              (unless (and ord (equal (list (jsown:val-safe e "target") (jsown:val-safe e "max")
                                            (jsown:val-safe e "baseFeeUpdateFraction"))
                                      (list (spec-blob-schedule-target ord) (spec-blob-schedule-max ord)
                                            (spec-blob-base-fee-update-fraction ord))))
                (refuse "blobSchedule ~A ~A" k (jsown:to-json e))))))
        (apply #'values (jval config "chainId") sched)))))

(defun ethereum-chain-spec (&optional (net "mainnet"))
  "Mainnet, the Hoodi testnet, or a devnet: mainnet's rules with its own chain id, genesis and
   Lean fork schedule, and no DAO block. ETH_RPC_URL and ETH_CACHE_DIR are the installed
   network's (a devnet has neither: its blocks come from its block source); a devnet's
   genesis.json is EITA_GENESIS (`replay --genesis`), its id and fork times read from it."
  (let ((hoodi (string= net "hoodi")) (devnet (string= net "devnet")))
    (assert (or hoodi devnet (string= net "mainnet")) () "unknown Ethereum network ~S (mainnet, hoodi, devnet)" net)
    (multiple-value-bind (id prague osaka bpo1 bpo2)
        (if devnet
            (devnet-schedule (or (eita.chain::env "GENESIS") (error "devnet: its genesis.json is --genesis (EITA_GENESIS)")))
            (if hoodi 560048 1))
      (let ((fork-ord (cond (hoodi (lambda (n ts) (declare (ignore n)) (spec-hoodi-fork-ord ts)))
                            (devnet (lambda (n ts) (declare (ignore n)) (spec-times-fork-ord ts prague osaka bpo1 bpo2)))
                            (t #'spec-mainnet-fork-ord))))
        (make-chain-spec
         :name (cond (hoodi "Ethereum Hoodi") (devnet (format nil "Ethereum devnet ~D" id)) (t "Ethereum mainnet")) :id id
         :genesis-path (cond (hoodi "chains/hoodi/genesis.json") (devnet (eita.chain::env "GENESIS")) (t "chains/ethereum/genesis.json"))
         :banner (cond (hoodi "Cancun from genesis, then by timestamp (Evm.Fork.ofHoodi)")
                       (devnet (format nil "Cancun from genesis, then Prague ~D, Osaka ~D, BPO1 ~D, BPO2 ~D (Evm.Fork.ofTimes)"
                                       prague osaka bpo1 bpo2))
                       (t "fork by block to the Merge, by timestamp after (Evm.Forks.ofBlock)"))
         :rpc-url (unless devnet (or (sb-ext:posix-getenv "ETH_RPC_URL") (and hoodi "https://rpc.hoodi.ethpandaops.io")))
         :cache-dir (unless devnet
                      (pathname (let ((d (sb-ext:posix-getenv "ETH_CACHE_DIR")))
                                  (cond ((and d (plusp (length d)))
                                         (if (char= (char d (1- (length d))) #\/) d (concatenate 'string d "/")))
                                        (hoodi "lean/external/hoodi-cache/")
                                        (t "lean/external/eth-cache/")))))
         :fork-ord fork-ord
         :block-setup (ethereum-block-setup fork-ord)
         :pre-block (ethereum-pre-block-hook (unless (or hoodi devnet) +dao-fork-block+)))))))   ; post-block: the Ethereum default

(register-chain-spec "ethereum" #'ethereum-chain-spec)
(register-chain-spec "hoodi" (lambda () (ethereum-chain-spec "hoodi")))
(register-chain-spec "devnet" (lambda () (ethereum-chain-spec "devnet")))

(defun main-ethereum (args &optional (net "mainnet"))
  (install-chain-spec! (ethereum-chain-spec net))
  (replay-main args))

