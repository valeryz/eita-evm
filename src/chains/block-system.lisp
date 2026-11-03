;;;; chains/block-system.lisp — per-block system work around the user transactions, chain-neutral.
;;;;
;;;; System calls (EELS process_unchecked_system_transaction / process_checked_system_
;;;; transaction: the derived spec-system-effect, Evm.CL.EffectSystemProof), under the chain's
;;;; rule (*chain-system-rule*; Ethereum = EELS: nothing warm, GASPRICE the base fee, no end
;;;; of tx). Pre-block:
;;;;   EIP-4788 (Cancun+): parent beacon block root → 0x000F3DF6…BEAC02 (apply-beacon-roots),
;;;;                        when the header carries one
;;;;   EIP-2935 (Prague+): parent hash → the history-storage contract 0x0000F908…2935
;;;; Post-block (EELS <fork>/fork.py apply_body after the txs), one observed system tx:
;;;;   rewards              block + ommer rewards, to London (none from Paris, EIP-3675)
;;;;   EIP-4895 (Shanghai+) withdrawals credited from the block body
;;;;                        (both: spec-block-credits, derived — Evm.CL.EffectBlockProof)
;;;;   EIP-7002/7251 (Prague+) system calls to the withdrawal- and consolidation-request
;;;;                        predeploys; with the EIP-6110 deposit logs their outputs hash to
;;;;                        the EIP-7685 requestsHash the header gate checks (receipts.lisp)
;;;; Default = Ethereum by fork. A chain that runs a different set installs
;;;; *chain-pre-block-hook* (Arc: EIP-2935 only) and/or *chain-post-block-hook* (Arc: the
;;;; SystemAccounting gas-values write; OP: nothing), and *chain-system-rule* when its system
;;;; calls start differently (Arc: arc-node's revm). Observed records of system work carry
;;;; tx index +preblock-tx+ (-1) / +postblock-tx+ (10^9), sorting around the txs.

(in-package #:eita.chain)

(defconstant +preblock-tx+ -1
  "The tx index observers see for pre-block system calls (sorts before every tx).")
(defconstant +postblock-tx+ 1000000000
  "The tx index observers see for post-block system writes (sorts after every tx).")
(defconstant +history-storage-address+ #x0000F90827F1C53a10cb7A02335B175320002935
  "EIP-2935 history storage contract.")
(defconstant +withdrawal-request-predeploy+ #x00000961Ef480Eb55e80D19ad83579A64c007002
  "EIP-7002 withdrawal-request predeploy (Evm.Prague.Requests.withdrawalRequestPredeploy).")
(defconstant +consolidation-request-predeploy+ #x0000BBdDc7CE488642fb579F8B00f3a590007251
  "EIP-7251 consolidation-request predeploy (Evm.Prague.Requests.consolidationRequestPredeploy).")
(defconstant +deposit-contract-address+ #x00000000219ab540356cBB839Cbe05303d7705Fa
  "The mainnet deposit contract (EIP-6110; Evm.Prague.Requests.depositContractAddress).")
(defconstant +deposit-event-signature+ #x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5
  "keccak256(\"DepositEvent(bytes,bytes,bytes,bytes,bytes)\").")
(defconstant +fork-ord-shanghai+ 15)
(defconstant +fork-ord-cancun+ 16)
(defvar *block-deposit-logs* '()
  "Data of this block's DepositEvent logs, newest first (collected by receipts-push!).")
(defvar *block-requests-hash* nil
  "EIP-7685 requestsHash of OUR execution of this block (ethereum-post-block!), or NIL when
   the fork has none; verify-block-header (receipts.lisp) compares it with the header.")

(defvar *chain-pre-block-hook* nil
  "(lambda (world n blk coinbase block-ctx)) replacing the Ethereum-by-fork default.")
(defvar *chain-post-block-hook* nil
  "(lambda (world n blk gas-used coinbase block-ctx)) after the txs; default: none.")

(defvar *chain-system-rule* nil
  "(lambda (target block-ctx)) -> (values seed end-of-tx-p gas-price): how a chain's system
   call starts and ends (Evm.Frontier.Vm.System.Rule). NIL = ethereum-system-rule.")

(defun ethereum-system-rule (target block-ctx)
  "EELS (System.eels): the message starts with EMPTY accessed sets — not the caller, the
   target or the precompiles (process_unchecked_system_transaction: accessed_addresses =
   set()) —, GASPRICE is the block's base fee (gas_price=block_env.base_fee_per_gas), and the
   accounts_to_delete and the touched set are dropped (no end of tx)."
  (declare (ignore target))
  (values '() nil (or (getf block-ctx :base-fee) 0)))

(defun system-call (target data block-ctx &key checked)
  "A system transaction to TARGET with DATA: the derived spec-system-effect (Evm.CL.EffectSystem,
   proved against Evm.Frontier.Vm.System in Evm.CL.EffectSystemProof) — SYSTEM_ADDRESS, the
   whole 30M SYSTEM_TRANSACTION_GAS, no value, no validation, nonce, intrinsic gas or fee —
   under the chain's rule (its warm-up as *system-seed*, its GASPRICE, its end of tx). CHECKED
   (EIP-7002/7251, process_checked_system_transaction): a target without code or a failed call
   invalidates the block — an error (a canonical block cannot carry one: our state or the
   source is wrong). Returns (values success output)."
  (reset-tx-state)
  (setf *last-tx-output* #())
  (multiple-value-bind (seed end gas-price)
      (funcall (or *chain-system-rule* #'ethereum-system-rule) target block-ctx)
    (multiple-value-bind (used out rej)
        (let ((*system-seed* seed))
          (spec-system-effect target data checked *prague-delegation*
                              (list* :effective-gas-price gas-price block-ctx)))
      (declare (ignore used))
      (unless (zerop rej)
        (invalid! "system contract empty" "block ~D: system contract ~(~40,'0x~) has no code" (getf block-ctx :number) target))
      (when (and checked (/= out 1))
        (invalid! "system call failed" "block ~D: system call to ~(~40,'0x~) failed" (getf block-ctx :number) target))
      (when end (spec-destroy-effect) (spec-sweep-effect))
      (values (= out 1) *last-tx-output*))))

(defun eip2935-store-parent-hash! (n parent-hash block-ctx)
  "EIP-2935: the parent hash into the history contract (EELS apply_body: unchecked — its
   outcome does not matter; none at block 0). Observed as the pre-block system tx."
  (when (plusp n)
    (observe-tx-begin!)
    (system-call +history-storage-address+ (u256->octets parent-hash 32) block-ctx)
    (observe-tx-end! n +preblock-tx+ t)))

(defun ethereum-pre-block-of! (n beacon parent-hash block-ctx)
  "Ethereum's pre-block system calls by fork: EIP-4788 (Cancun+, when the header has a
   parent beacon root BEACON), then EIP-2935 (Prague+). The generic driver and the fixture
   runner (src/fixtures/runner.lisp) both come through here."
  (when (and beacon (>= (el-fork) +fork-ord-cancun+))
    (observe-tx-begin!)
    (apply-beacon-roots beacon block-ctx)
    (observe-tx-end! n +preblock-tx+ t))
  (when (>= (el-fork) +fork-ord-prague+)
    (eip2935-store-parent-hash! n parent-hash block-ctx)))

(defun ethereum-pre-block! (world n blk coinbase block-ctx)
  "ethereum-pre-block-of! on a decoded block BLK."
  (declare (ignore world coinbase))
  (ethereum-pre-block-of! n (blk-parent-beacon-root blk) (blk-parent-hash blk) block-ctx))

(defun run-pre-block! (world n blk coinbase block-ctx)
  (funcall (or *chain-pre-block-hook* #'ethereum-pre-block!) world n blk coinbase block-ctx))

;;; --- EIP-4788: parent beacon block root system call ---

(defconstant +beacon-roots-address+
  #x000F3DF6D732807EF1319FB7B8BB8522D0BEAC02)

(defun apply-beacon-roots (parent-beacon-root block-ctx)
  "EIP-4788: at block start, the system call to +beacon-roots-address+ with the parent
   beacon block root as calldata (EELS apply_body: unchecked — its outcome does not matter)."
  (system-call +beacon-roots-address+ (u256->octets parent-beacon-root 32) block-ctx))

;;; --- The header gate: EELS validate_header and validate_ommers --------------------------
;;; A block's header against its parent's (and each ommer's against its canonical parent),
;;; every fork: the emitted spec-header-violation (Evm.CL.HeaderEmit.headerViolation, proved
;;; equal to Evm.Frontier.Spec.HeaderValidity.validateHeader — EELS <fork>/fork.py
;;; validate_header, check_gas_limit, calculate_block_difficulty, calculate_base_fee_per_gas,
;;; calculate_excess_blob_gas). The seam here only reads fields and compares bytes. Not
;;; checked: the proof-of-work seal (ethash validate_proof_of_work), Osaka's block RLP size.

(defparameter +empty-ommers-hash+
  (coerce #(#x1d #xcc #x4d #xe8 #xde #xc7 #x5d #x7a #xab #x85 #xb5 #x67 #xb6 #xcc #xd4 #x1a
            #xd3 #x12 #x45 #x1b #x94 #x8a #x74 #x13 #xf0 #xa1 #x42 #xfd #x40 #xd4 #x93 #x47)
          '(simple-array (unsigned-byte 8) (*)))
  "EMPTY_OMMER_HASH = keccak256(rlp([])) (paris/fork.py 67).")

(defparameter +dao-extra-data+ (map '(simple-array (unsigned-byte 8) (*)) #'char-code "dao-hard-fork")
  "The extra_data dao_fork/fork.py validate_header requires of blocks 1,920,000..1,920,009.")

(defparameter +header-violations+
  #(nil "excessBlobGas" "gasUsed above gasLimit" "gasLimit" "baseFeePerGas" "timestamp" "number"
    "extraData" "difficulty" "nonce" "ommersHash" "dao extraData")
  "The rule each spec-header-violation code names (Evm.Frontier.Spec.HeaderValidity.Violation.code).")

(defun header-record (blk &optional ommer-hashes)
  "What a child's header gate reads of BLK's header (a parent; NIL where the header has no
   such field), with its hash, its parent's and OMMER-HASHES, the hashes of the ommers it
   included (validate_ommers: an ommer may not be included twice)."
  (list :number (blk-number blk) :hash (blk-hash blk) :parent-hash (blk-parent-hash blk)
        :timestamp (blk-timestamp blk) :gas-limit (blk-gas-limit blk) :gas-used (blk-gas-used blk)
        :difficulty (blk-difficulty blk) :base-fee (blk-base-fee blk)
        :excess-blob-gas (blk-excess-blob-gas blk) :blob-gas-used (blk-blob-gas-used blk)
        :ommers-p (not (equalp (blk-sha3-uncles blk) +empty-ommers-hash+)) :ommer-hashes ommer-hashes))

(defun header-violation (blk parent fork-ord)
  "EELS validate_header of BLK's header (a block's or an ommer's) against PARENT (a
   header-record) at FORK-ORD: NIL when valid, else the rule's name (+header-violations+).
   A field the fork's header must carry and BLK's lacks is that field's violation (the
   header does not decode as the fork's)."
  (flet ((flag (x) (if x 1 0)) (int (v) (if v (octets-int v) 0)))
    (cond ((and (>= fork-ord 11) (null (blk-base-fee blk))) "baseFeePerGas")
          ((and (>= fork-ord 16) (null (blk-excess-blob-gas blk))) "excessBlobGas")
          (t (svref +header-violations+
                    (spec-header-violation
                     (blk-number blk) (blk-timestamp blk) (blk-gas-limit blk) (blk-gas-used blk)
                     (length (blk-extra-data blk)) (blk-difficulty blk) (int (blk-nonce blk))
                     (or (blk-base-fee blk) 0) (or (blk-excess-blob-gas blk) 0)
                     (getf parent :number) (getf parent :timestamp) (getf parent :gas-limit)
                     (getf parent :gas-used) (getf parent :difficulty) (or (getf parent :base-fee) 0)
                     (or (getf parent :excess-blob-gas) 0) (or (getf parent :blob-gas-used) 0)
                     (flag (equalp (blk-extra-data blk) +dao-extra-data+))
                     (flag (equalp (blk-sha3-uncles blk) +empty-ommers-hash+))
                     (flag (getf parent :ommers-p))
                     ;; the London fork block (EELS: number = FORK_CRITERIA.block_number) is
                     ;; the one whose parent has no base fee
                     (flag (null (getf parent :base-fee)))
                     fork-ord))))))

(defvar *recent-headers* '()
  "header-records of the canonical blocks before the current one, newest first, at most
   MAX_OMMER_DEPTH + 1 = 7 (EELS validate_ommers' recent_canonical_blocks): the parent the
   header gate reads, and the window validate-ommers! checks against.")

(defun note-canonical-block! (blk ommer-hashes)
  "BLK ran: it is the newest of *recent-headers*."
  (push (header-record blk ommer-hashes) *recent-headers*)
  (when (> (length *recent-headers*) 7) (setf *recent-headers* (subseq *recent-headers* 0 7))))

(defun validate-ommers! (blk uncles fork-ord)
  "EELS validate_ommers (frontier/fork.py 478-551; the same in every fork to Gray Glacier;
   from Paris any ommer is refused by the header's ommersHash) of BLK's UNCLES (decoded
   headers, already tied to its sha3Uncles), against *recent-headers*: each ommer 1 <= number
   < BLK's and valid against the canonical header at its number - 1 (validate_header,
   including its parent hash); at most 2; no two the same; none BLK itself, a recent
   canonical block or an ommer a recent block included; age 1..6; its parent a recent
   canonical block, not BLK's parent. One whose canonical parent is older than the window has
   age > 6 and is refused by the age rule (EELS's validate_header would look it up first:
   either way the block is invalid). Signals block-invalid."
  (let ((n (blk-number blk)))
    (dolist (u uncles)
      (unless (< 0 (blk-number u) n)
        (invalid! "ommer number" "block ~D: ommer number ~D" n (blk-number u)))
      (let ((parent (find (1- (blk-number u)) *recent-headers* :key (lambda (r) (getf r :number)))))
        (when parent
          (let ((bad (header-violation u parent fork-ord)))
            (when bad (invalid! bad "block ~D: ommer ~D: header ~A" n (blk-number u) bad)))
          (unless (= (blk-parent-hash u) (getf parent :hash))
            (invalid! "ommer parent" "block ~D: ommer ~D: parentHash is not block ~D's hash" n (blk-number u) (1- (blk-number u)))))))
    (when (> (length uncles) 2)
      (invalid! "too many ommers" "block ~D: ~D ommers" n (length uncles)))
    (let ((hashes (mapcar #'blk-header-hash uncles))
          (canonical (mapcar (lambda (r) (getf r :hash)) *recent-headers*))
          (included (loop for r in *recent-headers* append (getf r :ommer-hashes))))
      (unless (= (length hashes) (length (remove-duplicates hashes)))
        (invalid! "duplicate ommer" "block ~D: an ommer twice" n))
      (loop for u in uncles for h in hashes
            do (cond ((or (= h (blk-hash blk)) (member h canonical))
                      (invalid! "ommer in chain" "block ~D: ommer ~D is a canonical block" n (blk-number u)))
                     ((member h included)
                      (invalid! "ommer already included" "block ~D: ommer ~D was included before" n (blk-number u)))
                     ((not (<= 1 (- n (blk-number u)) 6))
                      (invalid! "ommer age" "block ~D: ommer ~D is ~D deep" n (blk-number u) (- n (blk-number u))))
                     ((not (member (blk-parent-hash u) canonical))
                      (invalid! "ommer parent" "block ~D: ommer ~D's parent is not a recent canonical block" n (blk-number u)))
                     ((= (blk-parent-hash u) (blk-parent-hash blk))
                      (invalid! "ommer is sibling" "block ~D: ommer ~D is a sibling of the block" n (blk-number u))))))))

;;; --- Block credits: rewards, withdrawals (the derived spec-block-credits) ----------

(defun block-credit! (addr wei)
  "A block-level credit (EELS create_ether outside a tx: a reward, a withdrawal), the
   primitive the emitted spec-block-credits calls: no journal, no tx."
  (fault-account! addr)                         ; a lazy world starts empty
  (incf (balance-of *current-world* addr) wei)
  (when *mpt-tracking* (mpt-touch! addr)))

;;; --- Post-block: rewards, withdrawals, requests -------------------------------------

(defun sha256-bytes (bytes)
  (let ((in (coerce bytes 'octets)) (out (make-array 32 :element-type '(unsigned-byte 8))))
    (cffi:with-pointer-to-vector-data (ip in)
      (cffi:with-pointer-to-vector-data (op out) (%sha256-hash ip (length in) op)))
    out))

(defun deposit-request (data)
  "EELS prague/requests.py extract_deposit_data: a DepositEvent's ABI data (576 bytes, five
   dynamic `bytes` at fixed offsets) → pubkey ‖ withdrawal_credentials ‖ amount ‖ signature
   ‖ index, 192 bytes. The offsets and lengths are checked as EELS does: anything else is
   not a deposit the chain could have accepted."
  (flet ((word (off) (let ((x 0)) (loop for i from off below (+ off 32) do (setf x (logior (ash x 8) (aref data i)))) x)))
    (unless (= (length data) 576) (invalid! "deposit layout" "DepositEvent data: ~D bytes, not 576" (length data)))
    (loop for (off size) in '((160 48) (256 32) (320 8) (384 96) (512 8)) for i from 0
          unless (and (= (word (* 32 i)) off) (= (word off) size))
            do (invalid! "deposit layout" "DepositEvent data: field ~D not at offset ~D with length ~D" i off size))
    (concatenate 'octets (subseq data 192 240) (subseq data 288 320) (subseq data 352 360)
                 (subseq data 416 512) (subseq data 544 552))))

(defun request-system-call (target block-ctx)
  "EELS process_checked_system_transaction for a request predeploy (the contract must have
   code and the call must succeed, else the block is invalid); its output is the type's
   payload."
  (nth-value 1 (system-call target #() block-ctx :checked t)))

(defun requests-hash (payloads)
  "EIP-7685: sha256 over sha256(type ‖ payload) of each non-empty type, in type order
   (EELS prague/requests.py compute_requests_hash; Evm.Prague.Spec.IsRequestsHashValid)."
  (sha256-bytes (apply #'concatenate 'octets
                       (loop for p in payloads for type from 0
                             when (plusp (length p)) collect (sha256-bytes (concatenate 'octets (vector type) p))))))

(defun ethereum-post-block-of! (world n uncles withdrawals coinbase block-ctx)
  "Ethereum's post-block state changes by fork, in EELS apply_body order, as one observed
   system tx: the block and ommer rewards (to London) and the EIP-4895 withdrawals (from
   Shanghai) — spec-block-credits, derived from Evm.Frontier.Vm.Block.postBlock (UNCLES
   (miner . number), WITHDRAWALS (address . gwei)) — then the EIP-7002/7251 request system
   calls whose outputs, with the block's deposit logs, give the EIP-7685 requestsHash
   (Prague+; compared with the header by verify-block-header). The generic driver and the
   fixture runner both come through here."
  (observe-tx-begin!)
  (let ((*current-world* world))
    (spec-block-credits coinbase n uncles withdrawals))
  (when (>= (el-fork) +fork-ord-prague+)
    (let* ((deposits (apply #'concatenate 'octets (mapcar #'deposit-request (reverse *block-deposit-logs*))))
           (withdrawals (request-system-call +withdrawal-request-predeploy+ block-ctx))
           (consolidations (request-system-call +consolidation-request-predeploy+ block-ctx)))
      (setf *block-requests-hash* (requests-hash (list deposits withdrawals consolidations)))))
  (observe-tx-end! n +postblock-tx+ t))

(defun block-ommers (blk)
  "BLK's ommer headers (fetch-uncles), tied to its header's sha3Uncles: they are body data,
   like the txs (EELS validate_ommers' first clause)."
  (let ((uncles (fetch-uncles blk)))
    (unless (equalp (blk-sha3-uncles blk)
                    (keccak256-bytes (coerce (rlp-encode-list (mapcar (lambda (u) (coerce (blk-header-rlp u) 'list)) uncles)) 'octets)))
      (invalid! "sha3Uncles" "block ~D: its ommer headers do not hash to the header's sha3Uncles" (blk-number blk)))
    uncles))

(defun ethereum-post-block! (world n blk gas-used coinbase block-ctx)
  "ethereum-post-block-of! on a decoded block BLK (its ommers (block-ommers) validated
   (validate-ommers!) before they pay); then BLK is the newest of *recent-headers*."
  (declare (ignore gas-used))
  (let ((uncles (block-ommers blk)))
    (when uncles (validate-ommers! blk uncles (el-fork)))
    (ethereum-post-block-of!
     world n
     (mapcar (lambda (u) (cons (blk-miner u) (blk-number u))) uncles)
     (mapcar (lambda (w) (cons (third w) (fourth w))) (blk-withdrawals blk))
     coinbase block-ctx)
    (note-canonical-block! blk (mapcar #'blk-header-hash uncles))))

(defun run-post-block! (world n blk gas-used coinbase block-ctx)
  (funcall (or *chain-post-block-hook* #'ethereum-post-block!) world n blk gas-used coinbase block-ctx))
