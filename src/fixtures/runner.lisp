;;;; fixtures.lisp — the BlockchainTests runner (ethereum/tests, execution-spec-tests), on
;;;; the generic driver's block pipeline: the pre-block system calls and the post-block
;;;; effects of block-system.lisp, the user txs of evm/run-tx.lisp (run-evm-tx: the derived tx
;;;; effect, settlement and end of tx) — the code every chain driver runs, so a fixture
;;;; checks it, not a second copy. Per test: the network's fork, the pre-state, the canonical
;;;; chain's blocks, each checked against its header as the driver checks it (validate_header,
;;;; hash, sha3Uncles, the ommers, verify-block-header) and its stateRoot (the driver's anchor check, here
;;;; every block), the post-state compared account by account. Then every
;;;; block the fixture marks `expectException` runs on that post-state and must be REJECTED
;;;; for the expected reason (`INVALID ...` lines, counted in the summary).
;;;;
;;;;   eita fixtures <test.json | flat directory>...
;;;;
;;;; Expected failures are listed, with their reasons, in src/fixtures/expected-failures.txt and
;;;; reported as XFAIL/XPASS.

(in-package #:eita.fixtures)



;;; --- JSON test parsing ---

(defun parse-account (json)
  (list :balance (hex->int (jval json "balance"))
        :nonce   (hex->int (jval json "nonce"))
        :code    (hex->bytes (jval json "code"))
        :storage (let ((s (jval json "storage")))
                   (when s
                     (loop for k in (jsown:keywords s)
                           collect (cons (hex->int k)
                                         (hex->int (jval s k))))))))

(defparameter +fixture-header-names+
  '(("uncleHash" . "sha3Uncles") ("coinbase" . "miner") ("transactionsTrie" . "transactionsRoot")
    ("receiptTrie" . "receiptsRoot") ("bloom" . "logsBloom"))
  "Fixture header keys that the JSON-RPC block object names differently.")

(defun rpc-header (hdr &rest more)
  "The fixture header JSON HDR under the JSON-RPC names, with the members MORE."
  `(:obj ,@(loop for (k . v) in (cdr hdr) collect (cons (or (cdr (assoc k +fixture-header-names+ :test #'string=)) k) v))
         ,@more))

(defun parse-block (json)
  "The fixture block JSON decoded by the driver's decoder (input/ decode-block), as an RPC
   block: its header under the RPC names, the txs (a tx with no \"sender\" recovers it),
   the withdrawals; the ommer headers (they pay the block rewards) as its uncles."
  (let ((blk (decode-block-json (rpc-header (jval json "blockHeader") (cons "transactions" (jval json "transactions"))
                                            (cons "withdrawals" (jval json "withdrawals"))))))
    (dolist (tx (blk-txs blk)) (unless (tx-sender tx) (setf (tx-sender tx) (or (recover-tx-sender tx) 0))))
    (setf (blk-uncles blk) (mapcar (lambda (u) (decode-block-json (rpc-header u))) (jval json "uncleHeaders"))
          (blk-uncle-count blk) (length (blk-uncles blk)))
    blk))

(defun parse-test (test-name json)
  (let* ((config (jval json "config"))
         (gen-hdr (jval json "genesisBlockHeader"))
         (gen-hash (when gen-hdr (hex->int (or (jval gen-hdr "hash") "0"))))
         (gen-num  (when gen-hdr (hex->int (or (jval gen-hdr "number") "0")))))
    (list :name      test-name
          ;; Newer fixtures store network under config.network; older
          ;; LegacyTests/Cancun fixtures use a top-level "network" field.
          :network   (or (and config (jval config "network"))
                         (jval json "network"))
          :genesis-hash gen-hash
          :genesis-number gen-num
          :genesis-header (when gen-hdr (header-record (decode-block-json (rpc-header gen-hdr))))
          ;; Eita's own mainnet repro fixtures (tests/data/mainnet-*.json.gz) carry only
          ;; the accounts and slots the block touches, so the header's stateRoot (a root over
          ;; the WHOLE state) cannot be reproduced from them; they say so, and the runner says
          ;; it did not check it. Receipts root, gasUsed and bloom still cover every tx.
          :partial-pre (eq (jval json "eitaPartialPreState") t)
          :lastblockhash (let ((s (jval json "lastblockhash")))
                           (and s (hex->int s)))
          :pre       (let ((pre (jval json "pre")))
                       (when pre
                         (loop for addr in (jsown:keywords pre)
                               collect (cons (hex->int addr)
                                             (parse-account (jval pre addr))))))
          ;; A block carrying `expectException` is one the client must REJECT (e.g.
          ;; TransactionException.NONCE_IS_MAX): it leaves no state, so the chain the
          ;; postState describes is the valid blocks only. The invalid ones run after it
          ;; (run-invalid-blocks), from their decoded form (`rlp_decoded`); one that has
          ;; none, or whose fields do not parse (a value past 2^256), has a NIL block.
          :blocks    (mapcar #'parse-block (remove-if (lambda (b) (jval b "expectException")) (jval json "blocks")))
          :invalid   (loop for b in (jval json "blocks")
                           for ex = (jval b "expectException")
                           when ex collect (cons ex (let ((d (jval b "rlp_decoded"))) (and d (ignore-errors (parse-block d))))))
          :post      (let ((p (jval json "postState")))
                       (when p
                         (loop for addr in (jsown:keywords p)
                               collect (cons (hex->int addr)
                                             (parse-account (jval p addr)))))))))

;;; --- Populate world from pre ---


;;; --- Compare post-state ---

(defun compare-post (world expected)
  "Returns list of mismatches; each is (kind addr ...)."
  (let ((mismatches '()))
    (dolist (entry expected)
      (let* ((addr (car entry))
             (acct (cdr entry))
             (exp-bal (getf acct :balance))
             (exp-nonce (getf acct :nonce))
             (exp-code (getf acct :code))
             (exp-storage (getf acct :storage))
             (got-bal (balance-of world addr))
             (got-nonce (nonce-of world addr))
             (got-code (with-acct (tb a) world addr (acct-code tb a))))
        (unless (= exp-bal got-bal)
          (push (list :balance addr :expected exp-bal :got got-bal) mismatches))
        (unless (= exp-nonce got-nonce)
          (push (list :nonce addr :expected exp-nonce :got got-nonce) mismatches))
        (unless (equalp exp-code got-code)
          (push (list :code addr :expected-len (length exp-code) :got-len (length got-code))
                mismatches))
        (dolist (kv exp-storage)
          (let ((slot (car kv))
                (exp-v (cdr kv))
                (got-v (world-storage-get world addr (car kv))))
            (unless (= exp-v got-v)
              (push (list :storage addr :slot slot :expected exp-v :got got-v)
                    mismatches))))))
    ;; Presence (what the state root sees and the fields above do not): every account of
    ;; the expected post-state exists, and no other does — an empty account left behind
    ;; or one destroyed too early. Not for a fixture that gives only postStateHash.
    (when expected
      (let ((*current-world* world)
            (listed (make-hash-table :test 'eql))
            (seen (make-hash-table :test 'eql)))
        (dolist (entry expected)
          (setf (gethash (car entry) listed) t)
          (unless (world-account-present-p (car entry))
            (push (list :absent (car entry)) mismatches)))
        (let ((tb (world-accts world))) (map-accts (lambda (r) (setf (gethash (acct-addr tb r) seen) t)) tb))
        (maphash (lambda (a v) (declare (ignore v))
                   (when (and (not (gethash a listed)) (world-account-present-p a))
                     (push (list :extra a) mismatches)))
                 seen)))
    (nreverse mismatches)))

;;; --- Test runner ---

(defvar *partial-pre-state* nil
  "True while running a fixture marked eitaPartialPreState: its stateRoot is not checked.")

(defun run-block-checked (world blk)
  "BLK on the generic driver's pipeline (src/chains/driver.lisp run-block) — the header
   gate against its parent (header-violation: EELS validate_header; the parent is the newest
   of *recent-headers*), the header hash, the pre-block system calls, the user txs
   (run-evm-tx: the derived tx effect, settlement, end of tx), the post-block effects (the
   ommers: validate-ommers!), then verify-block-header — on WORLD. NIL when the block is
   valid, else why not: (KIND . TEXT), KIND a header field or a `block-invalid` kind, :error
   for any other failure."
  (setf *current-block-number* (blk-number blk))
  (let ((bad (and *recent-headers* (header-violation blk (first *recent-headers*) *fork-ord*))))
    (when bad (return-from run-block-checked (cons bad (format nil "header ~A: EELS validate_header refuses it" bad)))))
  (unless (= (blk-header-hash blk) (blk-hash blk))
    (return-from run-block-checked (cons "hash" "the header does not hash to its hash")))
  (let* ((n (blk-number blk))
         (coinbase (blk-miner blk))
         (total-gas 0)
         (block-ctx (list :timestamp (blk-timestamp blk)
                          :number    n
                          :base-fee  (or (blk-base-fee blk) 0)
                          :gas-limit (blk-gas-limit blk)
                          ;; DIFFICULTY pre-Merge, RANDAO mix after (EIP-4399).
                          :prev-randao (if (< *fork-ord* 14) (blk-difficulty blk) (blk-mix-hash blk))
                          :coinbase  coinbase
                          :chain-id  1
                          ;; EIP-4844: the block's blob base fee, once per block.
                          :blob-base-fee (block-blob-base-fee (or (blk-excess-blob-gas blk) 0) *fork-ord*))))
    (setf *el-fork-ord* nil
          *prague-delegation* (>= *fork-ord* +fork-ord-prague+))
    (receipts-block-begin!)
    ;; receipts before Byzantium carry a per-tx state root (the Ethereum driver's rule)
    (setf *receipts-unverifiable* (< *fork-ord* 5))
    (handler-case
        (let ((*current-world* world))
          (run-pre-block! world n blk coinbase block-ctx)
          (loop for tx in (blk-txs blk) for idx from 0
                do (multiple-value-bind (gas status) (run-evm-tx world tx block-ctx coinbase n idx)
                     (incf total-gas gas)
                     (receipts-push! (tx-type tx) status gas *last-tx-logs*)))
          ;; the driver's: the ommers tied to sha3Uncles before they pay, then the post-block effects
          (run-post-block! world n blk total-gas coinbase block-ctx))
      (block-invalid (e) (return-from run-block-checked (cons (invalid-kind e) (princ-to-string e))))
      (error (e) (return-from run-block-checked (cons :error (remove #\Newline (princ-to-string e))))))
    (let ((bad (verify-block-header blk total-gas)))
      (cond (bad (cons (first bad) (format nil "header ~{~A~^, ~} not reproduced" bad)))
            (*partial-pre-state* nil)
            ((not (equal (world-state-root world) (string-downcase (blk-state-root blk))))
             (cons "stateRoot" "header stateRoot not reproduced"))))))


(defparameter *exception-kinds*
  ;; EEST's names, then ethereum/tests' legacy ones (TR_…)
  '(("tx type" "TYPE_1_TX_PRE_FORK" "TYPE_2_TX_PRE_FORK" "TYPE_3_TX_PRE_FORK" "TYPE_4_TX_PRE_FORK" "TR_TypeNotSupported")
    ("intrinsic gas" "INTRINSIC_GAS_TOO_LOW" "INTRINSIC_GAS_BELOW_FLOOR_GAS_COST" "TR_IntrinsicGas" "IntrinsicGas" "TR_NoFundsOrGas")
    ("init code size" "INITCODE_SIZE_EXCEEDED" "TR_InitCodeLimitExceeded") ("nonce overflow" "NONCE_IS_MAX" "TR_NonceHasMaxValue")
    ("gas above TX_MAX_GAS_LIMIT" "GAS_LIMIT_EXCEEDS_MAXIMUM")
    ("priority fee above max fee" "PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS" "TR_TipGtFeeCap")
    ("max fee below base fee" "INSUFFICIENT_MAX_FEE_PER_GAS" "TR_FeeCapLessThanBlocks")
    ("gas price below base fee" "INSUFFICIENT_MAX_FEE_PER_GAS" "TR_FeeCapLessThanBlocks")
    ("no blobs" "TYPE_3_TX_ZERO_BLOBS" "TR_EMPTYBLOB") ("too many blobs" "TYPE_3_TX_BLOB_COUNT_EXCEEDED")
    ("blob versioned hash version" "TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH" "TR_BLOBVERSION_INVALID")
    ("max blob fee below blob base fee" "INSUFFICIENT_MAX_FEE_PER_BLOB_GAS")
    ("type cannot create" "TYPE_3_TX_CONTRACT_CREATION" "TYPE_4_TX_CONTRACT_CREATION" "TR_BLOBCREATE")
    ("empty authorization list" "TYPE_4_EMPTY_AUTHORIZATION_LIST")
    ("nonce mismatch" "NONCE_MISMATCH_TOO_LOW" "NONCE_MISMATCH_TOO_HIGH" "TR_NonceTooLow" "TR_NonceTooHigh")
    ("insufficient balance" "INSUFFICIENT_ACCOUNT_FUNDS" "GASLIMIT_PRICE_PRODUCT_OVERFLOW" "TR_NoFunds" "TR_NoFundsX" "TR_NoFundsOrGas"
     "SenderNotEOAorNoCASH")                                   ; a legacy OR of two classes
    ("sender not an EOA" "SENDER_NOT_EOA" "SenderNotEOA" "SenderNotEOAorNoCASH")
    ("gas allowance" "GAS_ALLOWANCE_EXCEEDED" "GAS_USED_OVERFLOW" "TR_GasLimitReached" "TooMuchGasUsed")
    ("blob gas allowance" "TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED" "BLOB_GAS_USED_ABOVE_LIMIT" "TR_BLOBLIST_OVERSIZE")
    ("system contract empty" "SYSTEM_CONTRACT_EMPTY") ("system call failed" "SYSTEM_CONTRACT_CALL_FAILED")
    ("deposit layout" "INVALID_DEPOSIT_EVENT_LAYOUT")
    ("baseFeePerGas" "INVALID_BASEFEE_PER_GAS") ("excessBlobGas" "INCORRECT_EXCESS_BLOB_GAS")
    ("blobGasUsed" "INCORRECT_BLOB_GAS_USED")
    ("gasUsed" "INVALID_GAS_USED" "InvalidGasUsed") ("logsBloom" "INVALID_LOG_BLOOM" "InvalidLogBloom")
    ("receiptsRoot" "INVALID_RECEIPTS_ROOT" "InvalidReceiptsStateRoot")
    ("requestsHash" "INVALID_REQUESTS") ("transactionsRoot" "INVALID_TRANSACTIONS_ROOT" "InvalidTransactionsRoot")
    ("withdrawalsRoot" "INVALID_WITHDRAWALS_ROOT" "InvalidWithdrawals") ("hash" "INVALID_BLOCK_HASH")
    ("stateRoot" "INVALID_STATE_ROOT" "InvalidStateRoot") ("sha3Uncles" "InvalidUnclesHash")
    ;; the header gate (block-system.lisp header-violation: EELS validate_header)
    ("gasUsed above gasLimit" "GAS_USED_OVERFLOW" "TooMuchGasUsed") ("gasLimit" "INVALID_GASLIMIT" "GASLIMIT_TOO_BIG" "InvalidGasLimit" "InvalidGasLimit2")
    ("timestamp" "INVALID_BLOCK_TIMESTAMP_OLDER_THAN_PARENT" "InvalidTimestampOlderParent")
    ("number" "INVALID_BLOCK_NUMBER" "InvalidNumber") ("extraData" "EXTRA_DATA_TOO_BIG" "ExtraDataTooBig")
    ("dao extraData" "EXTRA_DATA_INVALID_DAO")
    ;; (ethereum/tests' 3675PoSBlockRejected: a proof-of-stake-shaped header before Paris, which
    ;; EELS refuses by the difficulty formula; 3675PreParis1559BlockRejected: a proof-of-work-
    ;; shaped header from Paris, refused by EIP-3675's difficulty / nonce / ommersHash clause)
    ("difficulty" "INVALID_DIFFICULTY" "IMPORT_IMPOSSIBLE_DIFFICULTY_OVER_PARIS" "InvalidDifficulty" "PostParisDifficultyIsNot0"
     "3675PoSBlockRejected" "3675PreParis1559BlockRejected")
    ("nonce" "3675PreParis1559BlockRejected")
    ("ommersHash" "IMPORT_IMPOSSIBLE_UNCLES_OVER_PARIS" "PostParisUncleHashIsNotEmpty" "3675PreParis1559BlockRejected")
    ;; the ommers (validate-ommers!: EELS validate_ommers)
    ("ommer number" "InvalidNumber") ("too many ommers" "TOO_MANY_UNCLES" "TooManyUncles") ("duplicate ommer")
    ("ommer in chain" "UNCLE_IN_CHAIN" "UNCLE_IS_ANCESTOR" "UncleInChain" "UncleIsAncestor")
    ("ommer already included" "UNCLE_IN_CHAIN" "UncleInChain")
    ("ommer age") ("ommer parent" "UNCLE_PARENT_INCORRECT" "UncleParentIsNotAncestor" "InvalidUncleParentHash")
    ("ommer is sibling" "UNCLE_IS_BROTHER" "UncleIsBrother"))
  "Our rejection kinds (run-block-checked) and the EEST exception classes each one is.")

(defun unchecked-p (expect)
  "Is every alternative of EXPECT (\"BlockException.A|B\") a class the replay does not check:
   an RLP-level defect (\"RLP_...\")? The runner, like the driver, reads the decoded block
   (rlp_decoded; JSON-RPC), never its RLP bytes. Such a block is counted `unchecked`, not run.
   (Every other class is checked; the header rules on proposer-chosen inputs — EELS
   validate_header, check_gas_limit, validate_ommers — since 2026-11-01, block-system.lisp
   header-violation and validate-ommers!. The proof-of-work seal is not checked; no fixture
   here expects it.)"
  (loop for start = 0 then (1+ bar)
        for bar = (position #\| expect :start start)
        for alt = (let ((a (subseq expect start bar))) (subseq a (1+ (or (position #\. a) -1))))
        always (and (> (length alt) 4) (string= "RLP_" alt :end2 4))
        while bar))

(defun expected-kind-p (expect kind)
  "Is our rejection KIND one of EXPECT's alternatives (\"TransactionException.A|BlockException.B\")?"
  (let ((ours (cdr (assoc kind *exception-kinds* :test #'equal))))
    (loop for start = 0 then (1+ bar)
          for bar = (position #\| expect :start start)
          for alt = (subseq expect start bar)
          thereis (member (subseq alt (1+ (or (position #\. alt) -1))) ours :test #'string=)
          while bar)))


(defparameter *invalid-counts* (list :rejected 0 :other 0 :accepted 0 :undecoded 0 :unchecked 0)
  "The invalid blocks' verdicts over the run: rejected for an expected reason, for another
   reason, accepted (a gate that does not fire), not runnable (no `rlp_decoded`, or not on
   the canonical head), or an RLP-level defect (unchecked-p).")

(defun run-invalid-blocks (test world head)
  "Each `expectException` block of TEST on a copy of WORLD (the canonical chain's post-state;
   HEAD its last block's hash, *recent-headers* its last blocks'): it must be rejected, for
   one of the expected reasons. One INVALID line per block not rejected as expected; returns
   a mismatch per accepted block."
  (loop with recent = *recent-headers*
        for (expect . blk) in (getf test :invalid)
        for verdict = (cond ((unchecked-p expect) :unchecked)
                            ((or (null blk) (/= (blk-parent-hash blk) head)) :undecoded)
                            (t (let ((why (let ((*recent-headers* recent)) (run-block-checked (copy-world* world) blk))))
                            (cond ((null why) :accepted)
                                  ((expected-kind-p expect (car why)) :rejected)
                                  (t (format t "~&INVALID other ~A: expected ~A, got ~A~%" (getf test :name) expect (cdr why))
                                     :other)))))
        do (incf (getf *invalid-counts* verdict))
        when (eq verdict :accepted)
          collect (progn (format t "~&INVALID accepted ~A: expected ~A~%" (getf test :name) expect)
                         (list :invalid-accepted expect))))

(defun run-test (test)
  (let ((network (getf test :network)))
    ;; Skip transition networks ("HomesteadToDaoAt5", ...) — single-fork
    ;; replays only. Unknown single forks would error in set-fork!.
    (unless (assoc network *network-fork-ords* :test #'string=)
      (return-from run-test (list :skipped (format nil "transition network ~A" network))))
    (set-fork! network))
  (let ((world (make-world))
        (*current-world* nil)
        ;; Canonical-chain selection: reorg fixtures (RPC_API_Test,
        ;; bcForkStressTest, bcMultiChainTest, ...) carry side-chain
        ;; blocks; the canonical chain is the parentHash-walk back from
        ;; lastblockhash. A linear replay of every block double-applies
        ;; the orphaned ones. Falls back to all blocks when the walk
        ;; isn't possible (no lastblockhash, or hash not found).
        (blocks (let ((all (getf test :blocks))
                      (lbh (getf test :lastblockhash)))
                  (or (when (and lbh (plusp lbh))
                        (let ((by-hash (make-hash-table :test 'eql)))
                          (dolist (b all)
                            (let ((h (blk-hash b)))
                              (when (and h (plusp h))
                                (setf (gethash h by-hash) b))))
                          (let ((chain '()))
                            (loop for h = lbh then (blk-parent-hash (first chain))
                                  for b = (gethash h by-hash)
                                  while b
                                  do (push b chain))
                            ;; Only trust a walk that anchors at genesis;
                            ;; a break midway (block missing its hash)
                            ;; would silently drop the chain's prefix.
                            (when (and chain
                                       (eql (blk-parent-hash (first chain))
                                            (getf test :genesis-hash)))
                              chain))))
                      (getf test :blocks)))))
    (populate-world world (getf test :pre))
    ;; Populate BLOCKHASH lookup: genesis + each canonical block.
    (setf *block-hashes* (make-hash-table :test 'eql))
    (let ((gh (getf test :genesis-hash))
          (gn (getf test :genesis-number)))
      (when gh (setf (gethash (or gn 0) *block-hashes*) gh)))
    (dolist (blk blocks)
      (let ((h (blk-hash blk))
            (n (blk-number blk)))
        (when (and h n) (setf (gethash n *block-hashes*) h))))
    ;; The canonical chain is parent-linked from genesis, so a block its header gates refuse
    ;; fails the test; then the post-state, then the invalid blocks on it.
    (when (getf test :partial-pre)
      (format t "~&  NOTE ~A: partial pre-state (eitaPartialPreState); the header stateRoot is NOT checked~%"
              (getf test :name)))
    ;; (post-block pushes each block that ran onto *recent-headers*, the header gate's parents)
    (let ((*recent-headers* (and (getf test :genesis-header) (list (getf test :genesis-header))))
          (head (getf test :genesis-hash))
          (*partial-pre-state* (getf test :partial-pre)))
      (dolist (blk blocks)
        (let ((why (run-block-checked world blk)))
          (when why (return-from run-test (list :fail (list (list :block (blk-number blk) (car why) (cdr why)))))))
        (setf head (blk-hash blk)))
      (let ((mismatches (or (compare-post world (getf test :post))
                            (run-invalid-blocks test world head))))
        (if (null mismatches)
            (list :pass)
            (list :fail mismatches))))))

(defun collect-json-files (path)
  "PATH's .json files: PATH itself, or a directory's (not its subdirectories — run-battery.sh
   runs each directory — nor a non-JSON file such as stShift/.stub)."
  (let ((p (probe-file path)))
    (cond ((null p) '())
          ((cl-fad:directory-pathname-p p)
           (remove-if-not (lambda (f) (and (not (cl-fad:directory-pathname-p f)) (string-equal "json" (pathname-type f))))
                          (cl-fad:list-directory p :follow-symlinks nil)))
          (t (list p)))))

(defparameter *expected-failures*
  (let ((h (make-hash-table :test 'equal)) (f (source-file "src/fixtures/expected-failures.txt"))
        (reason "expected failure"))
    (when (probe-file f)
      (with-open-file (in f)
        (loop for line = (read-line in nil) while line
              for s = (string-trim " " line)
              do (cond ((zerop (length s)))
                       ((and (> (length s) 2) (string= "#!" s :end2 2))
                        (setf reason (string-trim " " (subseq s 2))))
                       ((char= (char s 0) #\#))
                       (t (setf (gethash s h) reason))))))
    h)
  "Fixture tests that fail by design (src/fixtures/expected-failures.txt, which states why):
   reported as XFAIL (not FAIL), and as XPASS — a failure — if one starts to pass.")

(defun expected-failure (name)
  "The reason NAME is expected to fail (its section's `#!` line), or NIL."
  (gethash name *expected-failures*))

(defun main (args)
  (when (null args)
    (format t "usage: eita fixtures <test.json | dir>...~%")
    (sb-ext:exit :code 1))
  (let ((files (mapcan #'collect-json-files args))
        (pass 0) (fail 0) (skip 0) (xfail 0))
    (dolist (f files)
      (handler-case
          (let* ((contents (alexandria:read-file-into-string f))
                 (json (jsown:parse contents)))
            (dolist (name (jsown:keywords json))
              (let* ((test (parse-test name (jval json name)))
                     ;; A GeneralStateTest (env/transaction/post, no blocks) is another format:
                     ;; the same tests filled as blockchain tests are BlockchainTests/GeneralStateTests.
                     (result (if (and (jval (jval json name) "transaction") (not (jval (jval json name) "blocks")))
                                 (list :fail (list "a GeneralStateTest, not a BlockchainTest: run BlockchainTests/GeneralStateTests"))
                                 (run-test test))))
                (cond
                  ((eq (first result) :skipped)
                   (incf skip)
                   (format t "SKIP ~A (~A)~%" name (second result)))
                  ((and (eq (first result) :pass) (expected-failure name))
                   (incf fail)
                   (format t "XPASS ~A (expected to fail: ~A)~%" name (expected-failure name)))
                  ((eq (first result) :pass)
                   (incf pass)
                   (format t "PASS ~A~%" name))
                  ((and (eq (first result) :fail) (expected-failure name))
                   (incf xfail)
                   (format t "XFAIL ~A (~A)~%" name (expected-failure name)))
                  ((eq (first result) :fail)
                   (incf fail)
                   (format t "FAIL ~A~%" name)
                   (dolist (m (subseq (second result) 0 (min 5 (length (second result)))))
                     (format t "    ~A~%" m)))))))
        (error (e)
          (incf fail)
          (format t "ERROR ~A: ~A~%" f e))))
    (format t "---~%summary: pass=~D fail=~D skip=~D xfail=~D~%" pass fail skip xfail)
    (format t "invalid blocks: rejected=~D rejected-other=~D accepted=~D undecoded=~D unchecked=~D~%"
            (getf *invalid-counts* :rejected) (getf *invalid-counts* :other)
            (getf *invalid-counts* :accepted) (getf *invalid-counts* :undecoded) (getf *invalid-counts* :unchecked))
    (format t "jit: codes=~D no-jit=~D frames-jit=~D frames-interp=~D manifest-misses=~D chunk-evictions=~D~%"
            (getf *jit-stats* :codes-jit)
            (getf *jit-stats* :codes-no-jit)
            (getf *jit-stats* :frames-jit)
            (getf *jit-stats* :frames-interp)
            (getf *jit-stats* :manifest-misses)
            (getf *jit-stats* :chunk-evictions 0))))
