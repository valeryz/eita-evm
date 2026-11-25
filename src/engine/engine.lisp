;;;; engine/engine.lisp — `eita engine`: an execution client a consensus client drives over
;;;; the Engine API. One engine thread answers engine_newPayloadV4 / engine_forkchoiceUpdatedV3
;;;; with verdicts from the replay's own driver; the edge (rust/engine-api: HTTP, JWT, JSON-RPC
;;;; framing) forwards each call to it over a local socket. Validate-only: it builds no payloads.
;;;;
;;;;   eita engine --chain ethereum|hoodi|devnet [--genesis FILE] --state DIR --jwt FILE
;;;;               [--engine-listen 127.0.0.1:8551] [--blocks DIR]          (docs/run-a-node.md)
;;;;
;;;; Start. RUN starts the edge as a child process, installs this block source and runs the
;;;; chain's replay to `tip`: from the state directory's resume point (the newest anchor whose
;;;; root check passed), else from the genesis. The head block and the 256 below it (the
;;;; BLOCKHASH window, the header gate's parent) come from the executed blocks this source
;;;; keeps (<state>/engine-blocks/<n>.json), else from the block files of --blocks: how a
;;;; node starts on an anchor that a file replay (`eita replay --blocks`) produced.
;;;;
;;;; Threads. The engine thread is the replay thread (the source's FOLLOW): it takes calls
;;;; off a bounded queue (+queue-max+) and never touches a socket. A listener thread accepts
;;;; on <state>/engine.sock (mode 0600: the edge is the JWT boundary); each call is one
;;;; connection (a 4-byte big-endian length, then UTF-8 JSON {"method","params"}; the reply
;;;; the same with {"result"} or {"error":{"code","message"}}) served by its own thread, at
;;;; most +max-calls+ at once. That thread answers the cheap methods from the head under
;;;; *LOCK* and waits at most +verdict-wait+ (7 s) for the engine thread on the others:
;;;; SYNCING past it, the verdict recorded for the CL's retry.
;;;;
;;;; Verdicts (execution-apis src/engine/{paris,shanghai,cancun,prague,osaka}.md):
;;;;   params not ExecutionPayloadV3 + hashes + root + requests   -32602
;;;;   timestamp not Prague..BPO2 (the chain's Lean fork schedule)  -38005
;;;;   hash known VALID / INVALID                                   its recorded status
;;;;   structural check fails (header rebuilt from the payload ≠ blockHash, blob versioned
;;;;     hashes, a signature that does not recover)                 INVALID, lvh null, not
;;;;                                                                recorded (the hash may name
;;;;                                                                another, valid block)
;;;;   parent INVALID                                               INVALID, the parent's lvh
;;;;   parent = head: run-block (header gates, execution, the verifier: gas, bloom,
;;;;     receipts, tx/withdrawal roots, senders, requestsHash), then freeze, then the state
;;;;     root (`block-root!`)                                       VALID, head := block
;;;;     any of those fails: rolled back to the parent              INVALID, lvh parent
;;;;   otherwise (parent unknown, a side chain)                     stored, SYNCING
;;;; The verdict is per block: a refused block is rolled back (rollback-chain!), and the
;;;; next payload on the head is judged on its own.
;;;;
;;;; Bounds: the payload store (+store-max+) and the status table (+status-max+) are pruned
;;;; below the CL's finalized block, and by age past their bound; the executed blocks on disk
;;;; below min(finalized, head − 300).
;;;;
;;;; Not here: sync (a payload whose parent is not held stays SYNCING until the parent
;;;; arrives), reorgs (an fcU to anything but the head or a stored child of it is SYNCING),
;;;; payload building.

(in-package #:eita.engine)

(defconstant +verdict-wait+ 7 "Seconds a call waits for the engine thread before SYNCING.")
(defconstant +queue-max+ 64 "Calls waiting for the engine thread.")
(defconstant +max-calls+ 16 "Connections served at once.")
(defconstant +store-max+ 256 "Payloads held whose parent is not the head.")
(defconstant +status-max+ 4096 "Verdicts held (older ones go first when finality stalls).")
(defconstant +keep-blocks+ 300 "Executed blocks kept on disk below the head (BLOCKHASH: 256).")

(defun log! (fmt &rest args)
  (multiple-value-bind (s m h) (decode-universal-time (get-universal-time) 0)
    (format t "~&[engine ~2,'0D:~2,'0D:~2,'0DZ] ~?~%" h m s fmt args))
  (force-output))

(defun now-ms () (/ (get-internal-real-time) (/ internal-time-units-per-second 1000.0)))

;;; --- Hex, RLP ------------------------------------------------------------------------------

(deftype octets () '(simple-array (unsigned-byte 8) (*)))
(define-condition bad-payload (error) ((what :initarg :what :reader what))
  (:report (lambda (c s) (format s "~A" (what c)))))
(define-condition bad-params (error) ((what :initarg :what :reader what))
  (:report (lambda (c s) (format s "~A" (what c)))))
(defun bad (fmt &rest args) (error 'bad-payload :what (apply #'format nil fmt args)))
(defun bad-params (fmt &rest args) (error 'bad-params :what (apply #'format nil fmt args)))

(defun hex-p (s) (and (stringp s) (>= (length s) 2) (string= "0x" s :end2 2)))
(defun hex-octets (s)
  (unless (and (hex-p s) (evenp (length s))) (bad-params "not 0x-hex data: ~S" (if (stringp s) (subseq s 0 (min 20 (length s))) s)))
  (handler-case (coerce (eita.core::hex->bytes s) 'octets) (error () (bad-params "bad hex ~S" (subseq s 0 (min 20 (length s)))))))
(defun hex-int (s)
  (unless (and (hex-p s) (> (length s) 2)) (bad-params "not a 0x quantity: ~S" s))
  (handler-case (eita.core::hex->int s) (error () (bad-params "bad quantity ~S" s))))
(defun hash32 (s) (let ((v (hex-octets s))) (unless (= (length v) 32) (bad-params "not a 32-byte hash: ~S" s)) (be-int v)))
(defun int-hex (n) (format nil "0x~(~x~)" n))
(defun oct-hex (v) (eita.state::bytes->hex-string v "0x"))
(defun h32 (n) (format nil "0x~(~64,'0x~)" n))
(defun be-int (v) (let ((x 0)) (loop for b across v do (setf x (logior (ash x 8) b))) x))

(defun rlp-decode (b &optional (i 0) (end (length b)))
  "The RLP item at I of B: octets or a list of items; (values item next)."
  (flet ((need (k) (when (> k end) (bad "RLP runs past its end"))))
    (need (1+ i))
    (let ((p (aref b i)))
      (multiple-value-bind (start len list-p)
          (cond ((< p #x80) (values i 1 nil))
                ((<= p #xb7) (values (1+ i) (- p #x80) nil))
                ((<= p #xbf) (let ((ll (- p #xb7))) (need (+ 1 i ll)) (values (+ 1 i ll) (be-int (subseq b (1+ i) (+ 1 i ll))) nil)))
                ((<= p #xf7) (values (1+ i) (- p #xc0) t))
                (t (let ((ll (- p #xf7))) (need (+ 1 i ll)) (values (+ 1 i ll) (be-int (subseq b (1+ i) (+ 1 i ll))) t))))
        (need (+ start len))
        (values (if list-p
                    (loop with j = start while (< j (+ start len))
                          collect (multiple-value-bind (it nx) (rlp-decode b j (+ start len)) (setf j nx) it))
                    (subseq b start (+ start len)))
                (+ start len))))))

;;; --- A raw transaction as the JSON object input/decode.lisp reads ---------------------------

(defun q (v) (unless (typep v 'octets) (bad "a tx field is a list, not a quantity")) (int-hex (be-int v)))
(defun access-list-json (al)
  (unless (listp al) (bad "accessList is not a list"))
  (mapcar (lambda (e)
            (unless (and (listp e) (= (length e) 2) (listp (second e))) (bad "accessList entry"))
            `(:obj ("address" . ,(oct-hex (first e)))
                   ("storageKeys" . ,(mapcar (lambda (k) (h32 (be-int k))) (second e)))))
          al))

(defun raw-tx-json (raw)
  "The eth_getBlockByNumber-style object of the EIP-2718 bytes RAW (no `from`: the sender is
   recovered once the block is decoded, `recover-senders!`)."
  (when (zerop (length raw)) (bad "empty transaction"))
  (let* ((type (if (>= (aref raw 0) #xc0) 0 (aref raw 0)))
         (f (multiple-value-bind (it next) (rlp-decode raw (if (zerop type) 0 1))
              (unless (= next (length raw)) (bad "trailing bytes after a tx"))
              (unless (listp it) (bad "tx is not an RLP list"))
              it))
         (hash (oct-hex (eita.core::keccak256-bytes raw))))
    (flet ((n (k) (nth k f)) (to (v) (if (zerop (length v)) :null (oct-hex v))))
      (macrolet ((need (k) `(unless (= (length f) ,k) (bad "tx type ~D: ~D fields, not ~D" type (length f) ,k))))
        (case type
          (0 (need 9)
           `(:obj ("type" . "0x0") ("nonce" . ,(q (n 0))) ("gasPrice" . ,(q (n 1))) ("gas" . ,(q (n 2)))
                  ("to" . ,(to (n 3))) ("value" . ,(q (n 4))) ("input" . ,(oct-hex (n 5)))
                  ("v" . ,(q (n 6))) ("r" . ,(q (n 7))) ("s" . ,(q (n 8))) ("hash" . ,hash)))
          (1 (need 11)
           `(:obj ("type" . "0x1") ("chainId" . ,(q (n 0))) ("nonce" . ,(q (n 1))) ("gasPrice" . ,(q (n 2)))
                  ("gas" . ,(q (n 3))) ("to" . ,(to (n 4))) ("value" . ,(q (n 5))) ("input" . ,(oct-hex (n 6)))
                  ("accessList" . ,(access-list-json (n 7))) ("yParity" . ,(q (n 8))) ("r" . ,(q (n 9)))
                  ("s" . ,(q (n 10))) ("hash" . ,hash)))
          ((2 3 4)
           (need (case type (2 12) (3 14) (4 13)))
           (when (and (/= type 2) (zerop (length (n 5)))) (bad "tx type ~D has no `to` (no creation)" type))
           (let ((sig (last f 3)))
             `(:obj ("type" . ,(int-hex type)) ("chainId" . ,(q (n 0))) ("nonce" . ,(q (n 1)))
                    ("maxPriorityFeePerGas" . ,(q (n 2))) ("maxFeePerGas" . ,(q (n 3))) ("gas" . ,(q (n 4)))
                    ("to" . ,(to (n 5))) ("value" . ,(q (n 6))) ("input" . ,(oct-hex (n 7)))
                    ("accessList" . ,(access-list-json (n 8)))
                    ,@(when (= type 3)
                        `(("maxFeePerBlobGas" . ,(q (n 9)))
                          ("blobVersionedHashes" . ,(mapcar (lambda (h) (h32 (be-int h))) (n 10)))))
                    ,@(when (= type 4)
                        `(("authorizationList"
                           . ,(mapcar (lambda (a)
                                        (unless (and (listp a) (= (length a) 6)) (bad "an authorization is not 6 fields"))
                                        `(:obj ("chainId" . ,(q (first a))) ("address" . ,(oct-hex (second a)))
                                               ("nonce" . ,(q (third a))) ("yParity" . ,(q (fourth a)))
                                               ("r" . ,(q (fifth a))) ("s" . ,(q (sixth a)))))
                                      (n 9)))))
                    ("yParity" . ,(q (first sig))) ("r" . ,(q (second sig))) ("s" . ,(q (third sig)))
                    ("hash" . ,hash))))
          (t (bad "tx type ~D is not a type this fork has" type)))))))

;;; --- The payload: params checked, the block rebuilt --------------------------------------

(defparameter +empty-ommers+ "0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347")
(defparameter +payload-fields+
  '("parentHash" "feeRecipient" "stateRoot" "receiptsRoot" "logsBloom" "prevRandao" "blockNumber"
    "gasLimit" "gasUsed" "timestamp" "extraData" "baseFeePerGas" "blockHash" "transactions"
    "withdrawals" "blobGasUsed" "excessBlobGas")
  "ExecutionPayloadV3 (cancun.md), every field required.")

(defun obj-p (o) (and (consp o) (eq (car o) :obj)))
(defun jv (o k)
  "Field K of the object O; a missing or null field is not provided (cancun.md): -32602."
  (let ((v (and (obj-p o) (jsown:val-safe o k))))
    (if (or (null (and (obj-p o) (member k (jsown:keywords o) :test #'string=))) (eq v :null))
        (bad-params "payload lacks ~A" k)
        v)))

(defun check-payload-params (params)
  "newPayloadV4's four parameters (prague.md): (values payload versioned-hashes beacon-root
   requests), or -32602."
  (unless (and (listp params) (= (length params) 4)) (bad-params "newPayloadV4 takes 4 parameters, not ~A" (if (listp params) (length params) params)))
  (destructuring-bind (p versioned beacon requests) params
    (unless (obj-p p) (bad-params "the payload is not an object"))
    (let ((extra (set-difference (jsown:keywords p) +payload-fields+ :test #'string=)))
      (when extra (bad-params "payload fields ~{~A~^, ~} are not ExecutionPayloadV3's" extra)))
    (dolist (k +payload-fields+) (jv p k))
    (unless (and (listp (jv p "transactions")) (listp (jv p "withdrawals"))) (bad-params "transactions / withdrawals are not arrays"))
    (unless (listp versioned) (bad-params "expectedBlobVersionedHashes is not an array"))
    (when (eq requests :null) (bad-params "executionRequests is null"))
    (unless (listp requests) (bad-params "executionRequests is not an array"))
    ;; EIP-7685 as Engine V4 carries it: type-prefixed, non-empty, strictly ascending types
    (let ((reqs (mapcar #'hex-octets requests)))
      (loop with last = -1 for r in reqs
            do (when (<= (length r) 1) (bad-params "an execution request has no data"))
               (unless (> (aref r 0) last) (bad-params "execution requests not in strictly ascending type order"))
               (setf last (aref r 0)))
      (values p (mapcar #'hash32 versioned) (hash32 beacon) reqs))))

(defun payload->block (p versioned beacon-root reqs)
  "The payload P with newPayloadV4's other arguments as a decoded CHAIN-BLOCK whose header
   hashes to blockHash (else BAD-PAYLOAD), its senders recovered, and its block JSON (the
   disk's, with `from`)."
  (let* ((raws (mapcar (lambda (s) (handler-case (hex-octets s) (bad-params () (bad "a transaction is not hex"))))
                       (jv p "transactions")))
         (txs (mapcar #'raw-tx-json raws))
         (wds (jv p "withdrawals"))
         (payloads (make-list 3 :initial-element (make-array 0 :element-type '(unsigned-byte 8)))))
    (dolist (r reqs)
      (unless (< (aref r 0) 3) (bad "execution request type ~D does not exist at this fork" (aref r 0)))
      (setf (nth (aref r 0) payloads) (subseq r 1)))
    (let* ((txroot (eita.chain::list-root raws))
           (wroot (eita.chain::list-root
                   (mapcar (lambda (w) (eita.chain::withdrawal-rlp
                                        (list (hex-int (jv w "index")) (hex-int (jv w "validatorIndex"))
                                              (be-int (hex-octets (jv w "address"))) (hex-int (jv w "amount")))))
                           wds)))
           (obj `(:obj ("parentHash" . ,(jv p "parentHash")) ("sha3Uncles" . ,+empty-ommers+)
                       ("miner" . ,(jv p "feeRecipient")) ("stateRoot" . ,(jv p "stateRoot"))
                       ("transactionsRoot" . ,(oct-hex txroot)) ("receiptsRoot" . ,(jv p "receiptsRoot"))
                       ("logsBloom" . ,(jv p "logsBloom")) ("difficulty" . "0x0") ("number" . ,(jv p "blockNumber"))
                       ("gasLimit" . ,(jv p "gasLimit")) ("gasUsed" . ,(jv p "gasUsed")) ("timestamp" . ,(jv p "timestamp"))
                       ("extraData" . ,(jv p "extraData")) ("mixHash" . ,(jv p "prevRandao"))
                       ("nonce" . "0x0000000000000000") ("baseFeePerGas" . ,(jv p "baseFeePerGas"))
                       ("withdrawalsRoot" . ,(oct-hex wroot)) ("blobGasUsed" . ,(jv p "blobGasUsed"))
                       ("excessBlobGas" . ,(jv p "excessBlobGas")) ("parentBeaconBlockRoot" . ,(h32 beacon-root))
                       ("requestsHash" . ,(oct-hex (eita.chain::requests-hash payloads)))
                       ("hash" . ,(jv p "blockHash")) ("transactions" . ,txs) ("withdrawals" . ,wds)
                       ("uncles")))
           (blk (handler-case (eita.input::decode-block-json obj)
                  (error (e) (bad "the block does not decode: ~A" e)))))
      (unless (= (eita.input::blk-header-hash blk) (eita.input::blk-hash blk))
        (bad "blockHash ~A is not keccak(rlp(header)) ~A" (jv p "blockHash") (h32 (eita.input::blk-header-hash blk))))
      (let ((blobs (loop for tx in (eita.input::blk-txs blk) append (eita.evm::tx-blob-hashes tx))))
        (unless (equal blobs versioned)
          (bad "expected blob versioned hashes (~D) are not the transactions' (~D)" (length versioned) (length blobs))))
      (let ((i (eita.chain::recover-senders! (eita.input::blk-txs blk))))
        (when i (bad "the signature of tx ~D does not recover" i)))
      ;; the disk's JSON names each sender (eth_getBlockByNumber with full txs)
      (loop for tj in txs for tx in (eita.input::blk-txs blk)
            do (setf (cdr tj) (cons (cons "from" (h32-addr (eita.evm::tx-sender tx))) (cdr tj))))
      (values blk obj))))

(defun h32-addr (a) (format nil "0x~(~40,'0x~)" a))

;;; --- Block 0 from genesis.json -------------------------------------------------------------

(defvar *genesis* nil "(block . json) of block 0, derived from the chain's genesis.json.")

(defun genesis-block ()
  "Block 0 as the chain's genesis.json defines it: the header from its fields and the alloc's
   state root (the reference trie over a world of the alloc), with the header fields of the
   forks in force at its timestamp (base fee: London, withdrawals root: Shanghai, blob gas
   and beacon root: Cancun, requests hash: Prague). The CL holds the same header: block 1's
   parentHash names it (`new-payload`), eth_getBlockByNumber(0) serves it."
  (or *genesis*
      (let* ((path (eita.native::home-relative (or (eita.chain::env "GENESIS") eita.chain::*chain-genesis-path*)))
             (g (jsown:parse (alexandria:read-file-into-string path)))
             (w (eita.state::make-world))
             ;; a world of its own: none of the replay's snapshot hooks
             (eita.state::*fault-account-hook* nil) (eita.state::*fault-slot-hook* nil)
             (eita.state::*storage-wipe-hook* nil)
             (eita.state::*keep-zero-slots* nil))
        (eita.state::load-genesis-alloc w path)
        (flet ((field (k default)       ; keys as geth reads them (Go's JSON: any case)
                 (let ((v (let ((key (find k (jsown:keywords g) :test #'string-equal))) (and key (jsown:val g key)))))
                   (cond ((null v) default)
                         ((integerp v) (int-hex v))
                         ((hex-p v) v)
                         ((string= v "") "0x")
                         (t (int-hex (parse-integer v)))))))
          (let* ((ts (hex-int (field "timestamp" "0x0")))
                 (ord (funcall (eita.chain::chain-spec-fork-ord eita.chain::*chain-spec*) 0 ts))
                 (empty-trie (oct-hex (eita.chain::list-root '())))
                 (obj `(:obj ("parentHash" . ,(h32 0)) ("sha3Uncles" . ,+empty-ommers+)
                             ("miner" . ,(field "coinbase" (h32-addr 0))) ("stateRoot" . ,(eita.state::world-state-root w))
                             ("transactionsRoot" . ,empty-trie) ("receiptsRoot" . ,empty-trie)
                             ("logsBloom" . ,(oct-hex (make-array 256 :element-type '(unsigned-byte 8) :initial-element 0)))
                             ("difficulty" . ,(field "difficulty" "0x0")) ("number" . "0x0")
                             ("gasLimit" . ,(field "gasLimit" "0x0")) ("gasUsed" . "0x0") ("timestamp" . ,(int-hex ts))
                             ("extraData" . ,(field "extraData" "0x")) ("mixHash" . ,(field "mixHash" (h32 0)))
                             ("nonce" . ,(format nil "0x~(~16,'0x~)" (hex-int (field "nonce" "0x0"))))
                             ,@(when (>= ord 11) `(("baseFeePerGas" . ,(field "baseFeePerGas" (int-hex 1000000000)))))
                             ,@(when (>= ord 15) `(("withdrawalsRoot" . ,empty-trie)))
                             ,@(when (>= ord 16) `(("blobGasUsed" . ,(field "blobGasUsed" "0x0"))
                                                   ("excessBlobGas" . ,(field "excessBlobGas" "0x0"))
                                                   ("parentBeaconBlockRoot" . ,(h32 0))))
                             ,@(when (>= ord 17) `(("requestsHash" . ,(oct-hex (eita.chain::requests-hash '())))))
                             ("hash" . ,(h32 0)) ("transactions") ,@(when (>= ord 15) '(("withdrawals"))) ("uncles")))
                 (blk (eita.input::decode-block-json obj)))
            (setf (eita.input::blk-hash blk) (eita.input::blk-header-hash blk)
                  (jsown:val obj "hash") (h32 (eita.input::blk-header-hash blk)))
            (log! "genesis (~A): block 0 ~A, state root ~A" path (jsown:val obj "hash") (jsown:val obj "stateRoot"))
            (setf *genesis* (cons blk obj)))))))

;;; --- Engine state ----------------------------------------------------------------------------
;;; Written by the engine thread under *LOCK*; read under it by the call threads.

(defvar *lock* (sb-thread:make-mutex :name "engine state"))
(defvar *world* nil)
(defvar *head* nil "(number . hash) of the newest VALID block.")
(defvar *safe* nil) (defvar *finalized* nil "(number . hash), once the CL named a block we hold.")
(defvar *status* (make-hash-table) "block hash -> (status lvh error number): the verdicts.")
(defvar *store* (make-hash-table) "block hash -> (CHAIN-BLOCK . json) whose parent is not the head.")
(defvar *blocks* (make-hash-table) "number -> CHAIN-BLOCK of the executed chain (the last 300).")
(defvar *highest-seen* 0 "The highest block number a payload named (eth_syncing).")
(defvar *engine-stats* (list :valid 0 :invalid 0 :syncing 0))
(defvar *lowest-kept* 1 "The lowest engine-blocks/<n>.json not yet pruned.")

(defun blocks-dir () (merge-pathnames "engine-blocks/" (eita.state::state-dir)))
(defun block-path (n) (merge-pathnames (format nil "~D.json" n) (blocks-dir)))

(defun persist-block! (n obj)
  "Block N's JSON on disk before it runs: after a restart the driver reads its BLOCKHASH
   window and the header gate's parents here."
  (let ((p (block-path n)) (tmp (merge-pathnames (format nil ".~D.json.tmp" n) (blocks-dir))))
    (ensure-directories-exist p)
    (with-open-file (o tmp :direction :output :if-exists :supersede) (write-string (jsown:to-json obj) o))
    (rename-file tmp p)))

(defvar *files* nil "The block files of --blocks (a directory source), or NIL.")

(defun block-n (n)
  "The source's BLOCK: block N of the executed chain (0: the genesis), else of the block
   files a file replay ran before this node started."
  (if (zerop n)
      (car (genesis-block))
      (or (gethash n *blocks*)
          (let ((p (probe-file (block-path n))))
            (when p
              (remhash (- n +keep-blocks+) *blocks*)
              (setf (gethash n *blocks*) (eita.input::read-block-file p))))
          (and *files* (<= n (if *head* (car *head*) n))
               (funcall (eita.input::block-source-block *files*) n)))))

(defun forget-above! (top)
  "The source's FORGET-ABOVE: blocks above TOP leave the executed chain (RAM and disk)."
  (loop for k being the hash-keys of *blocks* when (> k top) do (remhash k *blocks*))
  (loop for k from (1+ top) for p = (probe-file (block-path k)) while p do (delete-file p)))

(defun status-json (status lvh err)
  `(:obj ("status" . ,status) ("latestValidHash" . ,(if lvh (h32 lvh) :null))
         ("validationError" . ,(or err :null))))

(defun record! (hash status lvh err number)
  (sb-thread:with-mutex (*lock*)
    (setf (gethash hash *status*) (list status lvh err number)))
  (incf (getf *engine-stats* (intern status :keyword) 0))
  (status-json status lvh err))

(defun prune! ()
  "Below the finalized block: verdicts, stored payloads, the executed blocks on disk (also
   above it, past +keep-blocks+ below the head); then each table to its bound, oldest first."
  (let ((fin (if *finalized* (car *finalized*) 0)))
    (sb-thread:with-mutex (*lock*)
      (flet ((cut (table number-of bound)
               (loop for k being the hash-keys of table using (hash-value v)
                     when (< (funcall number-of v) fin) do (remhash k table))
               (when (> (hash-table-count table) bound)
                 (let ((old (sort (loop for k being the hash-keys of table using (hash-value v)
                                        collect (cons (funcall number-of v) k))
                                  #'< :key #'car)))
                   (loop for (nil . k) in old repeat (- (hash-table-count table) bound)
                         unless (eql k (cdr *head*)) do (remhash k table))))))
        (cut *status* #'fourth +status-max+)
        (cut *store* (lambda (v) (eita.input::blk-number (car v))) +store-max+))))
  (let ((below (min (if *finalized* (car *finalized*) 0) (- (car *head*) +keep-blocks+))))
    (loop while (< *lowest-kept* below)
          do (let ((p (probe-file (block-path *lowest-kept*)))) (when p (delete-file p)))
             (incf *lowest-kept*))))

;;; --- The state root: one owner -------------------------------------------------------------

(defun block-root! (n)
  "THE ROOT PROVIDER: block N's state root against its header's, once N is frozen (`anchor!`
   queued its check). :valid, (values :mismatch why), or (values :unavailable why) for a
   check that could not run. Today the anchor's root check (`eita check-root`, a child over
   the base and the layers; every engine block is an anchor): about a second of process
   start, more with a compacted base's check queued first. An incremental root (a worker
   that keeps the trie) replaces this function, and nothing else."
  (eita.state::writer-drain!)
  (loop
    (let ((p eita.state::*pending-root*))
      (handler-case (if p (eita.state::root-check-finish! :force t) (eita.state::root-check-poll! n))
        (error (e)
          ;; this block's own check: a mismatch is its verdict; anything else (a compacted
          ;; base's check, the writer, a compaction) is ours, and stops the run
          (if (and p (eq (sixth p) :stack) (eql (first p) n))
              (return (values :mismatch (princ-to-string e)))
              (error e))))
      (cond ((eql eita.state::*last-good-anchor* n) (return :valid))
            ((and (null eita.state::*pending-root*) (not (assoc n eita.state::*anchor-queue*))
                  (null eita.state::*base-check-due*))
             (return (values :unavailable (format nil "the root check of block ~D could not run" n))))
            ((and (null p) (null eita.state::*pending-root*)) (sleep 0.005))))))

;;; --- Executing a payload on the head -----------------------------------------------------

(defvar *lat* '() "Recent (n exec-ms root-ms total-ms) of VALID blocks, newest first.")

(defun reject! (blk why)
  "BLK is INVALID: the state back to its parent (the head), the verdict recorded."
  (let* ((n (eita.input::blk-number blk)) (parent (eita.input::blk-parent-hash blk))
         (next (eita.chain::rollback-chain! *world* (1- n))))
    (unless (= next n)
      (error "rollback after INVALID block ~D reached block ~D, not ~D: the head is not a layer boundary" n (1- next) (1- n)))
    (log! "INVALID ~D ~A: ~A" n (h32 (eita.input::blk-hash blk)) why)
    (record! (eita.input::blk-hash blk) "INVALID" parent why n)))

(defun execute! (blk obj)
  "Run BLK (its parent is the head): VALID only after the header gates, the verifier and the
   state root; anything that fails rolls the state back to the parent."
  (let* ((n (eita.input::blk-number blk)) (hash (eita.input::blk-hash blk)) (t0 (now-ms)) t1)
    (persist-block! n obj)
    (setf (gethash n *blocks*) blk)
    (handler-case
        (progn (eita.chain::run-block *world* n :layer-point nil)
               (eita.evm::fw-drain))             ; the verifier's verdict: a refusal signals here
      (error (e) (return-from execute! (reject! blk (princ-to-string e)))))
    (setf t1 (now-ms))
    (eita.state::anchor! *world* n (eita.input::blk-state-root blk) :anchor t)
    (multiple-value-bind (verdict why) (block-root! n)
      (let ((t2 (now-ms)))
        (ecase verdict
          (:valid
           (sb-thread:with-mutex (*lock*) (setf *head* (cons n hash)))
           (push (list n (round (- t1 t0)) (round (- t2 t1)) (round (- t2 t0))) *lat*)
           (when (> (length *lat*) 2000) (setf *lat* (subseq *lat* 0 1000)))
           (log! "VALID ~D ~A  txs ~D gas ~D  exec ~D ms  root ~D ms  total ~D ms"
                 n (h32 hash) (length (eita.input::blk-txs blk)) (eita.input::blk-gas-used blk)
                 (round (- t1 t0)) (round (- t2 t1)) (round (- t2 t0)))
           (record! hash "VALID" hash nil n))
          (:mismatch (reject! blk why))
          (:unavailable                       ; not a verdict: the CL's retry runs it again
           (eita.chain::rollback-chain! *world* (1- n))
           (log! "block ~D: ~A; rolled back, SYNCING (unverified)" n why)
           (status-json "SYNCING" nil nil)))))))

(defun drain-store! ()
  "Run every stored payload that extends the head, in order."
  (loop for child = (loop for e being the hash-values of *store*
                          when (eql (eita.input::blk-parent-hash (car e)) (cdr *head*)) return e)
        while child
        do (sb-thread:with-mutex (*lock*) (remhash (eita.input::blk-hash (car child)) *store*))
           (execute! (car child) (cdr child))))

(defun payload-fork-ok-p (n ts)
  "newPayloadV4 covers Prague and Osaka (BPO1, BPO2 are Osaka's blob schedule): ords 17-20 of
   the chain's Lean fork schedule."
  (<= 17 (funcall (eita.chain::chain-spec-fork-ord eita.chain::*chain-spec*) n ts) 20))

(defun new-payload (params)
  (multiple-value-bind (p versioned beacon reqs) (check-payload-params params)
    (let ((hash (hash32 (jv p "blockHash"))) (ts (hex-int (jv p "timestamp"))) (n (hex-int (jv p "blockNumber"))))
      (unless (payload-fork-ok-p n ts)
        (return-from new-payload (values nil -38005 (format nil "Unsupported fork: timestamp ~D is not Prague or Osaka" ts))))
      (setf *highest-seen* (max *highest-seen* n))
      (let ((known (sb-thread:with-mutex (*lock*) (gethash hash *status*))))
        (when (and known (member (first known) '("VALID" "INVALID") :test #'string=))
          (return-from new-payload (status-json (first known) (second known) (third known)))))
      (multiple-value-bind (blk obj)
          (handler-case (payload->block p versioned beacon reqs)
            ;; not recorded: the payload may not be the block its hash names (a wrong
            ;; blockHash, versioned hashes, beacon root), and the block stays judgeable
            (bad-payload (e)
              (log! "INVALID (structural) ~D ~A: ~A" n (h32 hash) e)
              (incf (getf *engine-stats* :invalid 0))
              (return-from new-payload (status-json "INVALID" nil (princ-to-string e))))
            (bad-params (e) (error e))
            ;; not a verdict: ours (nothing ran yet, the state is untouched); loud, and no answer
            (error (e)
              (log! "block ~D ~A: decoding failed in Eita, not in the payload: ~A" n (h32 hash) e)
              (return-from new-payload (values nil -32603 (format nil "Internal error: ~A" e)))))
        (let* ((parent (eita.input::blk-parent-hash blk))
               (pstat (sb-thread:with-mutex (*lock*) (gethash parent *status*))))
          (cond ((and (= n 1) (/= parent (eita.input::blk-hash (car (genesis-block)))))
                 (log! "block 1 ~A: its parent ~A is not this network's genesis ~A (genesis.json): a different network"
                       (h32 hash) (h32 parent) (h32 (eita.input::blk-hash (car (genesis-block)))))
                 (record! hash "INVALID" nil "parent is not this network's genesis block (genesis.json)" n))
                ((and pstat (string= (first pstat) "INVALID"))
                 (record! hash "INVALID" (second pstat) "invalid ancestor" n))
                ((eql parent (cdr *head*))
                 (prog1 (execute! blk obj) (drain-store!)))
                (t (sb-thread:with-mutex (*lock*) (setf (gethash hash *store*) (cons blk obj)))
                   (log! "block ~D ~A: parent ~A is not the head ~D: stored, SYNCING" n (h32 hash) (h32 parent) (car *head*))
                   (record! hash "SYNCING" nil nil n))))))))

(defun forkchoice-state (state)
  (unless (and (obj-p state) (= (length (jsown:keywords state)) 3))
    (bad-params "forkchoiceState is not ForkchoiceStateV1"))
  (values (hash32 (jv state "headBlockHash")) (hash32 (jv state "safeBlockHash"))
          (hash32 (jv state "finalizedBlockHash"))))

(defun on-chain (hash)
  "(number . hash) when HASH is the head or a VALID block of the executed chain below it."
  (let ((st (gethash hash *status*)))
    (cond ((eql hash (cdr *head*)) *head*)
          ((and st (string= (first st) "VALID") (<= (fourth st) (car *head*))) (cons (fourth st) hash))
          ((eql hash (eita.input::blk-hash (car (genesis-block)))) (cons 0 hash)))))

(defun forkchoice-updated (params)
  (unless (and (listp params) (<= 1 (length params) 2)) (bad-params "forkchoiceUpdatedV3 takes 1 or 2 parameters"))
  (destructuring-bind (state &optional attrs) params
    (multiple-value-bind (head safe fin) (forkchoice-state state)
      ;; a head we stored: run its chain down from our head, if it links
      (when (gethash head *store*) (drain-store!))
      (let ((st (sb-thread:with-mutex (*lock*) (gethash head *status*))))
        (cond ((eql head (cdr *head*))
               ;; safe and finalized must be on the chain of the head (zero: not yet)
               (let ((s (or (zerop safe) (on-chain safe))) (f (or (zerop fin) (on-chain fin))))
                 (unless (and s f)
                   (return-from forkchoice-updated
                     (values nil -38002 "Invalid forkchoice state: safe or finalized is not an ancestor of the head")))
                 (sb-thread:with-mutex (*lock*)
                   (setf *safe* (and (consp s) s) *finalized* (if (consp f) f *finalized*)))
                 (prune!)
                 (when (and attrs (not (eq attrs :null)))
                   ;; the forkchoice update stands (it is not rolled back); no payload is built
                   (log! "forkchoiceUpdated with payload attributes: this node builds no payloads (validate-only); the CL must run no validators")
                   (return-from forkchoice-updated
                     (values nil -38003 "Invalid payload attributes: this node builds no payloads (validate-only)")))
                 `(:obj ("payloadStatus" . ,(status-json "VALID" head nil)) ("payloadId" . :null))))
              ((and st (string= (first st) "INVALID"))
               `(:obj ("payloadStatus" . ,(status-json "INVALID" (second st) (third st))) ("payloadId" . :null)))
              (t (log! "forkchoiceUpdated head ~A is not our head ~D (~A): SYNCING (no reorgs)"
                       (h32 head) (car *head*) (h32 (cdr *head*)))
                 `(:obj ("payloadStatus" . ,(status-json "SYNCING" nil nil)) ("payloadId" . :null))))))))

;;; --- The engine thread's queue ------------------------------------------------------------

(defvar *q-lock* (sb-thread:make-mutex :name "engine queue"))
(defvar *q-cv* (sb-thread:make-waitqueue))
(defvar *queue* '())
(defvar *queue-length* 0)
(defstruct job method params done result code message (cv (sb-thread:make-waitqueue)))

(defun enqueue-and-wait (method params)
  "Hand the call to the engine thread; its answer, or SYNCING after +verdict-wait+ s (the
   engine thread finishes it and records the verdict for the CL's retry)."
  (let ((job (make-job :method method :params params)))
    (sb-thread:with-mutex (*q-lock*)
      (when (>= *queue-length* +queue-max+) (return-from enqueue-and-wait (values nil -32000 "engine queue full")))
      (setf *queue* (append *queue* (list job)))
      (incf *queue-length*)
      (sb-thread:condition-broadcast *q-cv*)
      (let ((deadline (+ (get-internal-real-time) (* +verdict-wait+ internal-time-units-per-second))))
        (loop until (or (job-done job) (>= (get-internal-real-time) deadline))
              do (sb-thread:condition-wait (job-cv job) *q-lock*
                                           :timeout (max 0.01 (/ (- deadline (get-internal-real-time)) internal-time-units-per-second))))))
    (if (job-done job)
        (values (job-result job) (job-code job) (job-message job))
        (progn (log! "~A: no verdict in ~D s: SYNCING (it finishes in the background)" method +verdict-wait+)
               (incf (getf *engine-stats* :syncing 0))
               (values (if (string= method "engine_newPayloadV4")
                           (status-json "SYNCING" nil nil)
                           `(:obj ("payloadStatus" . ,(status-json "SYNCING" nil nil)) ("payloadId" . :null)))
                       nil nil)))))

(defun engine-loop ()
  "The engine (= replay) thread: take calls, answer them, one at a time."
  (loop
    (let ((job (sb-thread:with-mutex (*q-lock*)
                 (loop until *queue* do (sb-thread:condition-wait *q-cv* *q-lock*))
                 (decf *queue-length*)
                 (pop *queue*))))
      (multiple-value-bind (result code message)
          (handler-case
              (if (string= (job-method job) "engine_newPayloadV4")
                  (new-payload (job-params job))
                  (forkchoice-updated (job-params job)))
            (bad-params (e) (values nil -32602 (format nil "Invalid params: ~A" e))))
        (sb-thread:with-mutex (*q-lock*)
          (setf (job-result job) result (job-code job) code (job-message job) message (job-done job) t)
          (sb-thread:condition-broadcast (job-cv job)))))))

;;; --- The methods ------------------------------------------------------------------------------

(defparameter +capabilities+
  '("engine_getClientVersionV1" "engine_newPayloadV4" "engine_forkchoiceUpdatedV3")
  "What this node implements (validate-only, the current fork), nothing it would refuse;
   not engine_exchangeCapabilities itself (common.md: it MUST NOT be in the response list).")

(defvar *cl-capabilities* nil)

(defun client-version ()
  "ClientVersionV1 (identification.md). `commit` is the first four bytes of the engine's code
   version (the hash of the sources this binary was built from), not of a git commit."
  `((:obj ("code" . "EI") ("name" . "Eita") ("version" . ,(eita.cli::eita-version))
          ("commit" . ,(format nil "0x~A" (subseq (eita.evm::engine-code-version) 0 8))))))

(defun block-json (n full)
  "eth_getBlockByNumber's object for block N of the executed chain (NIL: not held)."
  (let ((obj (cond ((zerop n) (copy-tree (cdr (genesis-block))))
                   ((<= n (car *head*))
                    (let ((p (probe-file (block-path n))))
                      (and p (jsown:parse (alexandria:read-file-into-string p))))))))
    (when obj
      (unless full
        (setf (jsown:val obj "transactions") (mapcar (lambda (tx) (jsown:val tx "hash")) (jsown:val-safe obj "transactions"))))
      obj)))

(defun block-tag (tag)
  (sb-thread:with-mutex (*lock*)
    (cond ((member tag '("latest" "pending") :test #'equal) (car *head*))
          ((equal tag "safe") (and *safe* (car *safe*)))
          ((equal tag "finalized") (and *finalized* (car *finalized*)))
          ((equal tag "earliest") 0)
          (t (hex-int tag)))))

(defun dispatch (method params)
  "(values result error-code error-message), on the call's thread."
  (handler-case
      (cond ((string= method "engine_exchangeCapabilities")
             (unless (equal params *cl-capabilities*)
               (setf *cl-capabilities* params)
               (log! "CL capabilities: ~{~A~^ ~}" (first params)))
             +capabilities+)
            ((string= method "engine_getClientVersionV1")
             (log! "CL version: ~A" (jsown:to-json (first params)))
             (client-version))
            ((string= method "eth_chainId") (int-hex eita.chain::*chain-id*))
            ((string= method "eth_syncing")
             (let ((head (car *head*)))
               (if (> *highest-seen* head)
                   `(:obj ("startingBlock" . ,(int-hex head)) ("currentBlock" . ,(int-hex head))
                          ("highestBlock" . ,(int-hex *highest-seen*)))
                   :false)))
            ((string= method "eth_blockNumber") (int-hex (car *head*)))
            ((string= method "eth_getBlockByNumber")
             (let ((n (block-tag (first params)))) (or (and n (block-json n (eq (second params) t))) :null)))
            ((string= method "eth_getBlockByHash")
             (let* ((h (hash32 (first params)))
                    (n (sb-thread:with-mutex (*lock*) (car (on-chain h)))))
               (or (and n (block-json n (eq (second params) t))) :null)))
            ((member method '("engine_newPayloadV4" "engine_forkchoiceUpdatedV3") :test #'string=)
             (enqueue-and-wait method params))
            (t (log! "method ~A: not served (-32601)" method)
               (values nil -32601 (format nil "Method not found: ~A" method))))
    (bad-params (e) (values nil -32602 (format nil "Invalid params: ~A" e)))))

;;; --- The local socket ----------------------------------------------------------------------

(defun socket-path () (namestring (merge-pathnames "engine.sock" (eita.state::state-dir))))
(defvar *calls* 0 "Connections being served.")

(defun read-frame (s)
  (let ((h (make-array 4 :element-type '(unsigned-byte 8))))
    (when (= (read-sequence h s) 4)
      (let* ((len (be-int h)) (b (make-array len :element-type '(unsigned-byte 8))))
        (when (> len (* 64 1024 1024)) (error "a call of ~D bytes" len))
        (when (= (read-sequence b s) len) (sb-ext:octets-to-string b :external-format :utf-8))))))

(defun write-frame (s text)
  (let* ((b (sb-ext:string-to-octets text :external-format :utf-8)) (len (length b)))
    (write-sequence (make-array 4 :element-type '(unsigned-byte 8)
                                  :initial-contents (list (ldb (byte 8 24) len) (ldb (byte 8 16) len) (ldb (byte 8 8) len) (ldb (byte 8 0) len)))
                    s)
    (write-sequence b s)
    (force-output s)))

(defun reply-text (result code message)
  (jsown:to-json (if code
                     `(:obj ("error" . (:obj ("code" . ,code) ("message" . ,message))))
                     `(:obj ("result" . ,(if (null result) :null result))))))

(defun serve-call (sock)
  (let ((s (sb-bsd-sockets:socket-make-stream sock :input t :output t :element-type '(unsigned-byte 8) :buffering :full)))
    (unwind-protect
         (handler-case
             (let* ((text (read-frame s))
                    (req (and text (let ((jsown:*parsed-null-value* :null) (jsown:*parsed-false-value* :false))
                                     (jsown:parse text)))))
               (when req
                 (multiple-value-bind (result code message)
                     (handler-case (dispatch (jsown:val-safe req "method") (let ((p (jsown:val-safe req "params"))) (if (eq p :null) nil p)))
                       (error (e) (log! "~A failed: ~A" (jsown:val-safe req "method") e)
                         (values nil -32603 (format nil "Internal error: ~A" e))))
                   (write-frame s (reply-text result code message)))))
           (error (e) (log! "call: ~A" e)))
      (ignore-errors (close s))
      (ignore-errors (sb-bsd-sockets:socket-close sock))
      (sb-thread:with-mutex (*q-lock*) (decf *calls*)))))

(defun start-listener! ()
  (let ((path (socket-path)) (ls (make-instance 'sb-bsd-sockets:local-socket :type :stream)))
    (when (probe-file path) (delete-file path))
    (ensure-directories-exist path)
    (sb-bsd-sockets:socket-bind ls path)
    (sb-posix:chmod path #o600)
    (sb-bsd-sockets:socket-listen ls 64)
    (sb-thread:make-thread
     (lambda ()
       (loop (let ((c (sb-bsd-sockets:socket-accept ls)))
               (if (sb-thread:with-mutex (*q-lock*) (and (< *calls* +max-calls+) (incf *calls*)))
                   (sb-thread:make-thread (lambda () (serve-call c)) :name "engine call")
                   (let ((s (sb-bsd-sockets:socket-make-stream c :output t :element-type '(unsigned-byte 8))))
                     (ignore-errors (write-frame s (reply-text nil -32000 "busy: too many calls at once")))
                     (ignore-errors (close s)) (ignore-errors (sb-bsd-sockets:socket-close c)))))))
     :name "engine listener")
    (log! "Engine API calls on ~A" path)))

;;; --- The block source ------------------------------------------------------------------------

(defun follow (world start)
  "The source's FOLLOW: from the head START−1 (the genesis, or the anchor a resume mapped),
   serve the Engine API; never returns."
  (setf *world* world)
  (unless (eita.chain::chain-spec-fork-ord eita.chain::*chain-spec*)
    (error "the Engine API needs a chain with a fork schedule (ethereum, hoodi, devnet), not ~A" eita.chain::*chain-name*))
  (genesis-block)
  (let ((b (block-n (1- start))))
    (unless b (error "no block ~D in ~A~@[ or ~A~] to start from" (1- start) (blocks-dir) (eita.chain::env "BLOCKS_DIR")))
    (setf *head* (cons (1- start) (eita.input::blk-hash b)) *lowest-kept* (max 1 (- start +keep-blocks+)))
    (record! (eita.input::blk-hash b) "VALID" (eita.input::blk-hash b) nil (1- start))
    ;; the executed chain below it, as the CL names its safe and finalized blocks after a restart
    (loop for k from (max 1 (- start 1 +keep-blocks+)) below (1- start)
          for blk = (block-n k)
          when blk do (record! (eita.input::blk-hash blk) "VALID" (eita.input::blk-hash blk) nil k)))
  (log! "~A: head ~D ~A; waiting for the CL" eita.chain::*chain-name* (car *head*) (h32 (cdr *head*)))
  (start-listener!)
  (engine-loop))

(defun engine-block-source ()
  (eita.input::make-block-source :name "Engine API" :block #'block-n :forget-above #'forget-above! :follow #'follow))

;;; --- `eita engine` ---------------------------------------------------------------------------

(defun edge-path ()
  "The edge (rust/engine-api): beside the executable (build.sh copies it to bin/), else in
   the build tree."
  (let ((p (and (eita.native:executable-dir) (merge-pathnames "eita-engine-api" (eita.native:executable-dir)))))
    (if (and p (probe-file p))
        (namestring p)
        (eita.native:eita-file "rust/engine-api/target/release/eita-engine-api"))))

(defun start-edge! (listen jwt)
  "The edge as a child process: HTTP and JWT on LISTEN, each call forwarded to the socket.
   It exits when this process does (--parent), and this process when it does: a node whose
   port is closed is not running."
  (let ((exe (edge-path)))
    (unless (probe-file exe) (error "no Engine API edge at ~A (./build.sh builds it)" exe))
    (sb-ext:run-program exe (list "--listen" listen "--jwt" jwt "--socket" (socket-path)
                                  "--parent" (princ-to-string (sb-posix:getpid)))
                        :wait nil :output t :error t
                        :status-hook (lambda (p)
                                       (when (member (sb-ext:process-status p) '(:exited :signaled))
                                         (log! "the Engine API edge stopped (~(~A~) ~D): this node stops"
                                               (sb-ext:process-status p) (sb-ext:process-exit-code p))
                                         (sb-ext:exit :code 1 :abort t))))))

(defun run (chain &key state jwt listen genesis blocks)
  "Serve the Engine API for CHAIN (ethereum, hoodi, devnet with GENESIS) from the state
   directory STATE: the edge on LISTEN (default 127.0.0.1:8551; JWT secret: the file JWT), then the replay to `tip`
   with this block source, from STATE's resume point (the newest anchor whose root check
   passed; none: the genesis). BLOCKS: the block files of the file replay that made that
   anchor (the head and the BLOCKHASH window below it). Never returns."
  (let ((state (if (char= (char state (1- (length state))) #\/) state (concatenate 'string state "/"))))
    (ensure-directories-exist state)
    (sb-posix:setenv "EITA_STATE_DIR" state 1)     ; the socket's directory, before the replay
    (start-edge! (or listen "127.0.0.1:8551") jwt)
    (setf *files* (and blocks (eita.input::directory-block-source blocks))
          eita.input:*block-source* (engine-block-source))
    (let* ((r (let ((*standard-output* (make-broadcast-stream))) (eita.state.recovery:run-resume state)))
           (n (and (integerp r) (plusp r) r)))
      (when (eq r :refuse)
        (error "~A holds verified anchors but none with a sealed snapshot: no resume point (eita recovery peek)" state))
      (log! "~A: ~:[no anchor in ~A: from the genesis~;resume point ~:*~D~]" chain n state)
      (eita:replay chain 1 :to :tip :state state :genesis genesis :blocks blocks :resume n))))
