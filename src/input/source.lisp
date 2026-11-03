;;;; input/source.lisp — the block source: the seam between acquisition and execution, and the
;;;; directory source this repository ships.

(in-package #:eita.input)

;;; --- The block source: the seam between acquisition and execution ------------------------
;;;
;;; A source is a set of functions; only BLOCK is required.
;;;   block (n)          -> the CHAIN-BLOCK N (full txs; receipts/uncles when it has them), or NIL
;;;   hash (n)           -> block N's hash (default: BLOCK's `hash` field)
;;;   receipts (n)       -> block N's receipts (DECODE-RECEIPT plists) when BLOCK carried none, or NIL
;;;   uncles (blk)       -> BLK's ommer headers (CHAIN-BLOCKs) when BLOCK carried none
;;;   refetch (n)        -> a fresh copy of block N after a cached one failed its hash check
;;;   prepare (lo hi)    -> a hint: blocks LO..HI come next (a source may batch them)
;;;   begin (start)      -> the run starts at START (a lazy-state source pins its reads there)
;;;   forget-above (n)   -> drop any block above N it holds (a reorg rolled back to N)
;;;   fault-account (addr), fault-slot (addr slot)
;;;                      -> lazy state: load an account / slot on first touch. NIL: the source
;;;                         serves blocks only, and the run must hold full state (genesis or a
;;;                         snapshot).
;;;   prestate (n)       -> lazy state: pre-block state hints for block N
;;;   follow (world start) -> run from START and keep following the chain head; never returns.
;;;                         NIL: the source has no head to follow (`tip` is refused).
(defstruct (block-source (:constructor make-block-source
                             (&key (name "blocks") block hash receipts uncles refetch prepare
                                   begin forget-above fault-account fault-slot prestate follow)))
  name block hash receipts uncles refetch prepare begin forget-above
  fault-account fault-slot prestate follow)

(defvar *block-source* nil "The installed block source (MAKE-BLOCK-SOURCE).")

(defun block-source ()
  (or *block-source*
      (error "no block source: set EITA_BLOCKS_DIR to a directory of block files (docs/block-input.md), ~
              or install one in *block-source*")))

(defun source-call (slot &rest args)
  "Call the installed source's SLOT function with ARGS; NIL when the source has none."
  (let ((f (funcall slot (block-source)))) (and f (apply f args))))

(defun fetch-block (n)
  "Block N with full txs, from the installed source."
  (or (source-call #'block-source-block n)
      (error "block ~D: not available from the block source ~A" n (block-source-name (block-source)))))

;;; Block integrity: a block is only as good as its bytes, so it is checked against its own
;;; hash, keccak(RLP(header)) (decode-block computes it), before it is replayed. With the
;;; parent link run-block already checks, a chain of blocks is then hash-linked end to end.
(defun fetch-verified-block (n)
  "FETCH-BLOCK, checked: its header must hash to its `hash`. A copy that does not is
   replaced by the source's REFETCH, when it has one; if that does not hash either, stop loud."
  (let ((blk (fetch-block n)))
    (if (= (blk-header-hash blk) (blk-hash blk))
        blk
        (progn
          (format t "~&[input] block ~D does not hash to its own hash field (~(~x~) vs ~(~x~))~%"
                  n (blk-header-hash blk) (blk-hash blk))
          (force-output)
          (let ((fresh (source-call #'block-source-refetch n)))
            (unless (and fresh (= (blk-header-hash fresh) (blk-hash fresh)))
              (error "block ~D: header does not hash to its hash field — corrupt block data, or a header field this encoder does not know" n))
            fresh)))))

(defun fetch-block-hash (n)
  "Block hash of N (the BLOCKHASH window): the source's HASH, else its block's hash field
   (checked against the header)."
  (or (source-call #'block-source-hash n)
      (blk-hash (fetch-verified-block n))))

(defun fetch-receipts (n)
  "Block N's receipts when its block carried none: the source's RECEIPTS, or NIL (the
   driver then gates the block on its header alone)."
  (source-call #'block-source-receipts n))

(defun fetch-uncles (blk)
  "The ommer headers of BLK: the ones its block carried, else the source's UNCLES."
  (when (plusp (blk-uncle-count blk))
    (or (blk-uncles blk)
        (source-call #'block-source-uncles blk)
        (error "block ~D has ~D ommer(s) but the block source gave no ommer headers"
               (blk-number blk) (blk-uncle-count blk)))))

;;; --- The source this repository ships: a directory of block files --------------------------
;;; <dir>/<n>.json or <dir>/<n>.json.gz (N decimal), one per block, each either
;;;   * the block object: the `result` of eth_getBlockByNumber(N, true), or a whole JSON-RPC
;;;     reply carrying it; or
;;;   * {"block": <that object>, "receipts": [<eth_getBlockReceipts result>],
;;;      "uncles": [<eth_getUncleByBlockNumberAndIndex results>]} — receipts and uncles optional.
;;; docs/block-input.md describes the fields the decoder reads.

(defdecoder decode-block-file (blk receipts uncles result)
    (("block" blk decode-block) ("receipts" receipts jlist #'decode-receipt)
     ("uncles" uncles jlist #'decode-block) ("result" result decode-block))
  (let ((b (or blk result)))
    (when b
      (when receipts (setf (blk-receipts b) receipts))
      (when uncles (setf (blk-uncles b) uncles)))
    b))

(defun read-block-file (path)
  "The CHAIN-BLOCK in the block file PATH (any of the shapes above)."
  (let* ((b (read-file-octets path)) (i (jws b 0)))
    (or (values (decode-block-file b i))
        (values (decode-block b i)))))

(defun directory-block-source (dir &key (name nil))
  "A source over DIR's block files (<n>.json or <n>.json.gz). Blocks are decoded on demand
   and the last 300 kept (the BLOCKHASH window reads 256 back)."
  (let* ((dir (pathname (if (char= (char (namestring dir) (1- (length (namestring dir)))) #\/)
                            (namestring dir) (concatenate 'string (namestring dir) "/"))))
         (cache (make-hash-table :test 'eql)))
    (labels ((path (n) (or (probe-file (merge-pathnames (format nil "~D.json" n) dir))
                           (probe-file (merge-pathnames (format nil "~D.json.gz" n) dir))))
             (block-n (n)
               (or (gethash n cache)
                   (let ((p (path n)))
                     (when p
                       (remhash (- n 300) cache)
                       (setf (gethash n cache) (read-block-file p)))))))
      (make-block-source
       :name (or name (format nil "files in ~A" (namestring dir)))
       :block #'block-n
       :forget-above (lambda (top) (loop for k being the hash-keys of cache when (> k top) do (remhash k cache)))))))

(defun default-block-source ()
  "The source a run starts with when none is installed: EITA_SOURCE (a Lisp file that
   installs one) is loaded; else EITA_BLOCKS_DIR, else the chain's cache directory when it
   holds block files, as a DIRECTORY-BLOCK-SOURCE."
  (let ((src (sb-ext:posix-getenv "EITA_SOURCE"))
        (dir (sb-ext:posix-getenv "EITA_BLOCKS_DIR")))
    (cond ((and src (plusp (length src))) (load src) *block-source*)
          ((and dir (plusp (length dir))) (directory-block-source dir))
          ((and *cache-dir* (probe-file *cache-dir*)) (directory-block-source *cache-dir*)))))

;;; --- Gates and arguments -----------------------------------------------------------------

(defparameter *stats* (list :blocks 0 :txs 0 :deposits 0 :type4 0 :mismatches 0))

(defun gate (blk idx kind expected got)
  (cond ((eql expected got) t)
        (t (incf (getf *stats* :mismatches))
           (format t "~&MISMATCH blk=~D tx=~D ~A expected=~A got=~A~%"
                   blk idx kind expected got)
           nil)))


(defun parse-block-arg (s)
  (if (and (> (length s) 2) (string= "0x" (subseq s 0 2)))
      (hex->int s)
      (parse-integer s)))
