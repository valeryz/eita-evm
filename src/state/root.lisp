;;;; state/root.lisp — the state root of a binary snapshot (snap-N/), streaming.
;;;;
;;;;   eita check-root [--parent PID] <snap-dir> [<layer-dir> ...] [threads]
;;;;
;;;; Prints `CL trie root : <hex>` and MATCH / MISMATCH against the manifest's
;;;; :state-root (the header root it was written for); root-check-finish! reads the root
;;;; line. Exit 0 on MATCH. THREADS defaults to the hardware thread count. --parent PID
;;;; (the replay's spawn): exit as soon as process PID is no longer the parent.
;;;;
;;;; MEMORY DOES NOT GROW WITH THE STATE. The previous checker held a 32-byte key for
;;;; every account (plus sort buffers and every storage root) at once: 4.6-8 GB at
;;;; 38.9M accounts, ~20x that at the tip. Here a trie is never held: leaves arrive in
;;;; key order and go through a STACK TRIE (the open rightmost path, at most 64 frames
;;;; of 16 child references), every node being RLP-encoded and hashed the moment its key
;;;; range closes — the same node encoding as mpt.lisp `patricialise` (Trie.lean), whose
;;;; items it reuses; `Evm.Trie.Stack` is the Lean statement of this build.
;;;;
;;;; Two passes over the snapshot, both bounded:
;;;;   1. storage roots (a worker pool over chunks of 4096 accounts in addr order; both
;;;;      files are in addr order, so a chunk is a contiguous range of each). An
;;;;      account's slot keys are keccak'd straight out of the mapping, sorted (72 B per
;;;;      slot, in the worker) and streamed into a stack trie; a storage over *BIG* slots
;;;;      is split by its hashed keys' top byte and built by a pool of its own (GIANT-ROOT:
;;;;      4 B per slot off the heap, one 1/256 bucket per thread in it).
;;;;      Each account leaves one 136-byte record — keccak(addr), nonce, balance,
;;;;      codehash, storage root — in one of 256 (2048 past 2^26 accounts) BUCKET FILES by the
;;;;      top bits of its hashed key, beside the snapshot (.root-N/, removed at the end).
;;;;   2. the account trie: the buckets ARE the hashed-key order, bucket by bucket; a
;;;;      bucket (under ~150K records) is sorted in memory and streamed into the stack trie.
;;;;      With 2+ non-empty top nibbles the root is a branch, so the 16 subtries (base
;;;;      depth 1) run in parallel and the root branch combines them (SPLIT-ROOT, which
;;;;      also assembles a giant storage from its 256 subtries).
;;;; Measured (Mac, 12 threads): 4.9M blocks (21.9M accounts, 35.8M slots) 24 s wall,
;;;; 156 s CPU, 1.2 GB anonymous peak (138 s and 0.8 GB single-threaded); 5.8M (38.9M /
;;;; 84.3M) 58 s, 1.6 GB. The walk this replaces took 4213 s and 3.2 GB at 4.9M, and its
;;;; memory grew with the state. The snapshot's pages are released behind the scan; a
;;;; worker holds at most a 256K-slot contract's buffers (72 B per slot) between accounts,
;;;; and contracts over 1M slots are built one at a time, each by every thread. ~2.6 us of
;;;; CPU per leaf.

(in-package #:eita.state.root)

(defconstant +header+ 4096)
(defconstant +acct+ 96)
(defconstant +slot+ 88)
(defconstant +rec+ 136)                 ; bucket record: hash32 nonce8 balance32 codehash32 sroot32
(defconstant +chunk+ 4096)              ; accounts per pass-1 work item
(defconstant +large+ 262144)            ; slots: buffers this large are exact and dropped after use
(defparameter *big* 1000000)           ; slots: a storage this large is built by GIANT-ROOT (tests: lower)
(defconstant +slice+ 262144)            ; records per GIANT-ROOT partition task
(defconstant +wbuf+ 65536)

(deftype octets () '(simple-array (unsigned-byte 8) (*)))

;;; ------------------------------------------------------------ the stack trie
;;;
;;; Keys are 32 bytes (64 nibbles), pushed in ascending order, all distinct. A frame is a
;;; branch node under construction at nibble DEPTH, holding the finished children (RLP
;;; items as node-ref leaves them: inline or (:bytes hash)) and, above it, an extension
;;; over nibbles [EXT-FROM, DEPTH) of its keys. Frames form the rightmost path: frame
;;; k+1 starts at frame k's depth + 1. The last key pushed is the PENDING leaf, in the
;;; top frame's slot for its nibble, finished when the next key tells where it ends.
;;; BASE is the depth the paths start at (0 for a whole trie; 1 for a top-nibble subtrie).

(defstruct (frame (:constructor make-frame ()))
  (depth 0 :type fixnum) (ext-from 0 :type fixnum)
  (children (make-array 16 :initial-element nil) :type simple-vector))

(defstruct (stack-trie (:constructor %make-stack-trie) (:conc-name st-))
  (base 0 :type fixnum) (n 0 :type fixnum) (sp 0 :type fixnum)
  (prev (eita.mpt:make-nibbles 64) :type octets) (cur (eita.mpt:make-nibbles 64) :type octets)
  (pending nil)
  (frames (coerce (loop repeat 65 collect (make-frame)) 'simple-vector) :type simple-vector))

(defun make-stack-trie (&optional (base 0)) (st-reset (%make-stack-trie) base))

(defun st-reset (st base)
  (setf (st-base st) base (st-n st) 0 (st-sp st) 0 (st-pending st) nil)
  st)

(defvar *empty-item* (eita.mpt:rlp-bytes (make-array 0 :element-type '(unsigned-byte 8))))

(declaim (inline nibbles-of))
(defun nibbles-of (key off out)
  (declare (type octets key out) (type fixnum off) (optimize (speed 3) (safety 0)))
  (dotimes (i 32)
    (let ((b (aref key (+ off i))))
      (setf (aref out (* 2 i)) (ash b -4) (aref out (1+ (* 2 i))) (logand b 15)))))

(defun leaf-item (nibs from value)
  (eita.mpt:rlp-list (eita.mpt:rlp-bytes (eita.mpt:hex-prefix nibs t from 64))
                      (eita.mpt:rlp-bytes value)))

(defun st-top (st) (aref (st-frames st) (1- (st-sp st))))

(defun st-open (st depth ext-from)
  "Push a frame at DEPTH; the pending leaf (which must exist) becomes its first child."
  (unless (st-pending st) (error "stack trie: a frame opened under no pending leaf"))
  (let ((f (aref (st-frames st) (st-sp st))))
    (incf (st-sp st))
    (setf (frame-depth f) depth (frame-ext-from f) ext-from)
    (fill (frame-children f) nil)
    (st-place-pending st f)
    f))

(defun st-place-pending (st f)
  "Finish the pending leaf (if any) as a child of F: its path is what follows F's depth."
  (let ((v (st-pending st)))
    (when v
      (let ((prev (st-prev st)) (d (frame-depth f)))
        (setf (aref (frame-children f) (aref prev d)) (eita.mpt:node-ref (leaf-item prev (1+ d) v))
              (st-pending st) nil)))))

(defun st-close (st f from)
  "F's node: its branch, under an extension over nibbles [FROM, depth) when FROM < depth.
   Every key of F shares those nibbles, the last one pushed among them."
  (let ((branch (eita.mpt:rlp-list*
                 (nconc (loop for c across (frame-children f) collect (or c *empty-item*))
                        (list *empty-item*)))))
    (if (< from (frame-depth f))
        (eita.mpt:rlp-list (eita.mpt:rlp-bytes (eita.mpt:hex-prefix (st-prev st) nil from (frame-depth f)))
                            (eita.mpt:node-ref branch))
        branch)))

(defun st-push (st key off value)
  "Add the key at KEY[OFF, OFF+32) -> VALUE (its already RLP-encoded bytes). Keys come in
   ascending order."
  (declare (type octets key) (type fixnum off))
  (let ((cur (st-cur st)) (prev (st-prev st)) (base (st-base st)))
    (declare (type octets cur prev) (type fixnum base))
    (nibbles-of key off cur)
    (unless (zerop (st-n st))
      (let ((l (loop for d of-type fixnum from base below 64
                     while (= (aref prev d) (aref cur d)) finally (return d))))
        (declare (type fixnum l))
        (when (= l 64) (error "stack trie: duplicate key ~A" (eita.mpt:bytes->hex (subseq key off (+ off 32)))))
        (loop
          (when (zerop (st-sp st))        ; two keys so far: they split at L
            (st-open st l base) (return))
          (let* ((top (st-top st)) (d (frame-depth top)) (e (frame-ext-from top)))
            (declare (type fixnum d e))
            (cond ((> l d) (st-open st l (1+ d)) (return))     ; under the pending leaf
                  ((= l d) (st-place-pending st top) (return)) ; a sibling in TOP
                  (t                                           ; L is above TOP: close it
                   (st-place-pending st top)
                   (let ((node (st-close st top (max e (1+ l)))))
                     (decf (st-sp st))
                     (cond ((>= l e)
                            ;; the split is inside TOP's extension: a branch at L takes
                            ;; its place (same extension start) with TOP's node under it
                            (let ((f (aref (st-frames st) (st-sp st))))
                              (incf (st-sp st))
                              (setf (frame-depth f) l (frame-ext-from f) e)
                              (fill (frame-children f) nil)
                              (setf (aref (frame-children f) (aref prev l)) (eita.mpt:node-ref node))
                              (return)))
                           (t ; TOP is complete: it is the child of the frame below
                            (let ((below (st-top st)))
                              (setf (aref (frame-children below) (aref prev (frame-depth below)))
                                    (eita.mpt:node-ref node))))))))))))
    (setf (st-pending st) value)
    (rotatef (st-prev st) (st-cur st))
    (incf (st-n st))
    st))

(defun st-finish (st)
  "The root node's RLP item (as `patricialise` would return it), or NIL for no keys."
  (cond ((zerop (st-n st)) nil)
        ((zerop (st-sp st)) (leaf-item (st-prev st) (st-base st) (st-pending st)))
        (t (st-place-pending st (st-top st))
           (loop (let* ((top (st-top st)) (node (st-close st top (frame-ext-from top))))
                   (decf (st-sp st))
                   (when (zerop (st-sp st)) (return node))
                   (let ((below (st-top st)))
                     (setf (aref (frame-children below) (aref (st-prev st) (frame-depth below)))
                           (eita.mpt:node-ref node))))))))

(defun st-root-bytes (item)
  "Trie.rootBytes: keccak of the root node's encoding, however short; empty -> emptyRoot."
  (if item (eita.mpt:%keccak (eita.mpt:rlp-encode item)) (eita.mpt:empty-root-bytes)))

;;; ------------------------------------------------------------ sorting keys

(defstruct (sorter (:constructor make-sorter ()))
  (ka (make-array 0 :element-type '(unsigned-byte 64)) :type (simple-array (unsigned-byte 64) (*)))
  (kb (make-array 0 :element-type '(unsigned-byte 64)) :type (simple-array (unsigned-byte 64) (*)))
  (ia (make-array 0 :element-type '(unsigned-byte 32)) :type (simple-array (unsigned-byte 32) (*)))
  (ib (make-array 0 :element-type '(unsigned-byte 32)) :type (simple-array (unsigned-byte 32) (*)))
  (counts (make-array 65537 :element-type 'fixnum) :type (simple-array fixnum (*))))

;;; ALLOCATE FIRST, THEN STORE. SBCL 2.5.2 (production) marks an object's GC card once
;;; for several slot stores in one function, even when an allocation — a possible GC —
;;; falls between them: a GC there unmarks the card, the later stores leave the old
;;; struct pointing at young arrays the next GC cannot see, and those are freed under it
;;; ("no transport function", "heap_scavenge failure"; disassembly and verify_gens in
;;; the commit). Every multi-slot refill of a long-lived struct here builds its values
;;; first, so its stores have no allocation between them. 2.5.8 re-marks per store.
(defun sorter-ensure (s n)
  (when (< (length (sorter-ka s)) n)
    (let* ((m (max n (* 2 (length (sorter-ka s)))))
           (ka (make-array m :element-type '(unsigned-byte 64)))
           (kb (make-array m :element-type '(unsigned-byte 64)))
           (ia (make-array m :element-type '(unsigned-byte 32)))
           (ib (make-array m :element-type '(unsigned-byte 32))))
      (setf (sorter-ka s) ka (sorter-kb s) kb (sorter-ia s) ia (sorter-ib s) ib))))

(declaim (inline key-word))
(defun key-word (keys i stride)
  "The first 8 bytes of record I's key, big-endian, as a u64."
  (declare (type octets keys) (type fixnum i stride) (optimize (speed 3) (safety 0)))
  (let ((w 0) (o (* i stride)))
    (declare (type (unsigned-byte 64) w) (type fixnum o))
    (dotimes (j 8 w) (setf w (logior (logand (ash w 8) #xFFFFFFFFFFFFFFFF) (aref keys (+ o j)))))))

(defun key< (keys a b stride)
  (declare (type octets keys) (type fixnum a b stride) (optimize (speed 3) (safety 0)))
  (let ((oa (* a stride)) (ob (* b stride)))
    (declare (type fixnum oa ob))
    (dotimes (j 32 nil)
      (let ((x (aref keys (+ oa j))) (y (aref keys (+ ob j))))
        (cond ((< x y) (return t)) ((> x y) (return nil)))))))

(defun sort-keys (s keys n stride)
  "Indices 0..N-1 of the STRIDE-byte records in KEYS ordered by their 32-byte key
   (memcmp). Small sets: a comparison sort; else an LSD radix sort on the first 8 bytes
   in four 16-bit passes, runs with equal first 8 bytes ordered by the full key. Returns
   the sorter's index vector (its first N entries)."
  (declare (type octets keys) (type fixnum n stride) (optimize (speed 3) (safety 0)))
  (sorter-ensure s n)
  (let ((ia (sorter-ia s)))
    (when (< n 1024)
      (dotimes (i n) (setf (aref ia i) i))
      (replace ia (sort (subseq ia 0 n) (lambda (a b) (key< keys a b stride))))
      (return-from sort-keys ia))
    (let ((ka (sorter-ka s)) (kb (sorter-kb s)) (ib (sorter-ib s)) (counts (sorter-counts s)))
      (declare (type (simple-array (unsigned-byte 64) (*)) ka kb)
               (type (simple-array (unsigned-byte 32) (*)) ia ib) (type (simple-array fixnum (*)) counts))
      (dotimes (i n) (setf (aref ka i) (key-word keys i stride) (aref ia i) i))
      (loop for shift of-type fixnum from 0 below 64 by 16
            do (fill counts 0)
               (dotimes (i n) (incf (aref counts (1+ (ldb (byte 16 shift) (aref ka i))))))
               (loop for d from 1 to 65536 do (incf (aref counts d) (aref counts (1- d))))
               (dotimes (i n)
                 (let* ((k (aref ka i)) (d (ldb (byte 16 shift) k)) (p (aref counts d)))
                   (setf (aref kb p) k (aref ib p) (aref ia i) (aref counts d) (1+ p))))
               (rotatef ka kb) (rotatef ia ib))
      ;; 4 passes: the result is back in the sorter's own IA
      (let ((i 0))
        (declare (type fixnum i))
        (loop while (< i n)
              do (let ((j (1+ i)))
                   (declare (type fixnum j))
                   (loop while (and (< j n) (= (aref ka j) (aref ka i))) do (incf j))
                   (when (> (- j i) 1)
                     (replace ia (sort (subseq ia i j) (lambda (a b) (key< keys a b stride))) :start1 i))
                   (setf i j))))
      ia)))

;;; ------------------------------------------------------------ bytes

(defun minimal-be (sap off width)
  "The WIDTH bytes at SAP+OFF without leading zeros, as a fresh octet vector."
  (declare (type sb-sys:system-area-pointer sap) (type fixnum off width) (optimize (speed 3) (safety 0)))
  (let ((s (loop for i of-type fixnum from 0 below width while (zerop (sb-sys:sap-ref-8 sap (+ off i))) count t)))
    (declare (type fixnum s))
    (let ((v (make-array (- width s) :element-type '(unsigned-byte 8))))
      (dotimes (i (length v) v) (setf (aref v i) (sb-sys:sap-ref-8 sap (+ off s i)))))))

(defun minimal-vec (vec start end)
  "VEC[START, END) without leading zeros, as a fresh octet vector."
  (declare (type octets vec) (type fixnum start end))
  (subseq vec (or (position-if-not #'zerop vec :start start :end end) end) end))

(defun copy-sap (sap off n out &optional (start 0))
  (declare (type sb-sys:system-area-pointer sap) (type octets out) (type fixnum off n start)
           (optimize (speed 3) (safety 0)))
  (dotimes (i n out) (setf (aref out (+ start i)) (sb-sys:sap-ref-8 sap (+ off i)))))

(defun cmp-sap (sap1 off1 sap2 off2 n)
  "-1 / 0 / 1 comparing N bytes at SAP1+OFF1 with those at SAP2+OFF2."
  (declare (type sb-sys:system-area-pointer sap1 sap2) (type fixnum off1 off2 n)
           (optimize (speed 3) (safety 0)))
  (dotimes (i n 0)
    (let ((a (sb-sys:sap-ref-8 sap1 (+ off1 i))) (b (sb-sys:sap-ref-8 sap2 (+ off2 i))))
      (cond ((< a b) (return -1)) ((> a b) (return 1))))))

(defun keccak-into (sap offs lens n out)
  "keccak of the N ranges SAP+OFFS[i] of LENS[i] bytes, 32 bytes each into OUT, in one
   call (libkeccak_batch), hashing straight from the mapping."
  (declare (type (simple-array (unsigned-byte 64) (*)) offs lens) (type octets out))
  (sb-sys:with-pinned-objects (offs lens out)
    (eita.mpt:%keccak-batch-c sap (sb-sys:vector-sap offs) (sb-sys:vector-sap lens) (sb-sys:vector-sap out) n)))

;;; ------------------------------------------------------------ a worker's scratch

(defstruct (worker (:constructor make-worker ()))
  (sorter (make-sorter)) (trie (make-stack-trie))
  (keys (make-array 0 :element-type '(unsigned-byte 8)) :type octets)
  (offs (make-array 0 :element-type '(unsigned-byte 64)) :type (simple-array (unsigned-byte 64) (*)))
  (lens (make-array 0 :element-type '(unsigned-byte 64)) :type (simple-array (unsigned-byte 64) (*)))
  (recs (make-array (* +chunk+ +rec+) :element-type '(unsigned-byte 8)) :type octets)
  (bucket (make-array 0 :element-type '(unsigned-byte 8)) :type octets)
  (bkeys (make-array 0 :element-type '(unsigned-byte 8)) :type octets)   ; a chunk's base address hashes
  (obuf (eita.state.snapshot:make-obuf))                                            ; a layered address's slots
  (big 0 :type fixnum) (slots 0 :type fixnum)
  (threads 1 :type fixnum))                                               ; its pool's size

(defun worker-ensure (w n)
  "Room for N keys (32 bytes each) and N hash jobs: doubling for small sets, exact for large."
  (when (< (length (worker-offs w)) n)
    (let* ((m (if (> n +large+) n (max n (* 2 (length (worker-offs w))))))
           (keys (make-array (* 32 m) :element-type '(unsigned-byte 8)))
           (offs (make-array m :element-type '(unsigned-byte 64)))
           (lens (make-array m :element-type '(unsigned-byte 64))))
      (setf (worker-keys w) keys (worker-offs w) offs (worker-lens w) lens))))   ; see SORTER-ENSURE

(defun hash-records (w sap first count recsize keyoff keylen)
  "keccak of the key field of records FIRST..FIRST+COUNT-1 into the worker's key buffer."
  (worker-ensure w count)
  (let ((offs (worker-offs w)) (lens (worker-lens w)))
    (dotimes (i count)
      (setf (aref offs i) (+ +header+ (* (+ first i) recsize) keyoff) (aref lens i) keylen))
    (keccak-into sap offs lens count (worker-keys w))))

(defun worker-drop (w)
  "Give up the key and sort buffers (a large contract's: 72 B per slot)."
  (let ((keys (make-array 0 :element-type '(unsigned-byte 8)))
        (offs (make-array 0 :element-type '(unsigned-byte 64)))
        (lens (make-array 0 :element-type '(unsigned-byte 64)))
        (sorter (make-sorter)))
    (setf (worker-keys w) keys (worker-offs w) offs (worker-lens w) lens (worker-sorter w) sorter)))

(defun storage-root (w ssap si count &optional dsap (dcount 0))
  "(values root slots): the root (32 bytes) of the storage trie over slot records
   SI..SI+COUNT-1 of SSAP (one account's), and its slot count. With DSAP, the DCOUNT
   records there (layers composed, tombstones kept) are laid over them. A worker keeps its
   buffers up to +LARGE+ slots; past that they are exact and dropped after the account;
   past *BIG* (or with DSAP) GIANT-ROOT builds the trie with the worker's pool size."
  (cond ((or dsap (> count *big*)) (giant-root (worker-threads w) ssap si count dsap dcount))
        ((zerop count) (values (eita.mpt:empty-root-bytes) 0))
        ((> count +large+) (multiple-value-prog1 (values (storage-root-1 w ssap si count) count) (worker-drop w)))
        (t (values (storage-root-1 w ssap si count) count))))

(defun storage-root-1 (w ssap si count)
  (progn
    (hash-records w ssap si count +slot+ 20 32)
    (let* ((keys (worker-keys w))
           (order (sort-keys (worker-sorter w) keys count 32))
           (st (st-reset (worker-trie w) 0)))
      (dotimes (r count)
        (let ((i (aref order r)))
          (st-push st keys (* 32 i)
                   (eita.mpt:rlp-encode
                    (eita.mpt:rlp-bytes (minimal-be ssap (+ +header+ (* (+ si i) +slot+) 52) 32))))))
      (st-root-bytes (st-finish st)))))

;;; ------------------------------------------------------------ a giant storage
;;;
;;; A storage over *BIG* slots (XEN: 116.6M at 24M blocks, ~50M more per 1M blocks) is
;;; built by a pool of its own in two passes over its records, with no per-slot buffer in
;;; the heap: (1) per slice of records, keccak the keys and sort the record numbers by
;;; their hashed key's top byte (a counting sort) into the slice's part of IDX, leaving out
;;; the records not in the storage (a tombstone, a base slot a layer rewrites); (2) per
;;; top byte, gather its records from every slice, hash, sort and stack their keys (base
;;; depth 2), SPLIT-ROOT assembling the two branch levels above the 256 subtries. Off the
;;; heap: IDX, 4 B a record; in the heap, per pool thread, one top byte's buffers (72 B a
;;; slot of 1/256 of the storage). Records are read in place (the mapping, the composition
;;; buffer) by absolute address. *BIG-LOCK* is the memory budget: one giant at a time (a
;;; worker that meets a second one waits while the first one's pool keeps the cores busy).

(defvar *big-lock* (sb-thread:make-mutex :name "one giant storage at a time"))

(declaim (inline cmp-abs))
(defun cmp-abs (a b n)
  "-1 / 0 / 1 comparing the N bytes at absolute addresses A and B."
  (cmp-sap (sb-sys:int-sap 0) a (sb-sys:int-sap 0) b n))

(defun giant-root (nthreads bsap bi nb &optional dsap (nd 0))
  "(values root slots) of the storage over base slot records BI..BI+NB-1 at BSAP with,
   when DSAP, the ND composed layer records there (ascending, zeros kept) laid over them:
   on an equal key the layer's record wins; a zero value is no slot (Lean `apply`)."
  (sb-thread:with-mutex (*big-lock*)
    (let* ((n (+ nb nd))
           (nslices (max 1 (ceiling n +slice+)))
           (b0 (+ (sb-sys:sap-int bsap) +header+ (* bi +slot+)))
           (d0 (if dsap (+ (sb-sys:sap-int dsap) +header+) 0))
           (zero (sb-sys:int-sap 0))
           ;; slice C's records of top byte B: IDX[C*+SLICE+ + STARTS[257C+B], .. + STARTS[257C+B+1])
           (starts (make-array (* 257 nslices) :element-type 'fixnum :initial-element 0))
           (idx nil))
      (declare (type fixnum n nb nd b0 d0))
      (when (>= n (expt 2 32)) (error "giant storage: ~D records (record numbers are 32-bit)" n))
      (flet ((rec (e)
               (declare (type fixnum e))
               (if (< e nb) (+ b0 (* e +slot+)) (+ d0 (* (- e nb) +slot+))))
             (d-key (j) (declare (type fixnum j)) (+ d0 (* j +slot+) 20)))
        (declare (inline rec d-key))
        (unwind-protect
             (progn
               (setf idx (cffi:foreign-alloc :uint32 :count (max 1 n)))
               ;; 1. per slice: its records by top byte (256: not in the storage)
               (run-pool
                nthreads nslices
                (lambda (c w)
                  (let* ((e0 (* c +slice+)) (m (- (min n (+ e0 +slice+)) e0)) (row (* 257 c)) (j -1)
                         (tags (make-array m :element-type '(unsigned-byte 16))))
                    (declare (type fixnum e0 m row j))
                    (worker-ensure w m)
                    (let ((offs (worker-offs w)) (lens (worker-lens w)) (keys (worker-keys w)))
                      (dotimes (i m) (setf (aref offs i) (+ (rec (+ e0 i)) 20) (aref lens i) 32))
                      (keccak-into zero offs lens m keys)
                      (dotimes (i m)
                        (let* ((e (+ e0 i)) (a (+ (rec e) 20))
                               (gone (cond ((eita.state.snapshot:zero-bytes-p zero (+ a 32) 32) t)
                                           ((or (>= e nb) (zerop nd)) nil)
                                           (t ; a base slot: does a layer rewrite it? (D ascends, so do we)
                                            (when (< j 0)
                                              (let ((lo 0) (hi nd))
                                                (declare (type fixnum lo hi))
                                                (loop while (< lo hi)
                                                      do (let ((mid (ash (+ lo hi) -1)))
                                                           (if (minusp (cmp-abs (d-key mid) a 32)) (setf lo (1+ mid)) (setf hi mid))))
                                                (setf j lo)))
                                            (loop while (and (< j nd) (minusp (cmp-abs (d-key j) a 32))) do (incf j))
                                            (and (< j nd) (zerop (cmp-abs (d-key j) a 32))))))
                               (tag (if gone 256 (aref keys (* 32 i)))))
                          (setf (aref tags i) tag)
                          (incf (aref starts (+ row tag))))))
                    (let ((acc 0))              ; counts -> starts
                      (declare (type fixnum acc))
                      (dotimes (b 257) (let ((x (aref starts (+ row b)))) (setf (aref starts (+ row b)) acc) (incf acc x))))
                    (let ((pos (subseq starts row (+ row 256))))
                      (dotimes (i m)
                        (let ((tag (aref tags i)))
                          (unless (= tag 256)
                            (setf (sb-sys:sap-ref-32 idx (* 4 (+ e0 (aref pos tag)))) (+ e0 i))
                            (incf (aref pos tag)))))))))
               ;; 2. per top byte: its subtrie; the branches above them
               (flet ((size (b) (loop for c below nslices sum (- (aref starts (+ (* 257 c) b 1)) (aref starts (+ (* 257 c) b))))))
                 (let ((most (loop for b below 256 maximize (size b))))
                   (values
                    (st-root-bytes
                     (split-root
                      256 (lambda (b) (plusp (size b)))
                      (lambda (st b w)
                        (worker-ensure w most)              ; once per thread: no regrowth
                        (sorter-ensure (worker-sorter w) most)
                        (let ((offs (worker-offs w)) (lens (worker-lens w)) (keys (worker-keys w)) (m 0))
                          (declare (type fixnum m))
                          (dotimes (c nslices)
                            (loop for p from (aref starts (+ (* 257 c) b)) below (aref starts (+ (* 257 c) b 1))
                                  do (setf (aref offs m) (+ (rec (sb-sys:sap-ref-32 idx (* 4 (+ (* c +slice+) p)))) 20)
                                           (aref lens m) 32)
                                     (incf m)))
                          (keccak-into zero offs lens m keys)
                          (let ((order (sort-keys (worker-sorter w) keys m 32)))
                            (dotimes (r m)
                              (let ((i (aref order r)))
                                (st-push st keys (* 32 i)
                                         (eita.mpt:rlp-encode
                                          (eita.mpt:rlp-bytes (minimal-be zero (+ (aref offs i) 32) 32)))))))))
                      nthreads))
                    (loop for c below nslices sum (aref starts (+ (* 257 c) 256)))))))
          (when idx (cffi:foreign-free idx)))))))

;;; ------------------------------------------------------------ split roots

(defun split-root (ngroups nonempty feed nthreads)
  "The root item of a trie whose keys come in NGROUPS groups, by their top nibble (16) or
   top byte (256), in key order: (FEED st g w) pushes group G's keys into the stack trie
   ST in order, (NONEMPTY g) says it has some. When every branch above the groups has 2+
   non-empty children (the root; with 256 groups, each non-empty top nibble's node too),
   the groups' subtries (base depth 1 or 2) are built in parallel and the branches above
   them assembled; otherwise one stack trie (base 0) takes the groups in order."
  (let* ((levels (if (= ngroups 16) 1 2)) (per (floor ngroups 16))
         (under (loop for v below 16
                      collect (loop for g from (* per v) below (* per (1+ v)) count (funcall nonempty g)))))
    (flet ((branch (items start)
             (eita.mpt:rlp-list*
              (nconc (loop for i from start below (+ start 16)
                           collect (let ((x (aref items i))) (if x (eita.mpt:node-ref x) *empty-item*)))
                     (list *empty-item*)))))
      (if (and (>= (count-if #'plusp under) 2) (or (= levels 1) (not (member 1 under))))
          (let ((items (make-array ngroups :initial-element nil)))
            (run-pool nthreads ngroups
                      (lambda (g w)
                        (when (funcall nonempty g)
                          (let ((st (st-reset (worker-trie w) levels)))
                            (funcall feed st g w)
                            (setf (aref items g) (st-finish st))))))
            (if (= levels 1)
                (branch items 0)
                (let ((mids (make-array 16 :initial-element nil)))
                  (dotimes (v 16) (when (plusp (nth v under)) (setf (aref mids v) (branch items (* 16 v)))))
                  (branch mids 0))))
          (let ((w (make-worker)) (st (make-stack-trie 0)))
            (dotimes (g ngroups) (when (funcall nonempty g) (funcall feed st g w)))
            (st-finish st))))))

;;; ------------------------------------------------------------ the worker pool

(defstruct (counter (:constructor make-counter ())) (next 0 :type sb-ext:word))

(defun run-pool (nthreads ntasks fn)
  "Call FN on each task index 0..NTASKS-1 and the calling worker's scratch, from
   NTHREADS threads (a pool of 1 is the serial path). An error in a worker is re-signalled
   here once every thread has stopped."
  (let* ((c (make-counter)) (lock (sb-thread:make-mutex)) (failure nil)
         (threads
           (loop repeat (max 1 (min nthreads ntasks))
                 collect (sb-thread:make-thread
                          (lambda ()
                            (let ((w (make-worker)))
                              (setf (worker-threads w) nthreads)
                              (handler-case
                                  (loop (let ((i (sb-ext:atomic-incf (counter-next c))))
                                          (when (or (>= i ntasks) failure) (return))
                                          (funcall fn i w)))
                                (error (e)
                                  (sb-thread:with-mutex (lock) (setf failure (or failure e)))))))
                          :name "snapshot-root worker"))))
    (mapc #'sb-thread:join-thread threads)
    (when failure (error failure))))

;;; ------------------------------------------------------------ pass 1: storage roots -> buckets

(defun open-file-limit (want)
  "The soft open-file limit, raised to WANT (within the hard limit) if below it."
  (let ((nofile #+darwin 8 #-darwin 7))          ; RLIMIT_NOFILE
    (sb-alien:with-alien ((lim (sb-alien:array sb-alien:unsigned-long 2)))   ; rlim_cur rlim_max
      (sb-alien:alien-funcall
       (sb-alien:extern-alien "getrlimit" (function sb-alien:int sb-alien:int (* (sb-alien:array sb-alien:unsigned-long 2))))
       nofile (sb-alien:addr lim))
      (when (< (sb-alien:deref lim 0) want)
        (setf (sb-alien:deref lim 0) (min want (sb-alien:deref lim 1)))
        (sb-alien:alien-funcall
         (sb-alien:extern-alien "setrlimit" (function sb-alien:int sb-alien:int (* (sb-alien:array sb-alien:unsigned-long 2))))
         nofile (sb-alien:addr lim))
        (sb-alien:alien-funcall
         (sb-alien:extern-alien "getrlimit" (function sb-alien:int sb-alien:int (* (sb-alien:array sb-alien:unsigned-long 2))))
         nofile (sb-alien:addr lim)))
      (sb-alien:deref lim 0))))

(defun open-buckets (scratch na)
  "The bucket files: 256 (the first byte of the hashed key), or 2048 (11 bits) past 2^26
   accounts so a bucket stays under ~150K records at any state size. 2048 open files need
   the soft descriptor limit raised; when that is refused, 256."
  (let ((n (if (> na (expt 2 26)) 2048 256)))
    (when (and (= n 2048) (< (open-file-limit 2200) 2200))
      (format *error-output* "~&[snapshot-root] 256 buckets: the open-file limit stays under 2200~%")
      (setf n 256))
    (let ((buckets (make-array n)))
      (dotimes (b n buckets)
        (let ((path (format nil "~Ab~(~3,'0X~)" scratch b)))
          (setf (aref buckets b)
                (make-bucket (open path :direction :output :element-type '(unsigned-byte 8)
                                        :if-exists :supersede :if-does-not-exist :create)
                             path)))))))

(declaim (inline bucket-of))
(defun bucket-of (nbuckets recs off)
  "The bucket of the hashed key at RECS[OFF..]: its top log2(NBUCKETS) bits."
  (declare (type octets recs) (type fixnum nbuckets off))
  (if (= nbuckets 256)
      (aref recs off)
      (logior (ash (aref recs off) 3) (ash (aref recs (1+ off)) -5))))

(defstruct (bucket (:constructor make-bucket (stream path)))
  stream path (buf (make-array +wbuf+ :element-type '(unsigned-byte 8)) :type octets) (pos 0 :type fixnum)
  (count 0 :type fixnum))

(defun bucket-flush (b)
  (when (plusp (bucket-pos b))
    (write-sequence (bucket-buf b) (bucket-stream b) :end (bucket-pos b))
    (setf (bucket-pos b) 0)))

(defun bucket-put (b recs start)
  (declare (type octets recs) (type fixnum start))
  (when (> (+ (bucket-pos b) +rec+) +wbuf+) (bucket-flush b))
  (replace (bucket-buf b) recs :start1 (bucket-pos b) :start2 start :end2 (+ start +rec+))
  (incf (bucket-pos b) +rec+)
  (incf (bucket-count b)))

(defun slot-lower-bound (ssap ns asap aoff)
  "Index of the first storage record whose address is >= the 20 bytes at ASAP+AOFF."
  (let ((lo 0) (hi ns))
    (declare (type fixnum lo hi))
    (loop while (< lo hi)
          do (let ((mid (ash (+ lo hi) -1)))
               (if (minusp (cmp-sap ssap (+ +header+ (* mid +slot+)) asap aoff 20))
                   (setf lo (1+ mid))
                   (setf hi mid))))
    lo))

(defun base-record (w recs r asap aoff ssap si sj)
  "Bucket record R from the base account at ASAP+AOFF with slots SI..SJ (key already in
   place)."
  (copy-sap asap (+ aoff 24) 72 recs (+ (* r +rec+) 32))     ; nonce balance codehash
  (replace recs (storage-root w ssap si (- sj si)) :start1 (+ (* r +rec+) 104))
  (setf (worker-big w) (max (worker-big w) (- sj si)))
  (incf (worker-slots w) (- sj si)))

(defun layered-record (w recs r layers s addr &optional (si 0) (base-count 0))
  "Bucket record R for ADDR from the stack (Lean `view` at ADDR), or NIL when S1 leaves
   the address out of the state. Unlike a base account, whose slots are read in place,
   ADDR's slots are composed into the worker's buffer (88 B a slot), and a large buffer is
   dropped after use (at 11.5M, with ten threads each keeping its largest copy, 16 GB ran
   out). Over a giant base storage (BASE-COUNT > *BIG* slots from SI) only the layers are
   composed, tombstones kept, and GIANT-ROOT lays them over the base's slots in place —
   unless a layer wiped the storage, when the base's slots are not part of it."
  (let ((out (worker-obuf w)) (giant (> base-count *big*)) (fields nil) (root nil) (count 0))
    (multiple-value-bind (lfields wiped) (and giant (eita.state.snapshot:compose-address layers nil addr out))
      (if (or wiped (not giant))
          (progn
            (setf fields (eita.state.snapshot:compose-address layers s addr out :final t))
            (multiple-value-setq (root count) (storage-root w (eita.state.snapshot:obuf-sap out) 0 (eita.state.snapshot:obuf-count out))))
          (multiple-value-bind (found nonce balance codehash flag) (eita.state.snapshot:snap-account s addr)
            (setf fields (or lfields (and found (list nonce balance codehash flag))))
            (multiple-value-setq (root count)
              (storage-root w (eita.state.snapshot:mapping-sap (eita.state.snapshot:snap-slot-map s)) si base-count
                            (eita.state.snapshot:obuf-sap out) (eita.state.snapshot:obuf-count out))))))
    (when (> (eita.state.snapshot:obuf-count out) +large+)
      (eita.state.snapshot:obuf-free out) (setf (worker-obuf w) (eita.state.snapshot:make-obuf)))
    (destructuring-bind (&optional nonce balance codehash mark) fields
      (when (and nonce (eita.state.snapshot:s1-included-p nonce balance codehash (plusp count) mark))
        (let ((o (* r +rec+)))
          (replace recs (eita.mpt:%keccak (eita.state.snapshot:int->octets addr 20)) :start1 o)
          (replace recs (eita.state.snapshot:int->octets nonce 8) :start1 (+ o 32))
          (replace recs (eita.state.snapshot:int->octets balance 32) :start1 (+ o 40))
          (replace recs (eita.state.snapshot:int->octets codehash 32) :start1 (+ o 72))
          (replace recs root :start1 (+ o 104))
          (setf (worker-big w) (max (worker-big w) count))
          (incf (worker-slots w) count)
          t)))))

(defun chunk-records (w s layers a0 a1 s0 s1 lo hi)
  "The bucket records of base accounts A0..A1-1 (their slots S0..S1-1) of S, with the
   addresses LAYERS mention in [LO, HI) laid over them: into the worker's RECS, in address
   order. Returns their count."
  (let* ((asap (eita.state.snapshot:mapping-sap (eita.state.snapshot:snap-acct s)))
         (ssap (eita.state.snapshot:mapping-sap (eita.state.snapshot:snap-slot-map s)))
         (n (- a1 a0))
         (touched (and layers
                       (let ((l '()))
                         (eita.state.snapshot:map-touched-addresses layers (lambda (a) (push a l)) :lo lo :hi hi)
                         (nreverse l))))
         (cap (* +rec+ (+ n (length touched)))))
    (declare (type fixnum a0 a1 s0 s1 n))
    (when (< (length (worker-recs w)) cap)
      (let ((v (make-array cap :element-type '(unsigned-byte 8)))) (setf (worker-recs w) v)))
    (let ((recs (worker-recs w)) (si s0) (r 0))
      (declare (type fixnum si r))
      ;; keccak(addr) of the chunk's base accounts, in one batch
      (hash-records w asap a0 n +acct+ 0 20)
      (when (< (length (worker-bkeys w)) (* 32 n))
        (let ((v (make-array (* 32 n) :element-type '(unsigned-byte 8)))) (setf (worker-bkeys w) v)))
      (replace (worker-bkeys w) (worker-keys w) :end2 (* 32 n))
      (flet ((slots-end (aoff)
               ;; the end of the base account at AOFF's slots, from SI
               (when (and (< si s1) (minusp (cmp-sap ssap (+ +header+ (* si +slot+)) asap aoff 20)))
                 (error "~A: storage record ~D belongs to no account (S5)" (eita.state.snapshot:snap-dir s) si))
               (let ((sj si))
                 (declare (type fixnum sj))
                 (loop while (and (< sj s1) (zerop (cmp-sap ssap (+ +header+ (* sj +slot+)) asap aoff 20)))
                       do (incf sj))
                 sj)))
        (dotimes (k n)
          (let* ((aoff (+ +header+ (* (+ a0 k) +acct+)))
                 (base-key (eita.state.snapshot:sap-be asap aoff 20)))
            ;; layered addresses below this base account come first
            (loop while (and touched (< (first touched) base-key))
                  do (when (layered-record w recs r layers s (pop touched)) (incf r)))
            (let ((sj (slots-end aoff)))
              (if (and touched (= (first touched) base-key))
                  (when (layered-record w recs r layers s (pop touched) si (- sj si)) (incf r))
                  (progn
                    (replace recs (worker-bkeys w) :start1 (* r +rec+) :start2 (* 32 k) :end2 (* 32 (1+ k)))
                    (base-record w recs r asap aoff ssap si sj)
                    (incf r)))
              (setf si sj))))
        (dolist (addr touched)
          (when (layered-record w recs r layers s addr) (incf r)))
        (unless (= si s1)
          (error "~A: ~D storage records belong to no account (S5)" (eita.state.snapshot:snap-dir s) (- s1 si))))
      r)))

(defun storage-pass (s buckets lock nthreads &optional layers)
  "Every account's storage root and hashed key, into the buckets: the base S, or with
   LAYERS (layer snaps, newest first) the stack's merged state. Returns (values
   largest-storage slots-seen)."
  (let* ((acct (eita.state.snapshot:snap-acct s)) (slots (eita.state.snapshot:snap-slot-map s))
         (asap (eita.state.snapshot:mapping-sap acct)) (ssap (eita.state.snapshot:mapping-sap slots))
         (na (eita.state.snapshot:snap-n-accounts s)) (ns (eita.state.snapshot:snap-n-slots s))
         (nchunks (max 1 (ceiling na +chunk+))) (big 0) (seen 0))
    (run-pool
     nthreads nchunks
     (lambda (c w)
       (let* ((a0 (min na (* c +chunk+))) (a1 (min na (+ a0 +chunk+)))
              (s0 (if (zerop c) 0 (slot-lower-bound ssap ns asap (+ +header+ (* a0 +acct+)))))
              (s1 (if (= a1 na) ns (slot-lower-bound ssap ns asap (+ +header+ (* a1 +acct+)))))
              ;; the chunk's address range: from its first base account (0 for the first
              ;; chunk) to the next chunk's (none for the last)
              (lo (if (zerop c) nil (eita.state.snapshot:sap-be asap (+ +header+ (* a0 +acct+)) 20)))
              (hi (if (= a1 na) nil (eita.state.snapshot:sap-be asap (+ +header+ (* a1 +acct+)) 20)))
              (n (chunk-records w s layers a0 a1 s0 s1 lo hi))
              (recs (worker-recs w)))
         ;; the chunk's pages are done with (file-backed: dropped from this process only)
         (eita.state.snapshot:release-range acct (+ +header+ (* a0 +acct+)) (+ +header+ (* a1 +acct+)))
         (eita.state.snapshot:release-range slots (+ +header+ (* s0 +slot+)) (+ +header+ (* s1 +slot+)))
         (sb-thread:with-mutex (lock)
           (dotimes (k n) (bucket-put (aref buckets (bucket-of (length buckets) recs (* k +rec+))) recs (* k +rec+)))
           (setf big (max big (worker-big w)))
           (incf seen (worker-slots w))
           (setf (worker-slots w) 0)))))
    (values big seen)))

;;; ------------------------------------------------------------ pass 2: buckets -> account trie

(defun read-bucket (w b)
  "Bucket B's records, in the worker's (grow-only) buffer; returns their count."
  (with-open-file (in (bucket-path b) :element-type '(unsigned-byte 8))
    (let ((len (file-length in)))
      (when (< (length (worker-bucket w)) len)
        (setf (worker-bucket w) (make-array len :element-type '(unsigned-byte 8))))
      (unless (= (read-sequence (worker-bucket w) in :end len) len)
        (error "bucket ~A: short read" (bucket-path b)))
      (floor len +rec+))))

(defun feed-bucket (st w b)
  "Push bucket B's records into ST in key order."
  (when (plusp (bucket-count b))
    (let* ((n (read-bucket w b)) (recs (worker-bucket w))
           (order (sort-keys (worker-sorter w) recs n +rec+)))
      (unless (= n (bucket-count b)) (error "bucket ~A: ~D records on disk, ~D written" (bucket-path b) n (bucket-count b)))
      (dotimes (r n)
        (let ((o (* +rec+ (aref order r))))
          (st-push st recs o
                   (eita.mpt:account-leaf-value (minimal-vec recs (+ o 32) (+ o 40))
                                                 (minimal-vec recs (+ o 40) (+ o 72))
                                                 (subseq recs (+ o 104) (+ o 136))
                                                 (subseq recs (+ o 72) (+ o 104)))))))))

(defun account-pass (buckets nthreads)
  "The state root over the bucket files: SPLIT-ROOT over the 16 top nibbles, a nibble's
   buckets in order."
  (let ((per (floor (length buckets) 16)))   ; buckets per top nibble
    (st-root-bytes
     (split-root 16
                 (lambda (v) (loop for b from (* per v) below (* per (1+ v)) thereis (plusp (bucket-count (aref buckets b)))))
                 (lambda (st v w) (loop for b from (* per v) below (* per (1+ v)) do (feed-bucket st w (aref buckets b))))
                 nthreads))))

;;; ------------------------------------------------------------ the state root

(defun scratch-dir (s)
  "The bucket files live beside the snapshot, in .root-N-PID/ (invisible to the
   snap-*/ readers), for the duration of the check: one checker's own, so a checker still
   dying from a previous life of the replay never shares bucket files with a new one."
  (let* ((dir (string-right-trim "/" (namestring (eita.state.snapshot:snap-dir s))))
         (parent (subseq dir 0 (1+ (or (position #\/ dir :from-end t) -1)))))
    (format nil "~A.root-~D-~D/" parent (eita.state.snapshot:snap-block s) (sb-posix:getpid))))

(defun snapshot-root (dir &key (threads (eita.state.snapshot:hardware-threads)) buckets layers)
  "(values root-hex expected-hex n-accounts n-slots) for the snapshot at DIR, or with
   LAYERS (layer directories, oldest first) for the state of that stack over it (Lean
   `view`): no merged snapshot is written. BUCKETS: the bucket count to use instead of
   the one the state size picks (tests)."
  (let* ((s (eita.state.snapshot:snap-open dir :fence (and layers t)))  ; point lookups only under layers
         (ls (reverse (mapcar #'eita.state.snapshot:snap-open layers)))   ; newest first
         (top (or (first ls) s))
         (na (+ (eita.state.snapshot:snap-n-accounts s) (reduce #'+ ls :key #'eita.state.snapshot:snap-n-accounts)))
         (ns (eita.state.snapshot:snap-n-slots s))
         (threads (max 1 threads))
         (scratch (scratch-dir top))
         (buckets (if buckets (make-array buckets :initial-element nil) nil))
         (lock (sb-thread:make-mutex))
         (t0 (get-internal-real-time)))
    ;; The nursery defaults to 5% of the heap reservation (800 MB of garbage between
    ;; collections at the 16 GB production setting); the footprint must not follow it.
    ;; The large transients (a bucket, a big contract's sort buffers) live across a few
    ;; collections: promoted after one they would pile up in an older generation until it
    ;; is collected, so they stay in the nursery longer and die there.
    (setf (sb-ext:bytes-consed-between-gcs) (min (sb-ext:bytes-consed-between-gcs) (* 128 1024 1024))
          (sb-ext:generation-number-of-gcs-before-promotion 0) 2)
    (flet ((elapsed () (/ (- (get-internal-real-time) t0) internal-time-units-per-second)))
      (ensure-directories-exist scratch)
      (unwind-protect
           (progn
             (setf buckets (open-buckets scratch (if buckets (if (= (length buckets) 256) 0 (expt 2 27)) na)))
             (multiple-value-bind (big seen) (storage-pass s buckets lock threads ls)
               (unless (or ls (= seen ns))
                 (error "~A: ~D storage records seen, manifest says ~D" dir seen ns))
               (setf ns seen)
               (setf na (loop for b across buckets sum (bucket-count b)))   ; with layers: the merged count
               (format t "~&storage roots: ~D accounts, ~D slots (largest ~D) in ~,1Fs~%" na ns big (elapsed))
               (finish-output)
               (format *error-output* "~&[snapshot-root] ~D threads; storage pass ~,1Fs~%" threads (elapsed)))
             (loop for b across buckets do (bucket-flush b) (close (bucket-stream b)))
             (sb-ext:gc :full t)
             (let ((root (if (zerop (loop for b across buckets sum (bucket-count b)))
                             (eita.mpt:empty-root-bytes)
                             (account-pass buckets threads))))
               (format *error-output* "~&[snapshot-root] account trie done at ~,1Fs~%" (elapsed))
               (values (eita.mpt:bytes->hex root)
                       (let ((r (getf (eita.state.snapshot:snap-manifest top) :state-root)))
                         (and r (string-downcase (if (and (> (length r) 1) (string-equal "0x" r :end2 2)) (subseq r 2) r))))
                       na ns)))
        (when buckets
          (loop for b across buckets
                when b do (ignore-errors (close (bucket-stream b) :abort t))
                          (ignore-errors (delete-file (bucket-path b)))))
        (ignore-errors (sb-posix:rmdir (string-right-trim "/" scratch)))
        (mapc #'eita.state.snapshot:snap-close ls)
        (eita.state.snapshot:snap-close s)))))

(defun exit-with-parent (pid)
  "A checker the replay spawned (--parent PID) lives only as long as the replay: once its
   parent is gone (it is reparented) it exits within a second, releasing its heap and
   threads. Portable (Linux and macOS): polls getppid."
  (sb-thread:make-thread
   (lambda () (loop (unless (= (sb-posix:getppid) pid) (sb-ext:exit :code 3 :abort t)) (sleep 1)))
   :name "parent watch"))

(defun main (args)
  (let* ((p (position "--parent" args :test #'string=))
         (args (if p
                   (progn (exit-with-parent (parse-integer (nth (1+ p) args)))
                          (append (subseq args 0 p) (nthcdr (+ p 2) args)))
                   args))
         (dir (first args))
         (threads (find-if (lambda (a) (every #'digit-char-p a)) (rest args)))
         (layers (remove threads (rest args))))
    (unless dir (format t "usage: eita check-root [--parent PID] <snap-dir> [<layer-dir> ...] [threads]~%") (sb-ext:quit :unix-status 2))
    (multiple-value-bind (root expected na ns)
        (if threads
            (snapshot-root dir :threads (parse-integer threads) :layers layers)
            (snapshot-root dir :layers layers))
      (format t "~&parsed ~D accounts, ~D slots (snapshot)~%" na ns)
      (format t "~&CL trie root : ~A~%" root)
      (when expected (format t "snapshot root: ~A~%" expected))
      (if (and expected (string-equal root expected))
          (progn (format t "MATCH~%") (sb-ext:quit :unix-status 0))
          (progn (format t "~A~%" (if expected "MISMATCH" "(no state root to compare)"))
                 (sb-ext:quit :unix-status 1))))))
