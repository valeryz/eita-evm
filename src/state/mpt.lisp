;;;; mpt.lisp — Common Lisp Merkle-Patricia Trie (Ethereum state root).
;;;;
;;;; Pure-CL mirror of lean/Evm/Trie.lean (patricialise / hexPrefix /
;;;; nodeRef / root) and lean/Evm/Trie/Incremental.lean (persistent Node:
;;;; empty / leaf / ext / branch). RLP follows lean/Evm/Rlp.lean.
;;;;
;;;; REPRESENTATION DIVERGENCE FROM THE LEAN REFERENCE (deliberate).
;;;; Lean carries a nibble path as `List UInt8`; here it is a
;;;; (SIMPLE-ARRAY (UNSIGNED-BYTE 8) (*)), one nibble per element, and
;;;; recursion carries a START OFFSET instead of taking list tails. A CL
;;;; list cell is 24 bytes with the nibble packed into the pointer slot, so
;;;; a 32-byte key cost 1 536 bytes as a list against 64 as a vector — 24x.
;;;; That mattered in three places with three different lifetimes:
;;;;   * `trie-root` materialises one path per key BEFORE patricialise and
;;;;     holds them all for the whole build. Rebuilding the storage trie of
;;;;     Arc's largest contract (14 618 285 slots, 70% of that state) needed
;;;;     22.5 GB of nibble lists at once and exhausted a 20 GB heap.
;;;;   * `mtrie-insert` built one throwaway path per call: 1 536 B of churn.
;;;;   * `make-mleaf`/`make-mext` RETAIN their path. With 174k keys the trie
;;;;     is ~5 levels deep, so a leaf keeps ~59 of its 64 nibbles — ~245 MB
;;;;     of retained paths for that account trie, and it would be ~20 GB for
;;;;     a persistent 14.6M-leaf storage trie.
;;;; Roots are unchanged: the Lean reference keeps its list representation on
;;;; purpose, so the Lean replays stay an INDEPENDENT cross-check of this file
;;;; (state/root.lisp computes roots without building it). Paths are treated as
;;;; IMMUTABLE — subpaths may share structure with their parent vector.
;;;;
;;;; This is the basis for the incremental MPT (#20): nodes are persistent
;;;; structs with a cached-hash slot, and keccak is behind a *keccak*
;;;; indirection so a SHA3-accelerated backend can be swapped in later.
;;;;
;;;; Entry point:
;;;;   (account-state-root accounts)
;;;; where ACCOUNTS is a list of (addr nonce balance storage-alist code-bytes),
;;;; storage-alist = ((slot . value) ...). Returns the 32-byte root vector.
;;;;
;;;; This file only DEFINES things; it loads CFFI + libeita for keccak so it
;;;; can stand alone (it does not depend on replay-cl).


(in-package #:eita.mpt)

;;; --------------------------------------------------------------------
;;; Keccak FFI (the same entry points as eita.core; kept pluggable).
;;; --------------------------------------------------------------------

;; libeita and libkeccak_batch are opened by native/libraries.lisp (the one place).
(defcfun ("eita_keccak256" eita-keccak256) :void
  (input :pointer) (inlen :uint64) (output :pointer))

;; ARMv8.2 FEAT_SHA3-accelerated keccak (lean/c/keccak_sha3.c) — bit-identical to
;; the portable one (verified), used by the trie since it is hashing-bound.
(defcfun ("eita_keccak256_sha3" eita-keccak256-sha3) :void
  (input :pointer) (inlen :uint64) (output :pointer))

(defun %keccak-via (cfn bytes)
  "Hash BYTES (a sequence of u8) via CFN, return a fresh 32-byte vector."
  (let ((in (coerce bytes '(simple-array (unsigned-byte 8) (*))))
        (out (make-array 32 :element-type '(unsigned-byte 8))))
    (with-pointer-to-vector-data (i in)
      (with-pointer-to-vector-data (o out) (funcall cfn i (length in) o)))
    out))

(defun keccak256-bytes (bytes)      (%keccak-via #'eita-keccak256 bytes))
(defun keccak256-sha3-bytes (bytes) (%keccak-via #'eita-keccak256-sha3 bytes))

;; Indirection so the keccak backend is swappable; default to SHA3-accelerated.
(defparameter *keccak* #'keccak256-sha3-bytes
  "Function: (sequence-of-u8) -> 32-byte vector.")

(declaim (inline %keccak))
(defun %keccak (bytes) (funcall *keccak* bytes))

;;; --------------------------------------------------------------------
;;; Batched keccak (#237) — one FFI crossing hashes N inputs, optionally
;;; across worker threads. Used by the LEVEL-WAVEFRONT root recompute:
;;; all dirty nodes at the same trie depth are independent, so their
;;; >=32B encodings hash in a single call. Bit-identical to the per-node
;;; eita_keccak256_sha3 path (verified by the trie oracles). Lives in a
;;; SEPARATE dylib (c/libkeccak_batch.dylib) so libeita is never relinked.
;;; --------------------------------------------------------------------

(defcfun ("eita_keccak256_batch" %keccak-batch-c) :void
  (data :pointer) (offs :pointer) (lens :pointer) (outs :pointer) (count :uint64))
(defcfun ("eita_keccak256_batch_par" %keccak-batch-par-c) :void
  (data :pointer) (offs :pointer) (lens :pointer) (outs :pointer)
  (count :uint64) (nthreads :uint32))
(defcfun ("memcpy" %memcpy) :pointer (d :pointer) (s :pointer) (n :uint64))

(eita.native:defstartup *keccak-batch-threads*
  (min 8 (or (ignore-errors
               (parse-integer
                (with-output-to-string (s)
                  (sb-ext:run-program "/usr/sbin/sysctl" '("-n" "hw.ncpu")
                                      :output s))))
             8))
  "Worker threads for the parallel batched keccak (min 8, cores).")

(defun keccak-batch (vectors &optional (nthreads *keccak-batch-threads*))
  "VECTORS: a simple-vector of (unsigned-byte 8) arrays. Returns a
   simple-vector of fresh 32-byte result vectors, one per input. One
   marshaling pass (pack into a foreign buffer) + one FFI call (parallel
   when NTHREADS>1). (Measured by the June prof-keccak-batch probe; git history.)"
  (let* ((n (length vectors))
         (results (make-array n)))
    (when (zerop n) (return-from keccak-batch results))
    (let ((total (loop for v across vectors sum (length v))))
      (with-foreign-objects ((data :uint8 (max total 1)) (offs :uint64 n)
                             (lens :uint64 n) (outs :uint8 (* n 32)))
        (let ((off 0))
          (dotimes (i n)
            (let* ((v (aref vectors i)) (len (length v)))
              (setf (mem-aref offs :uint64 i) off
                    (mem-aref lens :uint64 i) len)
              (when (plusp len)
                (with-pointer-to-vector-data (sap v)
                  (%memcpy (inc-pointer data off) sap len)))
              (incf off len))))
        (if (> nthreads 1)
            (%keccak-batch-par-c data offs lens outs n nthreads)
            (%keccak-batch-c data offs lens outs n))
        (dotimes (i n)
          (let ((r (make-array 32 :element-type '(unsigned-byte 8))))
            (dotimes (j 32) (setf (aref r j) (mem-aref outs :uint8 (+ (* i 32) j))))
            (setf (aref results i) r)))))
    results))

;;; --------------------------------------------------------------------
;;; Byte helpers
;;; --------------------------------------------------------------------

(defun b (&rest elts) (coerce elts '(vector (unsigned-byte 8))))

(defun int->be-bytes (n)
  "Minimal big-endian byte vector for non-negative N. Zero -> empty
   vector (mirrors Rlp.natToBytes)."
  (if (zerop n)
      (make-array 0 :element-type '(unsigned-byte 8))
      (let ((acc '()))
        (loop for v = n then (ash v -8)
              while (plusp v)
              do (push (logand v 255) acc))
        (coerce acc '(vector (unsigned-byte 8))))))

(defun int->be-bytes-fixed (n width)
  "Fixed-WIDTH big-endian byte vector for N (zero-padded on the left)."
  (let ((out (make-array width :element-type '(unsigned-byte 8))))
    (loop for i from (1- width) downto 0
          do (setf (aref out i) (logand n 255)) (setf n (ash n -8)))
    out))

(defun bytes->hex (bytes)
  (string-downcase
   (with-output-to-string (s)
     (map nil (lambda (x) (format s "~2,'0X" x)) bytes))))

;;; --------------------------------------------------------------------
;;; RLP encoding — mirrors lean/Evm/Rlp.lean (Item = bytes | list).
;;; Items here are represented as:
;;;   (:bytes . <vector>)   or   (:list <item> <item> ...)
;;; encode returns a u8 vector.
;;; --------------------------------------------------------------------

(defun rlp-bytes (v) (cons :bytes (coerce v '(vector (unsigned-byte 8)))))
(defun rlp-list (&rest items) (cons :list items))
(defun rlp-list* (items) (cons :list items))

(defun rlp-write-length (len offset out pos)
  "Write the length prefix of a LEN-byte payload (OFFSET #x80 strings, #xc0 lists) into
   OUT at POS (OUT NIL: only measure); return its size. Mirrors Rlp.encodeLength."
  (if (< len 56)
      (progn (when out (setf (aref out pos) (+ offset len))) 1)
      (let ((n (ceiling (integer-length len) 8)))
        (when out
          (setf (aref out pos) (+ offset 55 n))
          (loop for i from 1 to n do (setf (aref out (+ pos i)) (ldb (byte 8 (* 8 (- n i))) len))))
        (1+ n))))

(defun rlp-write (item out pos)
  "Write ITEM's encoding into OUT from POS (OUT NIL: only measure); return where it ends. Nothing
   is allocated: the prefix was one to three small vectors per item per pass, a fifth of the
   replay's allocation in the receipts root."
  (declare (type (or null (simple-array (unsigned-byte 8) (*))) out) (type fixnum pos))
  (let* ((bytes (eq (car item) :bytes))
         (len (if bytes (length (cdr item)) (loop for x in (cdr item) sum (rlp-write x nil 0)))))
    (unless (and bytes (= len 1) (< (aref (cdr item) 0) #x80))
      (incf pos (rlp-write-length len (if bytes #x80 #xc0) out pos)))
    (cond (bytes (when out (replace out (cdr item) :start1 pos)) (+ pos len))
          (out (dolist (x (cdr item) pos) (setf pos (rlp-write x out pos))))
          (t (+ pos len)))))

(defun rlp-encode (item)
  "Encode an RLP ITEM to a u8 vector, written into one buffer (not copied once per level
   of nesting: that was a fifth of the replay, in the receipts root). Mirrors Rlp.encode."
  (let ((out (make-array (rlp-write item nil 0) :element-type '(unsigned-byte 8))))
    (rlp-write item out 0)
    out))

;;; --------------------------------------------------------------------
;;; Nibbles + hexPrefix — mirrors Trie.lean.
;;; --------------------------------------------------------------------

(deftype nibbles () '(simple-array (unsigned-byte 8) (*)))

(declaim (inline make-nibbles))
(defun make-nibbles (n) (make-array n :element-type '(unsigned-byte 8)))

(defparameter *no-nibbles* (make-nibbles 0)
  "The shared empty path. Safe to share because paths are immutable.")

(declaim (inline nib-empty))
(defun nib-empty () *no-nibbles*)

(defun bytes->nibbles (bytes)
  "High nibble then low nibble for each byte (Trie.bytesToNibbles), as a
   nibble VECTOR. One allocation of 2N bytes, not 2N list cells."
  (let* ((v (if (typep bytes 'nibbles)
                bytes
                (coerce bytes '(simple-array (unsigned-byte 8) (*)))))
         (len (length v))
         (out (make-nibbles (* 2 len))))
    (declare (type nibbles v out))
    (dotimes (i len out)
      (let ((byte (aref v i)))
        (setf (aref out (* 2 i))      (ash byte -4)
              (aref out (1+ (* 2 i))) (logand byte #x0f))))))

(defun nib-sub (path start &optional (end (length path)))
  "PATH[START..END) as an exact nibble vector — what gets STORED in a node.
   Returns PATH itself when the range is all of an already-exact vector;
   paths are immutable, so sharing is safe."
  (declare (type nibbles path))
  (if (and (= start 0) (= end (length path)))
      path
      (let ((out (make-nibbles (- end start))))
        (replace out path :start2 start :end2 end)
        out)))

(declaim (inline nib-single))
(defun nib-single (nib)
  (let ((out (make-nibbles 1))) (setf (aref out 0) nib) out))

(defun nib-cons (nib path)
  "NIB prepended to PATH, as a fresh vector."
  (declare (type nibbles path))
  (let* ((lp (length path)) (out (make-nibbles (1+ lp))))
    (setf (aref out 0) nib)
    (replace out path :start1 1)
    out))

(defun nib-concat (a b)
  "A followed by B, as a fresh vector."
  (declare (type nibbles a b))
  (let* ((la (length a)) (out (make-nibbles (+ la (length b)))))
    (replace out a)
    (replace out b :start1 la)
    out))

(defun nib= (a astart b bstart)
  "Suffix equality: A[ASTART..] = B[BSTART..]."
  (declare (type nibbles a b))
  (let ((la (- (length a) astart)) (lb (- (length b) bstart)))
    (and (= la lb)
         (loop for i below la
               always (= (aref a (+ astart i)) (aref b (+ bstart i)))))))

(defun nib-common-len (a astart b bstart)
  "Length of the longest common prefix of A[ASTART..] and B[BSTART..]."
  (declare (type nibbles a b))
  (let ((n (min (- (length a) astart) (- (length b) bstart))))
    (loop for i below n
          unless (= (aref a (+ astart i)) (aref b (+ bstart i)))
            do (return i)
          finally (return n))))

(declaim (inline nib-prefix-p))
(defun nib-prefix-p (p path start)
  "Is the whole of P a prefix of PATH[START..]?"
  (declare (type nibbles p path))
  (and (>= (- (length path) start) (length p))
       (= (nib-common-len p 0 path start) (length p))))

(defun hex-prefix (path is-leaf &optional (start 0) (end (length path)))
  "Compact (hex-prefix) encoding of the nibble range PATH[START..END)
   (Trie.hexPrefix): the flag byte (with the first nibble when the range is odd), then
   the remaining nibbles packed in pairs. Filled in place: one allocation per node path."
  (declare (type nibbles path) (type fixnum start end))
  (let* ((n (- end start))
         (out (make-array (1+ (floor n 2)) :element-type '(unsigned-byte 8)))
         (flag (if is-leaf #x20 #x00)))
    (declare (type fixnum n))
    (if (oddp n)
        (progn (setf (aref out 0) (logior flag #x10 (aref path start))) (incf start))
        (setf (aref out 0) flag))
    (loop for i of-type fixnum from 1 below (length out)
          for p of-type fixnum from start by 2
          do (setf (aref out i) (logior (ash (aref path p) 4) (aref path (1+ p)))))
    out))

;;; --------------------------------------------------------------------
;;; patricialise — mirrors Trie.lean. Items are (nibble-vector . value),
;;; with a DEPTH of already-consumed nibbles threaded through the recursion.
;;; Returns an RLP Item (not a Node), exactly like the Lean reference.
;;; --------------------------------------------------------------------

(defun common-prefix-len (items depth)
  "Longest common prefix length of every item key beyond DEPTH.
   Replaces the old list `reduce` over fresh prefix lists: no allocation."
  (let* ((k0 (car (first items)))
         (lim (- (length k0) depth)))
    (declare (type nibbles k0))
    (dotimes (i lim lim)
      (let ((nib (aref k0 (+ depth i))))
        (dolist (kv (rest items))
          (let ((k (car kv)))
            (declare (type nibbles k))
            (when (or (<= (length k) (+ depth i))
                      (/= (aref k (+ depth i)) nib))
              (return-from common-prefix-len i))))))))

(defun partition-16 (items depth)
  "Bucket ITEMS by the nibble at DEPTH. Returns (values buckets terminal);
   TERMINAL is the value of the key that ENDS at DEPTH, or NIL.
   The item conses are reused as-is — the dropped nibble is expressed by the
   caller recursing at DEPTH+1, so no key is copied or rebuilt per level."
  (let ((buckets (make-array 16 :initial-element '()))
        (terminal nil))
    (dolist (kv items)
      (let ((k (car kv)))
        (declare (type nibbles k))
        (if (= (length k) depth)
            (setf terminal (cdr kv))
            (push kv (aref buckets (aref k depth))))))
    ;; Preserve input order within a bucket (push reverses).
    (dotimes (i 16) (setf (aref buckets i) (nreverse (aref buckets i))))
    (values buckets terminal)))

(defun node-ref (rlp-item)
  "Wrap a node's RLP Item as it appears in its parent: inline if its
   encoding is < 32 bytes, else .bytes keccak256(encoding). Mirrors
   Trie.nodeRef."
  (let ((enc (rlp-encode rlp-item)))
    (if (< (length enc) 32)
        rlp-item
        (rlp-bytes (%keccak enc)))))

(defun patricialise (items &optional (depth 0))
  "Build the root RLP Item for (nibble-key . value) ITEMS (Trie.patricialise),
   where every key has already had its first DEPTH nibbles consumed. Every
   item at one call shares that DEPTH, which is why threading an integer
   replaces the reference's per-level `map` over freshly stripped keys.
   Empty value encoded as the empty byte string."
  (cond
    ((null items) (rlp-bytes (make-array 0 :element-type '(unsigned-byte 8))))
    ((null (cdr items))
     (let* ((kv (car items)) (k (car kv)) (v (cdr kv)))
       (rlp-list (rlp-bytes (hex-prefix k t depth)) (rlp-bytes v))))
    (t
     (let ((clen (common-prefix-len items depth)))
       (if (plusp clen)
           (let ((sub (patricialise items (+ depth clen))))
             (rlp-list (rlp-bytes (hex-prefix (car (first items)) nil
                                              depth (+ depth clen)))
                       (node-ref sub)))
           (multiple-value-bind (buckets terminal) (partition-16 items depth)
             (let ((children
                     (loop for i below 16
                           collect (let ((bucket (aref buckets i)))
                                     (if (null bucket)
                                         (rlp-bytes (make-array 0 :element-type '(unsigned-byte 8)))
                                         (node-ref (patricialise bucket (1+ depth))))))))
               (rlp-list* (append children
                                  (list (rlp-bytes (or terminal
                                                       (make-array 0 :element-type '(unsigned-byte 8)))))))))))) ))

;;; --------------------------------------------------------------------
;;; Root — mirrors Trie.rootBytes.
;;; --------------------------------------------------------------------

(defparameter *empty-root-bytes*
  ;; keccak256(rlp("")) = keccak256(0x80).
  nil)

(defun empty-root-bytes ()
  (or *empty-root-bytes*
      (setf *empty-root-bytes* (%keccak (b #x80)))))

(defun trie-root (items)
  "Trie root (32-byte vector) for (key . value) byte-string ITEMS.
   Mirrors Trie.rootBytes: empty -> emptyRoot; else keccak(rlp(rootNode)),
   regardless of how short rlp(rootNode) is."
  (if (null items)
      (empty-root-bytes)
      ;; One nibble VECTOR per key (64 B + header) instead of one 64-cell list
      ;; (1 536 B), and patricialise then copies no key at all.
      (let* ((nibble-items (mapcar (lambda (kv)
                                     (cons (bytes->nibbles (car kv)) (cdr kv)))
                                   items))
             (root-node (patricialise nibble-items 0)))
        (%keccak (rlp-encode root-node)))))

;;; --------------------------------------------------------------------
;;; Ethereum state semantics.
;;; --------------------------------------------------------------------

(defparameter *empty-code-hash*
  ;; keccak256("") — populated lazily.
  nil)

(defun empty-code-hash ()
  (or *empty-code-hash*
      (setf *empty-code-hash*
            (%keccak (make-array 0 :element-type '(unsigned-byte 8))))))

(defun rlp-uint (n)
  "RLP Item for a non-negative integer as a minimal big-endian string."
  (rlp-bytes (int->be-bytes n)))

(defun storage-root (storage-alist)
  "Per-account storage trie root (32-byte vector).
   key = keccak256(32-byte BE slot); value = RLP(minimal-BE bytes of value).
   Empty storage -> emptyRoot. Slots with value 0 are omitted (they are
   not present in the trie)."
  (let ((items '()))
    (dolist (kv storage-alist)
      (let ((slot (car kv)) (val (cdr kv)))
        (unless (zerop val)
          (let ((key (%keccak (int->be-bytes-fixed slot 32)))
                ;; value is RLP(minimal-BE(val)), then that *encoded* string
                ;; is the trie value.
                (rlpval (rlp-encode (rlp-uint val))))
            (push (cons key rlpval) items)))))
    (trie-root (nreverse items))))

(defun account-leaf-value (nonce balance storage-root-bytes code-hash-bytes)
  "RLP([nonce, balance, storageRoot, codeHash]) as a u8 vector. NONCE and BALANCE are
   integers, or already their minimal big-endian bytes (a snapshot record's, unconverted)."
  (flet ((uint (x) (if (integerp x) (rlp-uint x) (rlp-bytes x))))
    (rlp-encode
     (rlp-list (uint nonce)
               (uint balance)
               (rlp-bytes storage-root-bytes)
               (rlp-bytes code-hash-bytes)))))

(defun account-state-root (accounts)
  "World state root (32-byte vector).
   ACCOUNTS: list of (addr nonce balance storage-alist code-bytes).
   storage-alist = ((slot . value) ...) ; code-bytes = u8 sequence or NIL.
   key = keccak256(20-byte BE addr) -> RLP([nonce,balance,storageRoot,codeHash])."
  (let ((items '()))
    (dolist (acct accounts)
      (destructuring-bind (addr nonce balance storage-alist code-bytes) acct
        (let* ((key (%keccak (int->be-bytes-fixed addr 20)))
               (sroot (storage-root storage-alist))
               (chash (if (and code-bytes (plusp (length code-bytes)))
                          (%keccak code-bytes)
                          (empty-code-hash)))
               (val (account-leaf-value nonce balance sroot chash)))
          (push (cons key val) items))))
    (trie-root (nreverse items))))

;;; ====================================================================
;;; INCREMENTAL mutable Merkle-Patricia trie (#20).
;;;
;;; A mutable, in-place trie keyed by byte-vector keys (32-byte account
;;; keys = keccak(addr)). Each mutable node carries a CACHED RLP-Item
;;; (its node-ref as seen by its parent) plus a DIRTY flag, so that
;;; mtrie-root only recomputes hashes along paths that changed since the
;;; last root.
;;;
;;; The semantics MUST match the from-scratch trie-root / patricialise
;;; EXACTLY: the cached node-ref of a clean subtree equals what
;;; (node-ref (patricialise ...)) would produce for the same key set, and
;;; mtrie-root = keccak(rlp(top-node)).
;;;
;;; Mutable node structs:
;;;   mleaf   : path (nibble vector)           value (u8 vector)
;;;   mext    : path (nibble vector, non-empty) child (mnode)
;;;   mbranch : children #(16 mnode-or-nil)   value (u8 vector or nil)
;;; An empty trie is represented by a root slot of NIL.
;;;
;;; INVARIANT (matches patricialise structure produced from a key set):
;;;   * mext path is always non-empty and its child is an mbranch
;;;     (an ext only ever exists to carry a shared prefix down to a
;;;     branch; a single key is an mleaf, two+ keys that diverge form a
;;;     branch, and a shared prefix above a branch is an ext).
;;;   * mbranch always has >= 2 "occupants" (children + terminal value),
;;;     i.e. it never degenerates; delete restores this by collapsing.
;;; ====================================================================

(defstruct (mnode (:constructor nil))
  ;; cached node-ref RLP Item for this node as embedded in its parent
  ;; (inline item if rlp<32B, else (:bytes . keccak)); NIL when dirty.
  (ref nil)
  ;; cached full RLP encoding (u8 vector) of this node; NIL when dirty.
  (enc nil))

(defstruct (mleaf (:include mnode)
                  (:constructor make-mleaf (path value)))
  path value)

(defstruct (mext (:include mnode)
                 (:constructor make-mext (path child)))
  path child)

(defstruct (mbranch (:include mnode)
                    (:constructor make-mbranch (&optional children value)))
  (children (make-array 16 :initial-element nil))
  (value nil)
  ;; (3) Branch-encoding splice-patch cache. SPLICE-ENC holds the LAST full
  ;; RLP encoding of this branch (a u8 vector); unlike MNODE-ENC it is NOT
  ;; cleared by mnode-dirty!, so after a child changes we can splice the new
  ;; child-ref bytes into a copy of it. SLOT-OFFS/SLOT-LENS are 17-element
  ;; simple-vectors: slot i's RLP-encoding sits at SPLICE-ENC[offs[i] ..
  ;; offs[i]+lens[i]) (children 0..15, terminal value at 16). When a child's
  ;; new ref encodes to the SAME length, we splice (O(32)) instead of a full
  ;; 16-child list rebuild + re-encode (~530B). NIL until first encode.
  (splice-enc nil)
  (slot-offs nil)
  (slot-lens nil)
  ;; SLOT-REFS[i] = the child's cached MNODE-REF object (slot i, 0..15) at the
  ;; time SPLICE-ENC was produced, and SLOT-REFS[16] = the terminal value
  ;; object. A slot's encoding is unchanged iff its current ref/value is EQ to
  ;; the cached one, so splice-mbranch can skip re-encoding untouched slots
  ;; (only the few changed children of a dirty branch are re-encoded).
  (slot-refs nil))

;; The trie itself: a single mutable root slot (NIL = empty).
;; Slot accessor is MTRIE-TOP to avoid clashing with the public MTRIE-ROOT.
(defstruct (mtrie (:constructor make-mtrie ()))
  (top nil))

(declaim (inline empty-bytes))
(defun empty-bytes () (make-array 0 :element-type '(unsigned-byte 8)))

(defun mnode-dirty! (node)
  "Invalidate NODE's cached ref/enc (it or a descendant changed)."
  (setf (mnode-ref node) nil
        (mnode-enc node) nil))

;;; --------------------------------------------------------------------
;;; Hashing: turn a mutable node into its RLP Item, reusing cached refs
;;; of clean descendants. This is where dirty-path-only recompute lives.
;;; --------------------------------------------------------------------

(defun mnode-encode (node)
  "Full RLP encoding (u8 vector) of NODE, caching it. Recurses only into
   children whose cache is stale. Branch nodes use the splice-patch path."
  (or (mnode-enc node)
      (setf (mnode-enc node)
            (if (mbranch-p node)
                (mbranch-encode node)
                (rlp-encode (mnode->item node))))))

(defun child-ref (node)
  "The node-ref RLP Item for child NODE (inline if rlp<32B else hash),
   reusing the cached ref of a clean NODE."
  (or (mnode-ref node)
      (setf (mnode-ref node)
            (let ((enc (mnode-encode node)))
              (if (< (length enc) 32)
                  ;; inline: the child's own RLP Item
                  (mnode->item node)
                  (rlp-bytes (%keccak enc)))))))

(defun mnode->item (node)
  "RLP Item (NOT node-ref) for NODE — i.e. patricialise's output shape."
  (etypecase node
    (mleaf
     (rlp-list (rlp-bytes (hex-prefix (mleaf-path node) t))
               (rlp-bytes (mleaf-value node))))
    (mext
     (rlp-list (rlp-bytes (hex-prefix (mext-path node) nil))
               (child-ref (mext-child node))))
    (mbranch
     (let ((children
             (loop for i below 16
                   for c = (aref (mbranch-children node) i)
                   collect (if c (child-ref c) (rlp-bytes (empty-bytes))))))
       (rlp-list* (append children
                          (list (rlp-bytes (or (mbranch-value node)
                                               (empty-bytes))))))))))

;;; --------------------------------------------------------------------
;;; (3) Branch encoding with cached slot offsets + splice-patch.
;;;
;;; A branch's RLP is  rlp-list(slot0 .. slot15, value) :
;;;   <list-header> <enc(slot0)> ... <enc(slot15)> <enc(value)>
;;; where enc(slot_i) is the RLP-encoding of that child's node-ref (or the
;;; empty string #x80 for an absent child), and enc(value) is RLP(value).
;;; encode-mbranch-full records every slot's [offset,length) within the
;;; produced encoding so a later single-child change of equal length can be
;;; spliced in place (splice-mbranch) rather than re-encoding the whole list.
;;; The list header only depends on the TOTAL payload length, so as long as
;;; every changed slot keeps its length the header is byte-identical and the
;;; splice result equals a full re-encode exactly.
;;; --------------------------------------------------------------------

;; Distinct sentinel for an ABSENT child slot, so an empty slot's cache key is
;; never EQ to a present-but-not-yet-encoded child's (NIL) ref — that collision
;; would wrongly skip a freshly-inserted child in the lazy (non-wavefront)
;; encode order, where a dirty child's MNODE-REF is still NIL at parent time.
(defparameter *branch-empty-slot* '#:empty-slot)

(declaim (inline branch-slot-ref))
(defun branch-slot-ref (node i)
  "The cache key (object identity) for branch slot I: the child's CURRENT
   MNODE-REF for 0..15 (computing it if the child is dirty), the
   *BRANCH-EMPTY-SLOT* sentinel for an absent child, or the terminal value for
   I=16. Two encodings of slot I are byte-identical iff their slot-refs EQ."
  (if (< i 16)
      (let ((c (aref (mbranch-children node) i)))
        (if c (child-ref c) *branch-empty-slot*))
      (mbranch-value node)))

(declaim (inline branch-slot-enc))
(defun branch-slot-enc (node i)
  "RLP-encoding (u8 vector) of branch slot I: child ref for 0..15 (empty
   string for an absent child), terminal value at I=16."
  (if (< i 16)
      (let ((c (aref (mbranch-children node) i)))
        (if c
            (rlp-encode (child-ref c))
            (b #x80)))                          ; rlp("") for empty slot
      (rlp-encode (rlp-bytes (or (mbranch-value node) (empty-bytes))))))

(defun encode-mbranch-full (node)
  "Full re-encode of branch NODE, recording per-slot offsets/lengths/refs into
   its splice cache. Returns the encoding (u8 vector) and populates SPLICE-ENC
   / SLOT-OFFS / SLOT-LENS / SLOT-REFS. Byte-identical to a full re-encode."
  (let ((slots (make-array 17))
        (payload-len 0))
    (dotimes (i 17)
      (let ((e (branch-slot-enc node i)))
        (setf (aref slots i) e)
        (incf payload-len (length e))))
    (let* ((hlen (rlp-write-length payload-len #xc0 nil 0))
           (enc (make-array (+ hlen payload-len)
                            :element-type '(unsigned-byte 8)))
           (offs (make-array 17))
           (lens (make-array 17))
           (refs (make-array 17))
           (pos hlen))
      (rlp-write-length payload-len #xc0 enc 0)
      (dotimes (i 17)
        (let* ((e (aref slots i)) (len (length e)))
          (setf (aref offs i) pos
                (aref lens i) len
                (aref refs i) (branch-slot-ref node i))
          (replace enc e :start1 pos)
          (incf pos len)))
      (setf (mbranch-splice-enc node) enc
            (mbranch-slot-offs node) offs
            (mbranch-slot-lens node) lens
            (mbranch-slot-refs node) refs)
      enc)))

(defun splice-mbranch (node)
  "Recompute branch NODE's encoding by SPLICING only the slots whose child ref
   (or value) changed, when each keeps its prior length. Returns the encoding
   (u8 vector), or NIL if any changed slot changed LENGTH (caller must full
   re-encode). Requires a valid prior splice cache."
  (let ((old-enc (mbranch-splice-enc node))
        (offs    (mbranch-slot-offs node))
        (lens    (mbranch-slot-lens node))
        (refs    (mbranch-slot-refs node)))
    (when (null old-enc) (return-from splice-mbranch nil))
    ;; A slot changed iff its ref/value is no longer EQ to the cached one;
    ;; only those are re-encoded. Bail to a full re-encode if any changed
    ;; slot's length differs (that shifts the header and/or later offsets).
    (let ((new-slots nil))            ; list of (index . new-enc) to patch
      (dotimes (i 17)
        (unless (eq (branch-slot-ref node i) (aref refs i))
          (let ((new-e (branch-slot-enc node i))
                (oldlen (aref lens i)))
            (when (/= (length new-e) oldlen)
              ;; Length-changing slot: fall back to a full re-encode.
              (return-from splice-mbranch nil))
            ;; Same length, ref changed: schedule a splice and refresh the
            ;; cached ref so the next change is detected against current.
            (setf (aref refs i) (branch-slot-ref node i))
            (push (cons (aref offs i) new-e) new-slots))))
      ;; Every changed slot is length-preserving: splice into a fresh copy.
      ;; (The header is unchanged because the total payload length is the
      ;; same, so old-enc's prefix stays valid.)
      (let ((enc (copy-seq old-enc)))
        (dolist (pair new-slots)
          (replace enc (cdr pair) :start1 (car pair)))
        ;; The slot bytes moved but offsets/lengths are unchanged; refresh
        ;; the splice base so the NEXT change splices against current bytes.
        (setf (mbranch-splice-enc node) enc)
        enc))))

(defun mbranch-encode (node)
  "Encoding (u8 vector) of branch NODE: splice the changed equal-length slots
   when possible, else full re-encode. Bit-identical to a full re-encode."
  (or (splice-mbranch node)
      (encode-mbranch-full node)))

;;; --------------------------------------------------------------------
;;; Nibble helpers
;;; --------------------------------------------------------------------

;; nibbles= / nib-common are gone: `nib=` and `nib-common-len` above take a
;; start offset and allocate nothing, so no suffix is ever materialised just
;; to compare it.

(defun branch-occupants (br)
  "Return a list of occupied child indices (0-15), plus :value if the
   terminal value is set, for collapse decisions."
  (nconc (loop for i below 16
               when (aref (mbranch-children br) i) collect i)
         (when (mbranch-value br) (list :value))))

;;; --------------------------------------------------------------------
;;; INSERT.  Each helper returns the (possibly new) node to occupy the
;;; slot, and is responsible for dirtying nodes whose subtree changed.
;;; PATH is the remaining nibble suffix of the key at this node.
;;; --------------------------------------------------------------------

(defun mt-insert (node path pstart value)
  "Insert PATH[PSTART..]->VALUE under NODE (NIL = empty slot). Returns the
   node now occupying this slot. PSTART replaces the reference's list-tail
   walk, so descending allocates nothing."
  (if (null node)
      (make-mleaf (nib-sub path pstart) value)
      (etypecase node
        (mleaf   (insert-into-leaf   node path pstart value))
        (mext    (insert-into-ext    node path pstart value))
        (mbranch (insert-into-branch node path pstart value)))))

(defun insert-into-leaf (leaf path pstart value)
  (let ((lpath (mleaf-path leaf)))
    (cond
      ((nib= lpath 0 path pstart)
       ;; Overwrite in place.
       (setf (mleaf-value leaf) value)
       (mnode-dirty! leaf)
       leaf)
      (t
       ;; Split: build a branch over the divergence, with optional ext
       ;; for the shared prefix.
       (let ((clen (nib-common-len lpath 0 path pstart))
             (br (make-mbranch)))
         ;; Place the existing leaf, then the new key.
         (place-leaf-or-value br lpath clen (mleaf-value leaf))
         (place-leaf-or-value br path (+ pstart clen) value)
         (if (plusp clen)
             (make-mext (nib-sub lpath 0 clen) br)
             br))))))

(defun place-leaf-or-value (br path pstart value)
  "Insert PATH[PSTART..]->VALUE directly under branch BR (PSTART is already
   past the branch's own nibble). Empty suffix -> terminal value; else a
   child slot keyed by the next nibble."
  (if (= pstart (length path))
      (setf (mbranch-value br) value)
      (let ((idx (aref path pstart)))
        (setf (aref (mbranch-children br) idx)
              (make-mleaf (nib-sub path (1+ pstart)) value)))))

(defun insert-into-ext (ext path pstart value)
  (let* ((epath (mext-path ext))
         (clen (nib-common-len epath 0 path pstart)))
    (cond
      ((= clen (length epath))
       ;; Full ext prefix consumed; descend into its (branch) child.
       (setf (mext-child ext)
             (mt-insert (mext-child ext) path (+ pstart clen) value))
       (mnode-dirty! ext)
       ext)
      (t
       ;; Ext prefix diverges. Split it: shared prefix (maybe empty) ->
       ;; new branch; the branch routes the ext's remaining tail and the
       ;; new key.
       (let ((br (make-mbranch)))
         ;; The ext's old child goes under the first nibble of its tail
         ;; (non-empty here), behind a shortened ext or directly.
         (let ((idx (aref epath clen))
               (tail-start (1+ clen)))
           (setf (aref (mbranch-children br) idx)
                 (if (= tail-start (length epath))
                     (mext-child ext)              ; ext was 1 nibble: child sits directly
                     (make-mext (nib-sub epath tail-start) (mext-child ext)))))
         ;; The new key.
         (place-leaf-or-value br path (+ pstart clen) value)
         (if (plusp clen)
             (make-mext (nib-sub epath 0 clen) br)
             br))))))

(defun insert-into-branch (br path pstart value)
  (if (= pstart (length path))
      (progn (setf (mbranch-value br) value)
             (mnode-dirty! br)
             br)
      (let ((idx (aref path pstart)))
        (setf (aref (mbranch-children br) idx)
              (mt-insert (aref (mbranch-children br) idx) path (1+ pstart) value))
        (mnode-dirty! br)
        br)))

;;; --------------------------------------------------------------------
;;; DELETE.  Returns the (possibly new, possibly NIL) node for this slot.
;;; Collapse rules restore the patricialise invariant on the way up:
;;;   * a branch with a single remaining occupant collapses:
;;;       - one child, no value  -> prepend the branch nibble to that
;;;         child (leaf gets longer path; ext gets longer path; branch
;;;         child becomes the target of a 1-nibble ext).
;;;       - no children, only value -> a 0-length-path leaf.
;;;   * an ext whose child is a leaf  -> merge into one longer leaf.
;;;   * an ext whose child is an ext  -> merge the two ext paths.
;;;   * an ext whose child is a branch -> stays an ext.
;;; --------------------------------------------------------------------

(defun mt-delete (node path pstart)
  "Delete PATH[PSTART..] from NODE. Returns the node now occupying this slot
   (NIL if the subtree became empty). Second value T iff a key was removed."
  (if (null node)
      (values nil nil)
      (etypecase node
        (mleaf   (delete-from-leaf   node path pstart))
        (mext    (delete-from-ext    node path pstart))
        (mbranch (delete-from-branch node path pstart)))))

(defun delete-from-leaf (leaf path pstart)
  (if (nib= (mleaf-path leaf) 0 path pstart)
      (values nil t)                ; removed; slot empties
      (values leaf nil)))           ; absent; unchanged

(defun delete-from-ext (ext path pstart)
  (let* ((epath (mext-path ext))
         (elen (length epath)))
    (if (nib-prefix-p epath path pstart)
        ;; Prefix matches: descend. (The reference took `(subseq path 0 elen)`
        ;; here, allocating a list just to compare it.)
        (multiple-value-bind (new-child removed)
            (mt-delete (mext-child ext) path (+ pstart elen))
          (if (not removed)
              (values ext nil)
              ;; Child changed. By the invariant an ext's child was a
              ;; branch; after delete it is still a branch (delete-from-
              ;; branch always returns a branch or a collapsed node).
              ;; new-child cannot be NIL: a branch never empties via a
              ;; single delete to fewer than... it could collapse to a
              ;; leaf/ext, which we must merge into this ext.
              (values (merge-ext-child ext new-child) t)))
        (values ext nil))))         ; key not under this ext

(defun merge-ext-child (ext child)
  "Re-form EXT now that its CHILD may no longer be a branch. Maintains the
   invariant: ext path non-empty, ext child is a branch."
  (etypecase child
    (mbranch
     (setf (mext-child ext) child)
     (mnode-dirty! ext)
     ext)
    (mleaf
     ;; ext+leaf -> single leaf with concatenated path.
     (make-mleaf (nib-concat (mext-path ext) (mleaf-path child))
                 (mleaf-value child)))
    (mext
     ;; ext+ext -> single ext with concatenated path, same (branch) child.
     (make-mext (nib-concat (mext-path ext) (mext-path child))
                (mext-child child)))))

(defun delete-from-branch (br path pstart)
  (multiple-value-bind (changed)
      (if (= pstart (length path))
          (if (mbranch-value br)
              (progn (setf (mbranch-value br) nil) t)
              nil)
          (let* ((idx (aref path pstart))
                 (c (aref (mbranch-children br) idx)))
            (if (null c)
                nil
                (multiple-value-bind (new-c removed) (mt-delete c path (1+ pstart))
                  (when removed
                    (setf (aref (mbranch-children br) idx) new-c))
                  removed))))
    (if (not changed)
        (values br nil)
        (progn
          (mnode-dirty! br)
          (values (maybe-collapse-branch br) t)))))

(defun maybe-collapse-branch (br)
  "If BR has exactly one occupant, collapse it to a leaf/ext per Patricia.
   Otherwise return BR unchanged."
  (let ((occ (branch-occupants br)))
    (cond
      ((cdr occ) br)                       ; >= 2 occupants: stays a branch
      ((null occ) br)                      ; should not happen on a live trie
      ((eq (car occ) :value)
       ;; Only the terminal value remains -> a leaf with empty path.
       (make-mleaf (nib-empty) (mbranch-value br)))
      (t
       ;; Exactly one child remains at index IDX, no terminal value.
       (let* ((idx (car occ))
              (child (aref (mbranch-children br) idx)))
         (collapse-single-child idx child))))))

(defun collapse-single-child (idx child)
  "Branch had a single child at IDX. Prepend the branch's nibble IDX to
   CHILD's path, collapsing into a leaf/ext/1-nibble-ext as appropriate."
  (etypecase child
    (mleaf
     (make-mleaf (nib-cons idx (mleaf-path child)) (mleaf-value child)))
    (mext
     ;; ext child: prepend nibble -> longer ext (child stays a branch).
     (make-mext (nib-cons idx (mext-path child)) (mext-child child)))
    (mbranch
     ;; branch child: a 1-nibble ext now leads to it.
     (make-mext (nib-single idx) child))))

;;; --------------------------------------------------------------------
;;; Public API
;;; --------------------------------------------------------------------

(defun mtrie-insert (trie key-bytes value-bytes)
  "Insert/overwrite KEY-BYTES -> VALUE-BYTES (both u8 sequences). VALUE is
   stored verbatim as the leaf value (the RLP-encoded account, etc.)."
  (let ((path (bytes->nibbles key-bytes))
        (value (coerce value-bytes '(vector (unsigned-byte 8)))))
    (setf (mtrie-top trie) (mt-insert (mtrie-top trie) path 0 value)))
  trie)

(defun mtrie-delete (trie key-bytes)
  "Remove KEY-BYTES if present. No-op if absent. Returns T iff a key was
   actually removed (so callers can maintain a live-key count)."
  (let ((path (bytes->nibbles key-bytes)))
    (multiple-value-bind (new removed) (mt-delete (mtrie-top trie) path 0)
      (setf (mtrie-top trie) new)
      removed)))

(defun mt-member (node path pstart)
  "T iff PATH[PSTART..] is present under NODE (a stored key)."
  (and node
       (etypecase node
         (mleaf   (nib= (mleaf-path node) 0 path pstart))
         (mext    (let* ((ep (mext-path node)) (el (length ep)))
                    (and (nib-prefix-p ep path pstart)
                         (mt-member (mext-child node) path (+ pstart el)))))
         (mbranch (if (= pstart (length path))
                      (and (mbranch-value node) t)
                      (mt-member (aref (mbranch-children node) (aref path pstart))
                                 path (1+ pstart)))))))

(defun mtrie-member (trie key-bytes)
  "T iff KEY-BYTES is present in TRIE."
  (mt-member (mtrie-top trie) (bytes->nibbles key-bytes) 0))

;;; --------------------------------------------------------------------
;;; LEVEL-WAVEFRONT batched root recompute (#237).
;;;
;;; The only dependency between node refs is parent->child (a node's RLP
;;; embeds each child's ref). Nodes at the SAME depth are therefore
;;; independent and their keccaks batch into ONE FFI call. We recompute
;;; bottom-up:
;;;   1. DFS the trie collecting the DIRTY nodes (ref = NIL) grouped by
;;;      DEPTH. Clean nodes keep their cached ref and are NOT descended
;;;      into — this preserves incrementality (clean subtrees never
;;;      re-hash). A dirty node IS descended into so deeper dirty nodes
;;;      are found.
;;;   2. For depth = max down to 0: encode every dirty node at that depth
;;;      (children refs are ready — deeper levels done, clean children
;;;      cached). Split <32B (ref = inline item, no hash) from >=32B
;;;      (collect). Hash all the >=32B encodings of the level in ONE
;;;      parallel keccak-batch call; assign each node's ref (and enc).
;;;   3. Root = keccak(rlp(top)), regardless of size.
;;;
;;; Result is bit-identical to the per-node child-ref/mnode-encode path:
;;; only the SCHEDULING differs (a level batched vs one-at-a-time).
;;; --------------------------------------------------------------------

(defun collect-dirty-by-depth (root)
  "DFS from ROOT collecting dirty nodes (mnode-ref = NIL) into a vector
   indexed by depth (root = depth 0). Returns (values levels max-depth),
   where LEVELS is a (vector list) — LEVELS[d] = dirty nodes at depth d.
   Clean nodes are not recorded and not descended (their subtree's refs
   are all cached, so it needs no work)."
  (let ((levels (make-array 8 :initial-element nil :adjustable t))
        (max-depth -1))
    (labels ((ensure-depth (d)
               (when (>= d (length levels))
                 (adjust-array levels (max (* 2 (length levels)) (1+ d))
                               :initial-element nil)))
             (visit (node depth)
               (when (and node (null (mnode-ref node)))
                 (ensure-depth depth)
                 (push node (aref levels depth))
                 (when (> depth max-depth) (setf max-depth depth))
                 ;; Descend into children to find deeper dirty nodes.
                 (etypecase node
                   (mleaf nil)               ; no children
                   (mext (visit (mext-child node) (1+ depth)))
                   (mbranch
                    (loop for c across (mbranch-children node)
                          when c do (visit c (1+ depth))))))))
      (visit root 0))
    (values levels max-depth)))

(defun recompute-refs-wavefront! (root)
  "Assign mnode-ref (and mnode-enc) to every dirty node reachable from
   ROOT, bottom-up, batching each level's keccaks into one FFI call.
   After this returns, ROOT and all its descendants have valid cached
   refs."
  (multiple-value-bind (levels max-depth) (collect-dirty-by-depth root)
    (loop for depth from max-depth downto 0
          for nodes = (aref levels depth)
          when nodes do
            ;; All children refs are ready (deeper levels assigned, clean
            ;; children cached), so mnode->item / child-ref read cached
            ;; refs only — no recursive hashing fires here.
            (let ((to-hash '())      ; nodes whose enc is >=32B
                  (to-hash-encs '()))
              (dolist (node nodes)
                ;; Branch nodes splice the changed equal-length slots into
                ;; their cached encoding (O(32)/changed) rather than rebuild
                ;; the whole 16-child list; other nodes re-encode in full.
                (let ((enc (if (mbranch-p node)
                               (mbranch-encode node)
                               (rlp-encode (mnode->item node)))))
                  (setf (mnode-enc node) enc)
                  (if (< (length enc) 32)
                      ;; Inline: ref is the node's own RLP item, no hash.
                      ;; (Branches are always >=32B here; a freshly built
                      ;; branch has splice-enc set by encode-mbranch-full.)
                      (setf (mnode-ref node) (mnode->item node))
                      (progn (push node to-hash)
                             (push enc to-hash-encs)))))
              (when to-hash
                (let* ((encs (coerce (nreverse to-hash-encs) 'simple-vector))
                       (hashes (keccak-batch encs))
                       (nodes-v (coerce (nreverse to-hash) 'simple-vector)))
                  (dotimes (i (length nodes-v))
                    (setf (mnode-ref (aref nodes-v i))
                          (rlp-bytes (aref hashes i))))))))))

(defparameter *mtrie-root-batched* t
  "When true, mtrie-root uses the level-wavefront batched keccak path;
   when nil, the original per-node single-FFI recompute (mnode-encode).
   Both produce a bit-identical root; the flag exists for benchmarking.")

(defun mtrie-root (trie)
  "32-byte root vector, recomputing hashes only along dirty paths.
   Equals keccak(rlp(top-node)), matching the from-scratch trie-root.
   Uses level-wavefront batched keccak when *MTRIE-ROOT-BATCHED*."
  (let ((root (mtrie-top trie)))
    (cond
      ((null root) (empty-root-bytes))
      (*mtrie-root-batched*
       ;; Bring every dirty node's ref up to date level-by-level, then
       ;; the top node's full encoding is cached and we keccak it.
       (recompute-refs-wavefront! root)
       (%keccak (mnode-encode root)))
      (t (%keccak (mnode-encode root))))))
