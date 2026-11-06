;;;; state/world.lisp — the world: account tables, packed storage, the storage view, lazy faulting.

(in-package #:eita.state)

;;; --- World state: one interned id per account ---
;;;
;;; An address (an integer below 2^160) is interned once per ACCOUNT TABLE into an ID, a
;;; fixnum in interning order — the compact key Block-STM's versioned reads and writes
;;; need. The account's fields live in the table's vectors at that index (balance, nonce,
;;; code, storage — a SLOTS table, below — and flag bits): no object per account for the GC
;;; to scan or copy. The address index is open addressing over the address's three 64-bit
;;; words — no bignum hashing, nothing consed on a hit — with a one-entry cache, because an
;;; effect touches the same address object several times in a row (fault, read, journal,
;;; write). Ids are never reused: a deleted account keeps its id with its fields cleared. A
;;; table is the hot set of a layered world (snapshot-world.lisp): a freeze hands it whole
;;; to the frozen layer, and the world continues on a fresh one.

(declaim (inline u256-word))
(defun u256-word (n i)
  "64-bit word I (0 = least significant) of the non-negative integer N, or of the opaque
   word N points at (word-int)."
  (declare (type (or unsigned-byte sb-sys:system-area-pointer) n) (type (integer 0 3) i)
           (optimize (speed 3) (safety 0)))
  (cond ((typep n 'fixnum) (if (zerop i) n 0))
        ((sb-sys:system-area-pointer-p n) (sb-sys:sap-ref-64 n (* 8 i)))
        (t (if (< i (sb-bignum:%bignum-length n)) (sb-bignum:%bignum-ref n i) 0))))

(defconstant +acct-marked+ 1
  "In the existence set: present though empty (0 balance, 0 nonce, no code) — a CALL to
   an absent account (precompiles included) or an empty CREATE. Journaled (type 11).")
(defconstant +acct-faulted+ 2 "Its fields were loaded from the cold tier (fault-account!).")
(defconstant +acct-wiped+ 4 "Its storage was removed wholesale since the table began.")
(defvar +no-code+ (make-array 0) "An account's code when it has none (no entry).")

(defstruct (acct-table (:constructor %make-acct-table (keys vals mask)))
  (keys nil :type (simple-array (unsigned-byte 64) (*)))   ; three address words per bucket
  (vals nil :type (simple-array fixnum (*)))               ; bucket -> id, or -1 (empty)
  (mask 0 :type fixnum)
  (count 0 :type fixnum)                                   ; ids 0 .. count-1
  ;; per id
  (addrs (make-array 256) :type simple-vector)
  (balance (make-array 1024 :element-type '(unsigned-byte 64) :initial-element 0)  ; 4 limbs per id:
   :type (simple-array (unsigned-byte 64) (*)))                                     ; unboxed, no GC scan
  (nonce (make-array 256 :element-type '(unsigned-byte 64) :initial-element 0)
   :type (simple-array (unsigned-byte 64) (*)))
  (code (make-array 256 :initial-element +no-code+) :type simple-vector) ; +no-code+: no entry
  (storage (make-array 256 :initial-element nil) :type simple-vector)    ; SLOTS, or NIL
  (bits (make-array 256 :element-type 'fixnum :initial-element 0) :type (simple-array fixnum (*)))
  (last-addr nil) (last-id -1 :type fixnum)                ; the cache (the replay thread's)
  ;; a direct-mapped cache in front of the index (replay thread): the index is as large as
  ;; the hot set (millions of accounts), so a probe is a DRAM miss; a block touches few
  (cache-addrs (make-array 64 :initial-element nil) :type simple-vector)
  (cache-ids (make-array 64 :element-type 'fixnum :initial-element -1) :type (simple-array fixnum (*)))
  (faulted 0 :type fixnum))                                ; ids with +acct-faulted+

(defun make-acct-table (&optional (cap 1024))
  (%make-acct-table (make-array (* 3 cap) :element-type '(unsigned-byte 64))
                    (make-array cap :element-type 'fixnum :initial-element -1) (1- cap)))

(declaim (inline acct-bucket))
(defun acct-bucket (w0 w1 mask)
  (declare (type (unsigned-byte 64) w0 w1) (type fixnum mask) (optimize (speed 3) (safety 0)))
  (logand (ash (logand (* (logxor w0 w1) #x9E3779B97F4A7C15) #xFFFFFFFFFFFFFFFF) -21) mask))

(defun acct-table-place (tb id)
  "Put ID in the bucket of its address (not yet in the index)."
  (declare (type acct-table tb) (type fixnum id) (optimize (speed 3) (safety 0)))
  (let* ((addr (svref (acct-table-addrs tb) id)) (w0 (u256-word addr 0)) (w1 (u256-word addr 1))
         (keys (acct-table-keys tb)) (vals (acct-table-vals tb)) (mask (acct-table-mask tb))
         (i (acct-bucket w0 w1 mask)))
    (declare (type fixnum i mask))
    (loop until (= (aref vals i) -1) do (setf i (logand (1+ i) mask)))
    (setf (aref keys (* 3 i)) w0 (aref keys (+ 1 (* 3 i))) w1 (aref keys (+ 2 (* 3 i))) (u256-word addr 2)
          (aref vals i) id)))

(defun acct-table-grow (tb)
  "Double the index (rehash) and, when full, the per-id vectors."
  (let ((n (acct-table-count tb)) (cap (* 2 (1+ (acct-table-mask tb)))))
    (when (>= (* 4 (1+ n)) (* 3 (1+ (acct-table-mask tb))))
      (setf (acct-table-keys tb) (make-array (* 3 cap) :element-type '(unsigned-byte 64))
            (acct-table-vals tb) (make-array cap :element-type 'fixnum :initial-element -1)
            (acct-table-mask tb) (1- cap))
      (dotimes (id n) (acct-table-place tb id)))
    (when (= n (length (acct-table-addrs tb)))
      (flet ((more (v fill) (replace (make-array (* 2 n) :initial-element fill) v)))
        (setf (acct-table-addrs tb) (more (acct-table-addrs tb) 0)
              (acct-table-balance tb) (replace (make-array (* 8 n) :element-type '(unsigned-byte 64) :initial-element 0)
                                               (acct-table-balance tb))
              (acct-table-nonce tb) (replace (make-array (* 2 n) :element-type '(unsigned-byte 64) :initial-element 0)
                                             (acct-table-nonce tb))
              (acct-table-code tb) (more (acct-table-code tb) +no-code+)
              (acct-table-storage tb) (more (acct-table-storage tb) nil)
              (acct-table-bits tb) (replace (make-array (* 2 n) :element-type 'fixnum :initial-element 0)
                                            (acct-table-bits tb)))))))

(defun acct-table-find-words (tb w0 w1 w2)
  "The id of the address whose 64-bit words are W0 W1 W2 (least significant first), or -1.
   Neither caches nor interns: safe on a frozen table read by several threads."
  (declare (type acct-table tb) (type (unsigned-byte 64) w0 w1 w2) (optimize (speed 3) (safety 0)))
  (let* ((keys (acct-table-keys tb)) (vals (acct-table-vals tb)) (mask (acct-table-mask tb))
         (i (acct-bucket w0 w1 mask)))
    (declare (type fixnum i mask))
    (loop
      (let ((v (aref vals i)) (o (* 3 i)))
        (declare (type fixnum o v))
        (when (or (= v -1)
                  (and (= (aref keys o) w0) (= (aref keys (+ o 1)) w1) (= (aref keys (+ o 2)) w2)))
          (return v)))
      (setf i (logand (1+ i) mask)))))

(defun acct-table-find (tb addr)
  "ADDR's id in TB, or -1 (see acct-table-find-words)."
  (acct-table-find-words tb (u256-word addr 0) (u256-word addr 1) (u256-word addr 2)))

(defun acct-table-add (tb addr)
  "A new id for ADDR (not in TB), its fields blank."
  (acct-table-grow tb)
  (let ((id (acct-table-count tb)))
    (setf (svref (acct-table-addrs tb) id) addr (acct-table-count tb) (1+ id))
    (acct-table-place tb id)
    id))

(defun acct-table-intern (tb addr)
  "ADDR's id in TB, added when there is none. The replay thread's path: it caches the last
   address."
  (declare (type acct-table tb) (optimize (speed 3) (safety 0)))
  (if (eq addr (acct-table-last-addr tb))
      (acct-table-last-id tb)
      (let* ((slot (logand (u256-word addr 0) 63))
             (id (if (eql addr (svref (acct-table-cache-addrs tb) slot))
                     (aref (acct-table-cache-ids tb) slot)
                     (let ((id (acct-table-find tb addr)))
                       (declare (type fixnum id))
                       (when (= id -1) (setf id (acct-table-add tb addr)))
                       (setf (svref (acct-table-cache-addrs tb) slot) (svref (acct-table-addrs tb) id)
                             (aref (acct-table-cache-ids tb) slot) id)
                       id))))
        (declare (type fixnum slot id))
        (setf (acct-table-last-addr tb) addr (acct-table-last-id tb) id)
        id)))

(defun acct-table-intern-words (tb w0 w1 w2)
  "The canonical address object of the address with words W0 W1 W2, interned in TB: the
   native seam reads an address without consing one when it is in the table."
  (declare (type acct-table tb) (type (unsigned-byte 64) w0 w1 w2) (optimize (speed 3) (safety 0)))
  (let* ((slot (logand w0 63)) (c (svref (acct-table-cache-addrs tb) slot)))
    (declare (type fixnum slot))
    (if (and c (= (u256-word c 0) w0) (= (u256-word c 1) w1) (= (u256-word c 2) w2))
        (progn (setf (acct-table-last-addr tb) c (acct-table-last-id tb) (aref (acct-table-cache-ids tb) slot))
               c)
        (let ((id (acct-table-find-words tb w0 w1 w2)))
          (declare (type fixnum id))
          (when (= id -1) (setf id (acct-table-add tb (logior w0 (ash w1 64) (ash w2 128)))))
          (let ((addr (svref (acct-table-addrs tb) id)))
            (setf (acct-table-last-addr tb) addr (acct-table-last-id tb) id
                  (svref (acct-table-cache-addrs tb) slot) addr (aref (acct-table-cache-ids tb) slot) id)
            addr)))))

(defun map-accts (fn tb)
  "FN on every id of TB, in interning order."
  (dotimes (id (acct-table-count tb)) (funcall fn id)))

;;; Field access by (table, id).
(defmacro def-acct-field (name vec)
  `(progn (declaim (inline ,name (setf ,name)))
          (defun ,name (tb id) (svref (,vec tb) id))
          (defun (setf ,name) (v tb id) (setf (svref (,vec tb) id) v))))
(def-acct-field acct-addr acct-table-addrs)
(declaim (inline acct-balance (setf acct-balance) acct-nonce (setf acct-nonce)))
(defun acct-balance (tb id)
  (let ((v (acct-table-balance tb)) (o (* 4 id)))
    (words-u256 (aref v o) (aref v (+ o 1)) (aref v (+ o 2)) (aref v (+ o 3)))))
(defun (setf acct-balance) (x tb id)
  (unless (typep x '(unsigned-byte 256)) (error "balance of ~X out of range: ~A" (acct-addr tb id) x))
  (let ((v (acct-table-balance tb)) (o (* 4 id)))
    (setf (aref v o) (u256-word x 0) (aref v (+ o 1)) (u256-word x 1)
          (aref v (+ o 2)) (u256-word x 2) (aref v (+ o 3)) (u256-word x 3))
    x))
(defun acct-nonce (tb id) (aref (acct-table-nonce tb) id))
(defun (setf acct-nonce) (x tb id)
  (unless (typep x '(unsigned-byte 64)) (error "nonce of ~X out of range: ~A" (acct-addr tb id) x))
  (setf (aref (acct-table-nonce tb) id) x))
(def-acct-field acct-code acct-table-code)
(def-acct-field acct-storage acct-table-storage)
(declaim (inline acct-bits (setf acct-bits) acct-flag-p acct-code-entry))
(defun acct-bits (tb id) (aref (acct-table-bits tb) id))
(defun (setf acct-bits) (v tb id) (setf (aref (acct-table-bits tb) id) v))
(defun acct-flag-p (tb id bit) (logtest bit (acct-bits tb id)))
(defun acct-code-entry (tb id)
  "ID's code as stored, NIL when it has none (the persistence and observer view)."
  (let ((c (acct-code tb id))) (if (eq c +no-code+) nil c)))
(declaim (inline acct-empty-p))
(defun acct-empty-p (tb id)
  "EIP-161 emptiness of ID: balance 0 (its limbs: no bignum), nonce 0, no code."
  (let ((v (acct-table-balance tb)) (o (* 4 id)))
    (and (zerop (logior (aref v o) (aref v (+ o 1)) (aref v (+ o 2)) (aref v (+ o 3))))
         (zerop (acct-nonce tb id)) (zerop (length (acct-code tb id))))))
(defun acct-set-flag! (tb id bit) (setf (acct-bits tb id) (logior bit (acct-bits tb id))))
(defun acct-clear-flag! (tb id bit) (setf (acct-bits tb id) (logandc2 (acct-bits tb id) bit)))

(defstruct (world (:constructor make-world ()))
  (accts (make-acct-table) :type acct-table))

(defmacro with-acct ((tb id) w addr &body body)
  "Bind TB to W's account table and ID to ADDR's id in it (interned)."
  `(let* ((,tb (world-accts ,w)) (,id (acct-table-intern ,tb ,addr)))
     (declare (type fixnum ,id) (ignorable ,tb))
     ,@body))
;;; --- The storage view: the effect layer's one path to world state ----------
;;;
;;; docs/effect-layer-derivation.md §2. Every read and write the EFFECT LAYER (callbacks,
;;; apply-tx, fee settlement, sweeps, block effects, journal restores) makes of world
;;; state goes through these accessors; nothing outside persistence/loading touches the
;;; world tables directly. Two jobs, both here so neither can be missed at a call site:
;;;   * an observer's account pre-image (first write in a tx snapshots nonce/balance/code);
;;;   * the READ/WRITE STREAM: while `*view-log*` is true (inside a tx, and only when a
;;;     subscriber declared :wants-reads — `*capture-reads*`) every read is an event
;;;     (:read kind block tx addr slot value) and every write (:write kind block tx addr
;;;     slot pre post) — the logged read set of lean/Evm/Parallel/Reads.lean (`Faithful`:
;;;     the logged value is the value the view returned). KIND: :balance :nonce :code
;;;     :storage (SLOT = the slot) :present (the existence set) :account (whole-account
;;;     delete). SLOT is 0 for account fields.
;;; Off (no reads subscriber) an access costs one special-variable test.
(defvar *observe-capture* nil "True inside an observed tx window, outside state loading.")
(defvar *view-log* nil
  "True while the current tx's state accesses are streamed (set by observe-tx-begin! from
   *capture-reads*; never true while state is being loaded or persisted).")
(declaim (special *cur-block* *cur-tx* *mpt-tracking* *current-world*))
(defun view-log-read (kind addr slot value)
  (fw-push (list :read kind *cur-block* *cur-tx* addr (word-int slot) value))
  value)
(defun view-log-write (kind addr slot pre post)
  (fw-push (list :write kind *cur-block* *cur-tx* addr (word-int slot) pre post)))

(declaim (inline balance-of (setf balance-of) nonce-of (setf nonce-of) code-of (setf code-of)
                 storage-of (setf storage-of) account-marked-p))
(defun balance-of (w addr)
  (let ((v (with-acct (tb a) w addr (acct-balance tb a))))
    (if *view-log* (view-log-read :balance addr 0 v) v)))
(defun (setf balance-of) (v w addr)
  (when *observe-capture* (observe-acct-touch! addr))
  (with-acct (tb a) w addr
    (when *view-log* (view-log-write :balance addr 0 (acct-balance tb a) v))
    (setf (acct-balance tb a) v)))
(defun nonce-of (w addr)
  (let ((v (with-acct (tb a) w addr (acct-nonce tb a))))
    (if *view-log* (view-log-read :nonce addr 0 v) v)))
(defun (setf nonce-of) (v w addr)
  (when *observe-capture* (observe-acct-touch! addr))
  (with-acct (tb a) w addr
    (when *view-log* (view-log-write :nonce addr 0 (acct-nonce tb a) v))
    (setf (acct-nonce tb a) v)))
(defun code-of (w addr)
  "ADDR's code; an empty vector when it has none."
  (let ((v (with-acct (tb a) w addr (acct-code tb a))))
    (if *view-log* (view-log-read :code addr 0 v) v)))
(defun (setf code-of) (v w addr)
  (when *observe-capture* (observe-acct-touch! addr))
  (with-acct (tb a) w addr
    (when *view-log* (view-log-write :code addr 0 (acct-code tb a) v))
    (setf (acct-code tb a) v)))
(defun account-marked-p (w addr)
  "Is ADDR in the explicit existence set (an empty-but-present account)?"
  (let ((v (with-acct (tb a) w addr (acct-flag-p tb a +acct-marked+))))
    (if *view-log* (view-log-read :present addr 0 v) v)))

(defun nonce-clear! (w addr)
  "Clear ADDR's nonce (an un-done nonce write)."
  (setf (nonce-of w addr) 0))
(defun balance-clear! (w addr)
  (setf (balance-of w addr) 0))
(defun code-clear! (w addr)
  (setf (code-of w addr) +no-code+))
(defun account-mark! (w addr)
  (with-acct (tb a) w addr
    (when *view-log* (view-log-write :present addr 0 (acct-flag-p tb a +acct-marked+) t))
    (acct-set-flag! tb a +acct-marked+)))
(defun account-unmark! (w addr)
  (with-acct (tb a) w addr
    (when *view-log* (view-log-write :present addr 0 (acct-flag-p tb a +acct-marked+) nil))
    (acct-clear-flag! tb a +acct-marked+)))
(declaim (inline u256))
(defun u256 (x)
  "X mod 2^256 — the EffectIR word arithmetic (`WExp.add/sub/mul`, BitVec 256 semantics)."
  (if (typep x '(integer 0 #.(1- (ash 1 256)))) x (mod x #.(ash 1 256))))
(defun balance-delta! (w addr amount)
  "Balance += AMOUNT as a commutative DELTA (EffectIR `delta`; lean/Evm/Parallel/Reads.lean):
   it reads nothing, so the stream logs (:delta :balance block tx addr 0 amount) — exempt from
   validation — instead of a read and a write. A zero delta is no effect (it brings nothing
   into existence). Not journaled: only the tx-level settlement issues it."
  (unless (zerop amount)
    (when *observe-capture* (observe-acct-touch! addr))
    (when *view-log* (fw-push (list :delta :balance *cur-block* *cur-tx* addr 0 amount)))
    (when *mpt-tracking* (mpt-touch! addr))
    (with-acct (tb a) w addr (incf (acct-balance tb a) amount))))

;;; --- Packed storage (docs/state-snapshot-format.md) ---
;;;
;;; One account's storage: an open-addressing table whose keys and values are kept as four
;;; raw 64-bit words each, in one (unsigned-byte 64) vector — no bignum per key or value,
;;; no hash-table entry. An EQL hash table of bignums cost ~110 B per slot (measured: two
;;; 256-bit bignums plus the entry); this is 64 B per entry at most 3/4 full. A key that is
;;; PRESENT may hold 0: a snapshot-backed world keeps faulted zero slots that way, so
;;; "faulted" needs no second table (`*keep-zero-slots*`); a full world removes zeros.

(defstruct (slots (:constructor %make-slots (cap words state)))
  (count 0 :type fixnum)                ; present keys
  (used 0 :type fixnum)                 ; present + tombstones
  (cap 0 :type fixnum)                  ; a power of two
  (words nil :type (simple-array (unsigned-byte 64) (*)))   ; cap × (4 key + 4 value)
  (state nil :type (simple-array (unsigned-byte 8) (*))))   ; 0 empty, 1 full, 2 tombstone

(defun make-slots (&optional (cap 4))
  (%make-slots cap (make-array (* 8 cap) :element-type '(unsigned-byte 64))
               (make-array cap :element-type '(unsigned-byte 8) :initial-element 0)))

(defvar *keep-zero-slots* nil
  "True in a snapshot-backed world: a slot set to 0 stays present (it was faulted, and
   the checkpoint must delete it from the snapshot).")


(declaim (inline slots-hash))
(defun slots-hash (k0 k1 mask)
  (declare (type (unsigned-byte 64) k0 k1) (type fixnum mask) (optimize (speed 3) (safety 0)))
  (logand (ash (logand (+ (logand (* k0 #x9E3779B97F4A7C15) #xFFFFFFFFFFFFFFFF) k1) #xFFFFFFFFFFFFFFFF) -17) mask))

(defun slots-find (tbl key)
  "Index of KEY's entry, or (- -1 insertion-index) when absent."
  (declare (type slots tbl) (optimize (speed 3) (safety 0)))
  (let* ((k0 (u256-word key 0)) (k1 (u256-word key 1)) (k2 (u256-word key 2)) (k3 (u256-word key 3))
         (words (slots-words tbl)) (state (slots-state tbl))
         (mask (1- (slots-cap tbl))) (i (slots-hash k0 k1 mask)) (tomb -1))
    (declare (type (unsigned-byte 64) k0 k1 k2 k3) (type fixnum mask i tomb))
    (loop
      (let ((st (aref state i)))
        (cond ((= st 0) (return (- -1 (if (>= tomb 0) tomb i))))
              ((= st 2) (when (< tomb 0) (setf tomb i)))
              (t (let ((o (* 8 i)))
                   (declare (type fixnum o))
                   (when (and (= (aref words o) k0) (= (aref words (+ o 1)) k1)
                              (= (aref words (+ o 2)) k2) (= (aref words (+ o 3)) k3))
                     (return i))))))
      (setf i (logand (1+ i) mask)))))

(defun slots-get (tbl key)
  "(values value present-p); 0 when absent."
  (declare (type slots tbl))
  (let ((i (slots-find tbl key)))
    (declare (type fixnum i))
    (if (minusp i)
        (values 0 nil)
        (let ((w (slots-words tbl)) (o (* 8 i)))
          (values (words-u256 (aref w (+ o 4)) (aref w (+ o 5)) (aref w (+ o 6)) (aref w (+ o 7))) t)))))

(declaim (inline slots-present-p))
(defun slots-present-p (tbl key)
  "Is KEY present in TBL (a fault test: no value is built)?"
  (>= (the fixnum (slots-find tbl key)) 0))

(defun slots-grow (tbl)
  (let* ((old-w (slots-words tbl)) (old-s (slots-state tbl)) (old-cap (slots-cap tbl))
         (cap (if (> (* 2 (slots-count tbl)) old-cap) (* 2 old-cap) old-cap)))  ; same size: tombstones only
    (setf (slots-cap tbl) cap (slots-count tbl) 0 (slots-used tbl) 0
          (slots-words tbl) (make-array (* 8 cap) :element-type '(unsigned-byte 64))
          (slots-state tbl) (make-array cap :element-type '(unsigned-byte 8) :initial-element 0))
    (dotimes (i old-cap)
      (when (= (aref old-s i) 1)
        (let ((o (* 8 i)))
          (slots-put tbl (words-u256 (aref old-w o) (aref old-w (+ o 1)) (aref old-w (+ o 2)) (aref old-w (+ o 3)))
                     (words-u256 (aref old-w (+ o 4)) (aref old-w (+ o 5)) (aref old-w (+ o 6)) (aref old-w (+ o 7)))))))))

(defun slots-put (tbl key val)
  (declare (type slots tbl))
  (when (>= (* 4 (1+ (slots-used tbl))) (* 3 (slots-cap tbl))) (slots-grow tbl))
  (let* ((i (slots-find tbl key)) (w (slots-words tbl)))
    (declare (type fixnum i))
    (when (minusp i)
      (setf i (- -1 i))
      (when (= (aref (slots-state tbl) i) 0) (incf (slots-used tbl)))
      (setf (aref (slots-state tbl) i) 1)
      (incf (slots-count tbl))
      (let ((o (* 8 i)))
        (setf (aref w o) (u256-word key 0) (aref w (+ o 1)) (u256-word key 1)
              (aref w (+ o 2)) (u256-word key 2) (aref w (+ o 3)) (u256-word key 3))))
    (let ((o (* 8 i)))
      (setf (aref w (+ o 4)) (u256-word val 0) (aref w (+ o 5)) (u256-word val 1)
            (aref w (+ o 6)) (u256-word val 2) (aref w (+ o 7)) (u256-word val 3)))
    val))

(defun slots-remove (tbl key)
  (let ((i (slots-find tbl key)))
    (unless (minusp i)
      (setf (aref (slots-state tbl) i) 2)
      (decf (slots-count tbl)))))

(defun slots-map (fn tbl)
  "FN (key value) for every present key (values may be 0 in a snapshot-backed world)."
  (let ((w (slots-words tbl)) (s (slots-state tbl)))
    (dotimes (i (slots-cap tbl))
      (when (= (aref s i) 1)
        (let ((o (* 8 i)))
          (funcall fn (words-u256 (aref w o) (aref w (+ o 1)) (aref w (+ o 2)) (aref w (+ o 3)))
                   (words-u256 (aref w (+ o 4)) (aref w (+ o 5)) (aref w (+ o 6)) (aref w (+ o 7)))))))))

(defun world-get-storage-table (w addr)
  (with-acct (tb a) w addr
    (or (acct-storage tb a) (setf (acct-storage tb a) (make-slots)))))

(defun world-storage-get (w addr slot)
  (let ((tbl (with-acct (tb a) w addr (acct-storage tb a))))
    (if tbl (values (slots-get tbl slot)) 0)))

(defvar *cold-storage-map-hook* nil
  "(lambda (addr fn)): FN (slot value) for every cold-tier (snapshot) slot of ADDR that RAM
   does not override. NIL when RAM is the whole world (fixtures, an in-memory run).")

(defun world-storage-set (w addr slot val)
  (let ((tbl (world-get-storage-table w addr)))
    (if (and (zerop val) (not *keep-zero-slots*))
        (slots-remove tbl slot)
        (slots-put tbl slot val))))
;; The storage view (see "The storage view" above): world-storage-get/-set are the raw
;; table operations (loading, persistence, observer pre-images); the effect layer uses these.
(defun storage-of (w addr slot)
  (let ((v (world-storage-get w addr slot)))
    (if *view-log* (view-log-read :storage addr slot v) v)))
(defun (setf storage-of) (v w addr slot)
  (when *view-log* (view-log-write :storage addr slot (world-storage-get w addr slot) v))
  (world-storage-set w addr slot v)
  v)

;;; --- Durability helpers (anchors, snapshots, observers) ------------------------

(defun bytes->hex-string (v &optional (prefix ""))
  "Lower-case hex of byte vector V, after PREFIX."
  (let* ((n (length v)) (p (length prefix))
         (out (make-string (+ p (* 2 n)) :element-type 'base-char))
         (digits "0123456789abcdef"))
    (replace out prefix)
    (loop for i below n
          for b = (aref v i)
          do (setf (schar out (+ p (* 2 i)))     (schar digits (ash b -4))
                   (schar out (+ p 1 (* 2 i)))   (schar digits (logand b 15))))
    out))

(defun fsync-directory-of (path)
  (let ((fd (sb-posix:open (directory-namestring (merge-pathnames path)) sb-posix:o-rdonly)))
    (unwind-protect (sb-posix:fsync fd) (sb-posix:close fd))))

;;; --- Lazy world faulting (Base/OP lazy-RPC replay) ---
;;;
;;; Fixture/mainnet replays populate the whole world up front and leave
;;; both hooks nil (fault-* are no-ops). The Base replay installs hooks
;;; that, on first touch of an account / storage slot, fetch its value
;;; from an RPC endpoint pinned at the replay's start block. Every
;;; world read/write choke point calls fault-* BEFORE touching the
;;; world tables, so the default-0/absent fallbacks below only ever
;;; see post-fault state.

(defvar *fault-account-hook* nil
  "When set: (lambda (addr)) — ensure ADDR's balance/nonce/code are live.")
(defvar *fault-slot-hook* nil
  "When set: (lambda (addr slot)) — ensure the storage slot is live.")
(defvar *storage-wipe-hook* nil
  "When set: (lambda (addr)) — ADDR's whole storage was just removed. A lazy world must
   then answer 0 for every slot of ADDR it has not faulted, never the backing value.")

(defun world-storage-wipe! (w addr)
  "Remove ADDR's whole storage (SELFDESTRUCT, EIP-161 sweep)."
  (with-acct (tb a) w addr (setf (acct-storage tb a) nil))
  (when *storage-wipe-hook* (funcall *storage-wipe-hook* addr)))

(defun account-delete! (w addr)
  "The storage view's account deletion (EELS destroy_account: SELFDESTRUCT at tx end, the
   EIP-161 sweep, the EIP-161 coinbase rule): balance, nonce, code, the whole storage and the
   existence mark. The removed slots may have been written in earlier txs/blocks, so the
   incremental root check is told to re-read the whole account (no-op unless armed)."
  (when *observe-capture* (observe-acct-touch! addr))
  (when *view-log* (view-log-write :account addr 0 t nil))
  (when *mpt-tracking* (mpt-touch-all! addr))
  (with-acct (tb a) w addr
    (setf (acct-balance tb a) 0 (acct-nonce tb a) 0 (acct-code tb a) +no-code+)
    (world-storage-wipe! w addr)
    (acct-clear-flag! tb a +acct-marked+)))
(defun account-uncreate! (w addr was-present)
  "Undo a CREATE (journal entry 10): code, nonce and storage go — the creation's
   collision rule guarantees the account had none of them before — and the existence mark
   goes unless the account was present before the CREATE (WAS-PRESENT = 1: an existing
   empty account, pre-Spurious Dragon). The balance has its own journal entry. The storage
   table is dropped without the wipe hook (nothing below it was ever faulted)."
  (when *observe-capture* (observe-acct-touch! addr))
  (when *view-log* (view-log-write :account addr 0 t nil))
  (with-acct (tb a) w addr
    (setf (acct-code tb a) +no-code+ (acct-nonce tb a) 0 (acct-storage tb a) nil)
    (unless (eql was-present 1) (acct-clear-flag! tb a +acct-marked+))))
;;; Observation gate (the observation seam, further down). It
;;; lives here, ahead of the fault seam, because the inline fault-slot! below
;;; tests it on every access: the first fault of a slot within a tx snapshots its
;;; pre-image. Accounts snapshot theirs on first WRITE (the storage-view writers above),
;;; so read-only accounts cost nothing.
(defvar *observer* nil "The installed observer (the observation seam, below), or NIL.")

(declaim (inline fault-account! fault-slot!))
(defun fault-account! (addr)
  "Load ADDR into a lazy world on its first touch: the id's +acct-faulted+ bit is THE
   faulted test (one per world table; the hooks keep none). Loading is not a write: no
   pre-image capture while the hook installs state."
  (when *fault-account-hook*
    (with-acct (tb a) *current-world* addr
      (unless (acct-flag-p tb a +acct-faulted+)
        (acct-set-flag! tb a +acct-faulted+)
        (incf (acct-table-faulted tb))
        (let ((*observe-capture* nil) (*view-log* nil)) (funcall *fault-account-hook* addr))))))
(defun fault-slot! (addr slot)
  "Load (ADDR, SLOT) into a lazy world on its first touch. A key PRESENT in ADDR's table is
   live (faulted, or written after its fault: every writer faults first), so the hook is
   called only for an absent key, with the key's integer (SLOT may be an opaque word)."
  (when (and *fault-slot-hook*
             (not (with-acct (tb a) *current-world* addr
                    (let ((tbl (acct-storage tb a))) (and tbl (slots-present-p tbl slot))))))
    (let ((k (word-int slot)))
      (if *view-log*
          (let ((*view-log* nil)) (funcall *fault-slot-hook* addr k))
          (funcall *fault-slot-hook* addr k))))
  (when *observer* (observe-slot-touch! addr (word-int slot))))
