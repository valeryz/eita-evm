;;;; snapshot.lisp — the binary state snapshot (docs/state-snapshot-format.md, v1):
;;;; writer, mmap reader, verification. See docs/state-snapshot-format.md.
;;;;
;;;; A snapshot is the flat state after block N, in a directory published atomically:
;;;;   snap-N/accounts.dat  96 B records sorted by addr      (addr nonce balance codehash)
;;;;          storage.dat   88 B records sorted by addr,slot (value never 0)
;;;;          code.dat      variable records sorted by codehash
;;;;          code.idx      (codehash, offset) of every code record   (derived; lookups)
;;;;          MANIFEST.sexp counts, per-file sizes and FNV-1a 64, the content hash
;;;; Each file but the manifest starts with a 4096-byte header (format doc), so data is
;;;; page-aligned and the reader can mmap it. Everything big-endian; keys sort by memcmp.
;;;;
;;;; The writer is a MERGE: a sorted stream of changes laid over an older snapshot (or
;;;; over nothing), copying unchanged records byte for byte. So a checkpoint costs one
;;;; sequential pass over the old files plus the changed keys, never a decode/encode of
;;;; the whole state. The reader maps the files read-only; a point lookup goes through
;;;; the file's FENCE (an in-memory radix index built at open) to a bucket of at most a
;;;; few hundred records, then binary-searches it.
;;;;
;;;; A LAYER (layer-P-N/, docs/layered-snapshots.md) is the same file set holding only
;;;; what blocks P+1..N changed, over a base snap-B/ and the layers below it: one account
;;;; record per address it mentions, always with the fields (flag bit 0 = the RAM's
;;;; existence mark, bit 2 = the storage was WIPED), and slot records that may be 0 (a
;;;; tombstone). Readers look an address up through the stack newest layer first
;;;; (`view-account`, `view-slot`); the composers (`compose-address`) fold a run of
;;;; layers, with or without the base, one address at a time. Lean: Evm.Persist.Layered.
;;;;
;;;; Standalone: no libeita, no replay code (the importer, the root checker and the
;;;; tests load it alone). Codehashes are passed in, never computed here.

(in-package #:eita.state.snapshot)

(defconstant +header+ 4096)
(defconstant +acct-rec+ 96)
(defconstant +slot-rec+ 88)
(defconstant +flag-exists-empty+ 1)  ; base: empty and present; layer: the RAM existence mark
(defconstant +flag-wiped+ 4)         ; layer: the address's storage below was removed

(defparameter +empty-code-hash+
  #xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
  "keccak256 of the empty byte string: the codehash of an account without code.")

;;; ---------------------------------------------------------------- byte helpers

(declaim (inline put-be))
(defun put-be (buf pos n width)
  "Write the non-negative integer N as WIDTH big-endian bytes at BUF[POS]."
  (declare (type (simple-array (unsigned-byte 8) (*)) buf) (type fixnum pos width)
           (optimize (speed 3) (safety 0)))
  (if (typep n '(unsigned-byte 62))
      (let ((x n))
        (declare (type (unsigned-byte 62) x))
        (loop for i of-type fixnum from (+ pos width -1) downto pos
              do (setf (aref buf i) (logand x #xff) x (ash x -8))))
      ;; bignum: 8-byte words, least significant first, peeled off with a constant
      ;; mask and shift. (A variable-position (ldb (byte 64 (* 64 w)) n) here is
      ;; miscompiled by SBCL 2.6.0 on x86-64 at this policy: it wrote wrong words.)
      (let ((x n))
        (loop for w of-type fixnum from 0 below (ceiling width 8)
              do (let ((word (logand x #xFFFFFFFFFFFFFFFF)))
                   (declare (type (unsigned-byte 64) word))
                   (loop for b of-type fixnum from 0 below 8
                         for i of-type fixnum = (- (+ pos width -1) (* 8 w) b)
                         when (>= i pos) do (setf (aref buf i) (logand (ash word (* -8 b)) #xff)))
                   (setf x (ash x -64)))))))

(defun int->octets (n width)
  (let ((v (make-array width :element-type '(unsigned-byte 8))))
    (put-be v 0 n width) v))

(defun octets->int (v &optional (start 0) (end (length v)))
  (let ((n 0))
    (loop for i from start below end do (setf n (logior (ash n 8) (aref v i))))
    n))

(declaim (inline sap-be))
(defun sap-be (sap off width)
  "The WIDTH-byte big-endian integer at SAP+OFF."
  (declare (type fixnum off width) (optimize (speed 3) (safety 0)))
  (if (<= width 7)
      (let ((x 0))
        (declare (type (unsigned-byte 62) x))
        (dotimes (i width x) (setf x (logior (ash x 8) (sb-sys:sap-ref-8 sap (+ off i))))))
      (let ((n 0))
        ;; 7-byte (56-bit) fixnum chunks
        (loop with i of-type fixnum = 0
              while (< i width)
              do (let* ((k (min 7 (- width i))) (x 0))
                   (declare (type fixnum k) (type (unsigned-byte 62) x))
                   (dotimes (j k) (setf x (logior (ash x 8) (sb-sys:sap-ref-8 sap (+ off i j)))))
                   (setf n (logior (ash n (* 8 k)) x))
                   (incf i k)))
        n)))

(defun fnv64-sap (h sap start end)
  (declare (type (unsigned-byte 64) h) (type fixnum start end) (optimize (speed 3) (safety 0)))
  (loop for i of-type fixnum from start below end
        do (setf h (logand #xFFFFFFFFFFFFFFFF (* (logxor h (sb-sys:sap-ref-8 sap i)) #x100000001b3))))
  h)

(defun fnv64-buf (h buf start end)
  (declare (type (unsigned-byte 64) h) (type (simple-array (unsigned-byte 8) (*)) buf)
           (type fixnum start end) (optimize (speed 3) (safety 0)))
  (loop for i of-type fixnum from start below end
        do (setf h (logand #xFFFFFFFFFFFFFFFF (* (logxor h (aref buf i)) #x100000001b3))))
  h)

(defconstant +fnv-init+ #xcbf29ce484222325)

;;; ---------------------------------------------------------------- paths

(defun hardware-threads ()
  "The machine's hardware thread count (nproc, else sysctl hw.ncpu, else 4)."
  (flet ((ask (prog args)
           (ignore-errors
             (parse-integer (with-output-to-string (s) (sb-ext:run-program prog args :search t :output s :error nil))
                            :junk-allowed t))))
    (or (ask "nproc" '()) (ask "sysctl" '("-n" "hw.ncpu")) 4)))

(defun as-dir (p)
  "P as a directory pathname, whether or not it was written with a trailing slash."
  (let ((s (namestring p)))
    (pathname (if (and (plusp (length s)) (char= (char s (1- (length s))) #\/)) s (concatenate 'string s "/")))))

(defun snap-path (dir n) (merge-pathnames (format nil "snap-~D/" n) (pathname dir)))
(defun snap-tmp-path (dir n) (merge-pathnames (format nil ".tmp-snap-~D/" n) (pathname dir)))
(defun layer-path (dir p n) (merge-pathnames (format nil "layer-~D-~D/" p n) (pathname dir)))
(defun layer-tmp-path (dir p n) (merge-pathnames (format nil ".tmp-layer-~D-~D/" p n) (pathname dir)))

(defun fsync-path (path)
  (let ((fd (sb-posix:open (namestring path) sb-posix:o-rdonly)))
    (unwind-protect (sb-posix:fsync fd) (sb-posix:close fd))))

;;; ---------------------------------------------------------------- writer streams

(defconstant +wbuf+ (* 4 1024 1024))

(defstruct (out (:constructor %make-out))
  stream (buf (make-array +wbuf+ :element-type '(unsigned-byte 8)) :type (simple-array (unsigned-byte 8) (*)))
  (pos 0 :type fixnum) (h +fnv-init+ :type (unsigned-byte 64)) (bytes 0 :type fixnum) path)

(defun make-out (path)
  (let ((s (open path :direction :output :element-type '(unsigned-byte 8)
                      :if-exists :supersede :if-does-not-exist :create)))
    ;; header placeholder; rewritten at close (the hash covers the data only)
    (write-sequence (make-array +header+ :element-type '(unsigned-byte 8) :initial-element 0) s)
    (%make-out :stream s :path path)))

(defun out-flush (o)
  (let ((p (out-pos o)))
    (when (plusp p)
      (setf (out-h o) (fnv64-buf (out-h o) (out-buf o) 0 p))
      (incf (out-bytes o) p)
      (write-sequence (out-buf o) (out-stream o) :end p)
      (setf (out-pos o) 0))))

(declaim (inline out-room))
(defun out-room (o n)
  (when (> (+ (out-pos o) n) +wbuf+) (out-flush o)))

(defun out-bytes-total (o) (+ (out-bytes o) (out-pos o)))

(defun out-sap (o sap off n)
  "Copy N raw bytes from SAP+OFF (an unchanged record of the old snapshot)."
  (declare (type fixnum off n) (optimize (speed 3) (safety 0)))
  (when (> n +wbuf+)                    ; bigger than the buffer (Arc has 12.9 MB code)
    (loop for k of-type fixnum from 0 below n by +wbuf+
          do (out-sap o sap (+ off k) (min +wbuf+ (- n k))))
    (return-from out-sap))
  (out-room o n)
  (let ((buf (out-buf o)) (p (out-pos o)))
    (declare (type fixnum p))
    (dotimes (i n) (setf (aref buf (+ p i)) (sb-sys:sap-ref-8 sap (+ off i))))
    (setf (out-pos o) (+ p n))))

(defun out-octets (o v)
  (when (> (length v) +wbuf+)           ; bigger than the buffer: in buffer-sized pieces
    (loop for k from 0 below (length v) by +wbuf+
          do (out-octets o (subseq v k (min (length v) (+ k +wbuf+)))))
    (return-from out-octets))
  (out-room o (length v))
  (replace (out-buf o) v :start1 (out-pos o))
  (incf (out-pos o) (length v)))

(defun out-close (o table count recsize stride chain-id block)
  "Flush, write the header, fsync. Returns (bytes fnv-hex)."
  (out-flush o)
  (let ((s (out-stream o))
        (hdr (make-array +header+ :element-type '(unsigned-byte 8) :initial-element 0)))
    (replace hdr (map 'vector #'char-code "EITASNAP"))
    (put-be hdr 8 1 4) (put-be hdr 12 table 4) (put-be hdr 16 count 8) (put-be hdr 24 chain-id 8)
    (put-be hdr 32 block 8) (put-be hdr 40 recsize 4) (put-be hdr 44 stride 4)
    (file-position s 0)
    (write-sequence hdr s)
    (finish-output s)
    (sb-posix:fsync (sb-sys:fd-stream-fd s))
    (close s)
    (list (out-bytes o) (format nil "~(~16,'0X~)" (out-h o)))))

;;; ---------------------------------------------------------------- reader

(defstruct (mapping (:constructor %make-mapping)) sap len (released 0))

;;; A sequential scan of a mapped file leaves every page it passed resident in this
;;; process: clean file pages, which the kernel can reclaim, but which count toward RSS
;;; until unmapped. The merge scans the whole base snapshot and resume verification
;;; every file, so a 6.3 GB storage.dat showed as 6.3 GB more RSS (x86-64 Linux: 10.3 GB peak
;;; against 1.2 GB anonymous). Behind a scan, MADV_DONTNEED drops those pages from this
;;; process; the page cache keeps them, so a later touch refaults them without I/O.
;;; Darwin ignores MADV_DONTNEED on a file mapping (the pages stay in RSS); there
;;; msync(MS_INVALIDATE) drops a read-only mapping's clean pages instead (a no-op on Linux).
;;; Advice only: what is read never depends on it (a released page refaults the same bytes).
(defconstant +release-step+ (* 64 1024 1024))
(defconstant +madv-sequential+ 2)       ; Linux and Darwin alike
(defconstant +madv-dontneed+ 4)         ; Linux and Darwin alike
(defconstant +ms-invalidate+ 2)         ; Darwin

(defun page-range (len start end)
  "The pages of a mapping of LEN bytes that [START, END) names: (values start end). START
   is aligned down; END down, except that an END at or past LEN covers the last (partial)
   page and STOPS THERE: a page past it belongs to another mapping, and MADV_DONTNEED
   zeroes anonymous memory (the Lisp heap: CI 2026-11-14, `len + page` aligned down was
   one page past a page-aligned file)."
  (let ((mask (1- (sb-posix:getpagesize))))   ; run time: 4 KB on Linux, 16 KB on Apple Silicon
    (values (logandc2 (max 0 start) mask)
            (if (>= end len) (logandc2 (+ len mask) mask) (logandc2 end mask)))))

(defun advise (m start end advice)
  "madvise ADVICE over the pages of M in [START, END) (`page-range`), or with ADVICE
   :RELEASE drop those pages from this process."
  (multiple-value-bind (start end) (page-range (mapping-len m) start end)
    (when (> end start)
      (if (and (eq advice :release) (member :darwin *features*))
          (sb-alien:alien-funcall
           (sb-alien:extern-alien "msync" (function sb-alien:int sb-sys:system-area-pointer
                                                    sb-alien:unsigned-long sb-alien:int))
           (sb-sys:sap+ (mapping-sap m) start) (- end start) +ms-invalidate+)
          (sb-alien:alien-funcall
           (sb-alien:extern-alien "madvise" (function sb-alien:int sb-sys:system-area-pointer
                                                      sb-alien:unsigned-long sb-alien:int))
           (sb-sys:sap+ (mapping-sap m) start) (- end start)
           (if (eq advice :release) +madv-dontneed+ advice))))))

(defun release-range (m start end) (advise m start end :release))

(defun advise-sequential (m)
  "M is about to be read once, front to back: read ahead further, and (Linux) let its pages
   be the first reclaimed."
  (when m (advise m 0 (mapping-len m) +madv-sequential+)))

(defun release-behind (m off)
  "A scan of M has passed byte OFF: release what lies behind it, in steps of 64 MB."
  (when (and m (>= (- off (mapping-released m)) +release-step+))
    (release-range m (mapping-released m) off)
    (setf (mapping-released m) (logandc2 off (1- (sb-posix:getpagesize))))))

(defun release-all (m)
  "A scan of M is done: release all of it, and restart the watermark for the next one."
  (when m
    (release-range m 0 (mapping-len m))
    (setf (mapping-released m) 0)))

(defun map-file (path)
  "Map PATH read-only. The descriptor is closed once mapped (the mapping stays valid): an
   open snap costs no descriptors, so a stack of many layers cannot exhaust the open-file
   limit (the root checker's 2048 buckets left room for about 20 layers' six files each)."
  (let* ((fd (sb-posix:open (namestring path) sb-posix:o-rdonly))
         (len (handler-case (sb-posix:stat-size (sb-posix:fstat fd))
                (error (e) (sb-posix:close fd) (error e))))
         (sap (unwind-protect (sb-posix:mmap nil len sb-posix:prot-read sb-posix:map-shared fd 0)
                (sb-posix:close fd))))
    (%make-mapping :sap sap :len len)))

(defun unmap (m)
  (when m
    (ignore-errors (sb-posix:munmap (mapping-sap m) (mapping-len m)))))

(defstruct (snap (:constructor %make-snap))
  dir block manifest
  acct slot-map code-map code-idx
  (acct-fence nil) (slot-fence nil)     ; the in-memory indexes of accounts.dat, storage.dat
  (n-accounts 0 :type fixnum) (n-slots 0 :type fixnum) (n-codes 0 :type fixnum)
  (bloom nil)                           ; a layer's address filter (built at open)
  (fence-thread nil))                   ; the thread building the fences (`snap-open` :background)

(defun read-manifest (dir)
  (with-open-file (in (merge-pathnames "MANIFEST.sexp" (as-dir dir)) :if-does-not-exist nil)
    (and in (let ((*read-eval* nil)) (read in nil nil)))))

(defun snap-sealed-p (dir)
  "Complete: the manifest exists (it is written last, inside a directory renamed into
   place only after every file was fsynced) and every file has the size it records.
   Cheap; `snap-verify` checks the bytes."
  (let ((m (ignore-errors (read-manifest dir))))
    (and (listp m) (getf m :files)
         (every (lambda (f)
                  (destructuring-bind (name bytes fnv) f
                    (declare (ignore fnv))
                    (let ((p (probe-file (merge-pathnames name (as-dir dir)))))
                      (and p (= (+ +header+ bytes)
                                (with-open-file (s p :element-type '(unsigned-byte 8)) (file-length s)))))))
                (getf m :files))
         m)))

(defun snap-content-hash (manifest)
  "The snapshot's content hash: FNV-1a 64 over its files' names, sizes and hashes."
  (let ((h +fnv-init+))
    (dolist (f (getf manifest :files))
      (let ((s (map '(simple-array (unsigned-byte 8) (*)) #'char-code
                    (format nil "~A ~D ~A;" (first f) (second f) (third f)))))
        (setf h (fnv64-buf h s 0 (length s)))))
    (format nil "~(~16,'0X~)" h)))

(defun snap-open (dir &key (fence t))
  "Map the snapshot at DIR. FENCE: build its in-memory indexes (`build-fence`, a pass over
   the keys); without them a point lookup binary-searches the whole file (for a reader
   that only scans). :BACKGROUND builds them on a thread of their own and publishes each
   when done, lookups binary-searching until then: a resume runs at once instead of first
   reading every key (Ethereum's base: 190 GB, a quarter of an hour). :SCAN builds them
   releasing the pages behind the pass, for a reader that does not keep the files
   resident (the root check: on x300 an Ethereum check held 42 GB of the base's pages
   after its fences, and pushed the Arc replay's heap into swap). A snapshot from
   before the fences also holds accounts.idx and storage.idx: listed in its manifest (so
   verified and hashed as before), never read."
  (let* ((dir (as-dir dir)) (m (snap-sealed-p dir)))
    (unless m (error "snapshot ~A is not complete (no manifest, or a file of the wrong size)" dir))
    (flet ((mf (name) (map-file (merge-pathnames name dir))))
      (let ((c (getf m :counts)))
        (let ((s (%make-snap :dir dir :block (getf m :block) :manifest m
                             :acct (mf "accounts.dat") :slot-map (mf "storage.dat")
                             :code-map (mf "code.dat") :code-idx (mf "code.idx")
                             :n-accounts (getf c :accounts) :n-slots (getf c :slots) :n-codes (getf c :codes))))
          (flet ((fences () ; @veil snap-open/fences
                   ;; each published whole: its contents before the pointer to it (the
                   ;; replay's lookups read it without a lock; ARM64 orders their dependent loads)
                   (let ((f (build-fence (snap-acct s) +acct-rec+ 20 (snap-n-accounts s) (eq fence :scan)))) ; @veil snap-open/build
                     (sb-thread:barrier (:write))
                     (setf (snap-acct-fence s) f)) ; @veil snap-open/publish
                   (let ((f (build-fence (snap-slot-map s) +slot-rec+ 52 (snap-n-slots s) (eq fence :scan)))) ; @veil snap-open/build
                     (sb-thread:barrier (:write))
                     (setf (snap-slot-fence s) f)))) ; @veil snap-open/publish
            (case fence
              ((nil))
              (:background ; @veil snap-open/background
               (setf (snap-fence-thread s)
                     (sb-thread:make-thread
                      (lambda ()
                        ;; a failed build leaves lookups on the binary search: slower, not wrong
                        (handler-case (fences)
                          (error (e) (format *error-output* "~&[snapshot] fence of ~A not built: ~A~%" dir e))))
                      :name "snapshot fence")))
              (t (fences))))
          (when (snap-layer-p s)
            (let ((b (build-bloom s))) (setf (snap-bloom s) b)))
          s)))))

(defun snap-kind-p (m kind)
  "Is the manifest M of KIND (:base or :layer)? A manifest without :kind is a base (v1)."
  (eq (or (getf m :kind) :base) kind))
(defun snap-layer-p (s) (snap-kind-p (snap-manifest s) :layer))
(defun snap-parent (s) (getf (snap-manifest s) :parent))

(defun snap-close (s)
  (when s
    ;; a fence still being built reads the mappings
    (when (snap-fence-thread s) (sb-thread:join-thread (snap-fence-thread s) :default nil)) ; @veil snap-close/join
    (dolist (m (list (snap-acct s) (snap-slot-map s) (snap-code-map s) (snap-code-idx s)))
      (unmap m))))

(defun snap-verify (s)
  "Re-hash every file and compare with the manifest (I3: resume loads only the bytes
   whose root was checked). Returns the content hash, or signals."
  (let ((m (snap-manifest s)))
    (dolist (f (getf m :files))
      (destructuring-bind (name bytes fnv) f
        (let* ((mp (map-file (merge-pathnames name (snap-dir s))))
               (h (unwind-protect
                       (let ((h +fnv-init+) (end (+ +header+ bytes)))
                         (loop for start from +header+ below end by +release-step+
                               for stop = (min end (+ start +release-step+))
                               do (setf h (fnv64-sap h (mapping-sap mp) start stop))
                                  (release-behind mp stop))
                         h)
                    (unmap mp))))
          (unless (string-equal fnv (format nil "~(~16,'0X~)" h))
            (error "snapshot ~A: ~A has FNV ~(~16,'0X~), manifest says ~A" (snap-dir s) name h fnv)))))
    (snap-content-hash m)))

;;; key comparison: KEY is an octet vector; the record key is at SAP+OFF
(declaim (inline cmp-key))
(defun cmp-key (key sap off n)
  "-1 / 0 / 1: KEY[0,N) against the N bytes at SAP+OFF."
  (declare (type (simple-array (unsigned-byte 8) (*)) key) (type fixnum off n)
           (optimize (speed 3) (safety 0)))
  (dotimes (i n 0)
    (let ((a (aref key i)) (b (sb-sys:sap-ref-8 sap (+ off i))))
      (cond ((< a b) (return -1)) ((> a b) (return 1))))))

(defun cmp-sap* (sap1 off1 sap2 off2 n)
  "-1 / 0 / 1 comparing N bytes at SAP1+OFF1 with those at SAP2+OFF2."
  (declare (type fixnum off1 off2 n) (optimize (speed 3) (safety 0)))
  (dotimes (i n 0)
    (let ((a (sb-sys:sap-ref-8 sap1 (+ off1 i))) (b (sb-sys:sap-ref-8 sap2 (+ off2 i))))
      (cond ((< a b) (return -1)) ((> a b) (return 1))))))

;;; ---------------------------------------------------------------- the fence
;;;
;;; A point lookup narrows the sorted records to a few dozen through an in-memory radix
;;; index, the FENCE, then binary-searches them. A fence node covers records whose keys
;;; share their first BIT bits and splits them by the next R bits: A[p] is the first
;;; record whose R bits there are >= p, so bucket p is [A[p], A[p+1]). A bucket of more
;;; than +fence-split+ records gets a node of its own, keyed by the bits after its
;;; records' common prefix: in storage.dat a big contract's slots (one address) are split
;;; by the slot's bits. Built at open: a pass over the keys, and one over each big bucket;
;;; 4 bytes per 64..128 records (+fence-bucket+).

(defconstant +fence-bucket+ 128 "The most records per bucket the fence aims at.")
(defconstant +fence-split+ 512 "A bucket over this many records gets a node of its own.")

(defstruct (fence (:constructor %make-fence (a bit r)))
  (a (make-array 0 :element-type '(unsigned-byte 32)) :type (simple-array (unsigned-byte 32) (*)))
  (bit 0 :type fixnum) (r 0 :type fixnum)
  (kids nil))                           ; NIL, or bucket -> fence (a hash table)

(declaim (inline sap-bits))
(defun sap-bits (sap off bit r klen)
  "R bits (R <= 30) of the KLEN-byte key at SAP+OFF from bit BIT on (0 past its end)."
  (declare (type fixnum off bit r klen) (optimize (speed 3) (safety 0)))
  (let ((x 0) (b0 (ash bit -3)))
    (declare (type (unsigned-byte 40) x) (type fixnum b0))
    (dotimes (i 5) (let ((j (+ b0 i))) (setf x (logior (ash x 8) (if (< j klen) (sb-sys:sap-ref-8 sap (+ off j)) 0)))))
    (ldb (byte r (- 40 (logand bit 7) r)) x)))

(defun fence-node (sap recsize klen lo hi bit &optional release)
  "The node over records [LO, HI) of the file mapped at SAP (keys of KLEN bytes, equal
   in their first BIT bits). RELEASE: that mapping, whose pages the pass releases behind
   it, every +RELEASE-STEP+ bytes (a node's kids re-read their records and release them)."
  (declare (type fixnum recsize klen lo hi bit) (optimize (speed 3) (safety 0)))
  (let* ((r (min 30 (max 1 (integer-length (floor (- hi lo) +fence-bucket+)))))
         (a (make-array (1+ (ash 1 r)) :element-type '(unsigned-byte 32)))
         (f (%make-fence a bit r)) (p 0)
         (step (max 1 (floor +release-step+ recsize))) (done lo))
    (declare (type fixnum r p step done))
    (loop for j of-type fixnum from lo below hi
          do (let ((b (sap-bits sap (+ +header+ (* j recsize)) bit r klen)))
               (declare (type fixnum b))
               (loop while (<= p b) do (setf (aref a p) j) (incf p))
               (when (and release (>= (- j done) step))
                 (release-range release (+ +header+ (* done recsize)) (+ +header+ (* j recsize)))
                 (setf done j))))
    (when release (release-range release (+ +header+ (* done recsize)) (+ +header+ (* hi recsize))))
    (loop while (<= p (ash 1 r)) do (setf (aref a p) hi) (incf p))
    (dotimes (p (ash 1 r) f)
      (let ((blo (aref a p)) (bhi (aref a (1+ p))))
        (when (> (- bhi blo) +fence-split+)
          ;; the first bit where the bucket's first and last keys differ
          (let* ((o1 (+ +header+ (* blo recsize))) (o2 (+ +header+ (* (1- bhi) recsize)))
                 (cb (dotimes (i klen nil)
                       (let ((x (sb-sys:sap-ref-8 sap (+ o1 i))) (y (sb-sys:sap-ref-8 sap (+ o2 i))))
                         (unless (= x y) (return (+ (* 8 i) (- 8 (integer-length (logxor x y))))))))))
            (when cb
              (setf (gethash p (or (fence-kids f) (setf (fence-kids f) (make-hash-table))))
                    (fence-node sap recsize klen blo bhi cb release)))))))))

(defun build-fence (m recsize klen count &optional release)
  "The fence of the COUNT records of the mapping M (NIL when there are none). RELEASE:
   drop M's pages behind the pass (`snap-open` :scan)."
  (when (>= count (ash 1 32)) (error "fence: ~D records (its indexes are 32-bit)" count))
  (and (plusp count)
       (progn (when release (advise-sequential m))
              (fence-node (mapping-sap m) recsize klen 0 count 0 (and release m)))))

(defun lower-bound (m f count recsize key klen)
  "Index of the first of the COUNT records of the mapping M whose KLEN-byte key is >= KEY
   (COUNT when none), through its fence F (NIL: over the whole file)."
  (declare (type fixnum count recsize klen) (type (simple-array (unsigned-byte 8) (*)) key)
           (optimize (speed 3) (safety 0)))
  (let ((sap (mapping-sap m)) (lo 0) (hi count))
    (declare (type fixnum lo hi))
    (sb-sys:with-pinned-objects (key)
      (let ((ksap (sb-sys:vector-sap key)))
        (loop while f
              do (let ((p (sap-bits ksap 0 (fence-bit f) (fence-r f) klen)) (a (fence-a f)))
                   (declare (type fixnum p))
                   (setf lo (aref a p) hi (aref a (1+ p)))
                   (let ((kid (and (> (- hi lo) +fence-split+) (fence-kids f) (gethash p (fence-kids f)))))
                     (setf f nil)
                     (when kid
                       ;; the kid's records share their first BIT bits: a KEY that does not
                       ;; is below or above all of them
                       (let* ((bit (fence-bit kid)) (nb (ash bit -3)) (off (+ +header+ (* lo recsize)))
                              (c (cmp-sap* ksap 0 sap off nb)))
                         (declare (type fixnum bit nb off c))
                         (when (and (zerop c) (logtest bit 7))
                           (let ((x (ash (sb-sys:sap-ref-8 ksap nb) (- (logand bit 7) 8)))
                                 (y (ash (sb-sys:sap-ref-8 sap (+ off nb)) (- (logand bit 7) 8))))
                             (setf c (cond ((< x y) -1) ((> x y) 1) (t 0)))))
                         (cond ((minusp c) (setf hi lo))
                               ((plusp c) (setf lo hi))
                               (t (setf f kid))))))))))
    ;; the lower bound is in [lo, hi]
    (loop while (< lo hi)
          do (let ((mid (ash (+ lo hi) -1)))
               (declare (type fixnum mid))
               (if (plusp (cmp-key key sap (+ +header+ (* mid recsize)) klen))
                   (setf lo (1+ mid))
                   (setf hi mid))))
    lo))

(defun find-record (m f count recsize key klen)
  "Index of the record of the mapping M (fence F) whose KLEN-byte key equals KEY, or NIL."
  (let ((i (lower-bound m f count recsize key klen)))
    (declare (type fixnum i))
    (and (< i count) (zerop (cmp-key key (mapping-sap m) (+ +header+ (* i recsize)) klen)) i)))

(defun snap-account (s addr)
  "(values found nonce balance codehash exists-empty) for ADDR (an integer)."
  (let ((i (find-record (snap-acct s) (snap-acct-fence s) (snap-n-accounts s) +acct-rec+
                        (int->octets addr 20) 20)))
    (if (null i)
        (values nil 0 0 +empty-code-hash+ nil)
        (let ((sap (mapping-sap (snap-acct s))) (off (+ +header+ (* i +acct-rec+))))
          (values t (sap-be sap (+ off 24) 8) (sap-be sap (+ off 32) 32) (sap-be sap (+ off 64) 32)
                  (logtest +flag-exists-empty+ (sap-be sap (+ off 20) 4)))))))

(defun slot-key (addr slot)
  (let ((k (make-array 52 :element-type '(unsigned-byte 8))))
    (put-be k 0 addr 20) (put-be k 20 slot 32) k))

(defun snap-slot (s addr slot)
  "The value of ADDR's SLOT, 0 when absent."
  (let ((i (find-record (snap-slot-map s) (snap-slot-fence s) (snap-n-slots s) +slot-rec+
                        (slot-key addr slot) 52)))
    (if i (sap-be (mapping-sap (snap-slot-map s)) (+ +header+ (* i +slot-rec+) 52) 32) 0)))

(defun first-slot-of (s addr)
  "Index of the first storage record of ADDR (or where it would be)."
  (lower-bound (snap-slot-map s) (snap-slot-fence s) (snap-n-slots s) +slot-rec+ (slot-key addr 0) 52))

(defun snap-has-storage-p (s addr)
  (let ((i (first-slot-of s addr)))
    (and (< i (snap-n-slots s))
         (zerop (cmp-key (int->octets addr 20) (mapping-sap (snap-slot-map s)) (+ +header+ (* i +slot-rec+)) 20)))))

(defun snap-code (s codehash)
  "The code (a fresh octet vector) whose keccak is CODEHASH, or NIL."
  (when (= codehash +empty-code-hash+) (return-from snap-code (make-array 0 :element-type '(unsigned-byte 8))))
  (let ((i (find-record (snap-code-idx s) nil (snap-n-codes s) 40 (int->octets codehash 32) 32)))
    (when i
      (let* ((off (sap-be (mapping-sap (snap-code-idx s)) (+ +header+ (* i 40) 32) 8))
             (csap (mapping-sap (snap-code-map s)))
             (len (sap-be csap (+ +header+ off 32) 4))
             (v (make-array len :element-type '(unsigned-byte 8))))
        (dotimes (i len v) (setf (aref v i) (sb-sys:sap-ref-8 csap (+ +header+ off 36 i))))))))

(defun snap-map-accounts (s fn)
  "FN (addr nonce balance codehash exists-empty) for every account, in addr order."
  (let ((sap (mapping-sap (snap-acct s))))
    (setf (mapping-released (snap-acct s)) 0)
    (dotimes (i (snap-n-accounts s))
      (let ((off (+ +header+ (* i +acct-rec+))))
        (funcall fn (sap-be sap off 20) (sap-be sap (+ off 24) 8) (sap-be sap (+ off 32) 32)
                 (sap-be sap (+ off 64) 32) (logtest +flag-exists-empty+ (sap-be sap (+ off 20) 4)))
        (release-behind (snap-acct s) off)))
    (release-all (snap-acct s))))

(defun snap-map-storage (s fn)
  "FN (addr slot value) for every slot, in (addr, slot) order."
  (let ((sap (mapping-sap (snap-slot-map s))))
    (setf (mapping-released (snap-slot-map s)) 0)
    (dotimes (i (snap-n-slots s))
      (let ((off (+ +header+ (* i +slot-rec+))))
        (funcall fn (sap-be sap off 20) (sap-be sap (+ off 20) 32) (sap-be sap (+ off 52) 32))
        (release-behind (snap-slot-map s) off)))
    (release-all (snap-slot-map s))))

(defun snap-map-account-storage (s addr fn)
  "FN (slot value) for ADDR's slots, in slot order."
  (let ((sap (mapping-sap (snap-slot-map s))) (key (int->octets addr 20)))
    (loop for i from (first-slot-of s addr) below (snap-n-slots s)
          for off = (+ +header+ (* i +slot-rec+))
          while (zerop (cmp-key key sap off 20))
          do (funcall fn (sap-be sap (+ off 20) 32) (sap-be sap (+ off 52) 32)))))

(defun snap-map-codes (s fn)
  "FN (codehash offset length sap) for every code blob, in codehash order; the bytes are
   at SAP+OFFSET (no copy)."
  (let ((isap (mapping-sap (snap-code-idx s))) (csap (mapping-sap (snap-code-map s))))
    (dotimes (i (snap-n-codes s))
      (let* ((off (sap-be isap (+ +header+ (* i 40) 32) 8))
             (len (sap-be csap (+ +header+ off 32) 4)))
        (funcall fn (sap-be isap (+ +header+ (* i 40)) 32) (+ +header+ off 36) len csap)))
    (release-all (snap-code-idx s))
    (release-all (snap-code-map s))))

;;; ---------------------------------------------------------------- layers: lookup
;;;
;;; A stack is LAYERS (newest first) over BASE (a base snap, or NIL for the empty state).
;;; A layer is a layer snap, or a FOREIGN layer: the replay's frozen RAM layers, answered
;;; through *FOREIGN-LAYER* (snapshot-world.lisp), so the walk below is the one reader
;;; for both. Lean: `lookupAcct`, `lookupSlot`, `mat` (Evm.Persist.Layered).

(defvar *foreign-layer* nil
  "NIL, or a function (op layer &rest args) answering for a layer that is not a snap:
   (:account l addr) -> (values present nonce balance codehash mark code), CODE the
                        code octets when the layer holds them (else NIL: by CODEHASH)
   (:slot l addr slot) -> (values present value wiped)
   (:map-slots l addr fn) -> wiped (FN (slot value) for every slot it holds)
   (:code l hash) -> octets or NIL")

;;; Bloom filter over a layer's addresses, k = 3, about 16 bits per address: a lookup
;;; for an address the layer does not mention (almost all of them) costs three bit tests.
(defstruct (bloom (:constructor %make-bloom (bits mask)))
  (bits nil :type simple-bit-vector) (mask 0 :type fixnum))

(declaim (inline bloom-h))
(defun bloom-h (addr)
  "Two hashes of the 160-bit integer ADDR (double hashing gives the three probes)."
  (let* ((lo (ldb (byte 62 0) addr)) (hi (ldb (byte 62 62) addr)) (top (ldb (byte 36 124) addr))
         (a (ldb (byte 62 0) (* (logxor lo (* 31 top)) #x9E3779B97F4A7C15)))
         (b (logior 1 (ldb (byte 62 0) (* (logxor hi (* 131 top)) #xC2B2AE3D27D4EB4F)))))
    (values (ash a -11) (ash b -11))))

(defun bloom-add (bl addr)
  (multiple-value-bind (a b) (bloom-h addr)
    (dotimes (i 3) (setf (sbit (bloom-bits bl) (logand (+ a (* i b)) (bloom-mask bl))) 1))))

(defun bloom-maybe-p (bl addr)
  (or (null bl)
      (multiple-value-bind (a b) (bloom-h addr)
        (dotimes (i 3 t)
          (when (zerop (sbit (bloom-bits bl) (logand (+ a (* i b)) (bloom-mask bl)))) (return nil))))))

(defun build-bloom (s)
  (let* ((n (snap-n-accounts s))
         (m (max 1024 (ash 1 (integer-length (* 16 n)))))
         (bl (%make-bloom (make-array m :element-type 'bit :initial-element 0) (1- m)))
         (sap (mapping-sap (snap-acct s))))
    (dotimes (i n bl)
      (bloom-add bl (sap-be sap (+ +header+ (* i +acct-rec+)) 20)))))

(defun layer-account (s addr)
  "(values present nonce balance codehash mark wiped) for ADDR in the layer snap S."
  (when (bloom-maybe-p (snap-bloom s) addr)
    (let ((i (find-record (snap-acct s) (snap-acct-fence s) (snap-n-accounts s) +acct-rec+
                          (int->octets addr 20) 20)))
      (when i
        (let* ((sap (mapping-sap (snap-acct s))) (off (+ +header+ (* i +acct-rec+)))
               (flags (sap-be sap (+ off 20) 4)))
          (values t (sap-be sap (+ off 24) 8) (sap-be sap (+ off 32) 32) (sap-be sap (+ off 64) 32)
                  (logtest +flag-exists-empty+ flags) (logtest +flag-wiped+ flags)))))))

(defun layer-slot (s addr slot)
  "(values present value wiped) for ADDR's SLOT in the layer snap S: PRESENT when the layer
   sets it (VALUE may be 0), else WIPED when the layer removed ADDR's storage below it."
  (if (not (bloom-maybe-p (snap-bloom s) addr))
      (values nil 0 nil)
      (let ((i (find-record (snap-slot-map s) (snap-slot-fence s) (snap-n-slots s) +slot-rec+
                            (slot-key addr slot) 52)))
        (if i
            (values t (sap-be (mapping-sap (snap-slot-map s)) (+ +header+ (* i +slot-rec+) 52) 32) nil)
            (values nil 0 (nth-value 5 (layer-account s addr)))))))

(defun layer-map-slots (s addr fn)
  "FN (slot value) for every slot record of ADDR in the layer snap S (zeros included).
   Returns whether the layer wiped ADDR's storage below it."
  (when (bloom-maybe-p (snap-bloom s) addr)
    (snap-map-account-storage s addr fn)
    (nth-value 5 (layer-account s addr))))

(defun layer-op (op l &rest args)
  (if (snap-p l)
      (ecase op
        ;; the protocol's sixth value is the account's CODE (a RAM layer has it); a disk
        ;; layer's is NIL: `layer-account`'s sixth is its WIPED flag, which taken as code
        ;; installed T as an account's code (trial at 11,090,602)
        (:account (multiple-value-bind (present nonce balance codehash mark) (layer-account l (first args))
                    (values present nonce balance codehash mark nil)))
        (:slot (layer-slot l (first args) (second args)))
        (:map-slots (layer-map-slots l (first args) (second args)))
        (:code (snap-code l (first args))))
      (apply *foreign-layer* op l args)))

(defun lookup-account (layers base addr)
  "Lean `lookupAcct`: (values present nonce balance codehash mark code) from the newest
   layer that mentions ADDR, else from BASE (whose mark is its exists-empty flag)."
  (dolist (l layers (if base (snap-account base addr) (values nil 0 0 +empty-code-hash+ nil)))
    (multiple-value-bind (present nonce balance codehash mark code) (layer-op :account l addr)
      (when present (return (values t nonce balance codehash mark code))))))

(defun s1-included-p (nonce balance codehash has-storage mark)
  "The inclusion rule S1 (Lean `mat`): an account is in the state iff it is non-empty, has
   storage, or carries the existence mark. Its stored flag is then `empty`."
  (or (plusp nonce) (plusp balance) (/= codehash +empty-code-hash+) has-storage mark))

(defun view-account (layers base addr)
  "Lean `view` at ADDR (the merged state, materialized): (values found nonce balance
   codehash exists-empty code), the shape of `snap-account` (CODE: see `lookup-account`).
   An address no layer mentions and
   BASE lacks has no storage either (every layer carries the fields of the addresses
   whose storage it touches, and BASE is materialized), so it is absent."
  (multiple-value-bind (present nonce balance codehash mark code) (lookup-account layers base addr)
    (let ((empty (and (zerop nonce) (zerop balance) (= codehash +empty-code-hash+))))
      (cond ((not present) (values nil 0 0 +empty-code-hash+ nil))
            ((not empty) (values t nonce balance codehash nil code))
            ((or mark (view-has-storage-p layers base addr)) (values t 0 0 codehash t))
            (t (values nil 0 0 +empty-code-hash+ nil))))))

(defun view-slot (layers base addr slot)
  "Lean `lookupSlot`: the newest layer that sets SLOT decides; one that wiped ADDR's
   storage answers 0; else BASE."
  (dolist (l layers (if base (snap-slot base addr slot) 0))
    (multiple-value-bind (present value wiped) (layer-op :slot l addr slot)
      (cond (present (return value)) (wiped (return 0))))))

(defun view-code (layers base hash)
  "The code whose keccak is HASH from any layer or BASE (codes are content-addressed)."
  (or (dolist (l layers) (let ((c (layer-op :code l hash))) (when c (return c))))
      (and base (snap-code base hash))
      (and (= hash +empty-code-hash+) (make-array 0 :element-type '(unsigned-byte 8)))))

(defun view-map-account-storage (layers base addr fn)
  "FN (slot value) for every NONZERO slot of ADDR in the view, each slot once."
  (let ((seen (make-hash-table)))
    (flet ((visit (k v)
             (unless (gethash k seen)
               (setf (gethash k seen) t)
               (unless (zerop v) (funcall fn k v)))))
      (dolist (l layers)
        (when (layer-op :map-slots l addr #'visit)
          (return-from view-map-account-storage nil)))
      (when base (snap-map-account-storage base addr #'visit)))))

(defun view-has-storage-p (layers base addr)
  (view-map-account-storage layers base addr (lambda (k v) (declare (ignore k v))
                                               (return-from view-has-storage-p t)))
  nil)

;;; ---------------------------------------------------------------- layers: composing
;;;
;;; Lean `composeAll` / `apply` one address at a time, on raw records (no slot is decoded):
;;; minor compaction (layers -> one layer), major compaction (base + layers -> a base)
;;; and the layered root check all go through `compose-address`.

(defstruct (obuf (:constructor %make-obuf (sap cap)))
  ;; records at +HEADER+ + i*88, so the buffer reads like a mapped storage.dat. Outside
  ;; the Lisp heap: one account's slots can be gigabytes (20M+ slots), and a doubling
  ;; in-heap vector needs that much CONTIGUOUS free heap, which a fragmented heap lacks
  ;; (production 2026-10-27: 3 GB requested with 36 GB free). Freed by `obuf-free`.
  (sap (sb-sys:int-sap 0) :type sb-sys:system-area-pointer)
  (cap 0 :type fixnum)
  (count 0 :type fixnum))

(defun obuf-malloc (n)
  (let ((p (sb-alien:alien-funcall
            (sb-alien:extern-alien "realloc" (function sb-sys:system-area-pointer
                                                       sb-sys:system-area-pointer sb-alien:unsigned-long))
            (sb-sys:int-sap 0) n)))
    (when (zerop (sb-sys:sap-int p)) (error "obuf: malloc of ~D bytes failed" n))
    p))

(defun make-obuf ()
  (let ((cap (+ +header+ (* 1024 +slot-rec+)))) (%make-obuf (obuf-malloc cap) cap)))

(defun obuf-free (o)
  (unless (zerop (sb-sys:sap-int (obuf-sap o)))
    (sb-alien:alien-funcall (sb-alien:extern-alien "free" (function sb-alien:void sb-sys:system-area-pointer))
                            (obuf-sap o))
    (setf (obuf-sap o) (sb-sys:int-sap 0) (obuf-cap o) 0 (obuf-count o) 0)))

(defun obuf-room (o n)
  (let ((need (+ +header+ (* +slot-rec+ (+ (obuf-count o) n)))))
    (when (> need (obuf-cap o))
      (let* ((cap (max need (* 2 (obuf-cap o))))
             (p (sb-alien:alien-funcall
                 (sb-alien:extern-alien "realloc" (function sb-sys:system-area-pointer
                                                            sb-sys:system-area-pointer sb-alien:unsigned-long))
                 (obuf-sap o) cap)))
        (when (zerop (sb-sys:sap-int p)) (error "obuf: realloc to ~D bytes failed" cap))
        (setf (obuf-sap o) p (obuf-cap o) cap)))))

(defun zero-bytes-p (sap off n)
  (declare (type fixnum off n) (optimize (speed 3) (safety 0)))
  (dotimes (i n t) (unless (zerop (sb-sys:sap-ref-8 sap (+ off i))) (return nil))))

(defun copy-record (out sap off)
  (obuf-room out 1)
  (let ((d (obuf-sap out)) (p (+ +header+ (* (obuf-count out) +slot-rec+))))
    (declare (type fixnum p off))
    (dotimes (i +slot-rec+) (setf (sb-sys:sap-ref-8 d (+ p i)) (sb-sys:sap-ref-8 sap (+ off i))))
    (incf (obuf-count out))))

(defun acct-lower-bound (s key)
  "Index of the first account record of S whose address is >= KEY (20 octets)."
  (lower-bound (snap-acct s) (snap-acct-fence s) (snap-n-accounts s) +acct-rec+ key 20))

(defun map-touched-addresses (layers fn &key lo hi)
  "FN (addr) for every address some layer of LAYERS (snaps) mentions, ascending, each
   once; only addresses in [LO, HI) when given (integers; HI NIL: no bound)."
  (let* ((n (length layers))
         (cur (make-array n :element-type 'fixnum :initial-element 0))
         (saps (map 'vector (lambda (l) (mapping-sap (snap-acct l))) layers))
         (ends (map 'vector #'snap-n-accounts layers))
         (hikey (and hi (int->octets hi 20))))
    (when lo
      (loop for l in layers for i from 0 do (setf (aref cur i) (acct-lower-bound l (int->octets lo 20)))))
    (loop
      (let ((bi -1) (boff 0))
        (dotimes (i n)                  ; the smallest address under the cursors
          (when (< (aref cur i) (aref ends i))
            (let ((off (+ +header+ (* (aref cur i) +acct-rec+))))
              (when (or (< bi 0) (minusp (cmp-sap* (aref saps i) off (aref saps bi) boff 20)))
                (setf bi i boff off)))))
        (when (or (< bi 0) (and hikey (not (plusp (cmp-key hikey (aref saps bi) boff 20)))))
          (return))
        (let* ((bsap (aref saps bi)) (addr (sap-be bsap boff 20)))
          (dotimes (i n)
            (when (and (< (aref cur i) (aref ends i))
                       (zerop (cmp-sap* (aref saps i) (+ +header+ (* (aref cur i) +acct-rec+)) bsap boff 20)))
              (incf (aref cur i))))
          (funcall fn addr))))))

(defun slot-run (s addr)
  "(values start end): the indices of ADDR's slot records in S."
  (let* ((i (first-slot-of s addr)) (j i) (n (snap-n-slots s))
         (key (int->octets addr 20)) (sap (mapping-sap (snap-slot-map s))))
    (loop while (and (< j n) (zerop (cmp-key key sap (+ +header+ (* j +slot-rec+)) 20))) do (incf j))
    (values i j)))

(defun compose-address (layers base addr out &key final)
  "Lean `composeAll` (FINAL NIL) or `apply` over BASE (FINAL true) at ADDR, on raw
   records. LAYERS: layer snaps, newest first; BASE: a base snap or NIL. Writes ADDR's
   slot records (ascending; zeros kept unless FINAL) into the obuf OUT and returns
   (values fields wiped): FIELDS (nonce balance codehash mark) from the newest layer that
   mentions ADDR, else (FINAL) BASE's record, else NIL; WIPED: some layer removed the
   storage below it (BASE's slots are then not read)."
  (setf (obuf-count out) 0)
  (let ((runs '()) (fields nil) (wiped nil))
    (dolist (l layers)
      (multiple-value-bind (present nonce balance codehash mark w) (layer-account l addr)
        (when present
          (unless fields (setf fields (list nonce balance codehash mark)))
          (multiple-value-bind (i j) (slot-run l addr)
            (when (< i j) (setf runs (nconc runs (list (vector (mapping-sap (snap-slot-map l)) i j))))))
          (when w (setf wiped t) (return)))))
    (when (and final base)
      (unless fields
        (multiple-value-bind (found nonce balance codehash flag) (snap-account base addr)
          (when found (setf fields (list nonce balance codehash flag)))))
      (unless wiped
        (multiple-value-bind (i j) (slot-run base addr)
          (when (< i j) (setf runs (nconc runs (list (vector (mapping-sap (snap-slot-map base)) i j))))))))
    ;; RUNS: newest first, BASE last; on equal keys the first (newest) run wins
    (let* ((runs (coerce runs 'simple-vector)) (k (length runs)))
      (loop
        (let ((best -1) (boff 0))
          (dotimes (q k)
            (let ((r (aref runs q)))
              (when (< (aref r 1) (aref r 2))
                (let ((off (+ +header+ (* (aref r 1) +slot-rec+) 20)))
                  (when (or (< best 0) (minusp (cmp-sap* (aref r 0) off (aref (aref runs best) 0) boff 32)))
                    (setf best q boff off))))))
          (when (< best 0) (return))
          (let* ((bsap (aref (aref runs best) 0)) (rec (- boff 20)))
            (unless (and final (zero-bytes-p bsap (+ rec 52) 32))
              (copy-record out bsap rec))
            (dotimes (q k)              ; every run at this key moves on (the newest won)
              (let ((r (aref runs q)))
                (when (and (< (aref r 1) (aref r 2))
                           (zerop (cmp-sap* (aref r 0) (+ +header+ (* (aref r 1) +slot-rec+) 20) bsap boff 32)))
                  (incf (aref r 1)))))))))
    (values fields wiped)))

;;; ---------------------------------------------------------------- compositions
;;;
;;; A resume point is a COMPOSITION: a base and the layers above it, oldest first, each
;;; with its content hash — (:base B hash) (:layer P N hash) ... An anchor line records
;;; it (as its hash field) so a resume loads exactly the bytes the root check read:
;;;   "s4900000.4659a9fe4981dc3e+l4900000-4902000.2b53b206b9fa6058"
;;; A bare hash (every anchor before layers) is the base snap at the anchor's block.
;;; Lean: `Comp`, `Point` (Evm.Persist.Layered, Part D).

(defun composition-string (comps)
  (if (and (= (length comps) 1) (eq (first (first comps)) :base))
      (third (first comps))             ; a lone base keeps the v1 form: its hash
      (format nil "~{~A~^+~}"
              (mapcar (lambda (c)
                        (ecase (first c)
                          (:base (format nil "s~D.~A" (second c) (third c)))
                          (:layer (format nil "l~D-~D.~A" (second c) (third c) (fourth c)))))
                      comps))))

(defun parse-composition (string block)
  "The components of STRING (an anchor's hash field) for an anchor at BLOCK; NIL STRING
   (an anchor from before content hashes): the base at BLOCK, hash unknown."
  (flet ((num (str a b) (parse-integer str :start a :end b)))
    (cond ((null string) (list (list :base block nil)))
          ((not (find #\. string)) (list (list :base block string)))
          (t (loop for part in (split-string string #\+)
                   for dot = (position #\. part)
                   collect (ecase (char part 0)
                             (#\s (list :base (num part 1 dot) (subseq part (1+ dot))))
                             (#\l (let ((dash (position #\- part)))
                                    (list :layer (num part 1 dash) (num part (1+ dash) dot)
                                          (subseq part (1+ dot)))))))))))

(defun split-string (s ch)
  (loop with start = 0
        for p = (position ch s :start start)
        collect (subseq s start p)
        while p do (setf start (1+ p))))

(defun component-path (dir comp)
  (ecase (first comp)
    (:base (snap-path dir (second comp)))
    (:layer (layer-path dir (second comp) (third comp)))))

(defun component-of (s)
  "The component an open snap S is, with its content hash."
  (let ((m (snap-manifest s)))
    (if (snap-layer-p s)
        (list :layer (getf m :parent) (getf m :block) (getf m :content-hash))
        (list :base (getf m :block) (getf m :content-hash)))))

;;; ---------------------------------------------------------------- the merge writer
;;;
;;; Usage: (make-merge tmpdir chain-id block root base) where BASE is an open snap or NIL;
;;; then MERGE-ACCOUNT for every changed account in strictly ascending addr order; then
;;; MERGE-FINISH with the new codes. Accounts and slots of BASE that are not mentioned are
;;; copied raw. An account given to MERGE-ACCOUNT replaces BASE's record and storage:
;;;   (merge-account m addr :fields F :slots SLOTS :wiped W)
;;;     F      NIL — account fields unchanged (BASE's record, if any, is kept as is);
;;;            or (nonce balance codehash in-world-accounts) — the RAM values
;;;     SLOTS  ascending list of (slot . value) that override BASE (value 0 = deleted)
;;;     W      true — BASE's slots of ADDR are all dead (storage wiped)
;;;   (merge-account m addr :fields F :raw-slots (SAP OFF COUNT))
;;;            ADDR's complete storage as COUNT sorted 88-byte records at SAP+OFF (the
;;;            importer, and major compaction: `compose-address` :final); BASE's slots of
;;;            ADDR are dropped
;;; Inclusion (S1, the dump rule, `s1-included-p`): an account with fields is written iff
;;; nonce>0, balance>0, code, any storage left after the merge, or in the existence set.
;;;
;;; A LAYER is written by the same writer with :PARENT P (no BASE): every record is kept as
;;; given — slots set to 0 too (tombstones) — and every address gets an account record
;;; carrying its fields (F is required: FieldsCover), the mark and the WIPED bit.

(defstruct (smerge (:constructor %make-merge) (:conc-name merge-))
  dir chain-id block root base parent
  accts slots
  (acct-i 0 :type fixnum) (slot-i 0 :type fixnum)
  (n-acct 0 :type fixnum) (n-slot 0 :type fixnum)
  (rec (make-array 96 :element-type '(unsigned-byte 8)) :type (simple-array (unsigned-byte 8) (*)))
  (last-addr -1))

(defun make-merge (dir chain-id block root base &key parent)
  "PARENT: write a layer over the state at block PARENT (no BASE)."
  (when (and parent base) (error "make-merge: a layer is written without a base"))
  (ensure-directories-exist (merge-pathnames "x" (pathname dir)))
  (%make-merge :dir (pathname dir) :chain-id chain-id :block block :root root :base base :parent parent
               :accts (make-out (merge-pathnames "accounts.dat" (pathname dir)))
               :slots (make-out (merge-pathnames "storage.dat" (pathname dir)))))

(defun emit-acct-raw (m sap off)
  (out-sap (merge-accts m) sap off +acct-rec+)
  (incf (merge-n-acct m)))

(defun emit-slot-raw (m sap off)
  (out-sap (merge-slots m) sap off +slot-rec+)
  (incf (merge-n-slot m)))

(defun emit-slot (m addr slot value)
  (let ((r (merge-rec m)))
    (fill r 0)
    (put-be r 0 addr 20) (put-be r 20 slot 32) (put-be r 52 value 32)
    (out-room (merge-slots m) +slot-rec+)
    (replace (out-buf (merge-slots m)) r :start1 (out-pos (merge-slots m)) :end2 +slot-rec+)
    (incf (out-pos (merge-slots m)) +slot-rec+)
    (incf (merge-n-slot m))))

(defun emit-acct (m addr nonce balance codehash flags)
  "FLAGS: T (exists-empty), NIL, or the flag word."
  (let ((r (merge-rec m)))
    (fill r 0)
    (put-be r 0 addr 20) (put-be r 20 (case flags ((t) +flag-exists-empty+) ((nil) 0) (t flags)) 4)
    (put-be r 24 nonce 8) (put-be r 32 balance 32) (put-be r 64 codehash 32)
    (out-room (merge-accts m) +acct-rec+)
    (replace (out-buf (merge-accts m)) r :start1 (out-pos (merge-accts m)))
    (incf (out-pos (merge-accts m)) +acct-rec+)
    (incf (merge-n-acct m))))

(defun copy-base-upto (m key)
  "Copy BASE's accounts and slots whose address (20 octets) sorts below KEY (NIL: all
   of them) unchanged. Compares raw bytes: no record is decoded."
  (let ((base (merge-base m)))
    (when base
      (let ((asap (mapping-sap (snap-acct base))) (ssap (mapping-sap (snap-slot-map base)))
            (na (snap-n-accounts base)) (ns (snap-n-slots base)))
        (loop for i = (merge-acct-i m)
              while (and (< i na)
                         (or (null key) (plusp (cmp-key key asap (+ +header+ (* i +acct-rec+)) 20))))
              do (emit-acct-raw m asap (+ +header+ (* i +acct-rec+)))
                 (incf (merge-acct-i m)))
        (loop for i = (merge-slot-i m)
              while (and (< i ns)
                         (or (null key) (plusp (cmp-key key ssap (+ +header+ (* i +slot-rec+)) 20))))
              do (emit-slot-raw m ssap (+ +header+ (* i +slot-rec+)))
                 (incf (merge-slot-i m)))
        (release-behind (snap-acct base) (+ +header+ (* (merge-acct-i m) +acct-rec+)))
        (release-behind (snap-slot-map base) (+ +header+ (* (merge-slot-i m) +slot-rec+)))))))

(defun base-at-key-p (base kind i key)
  "BASE's KIND record I exists and its address is KEY."
  (ecase kind
    (:acct (and (< i (snap-n-accounts base))
                (zerop (cmp-key key (mapping-sap (snap-acct base)) (+ +header+ (* i +acct-rec+)) 20))))
    (:slot (and (< i (snap-n-slots base))
                (zerop (cmp-key key (mapping-sap (snap-slot-map base)) (+ +header+ (* i +slot-rec+)) 20))))))

(defun merge-account (m addr &key fields slots wiped raw-slots)
  (unless (> addr (merge-last-addr m))
    (error "merge-account: ~X after ~X — accounts must come in ascending order" addr (merge-last-addr m)))
  (setf (merge-last-addr m) addr)
  (cond ((merge-parent m) (merge-layer-account m addr fields slots wiped raw-slots))
        (raw-slots (merge-account-raw m addr fields raw-slots))
        (t (merge-account-1 m addr fields slots wiped))))

(defun emit-fields (m addr fields has-storage)
  "ADDR's record from FIELDS (nonce balance codehash mark) under S1."
  (destructuring-bind (nonce balance codehash mark) fields
    (when (s1-included-p nonce balance codehash has-storage mark)
      (emit-acct m addr nonce balance codehash
                 (and (zerop nonce) (zerop balance) (= codehash +empty-code-hash+))))))

(defun merge-layer-account (m addr fields slots wiped raw-slots)
  (unless fields (error "layer record for ~X without its fields (FieldsCover)" addr))
  (if raw-slots
      (destructuring-bind (sap off count) raw-slots
        (dotimes (i count) (emit-slot-raw m sap (+ off (* i +slot-rec+)))))
      (dolist (kv slots) (emit-slot m addr (car kv) (cdr kv))))
  (destructuring-bind (nonce balance codehash mark) fields
    (emit-acct m addr nonce balance codehash
               (logior (if mark +flag-exists-empty+ 0) (if wiped +flag-wiped+ 0)))))

(defun merge-account-raw (m addr fields raw-slots)
  (let ((key (int->octets addr 20)) (base (merge-base m)))
    (copy-base-upto m key)
    (when base                          ; BASE's record and slots of ADDR are replaced
      (when (base-at-key-p base :acct (merge-acct-i m) key) (incf (merge-acct-i m)))
      (loop while (base-at-key-p base :slot (merge-slot-i m) key) do (incf (merge-slot-i m))))
    (destructuring-bind (sap off count) raw-slots
      (dotimes (i count) (emit-slot-raw m sap (+ off (* i +slot-rec+))))
      (if fields
          (emit-fields m addr fields (plusp count))
          (when (plusp count) (emit-acct m addr 0 0 +empty-code-hash+ t))))))

(defun merge-account-1 (m addr fields slots wiped)
  (let ((key (int->octets addr 20)))
  (copy-base-upto m key)
  (let* ((base (merge-base m))
         (base-acct (and base (base-at-key-p base :acct (merge-acct-i m) key) (merge-acct-i m)))
         (n-before (merge-n-slot m)))
    ;; storage: BASE's slots of ADDR (unless wiped) merged with SLOTS
    (let ((ssap (and base (mapping-sap (snap-slot-map base)))) (rest slots))
      (loop while (and base (base-at-key-p base :slot (merge-slot-i m) key))
            do (let* ((off (+ +header+ (* (merge-slot-i m) +slot-rec+)))
                      (bslot (sap-be ssap (+ off 20) 32)))
                 ;; RAM slots below this base slot come first
                 (loop while (and rest (< (car (first rest)) bslot))
                       do (let ((kv (pop rest)))
                            (unless (zerop (cdr kv)) (emit-slot m addr (car kv) (cdr kv)))))
                 (cond ((and rest (= (car (first rest)) bslot))
                        (let ((kv (pop rest)))
                          (unless (zerop (cdr kv)) (emit-slot m addr (car kv) (cdr kv)))))
                       (wiped)
                       (t (emit-slot-raw m ssap off)))
                 (incf (merge-slot-i m))))
      (dolist (kv rest)
        (unless (zerop (cdr kv)) (emit-slot m addr (car kv) (cdr kv)))))
    (let ((has-storage (> (merge-n-slot m) n-before)))
      (if (null fields)
          ;; account unchanged: BASE's record as is (or, absent there, one the storage forces)
          (cond (base-acct (emit-acct-raw m (mapping-sap (snap-acct base)) (+ +header+ (* base-acct +acct-rec+))))
                (has-storage (emit-acct m addr 0 0 +empty-code-hash+ t)))
          (emit-fields m addr fields has-storage)))
    (when base-acct (incf (merge-acct-i m))))))

(defun merge-finish (m codes &key provenance)
  "Copy the rest of BASE, write the code table (BASE's codes plus CODES: an alist of
   (codehash . octets), any order, duplicates ignored), its index and the manifest.
   Returns the manifest. The directory is complete but not yet published. A code's
   octets may be a function of no arguments returning them."
  (copy-base-upto m nil)
  (when (merge-base m)
    (release-all (snap-acct (merge-base m)))
    (release-all (snap-slot-map (merge-base m))))
  (let* ((dir (merge-dir m)) (base (merge-base m))
         (cid (merge-chain-id m)) (blk (merge-block m))
         (files '())
         (acct (out-close (merge-accts m) 1 (merge-n-acct m) +acct-rec+ 0 cid blk))
         (slot (out-close (merge-slots m) 2 (merge-n-slot m) +slot-rec+ 0 cid blk)))
    (push (list* "accounts.dat" acct) files)
    (push (list* "storage.dat" slot) files)
    ;; code: BASE's (in hash order) merged with the new ones
    (let* ((new (sort (remove-duplicates (copy-list codes) :key #'car :test #'=) #'< :key #'car))
           (o (make-out (merge-pathnames "code.dat" dir)))
           (idx (make-array 0 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0))
           (n 0) (hdr (make-array 36 :element-type '(unsigned-byte 8))))
      (flet ((note (hash)
               (loop for b across (int->octets hash 32) do (vector-push-extend b idx))
               (loop for b across (int->octets (out-bytes-total o) 8) do (vector-push-extend b idx))
               (incf n))
             (pad ()
               (let ((r (mod (out-bytes-total o) 8)))
                 (unless (zerop r) (out-octets o (make-array (- 8 r) :element-type '(unsigned-byte 8) :initial-element 0))))))
        (flet ((put-new (hash bytes)
                 (when (functionp bytes) (setf bytes (funcall bytes)))   ; supplied lazily (importer)
                 (note hash)
                 (put-be hdr 0 hash 32) (put-be hdr 32 (length bytes) 4)
                 (out-octets o hdr) (out-octets o (coerce bytes '(simple-array (unsigned-byte 8) (*)))) (pad)))
          (when base
            (snap-map-codes base
                            (lambda (hash off len sap)
                              (loop while (and new (< (car (first new)) hash))
                                    do (let ((c (pop new))) (put-new (car c) (cdr c))))
                              (when (and new (= (car (first new)) hash)) (pop new))
                              (note hash)
                              (out-sap o sap (- off 36) (+ 36 len)) (pad))))
          (dolist (c new) (put-new (car c) (cdr c)))))
      (push (list* "code.dat" (out-close o 3 n 0 0 cid blk)) files)
      (let ((oi (make-out (merge-pathnames "code.idx" dir))))
        (out-octets oi (coerce idx '(simple-array (unsigned-byte 8) (*))))
        (push (list* "code.idx" (out-close oi 6 n 0 0 cid blk)) files))
      (let ((manifest (list* :version 1 :chain-id cid :block blk :state-root (merge-root m)
                             (append
                              (and (merge-parent m) (list :kind :layer :parent (merge-parent m)))
                              (list
                            :counts (list :accounts (merge-n-acct m) :slots (merge-n-slot m) :codes n)
                            :files (sort (nreverse files) #'string< :key #'first)
                            :provenance (or provenance "")
                            :created (multiple-value-bind (s mi h d mo y) (decode-universal-time (get-universal-time) 0)
                                       (format nil "~4,'0D-~2,'0D-~2,'0DT~2,'0D:~2,'0D:~2,'0DZ" y mo d h mi s)))))))
        (setf manifest (append manifest (list :content-hash (snap-content-hash manifest))))
        (with-open-file (f (merge-pathnames "MANIFEST.sexp" dir) :direction :output
                                                                 :if-exists :supersede :if-does-not-exist :create)
          (let ((*print-pretty* nil) (*print-case* :downcase)) (prin1 manifest f) (terpri f))
          (finish-output f)
          (sb-posix:fsync (sb-sys:fd-stream-fd f)))
        (fsync-path dir)
        manifest))))

(defun snap-publish (parent n tmpdir &key (final (snap-path parent n)))
  "Rename the finished TMPDIR to FINAL (default PARENT/snap-N) atomically (an existing one
   is moved aside first and deleted after), then fsync PARENT. Returns the final path."
  (let* ((fin (string-right-trim "/" (namestring final)))
         (old (format nil "~A/.old-~A" (string-right-trim "/" (namestring (pathname parent)))
                      (subseq fin (1+ (position #\/ fin :from-end t))))))
    (when (probe-file final) ; @veil snap-publish/probe
      (sb-posix:rename fin old)) ; @veil snap-publish/aside
    (sb-posix:rename (string-right-trim "/" (namestring tmpdir)) fin) ; @veil snap-publish/rename
    (fsync-path parent)
    (when (probe-file old)
      (sb-ext:run-program "rm" (list "-rf" old) :search t))
    final))

(defun write-composed (tmpdir chain-id block root layers base &key parent provenance)
  "Compaction, written to TMPDIR (not published). LAYERS: layer snaps, newest first.
   PARENT NIL (major): the base at BLOCK = BASE with LAYERS applied (Lean `view`: S1 on
   the merged state); PARENT P (minor): one layer over block P = LAYERS composed (Lean
   `composeAll`). Returns the manifest."
  (let ((m (make-merge tmpdir chain-id block root (and (null parent) base) :parent parent))
        (out (make-obuf)) (codes '()))
    (unwind-protect
         (map-touched-addresses
          layers
          (lambda (addr)
            (multiple-value-bind (fields wiped) (compose-address layers base addr out :final (null parent))
              (merge-account m addr :fields fields :wiped wiped
                                    :raw-slots (list (obuf-sap out) +header+ (obuf-count out))))))
      (obuf-free out))
    (dolist (l layers)
      (snap-map-codes l (lambda (hash off len sap)
                          (let ((v (make-array len :element-type '(unsigned-byte 8))))
                            (dotimes (i len) (setf (aref v i) (sb-sys:sap-ref-8 sap (+ off i))))
                            (push (cons hash v) codes)))))
    (merge-finish m codes :provenance provenance)))
