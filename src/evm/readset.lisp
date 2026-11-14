;;;; evm/readset.lisp — the read-set recorder: what each transaction read, per block, into
;;;; segment files (docs/readset-format.md, version 1).
;;;;
;;;; EITA_READSET_DIR=<dir> turns it on: a subscriber of the event stream (evm/stream.lisp)
;;;; that takes the storage view's accesses (state/world.lisp: reads, writes, deltas; the
;;;; callbacks add :codehash and :blockhash). Per tx it
;;;; keeps each account once with the fields read (and whether it was written), each slot
;;;; once (and whether it was written), the code read by hash, the block hashes read. A
;;;; segment holds the blocks of one +readset-segment+ range up to a layer point, and at most
;;;; *readset-segment-keys* accounts and slots (a segment's tables are its memory; the cut is
;;;; at a block boundary): it is written then, at the range's end, at every checkpoint and
;;;; at the end of the run, streamed into the file (no copy of the segment), and made
;;;; durable — with every segment written since the last — only at the latter two (before
;;;; the layer at N is published, so an anchor implies its read sets; a crash restarts at an
;;;; anchor, and the run drops the segments from its first block on). Off: one test per tx.
;;;; Nothing here steers execution; it runs on its own thread.

(in-package #:eita.evm)

(defconstant +readset-segment+ 10000 "Blocks per segment range.")
(defvar *readset-segment-keys* (ash 1 19)
  "Accounts + slots after which a segment is cut at the next block (~60 MB of tables).")
(defconstant +rs-written+ 128 "Account mask bit: the tx wrote a field of the account.")

(defun rs-mask-bit (kind)
  (ecase kind (:balance 1) (:nonce 2) (:code 4) (:codehash 8) (:present 16)))

;;; An octet sink: a growing buffer, or (with GZ) a fixed one written to a gzip stream when full.
(defstruct (obuf (:constructor make-obuf (size &optional gz)))
  (vec (make-array size :element-type '(unsigned-byte 8)) :type (simple-array (unsigned-byte 8) (*)))
  (fill 0 :type fixnum) gz)

(cffi:defcfun ("gzwrite" %gzwrite) :int (f :pointer) (buf :pointer) (len :unsigned-int))
(defun ob-write-gz (gz v n)
  (unless (= (cffi:with-pointer-to-vector-data (p v) (%gzwrite gz p n)) n) (error "readset: gzwrite failed")))
(defun ob-flush (o)
  (when (plusp (obuf-fill o)) (ob-write-gz (obuf-gz o) (obuf-vec o) (obuf-fill o)) (setf (obuf-fill o) 0)))
(declaim (inline ob-byte))
(defun ob-byte (o x)
  (let ((i (obuf-fill o)) (v (obuf-vec o)))
    (when (= i (length v))
      (if (obuf-gz o)
          (progn (ob-flush o) (setf i 0))
          (setf v (replace (make-array (* 2 i) :element-type '(unsigned-byte 8)) v) (obuf-vec o) v)))
    (setf (aref v i) x (obuf-fill o) (1+ i))))

(defun rs-put-varint (buf n)
  (loop (if (< n 128) (return (ob-byte buf n))
            (progn (ob-byte buf (logior 128 (logand n 127))) (setf n (ash n -7))))))
(defun rs-put-int (buf n bytes)
  "N's low BYTES bytes, big-endian."
  (loop for i from (1- bytes) downto 0 do (ob-byte buf (ldb (byte 8 (* 8 i)) n))))
(defun rs-varint-length (n) (max 1 (ceiling (integer-length n) 7)))

(defstruct (rs (:constructor make-rs (dir)))
  dir (range -1) (first nil) (last nil) (prev 0)
  (accts (make-hash-table)) (acct-keys (make-array 0 :adjustable t :fill-pointer 0))
  (slots (make-hash-table)) (slot-keys (make-array 0 :adjustable t :fill-pointer 0)) ; key: account id << 256 | slot
  (codes (make-hash-table)) (code-keys (make-array 0 :adjustable t :fill-pointer 0))
  (code-memo (make-hash-table :test 'eq))
  (buf (make-obuf 4096))
  (marks '())                                     ; (block . buf offset), newest first
  (unsynced '())                                  ; segment paths written since the last durable flush
  (block nil) (tx nil) (started nil)
  (tx-accts (make-hash-table)) (tx-codes (make-hash-table)) (tx-slots (make-hash-table)) (tx-bh '()))

(defun rs-keys (r) (+ (fill-pointer (rs-acct-keys r)) (fill-pointer (rs-slot-keys r))))

(defun rs-intern (table keys key)
  (or (gethash key table)
      (setf (gethash key table) (vector-push-extend key keys))))

(defun rs-end-tx (r)
  "The current tx's record into the segment buffer: accounts, slots, block hashes, each by
   ascending id as deltas (docs/readset-format.md)."
  (when (rs-tx r)
    (let ((b (rs-buf r)))
      (rs-put-varint b (+ (rs-tx r) 2))           ; +preblock-tx+ (-1) is 1, tx 0 is 2
      (flet ((ids (h) (sort (loop for k being the hash-keys of h collect k) #'<)))
        (let ((ids (ids (rs-tx-accts r))) (prev 0))
          (rs-put-varint b (length ids))
          (dolist (id ids)
            (let ((mask (gethash id (rs-tx-accts r))))
              (rs-put-varint b (- id prev)) (ob-byte b mask) (setf prev id)
              (when (logtest mask 4) (rs-put-varint b (gethash id (rs-tx-codes r)))))))
        (let ((ids (ids (rs-tx-slots r))) (prev 0))
          (rs-put-varint b (length ids))
          (dolist (id ids)
            (rs-put-varint b (logior (ash (- id prev) 1) (gethash id (rs-tx-slots r)))) (setf prev id))))
      (let ((bh (sort (remove-duplicates (rs-tx-bh r)) #'>)))
        (rs-put-varint b (length bh))
        (dolist (n bh) (rs-put-varint b (- (rs-block r) n)))))
    (clrhash (rs-tx-accts r)) (clrhash (rs-tx-codes r)) (clrhash (rs-tx-slots r))
    (setf (rs-tx-bh r) '() (rs-tx r) nil)))

(defun rs-end-block (r)
  (rs-end-tx r)
  (when (rs-block r)
    (ob-byte (rs-buf r) 0)                        ; the block's txs end
    (setf (rs-last r) (rs-block r) (rs-block r) nil)))

(defun rs-segment-path (r first last)
  (format nil "~A~10,'0D-~10,'0D.rset" (rs-dir r) first last))

(defun rs-segments (r)
  "(first last path) of every segment file in the directory."
  (loop for p in (directory (concatenate 'string (rs-dir r) "*.rset"))
        for name = (pathname-name p) for dash = (position #\- name)
        when dash collect (list (parse-integer name :end dash) (parse-integer name :start (1+ dash)) p)))

(defun rs-drop-from! (r n)
  "Delete the segment files whose first block is N or later (a run re-records them)."
  (loop for (first nil p) in (rs-segments r) when (>= first n) do (delete-file p)))

(defun rs-flush! (r &optional durable)
  "Write the segment (its blocks first..last) and start an empty one; with DURABLE, fsync it,
   every segment written since the last durable flush, and the directory. Each section's
   length is computed first, so the encoding streams into the file through one small buffer."
  (rs-end-block r)
  (when (rs-first r)
    (let* ((path (rs-segment-path r (rs-first r) (rs-last r)))
           (tmp (concatenate 'string path ".tmp"))
           (f (eita.input::%gzopen tmp "wb6"))
           (out (make-obuf 65536 f)))
      (when (cffi:null-pointer-p f) (error "readset: gzopen ~A failed" tmp))
      (unwind-protect
           (let ((accts (rs-acct-keys r)) (slots (rs-slot-keys r)) (codes (rs-code-keys r)))
             (flet ((section (tag len) (ob-byte out tag) (rs-put-varint out len)))
               (map nil (lambda (c) (ob-byte out (char-code c))) "ERS")
               (ob-byte out 1)                    ; format version
               (rs-put-int out (rs-first r) 8) (rs-put-int out (rs-last r) 8)
               (section 1 (+ (rs-varint-length (length accts)) (* 20 (length accts))))
               (rs-put-varint out (length accts))
               (loop for a across accts do (rs-put-int out a 20))
               (section 2 (+ (rs-varint-length (length slots))
                             (loop for k across slots sum (+ 32 (rs-varint-length (ash k -256))))))
               (rs-put-varint out (length slots))
               (loop for k across slots do (rs-put-varint out (ash k -256)) (rs-put-int out k 32))
               (section 3 (+ (rs-varint-length (length codes)) (* 32 (length codes))))
               (rs-put-varint out (length codes))
               (loop for h across codes do (rs-put-int out h 32))
               (let ((b (rs-buf r)))
                 (section 4 (obuf-fill b))
                 (ob-flush out)
                 (when (plusp (obuf-fill b)) (ob-write-gz f (obuf-vec b) (obuf-fill b))))
               (ob-flush out)))
        (eita.input::%gzclose f))
      (sb-posix:rename tmp path)
      (push path (rs-unsynced r))))
  (when (and durable (rs-unsynced r))
    (dolist (p (cons (rs-dir r) (rs-unsynced r)))      ; one a rollback deleted: skipped
      (let ((fd (ignore-errors (sb-posix:open p sb-posix:o-rdonly))))
        (when fd (unwind-protect (sb-posix:fsync fd) (sb-posix:close fd)))))
    (setf (rs-unsynced r) '()))
  (let ((next (make-rs (rs-dir r))))            ; the next segment: the same range, run
    (setf (rs-range next) (rs-range r) (rs-started next) (rs-started r) (rs-unsynced next) (rs-unsynced r))
    next))

(defun rs-code-id (r code)
  (rs-intern (rs-codes r) (rs-code-keys r)
             (or (gethash code (rs-code-memo r))
                 (setf (gethash code (rs-code-memo r))
                       (let ((h 0)) (loop for x across (keccak256-bytes code) do (setf h (logior (ash h 8) x))) h)))))

(defun make-readset-recorder (dir)
  "The recorder into DIR: (values on-event on-access finish), the subscriber's event and
   access functions and the end-of-run flush."
  (ensure-directories-exist dir)
  (let ((r (make-rs dir)))
    (labels ((at (block tx)
               (unless (rs-started r)          ; this run re-records from its first block on
                 (rs-drop-from! r block) (setf (rs-started r) t))
               (unless (eql block (rs-block r))
                 (rs-end-block r)
                 (let ((range (floor block +readset-segment+)))
                   (unless (and (= range (rs-range r)) (< (rs-keys r) *readset-segment-keys*))
                     (setf r (rs-flush! r) (rs-range r) range)))
                 (unless (rs-first r) (setf (rs-first r) block (rs-prev r) (1- block)))
                 (push (cons block (obuf-fill (rs-buf r))) (rs-marks r))
                 (rs-put-varint (rs-buf r) (- block (rs-prev r)))
                 (setf (rs-prev r) block (rs-block r) block))
               (unless (eql tx (rs-tx r)) (rs-end-tx r) (setf (rs-tx r) tx)))
             (acct (addr bits)
               (let ((id (rs-intern (rs-accts r) (rs-acct-keys r) addr)))
                 (setf (gethash id (rs-tx-accts r)) (logior bits (gethash id (rs-tx-accts r) 0)))
                 id))
             (slot (addr key written)
               (let ((id (rs-intern (rs-slots r) (rs-slot-keys r) (logior (ash (acct addr 0) 256) key))))
                 (setf (gethash id (rs-tx-slots r)) (logior written (gethash id (rs-tx-slots r) 0)))))
             (rollback (n)
               (rs-end-block r)
               (let ((mark (find-if (lambda (m) (<= (car m) n)) (rs-marks r))))
                 (loop while (and (rs-marks r) (> (car (first (rs-marks r))) n))
                       do (setf (obuf-fill (rs-buf r)) (cdr (pop (rs-marks r)))))
                 (setf (rs-last r) (and mark (car mark)) (rs-prev r) (if mark (car mark) (1- (or (rs-first r) 1))))
                 (unless mark (setf (rs-first r) nil)))
               (rs-drop-from! r (1+ n)))
             (on-access (op kind block tx addr key value b)
               (declare (ignore b))
               (at block tx)
               (cond ((not (eq op :read)) (if (eq kind :storage) (slot addr key 1) (acct addr +rs-written+)))
                     ((eq kind :storage) (slot addr key 0))
                     ((eq kind :blockhash) (push key (rs-tx-bh r)))
                     (t (let ((id (acct addr (rs-mask-bit kind))))
                          (when (and (eq kind :code) (not (gethash id (rs-tx-codes r))))
                            (setf (gethash id (rs-tx-codes r)) (rs-code-id r value)))))))
             (on-event (ev)
               (case (car ev)
                 (:checkpoint (setf r (rs-flush! r t)))
                 (:rollback (rollback (second ev)))
                 (:finalize (setf r (rs-flush! r t))))))
      (values #'on-event #'on-access (lambda () (setf r (rs-flush! r t)))))))

(defun readset-attach! ()
  "Attach the recorder to the event stream (check-subscribers, when *readset-dir* is set)."
  (multiple-value-bind (on-event on-access finish) (make-readset-recorder *readset-dir*)
    (attach-subscriber! "readset" on-event :on-access on-access :rolls-back t :on-finalize finish)))

;;; --- Reading a segment (docs/readset-format.md) ---
(defun readset-read-segment (path)
  "Segment file PATH: (values first last blocks), BLOCKS a list of (block . txs), a tx
   (tx-index accounts slots blockhashes): accounts (addr mask codehash-or-NIL), slots (addr
   slot written-p), block hashes the block numbers read. Unknown sections are skipped."
  (let ((b (eita.input::read-file-octets path)) (i 0) accts slots codes blocks)
    (labels ((u8 () (prog1 (aref b i) (incf i)))
             (int (n) (let ((x 0)) (dotimes (k n x) (setf x (logior (ash x 8) (u8))))))
             (varint () (loop with x = 0 for shift from 0 by 7 for c = (u8)
                              do (setf x (logior x (ash (logand c 127) shift)))
                              unless (logtest c 128) return x)))
      (unless (and (equalp (subseq b 0 3) #(69 82 83)) (= (aref b 3) 1)) (error "~A: not a version-1 read-set segment" path))
      (setf i 4)
      (let ((first (int 8)) (last (int 8)))
        (loop while (< i (length b))
              do (let* ((tag (u8)) (len (varint)) (end (+ i len)))
                   (case tag
                     (1 (setf accts (coerce (loop repeat (varint) collect (int 20)) 'vector)))
                     (2 (setf slots (coerce (loop repeat (varint) collect (let ((a (varint))) (list (aref accts a) (int 32)))) 'vector)))
                     (3 (setf codes (coerce (loop repeat (varint) collect (int 32)) 'vector)))
                     (4 (let ((block (1- first)))
                          (loop while (< i end)
                                do (incf block (varint))
                                   (push (cons block
                                               (loop for tx = (varint) until (zerop tx)
                                                     collect (list (- tx 2)
                                                                   (let ((id 0)) (loop repeat (varint)
                                                                                       collect (let* ((d (varint)) (mask (u8)))
                                                                                                 (incf id d)
                                                                                                 (list (aref accts id) mask (and (logtest mask 4) (aref codes (varint)))))))
                                                                   (let ((id 0)) (loop repeat (varint)
                                                                                       collect (let ((x (varint)))
                                                                                                 (incf id (ash x -1))
                                                                                                 (list (first (aref slots id)) (second (aref slots id)) (logbitp 0 x)))))
                                                                   (loop repeat (varint) collect (- block (varint))))))
                                         blocks)))))
                   (setf i end)))
        (values first last (nreverse blocks))))))
