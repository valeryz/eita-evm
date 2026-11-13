;;;; evm/readset.lisp — the read-set recorder: what each transaction read, per block, into
;;;; segment files (docs/readset-format.md, version 1).
;;;;
;;;; EITA_READSET_DIR=<dir> turns it on: a subscriber of the event stream (evm/stream.lisp)
;;;; that wants the storage view's reads (state/world.lisp: (:read kind block tx addr slot
;;;; value), (:write …), (:delta …); the callbacks add :codehash and :blockhash). Per tx it
;;;; keeps each account once with the fields read (and whether it was written), each slot
;;;; once (and whether it was written), the code read by hash, the block hashes read. A
;;;; segment holds the blocks of one +readset-segment+ range up to a layer point: it is
;;;; written at the range's end, at every checkpoint (before the layer at N is published,
;;;; so an anchor implies its read sets) and at the end of the run. Off: one test per tx.
;;;; Nothing here steers execution; it runs on its own thread.

(in-package #:eita.evm)

(defconstant +readset-segment+ 10000 "Blocks per segment range.")
(defconstant +rs-written+ 128 "Account mask bit: the tx wrote a field of the account.")

(defun rs-mask-bit (kind)
  (ecase kind (:balance 1) (:nonce 2) (:code 4) (:codehash 8) (:present 16)))

(defstruct (rs (:constructor make-rs (dir)))
  dir (range -1) (first nil) (last nil) (prev 0)
  (accts (make-hash-table)) (acct-keys (make-array 0 :adjustable t :fill-pointer 0))
  (slots (make-hash-table)) (slot-keys (make-array 0 :adjustable t :fill-pointer 0))
  (codes (make-hash-table)) (code-keys (make-array 0 :adjustable t :fill-pointer 0))
  (code-memo (make-hash-table :test 'eq))
  (buf (make-array 4096 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0))
  (marks '())                                     ; (block . buf offset), newest first
  (block nil) (tx nil) (started nil)
  (tx-accts (make-hash-table)) (tx-codes (make-hash-table)) (tx-slots (make-hash-table)) (tx-bh '()))

(defun rs-put-varint (buf n)
  (loop (if (< n 128) (return (vector-push-extend n buf))
            (progn (vector-push-extend (logior 128 (logand n 127)) buf) (setf n (ash n -7))))))
(defun rs-put-int (buf n bytes)
  (loop for i from (1- bytes) downto 0 do (vector-push-extend (ldb (byte 8 (* 8 i)) n) buf)))

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
              (rs-put-varint b (- id prev)) (vector-push-extend mask b) (setf prev id)
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
    (vector-push-extend 0 (rs-buf r))             ; the block's txs end
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

(cffi:defcfun ("gzwrite" %gzwrite) :int (f :pointer) (buf :pointer) (len :unsigned-int))

(defun rs-flush! (r)
  "Write the segment (its blocks first..last) and start an empty one."
  (rs-end-block r)
  (when (rs-first r)
    (let ((out (make-array (+ 4096 (fill-pointer (rs-buf r))) :element-type '(unsigned-byte 8)
                                                                :adjustable t :fill-pointer 0)))
      (map nil (lambda (c) (vector-push-extend (char-code c) out)) "ERS")
      (vector-push-extend 1 out)                  ; format version
      (rs-put-int out (rs-first r) 8) (rs-put-int out (rs-last r) 8)
      (flet ((section (tag fill)
               (let ((s (make-array 1024 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0)))
                 (funcall fill s)
                 (vector-push-extend tag out) (rs-put-varint out (fill-pointer s))
                 (loop for x across s do (vector-push-extend x out)))))
        (section 1 (lambda (s) (rs-put-varint s (fill-pointer (rs-acct-keys r)))
                     (loop for a across (rs-acct-keys r) do (rs-put-int s a 20))))
        (section 2 (lambda (s) (rs-put-varint s (fill-pointer (rs-slot-keys r)))
                     (loop for k across (rs-slot-keys r)
                           do (rs-put-varint s (gethash (ash k -256) (rs-accts r)))
                              (rs-put-int s (ldb (byte 256 0) k) 32))))
        (section 3 (lambda (s) (rs-put-varint s (fill-pointer (rs-code-keys r)))
                     (loop for h across (rs-code-keys r) do (rs-put-int s h 32))))
        (section 4 (lambda (s) (loop for x across (rs-buf r) do (vector-push-extend x s)))))
      (let* ((path (rs-segment-path r (rs-first r) (rs-last r)))
             (tmp (concatenate 'string path ".tmp"))
             (f (eita.input::%gzopen tmp "wb6")))
        (when (cffi:null-pointer-p f) (error "readset: gzopen ~A failed" tmp))
        (let ((v (coerce out '(simple-array (unsigned-byte 8) (*)))))
          (unwind-protect
               (unless (= (cffi:with-pointer-to-vector-data (p v) (%gzwrite f p (length v))) (length v))
                 (error "readset: gzwrite ~A failed" tmp))
            (eita.input::%gzclose f)))
        (let ((fd (sb-posix:open tmp sb-posix:o-rdonly)))
          (unwind-protect (sb-posix:fsync fd) (sb-posix:close fd)))
        (sb-posix:rename tmp path))))
  (let ((next (make-rs (rs-dir r))))            ; the next segment: the same range, run
    (setf (rs-range next) (rs-range r) (rs-started next) (rs-started r))
    next))

(defun rs-code-id (r code)
  (rs-intern (rs-codes r) (rs-code-keys r)
             (or (gethash code (rs-code-memo r))
                 (setf (gethash code (rs-code-memo r))
                       (let ((h 0)) (loop for x across (keccak256-bytes code) do (setf h (logior (ash h 8) x))) h)))))

(defun make-readset-recorder (dir)
  "The recorder into DIR: (values on-event finish), the subscriber's event function and the
   end-of-run flush."
  (ensure-directories-exist dir)
  (let ((r (make-rs dir)))
    (labels ((at (block tx)
               (unless (rs-started r)          ; this run re-records from its first block on
                 (rs-drop-from! r block) (setf (rs-started r) t))
               (unless (eql block (rs-block r))
                 (rs-end-block r)
                 (let ((range (floor block +readset-segment+)))
                   (unless (= range (rs-range r)) (setf r (rs-flush! r) (rs-range r) range)))
                 (unless (rs-first r) (setf (rs-first r) block (rs-prev r) (1- block)))
                 (push (cons block (fill-pointer (rs-buf r))) (rs-marks r))
                 (rs-put-varint (rs-buf r) (- block (rs-prev r)))
                 (setf (rs-prev r) block (rs-block r) block))
               (unless (eql tx (rs-tx r)) (rs-end-tx r) (setf (rs-tx r) tx)))
             (acct (addr bits)
               (let ((id (rs-intern (rs-accts r) (rs-acct-keys r) addr)))
                 (setf (gethash id (rs-tx-accts r)) (logior bits (gethash id (rs-tx-accts r) 0)))
                 id))
             (slot (addr key written)
               (acct addr 0)
               (let ((id (rs-intern (rs-slots r) (rs-slot-keys r) (logior (ash addr 256) key))))
                 (setf (gethash id (rs-tx-slots r)) (logior written (gethash id (rs-tx-slots r) 0)))))
             (rollback (n)
               (rs-end-block r)
               (let ((mark (find-if (lambda (m) (<= (car m) n)) (rs-marks r))))
                 (loop while (and (rs-marks r) (> (car (first (rs-marks r))) n))
                       do (setf (fill-pointer (rs-buf r)) (cdr (pop (rs-marks r)))))
                 (setf (rs-last r) (and mark (car mark)) (rs-prev r) (if mark (car mark) (1- (or (rs-first r) 1))))
                 (unless mark (setf (rs-first r) nil)))
               (rs-drop-from! r (1+ n)))
             (on-event (ev)
               (case (car ev)
                 (:read (destructuring-bind (kind block tx addr key value) (cdr ev)
                          (at block tx)
                          (case kind
                            (:storage (slot addr key 0))
                            (:blockhash (push key (rs-tx-bh r)))
                            (t (let ((id (acct addr (rs-mask-bit kind))))
                                 (when (and (eq kind :code) (not (gethash id (rs-tx-codes r))))
                                   (setf (gethash id (rs-tx-codes r)) (rs-code-id r value))))))))
                 ((:write :delta) (destructuring-bind (kind block tx addr key &rest vals) (cdr ev)
                                    (declare (ignore vals))
                                    (at block tx)
                                    (if (eq kind :storage) (slot addr key 1) (acct addr +rs-written+))))
                 (:checkpoint (setf r (rs-flush! r)))
                 (:rollback (rollback (second ev)))
                 (:finalize (setf r (rs-flush! r))))))
      (values #'on-event (lambda () (setf r (rs-flush! r)))))))

(defun readset-attach! ()
  "Attach the recorder to the event stream (check-subscribers, when *readset-dir* is set)."
  (multiple-value-bind (on-event finish) (make-readset-recorder *readset-dir*)
    (attach-subscriber! "readset" on-event :wants-reads t :rolls-back t :on-finalize finish)))

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
