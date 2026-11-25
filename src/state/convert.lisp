;;;; state/convert.lisp — `eita convert-snapshot`: a verified version 1 state as a version 2 base.
;;;;
;;;;   eita convert-snapshot --from V1-STATE-DIR --to V2-STATE-DIR [--tmp DIR] [--threads N] [--block N]
;;;;
;;;; docs/state-snapshot-format.md §10, "The converter": the composition an anchor of
;;;; V1-STATE-DIR names is composed (as the version 1 root check reads it), S1 applied, every
;;;; key hashed and partitioned into 4,096 bucket files by its top 12 bits (pass 1); the
;;;; buckets are sorted in RAM and fed in key order to the version 2 writer (pass 2); the
;;;; result is published as snap-N/ with its anchor line only if `snapshot-root` over it
;;;; equals the header root at N. The frontier (§7) is not written yet.

(in-package #:eita.state.root)

(defconstant +nb+ 4096)                 ; buckets: the top 12 bits of hkey / haddr
(defconstant +a2+ 128)                  ; v2 account record
(defconstant +s2+ 96)                   ; v2 slot record
(defconstant +batch+ 65536)             ; slots hashed per keccak call
(defconstant +flush+ (* 16 1024 1024))  ; a worker's slot records go to the buckets past this
(defconstant +bucket-wbuf+ 32768)       ; per bucket file: 8,192 of them open at once

(declaim (inline top12))
(defun top12 (recs off)
  (declare (type octets recs) (type fixnum off))
  (logior (ash (aref recs off) 4) (ash (aref recs (1+ off)) -4)))

(defun make-buckets (prefix n)
  (let ((v (make-array n)))
    (dotimes (b n v) (setf (aref v b) (make-bucket (format nil "~A~(~3,'0X~)" prefix b) +bucket-wbuf+)))))

(defstruct (conv (:constructor %make-conv))
  base layers scratch accts slots
  (lock (sb-thread:make-mutex :name "convert buckets"))
  (giants '())                          ; (hkey . its 256 buckets)
  (n-acct 0) (n-slot 0) (largest 0))

;;; ------------------------------------------------------------ pass 1: records -> buckets
;;;
;;; A SINK takes one chunk's output in the worker's buffers: account records (RECS, NA of
;;; them) and slot records (BUCKET, SPOS bytes). Slots arrive as the absolute addresses of
;;; v1 records (88 B: addr 20 · slot 32 · value 32), K of them batched in the worker's OFFS
;;; until hashed; the account's HADDR is set by `sink-begin`.

(defstruct (sink (:constructor make-sink (w)))
  w (na 0 :type fixnum) (spos 0 :type fixnum) (k 0 :type fixnum) (count 0 :type fixnum)
  (haddr (make-array 32 :element-type '(unsigned-byte 8)) :type octets)
  (giant nil) (rel nil) (rel-from 0 :type fixnum))

(defun sink-begin (sk hkey hoff giant scratch rel)
  "The next slots are those of the account whose hkey is HKEY[HOFF..]: into the chunk's
   buffer, or GIANT: into 256 files of their own (REL: the base's slot mapping, released
   behind them)."
  (replace (sink-haddr sk) hkey :start2 hoff :end2 (+ hoff 32))
  (setf (sink-count sk) 0 (sink-rel sk) (and giant rel) (sink-rel-from sk) 0
        (sink-giant sk) (and giant (make-buckets (format nil "~Ag~A-" scratch (eita.state.snapshot::key-hex (sink-haddr sk) 0 8)) 256))))

(defun sink-hash (sk)
  "Hash the batched slots and write their v2 records."
  (let* ((w (sink-w sk)) (k (sink-k sk)) (offs (worker-offs w)) (keys (worker-keys w)) (zero (sb-sys:int-sap 0)))
    (declare (type fixnum k))
    (when (plusp k)
      (keccak-into zero offs (worker-lens w) k keys)
      (let ((g (sink-giant sk)))
        (unless g
          (let ((need (+ (sink-spos sk) (* k +s2+))))
            (when (< (length (worker-bucket w)) need)
              (let ((v (make-array (max need (* 2 (length (worker-bucket w)))) :element-type '(unsigned-byte 8))))
                (replace v (worker-bucket w) :end2 (sink-spos sk))
                (setf (worker-bucket w) v)))))
        (let ((out (if g (make-array +s2+ :element-type '(unsigned-byte 8)) (worker-bucket w))))
          (dotimes (i k)
            (let ((o (if g 0 (+ (sink-spos sk) (* i +s2+)))))
              (replace out (sink-haddr sk) :start1 o)
              (replace out keys :start1 (+ o 32) :start2 (* 32 i) :end2 (* 32 (1+ i)))
              (copy-sap zero (+ (aref offs i) 32) 32 out (+ o 64))   ; the value, after the slot key
              (when g (bucket-put (aref g (aref out 32)) out 0 +s2+))))
          (unless g (incf (sink-spos sk) (* k +s2+)))))
      (let ((m (sink-rel sk)))              ; a giant base storage: its pages are done with
        (when m
          (let ((off (- (aref offs (1- k)) 20 (sb-sys:sap-int (eita.state.snapshot:mapping-sap m)))))
            (when (< 0 off (eita.state.snapshot::mapping-len m))
              (eita.state.snapshot:release-range m (sink-rel-from sk) off)
              (setf (sink-rel-from sk) off)))))
      (incf (sink-count sk) k)
      (setf (sink-k sk) 0))))

(declaim (inline sink-slot))
(defun sink-slot (sk addr)
  "One slot: the v1 record at absolute address ADDR."
  (let ((w (sink-w sk)) (k (sink-k sk)))
    (setf (aref (worker-offs w) k) (+ addr 20) (aref (worker-lens w) k) 32 (sink-k sk) (1+ k))
    (when (= (1+ k) +batch+) (sink-hash sk))))

(defun sink-end (sk cv)
  "The account's slots are all in: their count."
  (sink-hash sk)
  (let ((g (sink-giant sk)))
    (when g                             ; (with no slots left, as if there were none)
      (close-buckets g)
      (loop for b across g do (setf (bucket-buf b) (make-array 0 :element-type '(unsigned-byte 8))))   ; kept: path, count
      (if (zerop (sink-count sk))
          (remove-buckets g)
          (sb-thread:with-mutex ((conv-lock cv)) (push (cons (copy-seq (sink-haddr sk)) g) (conv-giants cv))))
      (setf (sink-giant sk) nil)))
  (sb-thread:with-mutex ((conv-lock cv)) (setf (conv-largest cv) (max (conv-largest cv) (sink-count sk))))
  (sink-count sk))

(defun sink-account (sk fill)
  "The account record: (FILL recs off) writes its 128 bytes at RECS[OFF..]."
  (let* ((w (sink-w sk)) (o (* (sink-na sk) +a2+)))
    (when (< (length (worker-recs w)) (+ o +a2+))
      (let ((v (make-array (* 2 (+ o +a2+)) :element-type '(unsigned-byte 8))))
        (replace v (worker-recs w) :end2 o)
        (setf (worker-recs w) v)))
    (funcall fill (worker-recs w) o)
    (incf (sink-na sk))))

(defun sink-flush (sk cv)
  "The chunk's records so far into their buckets."
  (let* ((w (sink-w sk)) (recs (worker-recs w)) (slots (worker-bucket w)) (ns (floor (sink-spos sk) +s2+)))
    (sb-thread:with-mutex ((conv-lock cv))
      (dotimes (i (sink-na sk)) (bucket-put (aref (conv-accts cv) (top12 recs (* i +a2+))) recs (* i +a2+) +a2+))
      (dotimes (i ns) (bucket-put (aref (conv-slots cv) (top12 slots (* i +s2+))) slots (* i +s2+) +s2+))
      (incf (conv-n-acct cv) (sink-na sk)) (incf (conv-n-slot cv) ns))
    (setf (sink-na sk) 0 (sink-spos sk) 0)))

(defun convert-chunk (cv c w)
  "Chunk C: base accounts c·4096.. and the addresses the layers mention in its range."
  (let* ((s (conv-base cv)) (layers (conv-layers cv)) (scratch (conv-scratch cv))
         (acct (eita.state.snapshot:snap-acct s)) (slots (eita.state.snapshot:snap-slot-map s))
         (asap (eita.state.snapshot:mapping-sap acct)) (ssap (eita.state.snapshot:mapping-sap slots))
         (na (eita.state.snapshot:snap-n-accounts s)) (ns (eita.state.snapshot:snap-n-slots s))
         (a0 (min na (* c +chunk+))) (a1 (min na (+ a0 +chunk+))) (n (- a1 a0))
         (s0 (if (zerop c) 0 (slot-lower-bound ssap ns asap (+ +header+ (* a0 +acct+)))))
         (s1 (if (= a1 na) ns (slot-lower-bound ssap ns asap (+ +header+ (* a1 +acct+)))))
         (lo (if (zerop c) nil (eita.state.snapshot:sap-be asap (+ +header+ (* a0 +acct+)) 20)))
         (hi (if (= a1 na) nil (eita.state.snapshot:sap-be asap (+ +header+ (* a1 +acct+)) 20)))
         (touched (and layers
                       (let ((l '()) (klo (and lo (eita.state.snapshot:int->octets lo 20)))
                             (khi (and hi (eita.state.snapshot:int->octets hi 20))))
                         (eita.state.snapshot:compose-range
                          (mapcar (lambda (l) (eita.state.snapshot:snap-run l :accounts klo khi)) layers)
                          (lambda (sap off) (push (eita.state.snapshot:sap-be sap off 20) l)))
                         (nreverse l))))
         (sbase (+ (sb-sys:sap-int ssap) +header+))
         (sk (make-sink w)) (si s0))
    (declare (type fixnum a0 a1 n si sbase))
    (hash-records w asap a0 n +acct+ 0 20)
    (when (< (length (worker-bkeys w)) (* 32 n))
      (let ((v (make-array (* 32 n) :element-type '(unsigned-byte 8)))) (setf (worker-bkeys w) v)))
    (replace (worker-bkeys w) (worker-keys w) :end2 (* 32 n))
    (worker-ensure w +batch+)
    (labels ((next () (when (> (sink-spos sk) +flush+) (sink-flush sk cv)))
             (base-account (k sj)
               (let ((aoff (+ +header+ (* (+ a0 k) +acct+))))
                 (sink-begin sk (worker-bkeys w) (* 32 k) (> (- sj si) *big*) scratch slots)
                 (loop for i of-type fixnum from si below sj do (sink-slot sk (+ sbase (* i +slot+))))
                 (sink-end sk cv)
                 (sink-account sk (lambda (recs o)            ; hkey, then the v1 record: the same fields
                                    (replace recs (worker-bkeys w) :start1 o :start2 (* 32 k) :end2 (* 32 (1+ k)))
                                    (copy-sap asap aoff +acct+ recs (+ o 32))))))
             (layered (addr ai count)
               ;; the layers' slots of ADDR (zeros kept) over the base's, the first wipe stopping it
               (let ((out (worker-obuf w)) (hkey (eita.mpt:%keccak (eita.state.snapshot:int->octets addr 20))))
                 (multiple-value-bind (lfields wiped) (eita.state.snapshot:compose-address layers nil addr out)
                   (let ((runs (cons (eita.state.snapshot::make-run (eita.state.snapshot:obuf-sap out) 0
                                                                    (eita.state.snapshot:obuf-count out) +slot+ 52)
                                     (and (not wiped) (plusp count)
                                          (list (eita.state.snapshot::make-run ssap si (+ si count) +slot+ 52))))))
                     (sink-begin sk hkey 0 (> (+ (eita.state.snapshot:obuf-count out) (if wiped 0 count)) *big*) scratch slots)
                     (eita.state.snapshot:compose-range runs (lambda (sap off) (sink-slot sk (+ (sb-sys:sap-int sap) off)))
                                                        :drop-zero 52)
                     (let ((nslots (sink-end sk cv)))
                       (destructuring-bind (nonce balance codehash mark)
                           (or lfields (eita.state.snapshot:acct-fields s ai))
                         (when (eita.state.snapshot:s1-included-p nonce balance codehash (plusp nslots) mark)
                           (let ((empty (and (zerop nonce) (zerop balance) (= codehash eita.state.snapshot::+empty-code-hash+))))
                             (sink-account sk (lambda (recs o)
                                                (fill recs 0 :start o :end (+ o +a2+))
                                                (replace recs hkey :start1 o)
                                                (eita.state.snapshot::put-be recs (+ o 32) addr 20)
                                                (eita.state.snapshot::put-be recs (+ o 52) (if empty 1 0) 4)
                                                (eita.state.snapshot::put-be recs (+ o 56) nonce 8)
                                                (eita.state.snapshot::put-be recs (+ o 64) balance 32)
                                                (eita.state.snapshot::put-be recs (+ o 96) codehash 32))))))))
                   (when (> (eita.state.snapshot:obuf-count out) +large+)
                     (eita.state.snapshot:obuf-free out) (setf (worker-obuf w) (eita.state.snapshot:make-obuf)))))))
      (dotimes (k n)
        (let* ((aoff (+ +header+ (* (+ a0 k) +acct+)))
               (base-key (eita.state.snapshot:sap-be asap aoff 20)))
          (loop while (and touched (< (first touched) base-key))   ; not in the base: no slots there (S5)
                do (layered (pop touched) nil 0) (next))
          (let ((sj (slots-end s asap aoff ssap si s1)))
            (if (and touched (= (first touched) base-key))
                (layered (pop touched) (+ a0 k) (- sj si))
                (base-account k sj))
            (setf si sj)
            (next))))
      (dolist (addr touched) (layered addr nil 0) (next))
      (unless (= si s1)
        (error "~A: ~D storage records belong to no account (S5)" (eita.state.snapshot:snap-dir s) (- s1 si)))
      (sink-flush sk cv))
    (eita.state.snapshot:release-range acct (+ +header+ (* a0 +acct+)) (+ +header+ (* a1 +acct+)))
    (eita.state.snapshot:release-range slots (+ +header+ (* s0 +slot+)) (+ +header+ (* s1 +slot+)))))

;;; ------------------------------------------------------------ pass 2: buckets -> the v2 base

(defun read-octets (b)
  "Bucket B's bytes (fresh), its file deleted."
  (if (null (bucket-stream b))
      (make-array 0 :element-type '(unsigned-byte 8))
      (prog1 (with-open-file (in (bucket-path b) :element-type '(unsigned-byte 8))
               (let ((v (make-array (file-length in) :element-type '(unsigned-byte 8))))
                 (unless (= (read-sequence v in) (length v)) (error "bucket ~A: short read" (bucket-path b)))
                 v))
        (delete-file (bucket-path b)))))

(defun u32-copy (v n)
  (let ((o (make-array n :element-type '(unsigned-byte 32)))) (replace o v :end2 n) o))

(defun prepare-bucket (cv b w)
  "Bucket B sorted: (A aorder S sorder rlens), the slot runs in haddr order, each in hslot
   order (SORDER), RLENS their lengths."
  (let* ((a (read-octets (aref (conv-accts cv) b))) (na (floor (length a) +a2+))
         (aorder (u32-copy (sort-keys (worker-sorter w) a na +a2+) na))
         (s (read-octets (aref (conv-slots cv) b))) (ns (floor (length s) +s2+))
         (starts '()))
    (sb-sys:with-pinned-objects (s)
      (let ((sap (sb-sys:vector-sap s)))
        (dotimes (i ns)
          (when (or (zerop i) (/= 0 (cmp-sap sap (* i +s2+) sap (* (1- i) +s2+) 32))) (push i starts)))))
    (let* ((starts (coerce (nreverse starts) '(simple-array fixnum (*)))) (nr (length starts))
           (rkeys (make-array (* 32 nr) :element-type '(unsigned-byte 8)))
           (sorder (make-array ns :element-type '(unsigned-byte 32)))
           (rlens (make-array nr :element-type 'fixnum)) (p 0))
      (dotimes (r nr) (replace rkeys s :start1 (* 32 r) :start2 (* +s2+ (aref starts r)) :end2 (+ 32 (* +s2+ (aref starts r)))))
      (loop for x across (u32-copy (sort-keys (worker-sorter w) rkeys nr 32) nr) for i from 0
            do (let* ((st (aref starts x)) (len (- (if (< (1+ x) nr) (aref starts (1+ x)) ns) st)))
                 (setf (aref rlens i) len)
                 (if (= len 1)
                     (setf (aref sorder p) st)
                     (let ((ia (sort-keys (worker-sorter w) s len +s2+ (+ (* st +s2+) 32))))
                       (dotimes (j len) (setf (aref sorder (+ p j)) (+ st (aref ia j))))))
                 (incf p len)))
      (list a aorder s sorder rlens))))

(defun write-giant (wr buckets w)
  "A giant storage's slots, its 256 files in order, each sorted by hslot."
  (loop for g across buckets
        do (let* ((s (read-octets g)) (n (floor (length s) +s2+)) (ia (sort-keys (worker-sorter w) s n +s2+ 32)))
             (sb-sys:with-pinned-objects (s)
               (dotimes (j n) (eita.state.snapshot:writer-record wr :storage (sb-sys:vector-sap s) (* +s2+ (aref ia j))))))))

(defun write-bucket (wr prepared giants w)
  "One sorted bucket into the writer: per account its slots, then its record. GIANTS: the
   giants not yet written, ascending by hkey. Returns the rest of them."
  (destructuring-bind (a aorder s sorder rlens) prepared
    (let ((p 0) (r 0) (nr (length rlens)))
      (declare (type fixnum p r nr))
      (sb-sys:with-pinned-objects (a s)
        (let ((asap (sb-sys:vector-sap a)) (ssap (sb-sys:vector-sap s)))
          (loop for x across aorder
                do (let ((aoff (* x +a2+)))
                     (when giants
                       (let ((c (eita.state.snapshot::cmp-key (car (first giants)) asap aoff 32)))
                         (when (minusp c) (error "convert: a giant storage without an account (S5)"))
                         (when (zerop c) (write-giant wr (cdr (pop giants)) w))))
                     (when (< r nr)
                       (let ((c (cmp-sap ssap (* +s2+ (aref sorder p)) asap aoff 32)))
                         (when (minusp c) (error "convert: slots of ~A without an account (S5)" (eita.state.snapshot::key-hex s (* +s2+ (aref sorder p)) 32)))
                         (when (zerop c)
                           (dotimes (j (aref rlens r)) (eita.state.snapshot:writer-record wr :storage ssap (* +s2+ (aref sorder (+ p j)))))
                           (incf p (aref rlens r)) (incf r))))
                     (eita.state.snapshot:writer-record wr :accounts asap aoff)))))
      (unless (= r nr) (error "convert: ~D slot runs without an account (S5)" (- nr r)))
      giants)))

(defun sort-and-write (cv wr threads)
  "Pass 2: the pool sorts buckets at most THREADS + 2 ahead of this thread, which writes them."
  (let* ((ready (make-array +nb+ :initial-element nil)) (next 0) (done 0) (window (+ threads 2))
         (lock (sb-thread:make-mutex :name "convert window")) (q (sb-thread:make-waitqueue)) (failure nil)
         (giants (sort (copy-list (conv-giants cv)) #'< :key (lambda (g) (eita.state.snapshot:octets->int (car g)))))
         (pool (loop repeat threads
                     collect (sb-thread:make-thread
                              (lambda ()
                                (let ((w (make-worker)))
                                  (loop (let ((b nil))
                                          (sb-thread:with-mutex (lock)
                                            (loop while (and (< next +nb+) (>= next (+ done window)) (not failure))
                                                  do (sb-thread:condition-wait q lock))
                                            (when (or failure (>= next +nb+)) (return))
                                            (setf b next) (incf next))
                                          (let ((r (handler-case (prepare-bucket cv b w)
                                                     (error (e) (sb-thread:with-mutex (lock) (setf failure (or failure e))
                                                                  (sb-thread:condition-broadcast q))
                                                       (return)))))
                                            (sb-thread:with-mutex (lock) (setf (aref ready b) r) (sb-thread:condition-broadcast q)))))))
                              :name "convert sorter")))
         (w (make-worker)))
    (unwind-protect
         (dotimes (b +nb+)
           (let ((prepared (sb-thread:with-mutex (lock)
                             (loop until (or (aref ready b) failure) do (sb-thread:condition-wait q lock))
                             (when failure (error failure))
                             (shiftf (aref ready b) nil))))
             (setf giants (write-bucket wr prepared giants w))
             (sb-thread:with-mutex (lock) (setf done (1+ b)) (sb-thread:condition-broadcast q))))
      (sb-thread:with-mutex (lock) (setf failure (or failure :stop)) (sb-thread:condition-broadcast q))
      (mapc #'sb-thread:join-thread pool))
    (when giants (error "convert: ~D giant storages without an account (S5)" (length giants)))))

(defun convert-stack (base layers tmpdir scratch &key (threads (eita.state.snapshot:hardware-threads)) provenance)
  "The v2 base at TMPDIR (written, not published) of the state the v1 BASE (an open snap)
   under LAYERS (layer snaps, newest first) reads as; bucket files in the directory
   SCRATCH. Returns the manifest."
  (let* ((top (or (first layers) base)) (m (eita.state.snapshot:snap-manifest top))
         (srcs (cons base layers))
         (cv (%make-conv :base base :layers layers :scratch scratch
                         :accts (make-buckets (format nil "~Aa" scratch) +nb+) :slots (make-buckets (format nil "~As" scratch) +nb+)))
         (files (+ (* 2 +nb+) (* 256 threads) 600))   ; the buckets, a giant's files per thread, the rest
         (t0 (get-internal-real-time)))
    (flet ((elapsed () (/ (- (get-internal-real-time) t0) internal-time-units-per-second)))
      (when (< (open-file-limit files) files)
        (error "convert: the open-file limit stays under ~D (ulimit -n)" files))
      (ensure-directories-exist scratch)
      (setf (sb-ext:bytes-consed-between-gcs) (min (sb-ext:bytes-consed-between-gcs) (* 128 1024 1024)))
      (unwind-protect
           (let ((na (eita.state.snapshot:snap-n-accounts base)))
             (eita.state.snapshot:advise-sequential (eita.state.snapshot:snap-acct base))
             (eita.state.snapshot:advise-sequential (eita.state.snapshot:snap-slot-map base))
             (run-pool threads (max 1 (ceiling na +chunk+)) (lambda (c w) (convert-chunk cv c w)))
             (close-buckets (conv-accts cv)) (close-buckets (conv-slots cv))
             (format t "~&convert: partitioned ~D accounts, ~D slots (largest storage ~D, ~D over ~D) in ~,1Fs~%"
                     (conv-n-acct cv) (+ (conv-n-slot cv) (loop for (nil . g) in (conv-giants cv) sum (loop for b across g sum (bucket-count b))))
                     (conv-largest cv) (length (conv-giants cv)) *big* (elapsed))
             (finish-output)
             (let ((wr (eita.state.snapshot:make-writer
                        tmpdir (getf m :chain-id) (getf m :block) (getf m :state-root)
                        :expect (list (reduce #'+ srcs :key #'eita.state.snapshot:snap-n-accounts)
                                      (reduce #'+ srcs :key #'eita.state.snapshot:snap-n-slots)))))
               (sort-and-write cv wr (max 1 threads))
               (format t "~&convert: records written at ~,1Fs~%" (elapsed)) (finish-output)
               (prog1 (eita.state.snapshot:writer-finish wr (eita.state.snapshot::layer-codes layers) :base base :provenance provenance)
                 (format t "~&convert: ~A written in ~,1Fs~%" tmpdir (elapsed)))))
        (mapc #'remove-buckets (list* (conv-accts cv) (conv-slots cv) (mapcar #'cdr (conv-giants cv))))
        (ignore-errors (sb-ext:delete-directory scratch :recursive t))))))

;;; ------------------------------------------------------------ the command

(defun pick-composition (from block)
  "The components (oldest first) of FROM's newest passed anchor (at BLOCK, if given) whose
   components are all sealed."
  (loop for (b ok hash) in (sort (eita.state.recovery::read-anchors from) #'> :key #'first)
        for comps = (and ok (or (null block) (= b block)) (eita.state.snapshot:parse-composition hash b))
        when (and comps (every (lambda (c) (eita.state.snapshot:snap-sealed-p (eita.state.snapshot:component-path from c))) comps))
          return comps))

(defun convert-snapshot (from to &key tmp (threads (eita.state.snapshot:hardware-threads)) block)
  "Convert the v1 composition of FROM's anchor (`pick-composition`) into a root-checked v2
   base under TO, and record its anchor there. Returns snap-N/, or NIL on a root mismatch."
  (let* ((from (eita.state.snapshot::as-dir from)) (to (eita.state.snapshot::as-dir to))
         (comps (or (pick-composition from block)
                    (error "convert: ~A has no passed anchor~@[ at ~D~] whose components are all sealed" from block)))
         (snaps '()))
    (unwind-protect
         (progn
           (dolist (c comps)
             (let ((s (eita.state.snapshot:snap-open (eita.state.snapshot:component-path from c)
                                                     :fence (if (eq (first c) :base) nil :scan))))
               (push s snaps)
               (unless (= 1 (eita.state.snapshot::snap-version s)) (error "convert: ~A is not version 1" (eita.state.snapshot:snap-dir s)))
               (unless (string-equal (car (last c)) (eita.state.snapshot:snap-content-hash (eita.state.snapshot:snap-manifest s)))
                 (error "convert: ~A does not have the content hash its anchor recorded" (eita.state.snapshot:snap-dir s)))))
           (let* ((top (first snaps)) (n (eita.state.snapshot:snap-block top))
                  (tmpdir (eita.state.snapshot:snap-tmp-path to n)) (final (eita.state.snapshot:snap-path to n))
                  (scratch (format nil "~Aconvert-~D-~D/" (eita.state.snapshot::as-dir (or tmp to)) n (sb-posix:getpid)))
                  (comp (eita.state.snapshot:composition-string comps)) (t0 (get-internal-real-time)))
             (format t "~&convert: ~A at block ~D: ~A~%" from n comp) (finish-output)
             (when (probe-file final) (error "convert: ~A exists" final))
             (when (probe-file tmpdir) (sb-ext:run-program "rm" (list "-rf" (namestring tmpdir)) :search t))
             (convert-stack (car (last snaps)) (butlast snaps) tmpdir scratch :threads threads
                            :provenance (format nil "eita convert-snapshot from v1 ~A" comp))
             (multiple-value-bind (got expected) (snapshot-root tmpdir :threads threads)
               (format t "~&CL trie root : ~A~%header root  : ~A~%" got expected)
               (cond ((and expected (string-equal got expected))
                      (mark-root-checked tmpdir)
                      (eita.state.snapshot:snap-publish to n tmpdir)
                      (eita.state::append-anchor!
                       (list n (concatenate 'string "0x" expected) got t
                             (getf (eita.state.snapshot:read-manifest final) :content-hash))
                       (merge-pathnames "anchors.sexp" to))
                      (format t "MATCH: published ~A and its anchor in ~,1Fs~%" final
                              (/ (- (get-internal-real-time) t0) internal-time-units-per-second))
                      final)
                     (t (format t "MISMATCH: the conversion stays quarantined in ~A~%" tmpdir)
                        nil)))))
      (mapc #'eita.state.snapshot:snap-close snaps))))
