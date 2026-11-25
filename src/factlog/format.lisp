;;;; factlog/format.lisp — the fact log's format: the one Common Lisp reader and encoder of its
;;;; shards, and its history index (docs/fact-log.md). The layout is lean/Evm/FactLog/Format.lean
;;;; (shards, groups, columns) and History.lean (the index, `lookup`).
;;;;
;;;; Standalone: it needs SBCL and libzstd, nothing of the engine, so any program reads a fact
;;;; log through it (`sbcl --script` or `load`). In the engine the writer (factlog/writer.lisp)
;;;; encodes its shards and reads its own footers, digests and resume prefixes through it.
;;;; scripts/factlog.py is its Python twin; both decode the Lean-emitted vectors
;;;; (scripts/verify-factlog-emit.sh).
;;;;
;;;;   <dir>/<kind>/<lo>-<hi>.fct        rows: columnar groups, then (storage_diff,
;;;;                                     account_diff) the history index section
;;;;   <dir>/<kind>/<lo>-<hi>.sexp[.gz]  the text form (read, never written)
;;;;   <dir>/<kind>/<lo>-<hi>.sealed     footer plist (:rows :first-block :last-block :min-block
;;;;                                     :max-block :bytes :fnv :content :index :bloom-bits
;;;;                                     :bloom-k :keys :version :versions)
;;;;   <dir>/<kind>/blooms.idx           every sealed shard's key filter (scripts/factlog.py index)
;;;;
;;;; The column types and layout constants come from src/generated/factlog-schema.lisp, emitted
;;;; from the Lean definitions. The row model is READ's: a row is a list, integers decimal, NIL
;;;; for a missing `to`, a list for topics and a lower-case hex string for log data — the same
;;;; whether the shard is text or binary. A row is as wide as the group it was written in
;;;; (Format.lean `colsAt`): a table only gains optional columns at its end, and an older group
;;;; has fewer (block rows without the blob-gas columns: 7 fields).
;;;;
;;;; Questions:
;;;;   state-at     DIR KIND KEY BLOCK     storage value / (nonce balance code) at the end of BLOCK,
;;;;                                       through the history index (History.lean `lookup`)
;;;;   key-history  DIR KIND KEY LO HI     every change of KEY in [LO, HI], through the index
;;;;   map-rows     FN DIR KIND LO HI      FN on every row of KIND with LO <= block <= HI, a group
;;;;                                       at a time, decoding only the columns asked for
;;;;   fact-scan    FL KIND LO HI          every row of KIND with LO <= block <= HI, as a list
;;;;   fact-logs    FL ADDR TOPIC0 LO HI   logs emitted by ADDR with that signature
;;;; A key never written inside the log's coverage answers :unknown: the fact log asserts what
;;;; the replay changed, not the state before it.
;;;;
;;;; CLI:
;;;;   sbcl --script src/factlog/format.lisp <dir> vectors <factlog-vectors.sexp>
;;;;   sbcl --script src/factlog/format.lisp <dir> convert [<kind>] [--delete]   text shards -> .fct

(require :sb-posix)

(defpackage :eita-factlog
  (:use :cl)
  (:export #:*shard-blocks* #:+kinds+ #:shard-file #:rows-file #:shard-ranges
           #:read-footer #:footer-complete-p #:fnv64-bytes #:digest
           #:read-shard #:fct-prefix-end #:map-fct-groups
           #:table-cols #:make-group-builder #:builder-push! #:builder-push-fields!
           #:builder-content #:group-builder-raw-bytes #:builder-finish #:write-group! #:index-section #:fct-builder
           #:state-at #:open-factlog #:fact-scan #:fact-logs #:map-rows
           #:key-history #:factlog-coverage #:convert-shard! #:convert-dir!))
(in-package :eita-factlog)

(defvar *shard-blocks* 1000 "Blocks per shard; the writer's EITA_FACTLOG_SHARD.")
(defparameter +kinds+ '(:storage_diff :account_diff :transfer :log :tx :block :call))
(deftype octets () '(simple-array (unsigned-byte 8) (*)))

;; The source file's own directory, read-time: under ASDF the fasl's *load-truename* is the
;; cache, not the source; in bin/eita the schema below is read when the image is built.
(defvar *here* (directory-namestring #.(or *compile-file-truename* *load-truename*)))

;;; --- The schema, emitted from Lean ---------------------------------------------------
(defvar *schema*
  (with-open-file (in (merge-pathnames "../generated/factlog-schema.lisp" *here*))
    (let ((*read-eval* nil) (*package* (find-package :keyword))) (read in)))
  "The plist of src/generated/factlog-schema.lisp (lake exe emitFactLog lisp).")

(defun table-name (kind) (string-downcase (string kind)))
(defun table-cols (kind)
  "The column types of KIND (a keyword or string), as keywords, or NIL for an unknown table."
  (cdr (assoc (table-name kind) (getf *schema* :tables) :test #'string=)))
(defun cols-at (kind k)
  "The column types a group (or row) of K columns of KIND is read with (Format.lean colsAt):
   the table's first K, when every column past K is optional; NIL when K is no width of KIND."
  (let ((types (table-cols kind)))
    (and (<= k (length types)) (every (lambda (ty) (member ty '(:optaddr :optu64))) (nthcdr k types))
         (subseq types 0 k))))
(defparameter +magic+ (coerce '(69 70 71 49) 'octets))
(defparameter +index-magic+ (coerce '(69 70 73 49) 'octets))
(defconstant +header-fixed+ 29) (defconstant +dir-entry+ 9) (defconstant +index-header+ 17)
(defconstant +bloom-k+ 7)
(defun indexed-p (kind) (member (table-name kind) '("storage_diff" "account_diff") :test #'string=))

;;; --- Paths and discovery -------------------------------------------------------------
(defun as-dir (dir)
  "\"…/log\" and \"…/log/\" both mean the directory."
  (let ((d (namestring dir)))
    (pathname (if (char= (char d (1- (length d))) #\/) d (concatenate 'string d "/")))))

(defun shard-file (dir kind lo hi type)
  (merge-pathnames (format nil "~(~A~)/~D-~D.~A" kind lo hi type) (as-dir dir)))

(defun rows-file (dir kind lo hi)
  "The rows file of KIND's range in whichever form exists (.fct, .sexp, .sexp.gz), or NIL."
  (loop for type in '("fct" "sexp" "sexp.gz")
        for p = (shard-file dir kind lo hi type)
        when (probe-file p) return p))

(defun shard-ranges (dir kind)
  "Sorted list of (lo hi path) for KIND from the directory listing (any form; .fct preferred,
   then .sexp, then .sexp.gz)."
  (let ((seen (make-hash-table)) (out '()))
    (dolist (glob '("*.fct" "*.sexp" "*.sexp.gz"))
      (dolist (f (directory (merge-pathnames (format nil "~(~A~)/~A" kind glob) (as-dir dir))))
        (let* ((name (pathname-name f))          ; "lo-hi" or "lo-hi.sexp" (compacted .gz)
               (dash (position #\- name))
               (dot (position #\. name)))
          (when dash
            (let ((lo (parse-integer name :end dash)))
              (unless (gethash lo seen)
                (setf (gethash lo seen) t)
                (push (list lo (parse-integer name :start (1+ dash) :end dot) f) out)))))))
    (sort out #'< :key #'first)))

(defun read-footer (path)
  "The plist of a `.sealed` footer or a `.at-N` prefix record; NIL when absent or torn."
  (ignore-errors
    (with-open-file (f path :if-does-not-exist nil)
      (and f (let ((*read-eval* nil) (ft (read f nil nil))) (and (listp ft) ft))))))

(defun footer-complete-p (ft lo hi)
  "Does footer FT cover [LO, HI] entirely? Block 0 is the genesis, which no replay runs: a
   from-genesis log's first range starts at block 1 (Arc's 0-999)."
  (and ft (member (getf ft :first-block) (list lo (max lo 1))) (eql (getf ft :last-block) hi) t))

(declaim (inline fnv64-bytes))   ; an unboxed 64-bit result in the row encoder
(defun fnv64-bytes (h buf start end)
  "FNV-1a 64 of BUF[START,END) continuing from H."
  (declare (optimize (speed 3) (safety 0)) (type (unsigned-byte 64) h)
           (type octets buf) (type fixnum start end))
  (loop for i of-type fixnum from start below end
        do (setf h (logand #xFFFFFFFFFFFFFFFF (* (logxor h (aref buf i)) #x100000001b3))))
  h)
(defconstant +fnv-basis+ #xcbf29ce484222325)
(defun hex64 (h) (format nil "~(~16,'0X~)" h))

(defun read-file-bytes (path)
  (with-open-file (in path :element-type '(unsigned-byte 8))
    (let ((v (make-array (file-length in) :element-type '(unsigned-byte 8))))
      (read-sequence v in) v)))

(defun gunzip-stream (path fn)
  "Call FN on a byte stream of PATH's gzip content; error unless gzip exits 0."
  (let* ((p (sb-ext:run-program "gzip" (list "-dc" (namestring path)) :search t
                                :output :stream :wait nil))   ; bivalent: byte reads work
         (result (unwind-protect (funcall fn (sb-ext:process-output p))
                   (sb-ext:process-wait p) (sb-ext:process-close p))))
    (unless (eql (sb-ext:process-exit-code p) 0) (error "gzip -dc ~A failed" path))
    result))

(defun digest (path &key limit)
  "(values bytes fnv-hex) of PATH's content — inflated when PATH is a .gz — with FNV-1a
   64; with LIMIT, of its first LIMIT bytes at most. NIL when absent or unreadable."
  (ignore-errors
    (let ((buf (make-array (* 1024 1024) :element-type '(unsigned-byte 8)))
          (h +fnv-basis+) (n 0))
      (declare (type (unsigned-byte 64) h))
      (flet ((eat (in)
               (loop for len = (read-sequence buf in :end (if limit
                                                              (max 0 (min (length buf) (- limit n)))
                                                              (length buf)))
                     while (plusp len)
                     do (setf h (fnv64-bytes h buf 0 len)) (incf n len))))
        (if (string= (pathname-type path) "gz")
            (gunzip-stream path #'eat)
            (with-open-file (in path :element-type '(unsigned-byte 8) :if-does-not-exist nil)
              (unless in (return-from digest nil))
              (eat in))))
      (values n (hex64 h)))))

;;; --- zstd, through sb-alien (libzstd is on every box; no Lisp package) ---------------
(defun open-libzstd ()
  (sb-alien:load-shared-object (or (probe-file "/opt/homebrew/lib/libzstd.dylib") "libzstd.so.1")
                               :dont-save t))
(open-libzstd)
;; Compiled into bin/eita-node: reopened when the saved image starts (core native/startup.lisp).
(let ((reg (and (find-package :eita.native) (find-symbol "REGISTER-STARTUP" :eita.native))))
  (when reg (funcall reg 'libzstd #'open-libzstd)))
(sb-alien:define-alien-routine ("ZSTD_compress" %zstd-compress) sb-alien:unsigned-long
  (dst sb-sys:system-area-pointer) (dst-cap sb-alien:unsigned-long)
  (src sb-sys:system-area-pointer) (src-size sb-alien:unsigned-long) (level sb-alien:int))
(sb-alien:define-alien-routine ("ZSTD_decompress" %zstd-decompress) sb-alien:unsigned-long
  (dst sb-sys:system-area-pointer) (dst-cap sb-alien:unsigned-long)
  (src sb-sys:system-area-pointer) (src-size sb-alien:unsigned-long))
(sb-alien:define-alien-routine ("ZSTD_compressBound" %zstd-bound) sb-alien:unsigned-long
  (size sb-alien:unsigned-long))
(sb-alien:define-alien-routine ("ZSTD_isError" %zstd-error-p) sb-alien:unsigned-int
  (code sb-alien:unsigned-long))
(defvar *zstd-level* 3 "Per-column compression level (measured: 3 within 4 % of 9, 3x faster).")

(defun zstd-compress (src start end)
  "SRC[START,END) compressed, as a fresh octet vector; NIL when zstd fails."
  (declare (type octets src))
  (let* ((n (- end start))
         (dst (make-array (%zstd-bound n) :element-type '(unsigned-byte 8))))
    (sb-sys:with-pinned-objects (src dst)
      (let ((r (%zstd-compress (sb-sys:vector-sap dst) (length dst)
                               (sb-sys:sap+ (sb-sys:vector-sap src) start) n *zstd-level*)))
        (if (zerop (%zstd-error-p r)) (subseq dst 0 r) nil)))))

(defvar *scratch* (cons nil nil) "(thread . octets): one thread's reusable inflate buffer (a thread may bind its own)")
(defun scratch-octets (n)
  "An octet vector of at least N bytes, its contents undefined: the first thread to ask owns a
   reused one (a decoded column's raw bytes die with the decode, and a fresh zeroed vector per
   column dominates a scan's allocation); other threads get a fresh one."
  (let ((s *scratch*) (me sb-thread:*current-thread*))
    (when (null (car s)) (sb-ext:compare-and-swap (car s) nil me))
    (if (eq (car s) me)
        (let ((v (cdr s))) (if (and v (>= (length v) n)) v (setf (cdr s) (make-array (max n (* 2 (length (or v #())))) :element-type '(unsigned-byte 8)))))
        (make-array n :element-type '(unsigned-byte 8)))))

(defun zstd-decompress (src start end raw-len &optional dst)
  "SRC[START,END) inflated into a fresh octet vector of RAW-LEN bytes, or into the first RAW-LEN
   bytes of DST."
  (declare (type octets src))
  (let ((dst (or dst (make-array raw-len :element-type '(unsigned-byte 8)))))
    (sb-sys:with-pinned-objects (src dst)
      (let ((r (%zstd-decompress (sb-sys:vector-sap dst) raw-len
                                 (sb-sys:sap+ (sb-sys:vector-sap src) start) (- end start))))
        (unless (and (zerop (%zstd-error-p r)) (= r raw-len))
          (error "zstd: bad column payload (~D of ~D bytes)" r raw-len))))
    dst))

;;; --- Growable byte buffers and the field codecs (Format.lean encodeField) --------------
(defstruct (buf (:constructor %make-buf))
  (data (make-array 4096 :element-type '(unsigned-byte 8)) :type octets)
  (fill 0 :type fixnum))
(defun make-buf (&optional (size 4096)) (%make-buf :data (make-array size :element-type '(unsigned-byte 8))))
(defun buf-reset! (b) (setf (buf-fill b) 0))
(declaim (inline buf-ensure!))
(defun buf-ensure! (b n)
  (let ((need (+ (buf-fill b) n)) (d (buf-data b)))
    (when (> need (length d))
      (let ((new (make-array (max need (* 2 (length d))) :element-type '(unsigned-byte 8))))
        (replace new d :end2 (buf-fill b))
        (setf (buf-data b) new)))))
(defun put-bytes! (b v &key (start 0) (end (length v)))
  (buf-ensure! b (- end start))
  (replace (buf-data b) v :start1 (buf-fill b) :start2 start :end2 end)
  (incf (buf-fill b) (- end start)))

(defun hex->bytes (s)
  (let ((v (make-array (floor (length s) 2) :element-type '(unsigned-byte 8))))
    (dotimes (i (length v) v) (setf (aref v i) (parse-integer s :start (* 2 i) :end (+ 2 (* 2 i)) :radix 16)))))
(defun bytes->hex (v &optional (start 0) (end (length v)))
  (declare (type octets v) (type fixnum start end) (optimize (speed 3) (safety 0)))
  (let ((out (make-string (* 2 (- end start)) :element-type 'base-char)) (digits "0123456789abcdef"))
    (loop for i from start below end for j from 0
          do (setf (schar out (* 2 j)) (schar digits (ash (aref v i) -4))
                   (schar out (1+ (* 2 j))) (schar digits (logand (aref v i) 15))))
    out))

(defun column-width (type)
  (ecase type (:u8 1) (:u16 2) (:u32 4) (:u64 8) (:i64 8) (:addr 20) (:optaddr 21) (:optu64 9) (:u256 32)
         ((:u256list :bytes) nil)))

(defun put-le! (b v k)
  "V in K little-endian bytes (mod 256^K), read straight from V's fixnum
   or bignum digits: no intermediate integers (the writer encodes every field through here)."
  (declare (optimize (speed 3) (safety 0)) (type unsigned-byte v) (type (integer 1 32) k))
  (buf-ensure! b k)
  (let ((d (buf-data b)) (p (buf-fill b)))
    (declare (type octets d) (type fixnum p))
    (if (typep v 'fixnum)
        (let ((w v))
          (declare (type (unsigned-byte 62) w))
          (dotimes (i (min k 8)) (setf (aref d (+ p i)) (ldb (byte 8 (* 8 i)) w)))
          (loop for i from 8 below k do (setf (aref d (+ p i)) 0)))
        (let ((n (sb-bignum:%bignum-length v)))
          (dotimes (i k)
            (let ((wi (ash i -3)))
              (setf (aref d (+ p i))
                    (if (< wi n)
                        (ldb (byte 8 (* 8 (logand i 7))) (the (unsigned-byte 64) (sb-bignum:%bignum-ref v wi)))
                        0))))))
    (setf (buf-fill b) (+ p k))))

(defun encode-field! (b type v)
  "Append field V of TYPE to buffer B; an error names a value that does not fit."
  (flet ((unsigned (k bits)
           (unless (and (typep v 'unsigned-byte) (<= (integer-length v) bits)) (error "~A does not fit ~A" v type))
           (put-le! b v k)))
    (case type
      (:u256 (unsigned 32 256)) (:addr (unsigned 20 160)) (:u64 (unsigned 8 64))
      (:u8 (unsigned 1 8)) (:u16 (unsigned 2 16)) (:u32 (unsigned 4 32))
      (:i64 (unless (and (integerp v) (<= (integer-length v) 63)) (error "~A does not fit i64" v))
            (if (typep v 'fixnum)               ; two's complement straight from the fixnum
                (let ((p (progn (buf-ensure! b 8) (buf-fill b))) (d (buf-data b)))
                  (dotimes (i 8) (setf (aref d (+ p i)) (ldb (byte 8 (* 8 i)) (the fixnum v))))
                  (setf (buf-fill b) (+ p 8)))
                (put-le! b (ldb (byte 64 0) v) 8)))
      (:optaddr (cond ((null v) (put-le! b 0 1) (put-le! b 0 20))
                      ((and (typep v 'unsigned-byte) (<= (integer-length v) 160)) (put-le! b 1 1) (put-le! b v 20))
                      (t (error "~A does not fit optaddr" v))))
      (:optu64 (cond ((null v) (put-le! b 0 1) (put-le! b 0 8))
                     ((and (typep v 'unsigned-byte) (<= (integer-length v) 64)) (put-le! b 1 1) (put-le! b v 8))
                     (t (error "~A does not fit optu64" v))))
      (:u256list (unless (and (listp v) (< (length v) 256)) (error "~A does not fit u256list" v))
                 (put-le! b (length v) 1)
                 (dolist (x v) (unless (and (typep x 'unsigned-byte) (<= (integer-length x) 256)) (error "~A does not fit u256" x))
                   (put-le! b x 32)))
      (:bytes (let ((v (if (stringp v) (hex->bytes v) v)))
                (put-le! b (length v) 4) (put-bytes! b v)))
      (t (error "no such field type ~A" type)))))

;;; --- Decoding fields and columns (Format.lean decodeColumn) ---------------------------
(declaim (inline get-le))
(defun get-le (v off k)
  (declare (type octets v) (type fixnum off k))
  (if (<= k 7)
      (let ((n 0)) (declare (type fixnum n))
        (loop for i from (1- k) downto 0 do (setf n (logior (ash n 8) (aref v (+ off i))))) n)
      (if (= k 8)
          (let ((n 0)) (declare (type (unsigned-byte 64) n))
            (loop for i from 7 downto 0 do (setf n (logior (ldb (byte 64 0) (ash n 8)) (aref v (+ off i))))) n)
          (let ((n 0)) (loop for i from (1- k) downto 0 do (setf n (logior (ash n 8) (aref v (+ off i))))) n))))

(declaim (inline digits->integer))
(defun digits->integer (d0 d1 d2 d3)
  "The integer d3·2^192 + d2·2^128 + d1·2^64 + d0 (each an unsigned 64-bit digit), built as one
   bignum: assembling it through ASH and LOGIOR makes ~7 intermediate bignums per 32-byte value,
   and decoding dominates a scan."
  (declare (type (unsigned-byte 64) d0 d1 d2 d3) (optimize (speed 3) (safety 0)))
  (let ((n (cond ((/= d3 0) 4) ((/= d2 0) 3) ((/= d1 0) 2) (t 1))))
    (declare (type (integer 1 4) n))
    (if (and (= n 1) (< d0 most-positive-fixnum))
        d0
        (let* ((top (case n (1 d0) (2 d1) (3 d2) (t d3)))
               (len (if (logbitp 63 top) (1+ n) n))          ; two's complement: a set top bit needs a 0 digit
               (b (sb-bignum:%allocate-bignum len)))
          (sb-bignum:%bignum-set b 0 d0)
          (when (> len 1) (sb-bignum:%bignum-set b 1 (if (> n 1) d1 0)))
          (when (> len 2) (sb-bignum:%bignum-set b 2 (if (> n 2) d2 0)))
          (when (> len 3) (sb-bignum:%bignum-set b 3 (if (> n 3) d3 0)))
          (when (> len 4) (sb-bignum:%bignum-set b 4 0))
          b))))

(defun get-le-wide (v off k)
  "The K-byte (20 or 32) little-endian unsigned integer at OFF in V; = (get-le v off k), read a
   64-bit digit at a time (the hosts are little-endian: arm64, x86-64)."
  (declare (type octets v) (type fixnum off) (type (member 20 32) k) (optimize (speed 3) (safety 0)))
  #+big-endian (error "get-le-wide: a little-endian host only")
  (sb-sys:with-pinned-objects (v)
    (let ((sap (sb-sys:vector-sap v)))
      (if (= k 32)
          (digits->integer (sb-sys:sap-ref-64 sap off) (sb-sys:sap-ref-64 sap (+ off 8))
                           (sb-sys:sap-ref-64 sap (+ off 16)) (sb-sys:sap-ref-64 sap (+ off 24)))
          (digits->integer (sb-sys:sap-ref-64 sap off) (sb-sys:sap-ref-64 sap (+ off 8))
                           (sb-sys:sap-ref-32 sap (+ off 16)) 0)))))

(defun decode-column (type raw n &optional mask (raw-len (length raw)))
  "The N values of a column from its raw bytes (RAW[0, RAW-LEN)), as a simple-vector; with MASK (a
   bit-vector), only the rows whose bit is 1 are decoded, the others read NIL (skipped, not built)."
  (declare (type octets raw) (type fixnum n raw-len) (type (or null simple-bit-vector) mask) (optimize (speed 3)))
  (let ((out (make-array n :initial-element nil)) (off 0) (w (column-width type)))
    (declare (type fixnum off))
    (macrolet ((each (form &optional (skip `(incf off w)))
                 `(dotimes (i n) (if (and mask (zerop (sbit mask i))) ,skip (setf (svref out i) ,form)))))
      (ecase type
        ((:u8 :u16 :u32 :u64) (let ((w w)) (declare (type (integer 1 8) w)) (each (prog1 (get-le raw off w) (incf off w)))))
        ((:addr :u256) (let ((w w)) (declare (type (member 20 32) w)) (each (prog1 (get-le-wide raw off w) (incf off w)))))
        (:i64 (each (let ((u (get-le raw off 8))) (incf off 8) (if (>= u (ash 1 63)) (- u (ash 1 64)) u)) (incf off 8)))
        (:optaddr (each (prog1 (if (zerop (aref raw off)) nil (get-le-wide raw (1+ off) 20)) (incf off 21)) (incf off 21)))
        (:optu64 (each (prog1 (if (zerop (aref raw off)) nil (get-le raw (1+ off) 8)) (incf off 9)) (incf off 9)))
        (:u256list (each (let ((k (aref raw off)))
                           (incf off)
                           (loop repeat k collect (get-le-wide raw off 32) do (incf off 32)))
                         (incf off (1+ (* 32 (aref raw off))))))
        (:bytes (each (let ((len (get-le raw off 4)))
                        (declare (type fixnum len))
                        (incf off 4)
                        (prog1 (bytes->hex raw off (+ off len)) (incf off len)))
                      (incf off (+ 4 (the fixnum (get-le raw off 4))))))))
    (unless (= off raw-len) (error "column ~A: ~D trailing bytes" type (- raw-len off)))
    out))

(defun decode-group (buf off kind &key cols mask-cols mask-fn)
  "The group at OFF in BUF (Format.lean decodeGroupAny): (values columns next-off mask), COLUMNS
   a simple-vector as long as the group is wide (cols-at: an older group of a table that has
   since gained columns is narrower), with the decoded values (a simple-vector) at each
   requested position (all when COLS is NIL). NIL when BUF holds no complete group at OFF (a
   torn tail); (values :index next-off) at the history index section.
   MASK-FN (columns n) -> bit-vector or NIL: called with only MASK-COLS decoded; the other
   columns are then decoded at the rows whose bit is 1 (a filter before the decode; NIL: all)."
  (declare (type octets buf))
  (let ((len (length buf)))
    (when (< len (+ off 4)) (return-from decode-group nil))
    (cond ((equalp (subseq buf off (+ off 4)) +index-magic+)
           (when (< len (+ off 8)) (return-from decode-group nil))
           (let ((ln (get-le buf (+ off 4) 4)))
             (return-from decode-group (if (>= len (+ off ln)) (values :index (+ off ln)) nil))))
          ((not (equalp (subseq buf off (+ off 4)) +magic+))
           (error "not a fact-log group at offset ~D" off)))
    (when (< len (+ off +header-fixed+)) (return-from decode-group nil))
    (let* ((total (get-le buf (+ off 4) 4)) (n (get-le buf (+ off 8) 4))
           (ncols (aref buf (+ off 28))) (types (cols-at kind ncols)))
      (when (< len (+ off total)) (return-from decode-group nil))
      (unless types (error "~A: group has ~D columns, the table ~D" kind ncols (length (table-cols kind))))
      (let* ((dir (+ off +header-fixed+)) (pay (+ off +header-fixed+ (* +dir-entry+ ncols)))
             (out (make-array ncols :initial-element nil))
             (entries (loop for i from 0 for type in types
                            for codec = (aref buf (+ dir (* +dir-entry+ i)))
                            for raw-len = (get-le buf (+ dir 1 (* +dir-entry+ i)) 4)
                            for enc-len = (get-le buf (+ dir 5 (* +dir-entry+ i)) 4)
                            collect (list i type codec raw-len pay enc-len) do (incf pay enc-len)))
             (mask nil))
        (unless (= pay (+ off total)) (error "~A: payloads end at ~D, header says ~D" kind pay (+ off total)))
        (flet ((decode (e mask)
                 (destructuring-bind (i type codec raw-len pay enc-len) e
                   (let ((raw (if (zerop codec)
                                  (subseq buf pay (+ pay enc-len))
                                  (zstd-decompress buf pay (+ pay enc-len) raw-len (scratch-octets raw-len)))))
                     (when (and (zerop codec) (/= enc-len raw-len)) (error "~A column ~D: ~D raw bytes, directory says ~D" kind i enc-len raw-len))
                     (setf (svref out i) (decode-column type raw n mask raw-len))))))
          (let ((wanted (remove-if-not (lambda (e) (or (null cols) (member (first e) cols))) entries)))
            (when mask-fn
              (dolist (e wanted) (when (member (first e) mask-cols) (decode e nil)))
              (setf mask (funcall mask-fn out n) wanted (remove-if (lambda (e) (member (first e) mask-cols)) wanted)))
            (unless (and mask (not (find 1 mask))) (dolist (e wanted) (decode e mask)))))
        (values out (+ off total) mask)))))

(defun columns->rows (columns)
  "Rows (lists) from a group's columns."
  (let ((n (length (svref columns 0))))
    (loop for i below n collect (loop for c across columns collect (svref c i)))))

(defun map-fct-groups (fn buf kind &key cols (start 0))
  "Call FN on (columns next-off) for every complete group from START; stops at the index
   section or a torn tail. Returns the offset where it stopped."
  (let ((off start))
    (loop
      (multiple-value-bind (columns next) (decode-group buf off kind :cols cols)
        (when (or (null columns) (eq columns :index)) (return off))
        (funcall fn columns next)
        (setf off next)))))

(defun read-fct-rows (path kind)
  (let ((rows '()))
    (map-fct-groups (lambda (columns next) (declare (ignore next))
                      (setf rows (nconc rows (columns->rows columns))))
                    (read-file-bytes path) kind)
    rows))

(defun kind-of-path (path)
  "The table a rows file belongs to, from its directory name."
  (intern (string-upcase (car (last (pathname-directory path)))) :keyword))

(defun parse-text-row (line)
  "One text row — `(block tx … )` with decimal integers, NIL, a list of integers (topics), a
   \"hex\" string (log data) — as the CL row model, without READ (which is 5x slower on
   bignums). A trailing keyword (the test-only :skew) is kept as a keyword."
  (declare (type simple-string line))
  (let ((pos 1) (end (1- (length line))) (out '()))
    (loop
      (loop while (and (< pos end) (char= (char line pos) #\Space)) do (incf pos))
      (when (>= pos end) (return (nreverse out)))
      (let ((c (char line pos)))
        (cond ((char= c #\()
               (let ((close (position #\) line :start pos)) (items '()) (p (1+ pos)))
                 (loop
                   (loop while (and (< p close) (char= (char line p) #\Space)) do (incf p))
                   (when (>= p close) (return))
                   (let ((e (or (position #\Space line :start p :end close) close)))
                     (push (parse-integer line :start p :end e) items) (setf p e)))
                 (push (nreverse items) out) (setf pos (1+ close))))
              ((char= c #\")
               (let ((close (position #\" line :start (1+ pos))))
                 (push (subseq line (1+ pos) close) out) (setf pos (1+ close))))
              (t (let ((e (or (position #\Space line :start pos :end end) end)))
                   (push (cond ((string= line "NIL" :start1 pos :end1 e) nil)
                               ((char= c #\:) (intern (string-upcase (subseq line (1+ pos) e)) :keyword))
                               (t (parse-integer line :start pos :end e)))
                         out)
                   (setf pos e))))))))

(defun read-shard (path &optional kind)
  "Rows of one shard file, in file order, in the CL row model; a compacted text shard is
   inflated, a binary one decoded."
  (let ((kind (or kind (kind-of-path path))))
    (if (string= (pathname-type path) "fct")
        (read-fct-rows path kind)
        (flet ((slurp (s) (let ((rows '()))
                            (loop for line = (read-line s nil nil) while line
                                  do (when (and (plusp (length line)) (char= (char line 0) #\())
                                       (push (parse-text-row (coerce line 'simple-string)) rows)))
                            (nreverse rows))))
          (if (string= (pathname-type path) "gz")
              (gunzip-stream path #'slurp)
              (with-open-file (s path) (slurp s)))))))

;;; --- The group builder: the writer's encoder (Format.lean encodeGroup) ----------------
(defstruct (group-builder (:constructor %make-group-builder))
  kind (types #() :type simple-vector) (cols #() :type simple-vector) (rows 0 :type fixnum) first-block last-block
  (width nil)                                           ; the pending rows' width (colsAt): one per group
  (content +fnv-basis+ :type (unsigned-byte 64))       ; FNV over the canonical row bytes so far
  (raw-bytes 0 :type fixnum)                            ; raw bytes buffered (flush policy)
  key-addrs key-slots)  ; indexed tables: every row's key (address; storage_diff: slot) since the
                        ; shard began, the shard index's input (row order; integers, not bytes)

(defun make-group-builder (kind)
  (let ((types (table-cols kind)))
    (unless types (error "no such fact table: ~A" kind))
    (%make-group-builder :kind kind :types (coerce types 'simple-vector)
                         :cols (coerce (loop repeat (length types) collect (make-buf)) 'simple-vector)
                         :key-addrs (and (indexed-p kind) (make-array 1024 :adjustable t :fill-pointer 0))
                         :key-slots (and (string= (table-name kind) "storage_diff")
                                         (make-array 1024 :adjustable t :fill-pointer 0)))))

(defun builder-push-fields! (gb src start &optional (width (length (group-builder-types gb))))
  "Append the row whose field values, in column order, are SRC[START, START + WIDTH) (SRC a
   simple-vector) to the pending group: the one row encoder — the writer passes its capture
   buffer (full width), list rows go through `builder-push!`. WIDTH below the table's is an
   older row (cols-at); a group holds rows of one width."
  (declare (type simple-vector src) (type fixnum start width))
  (let* ((types (group-builder-types gb)) (cols (group-builder-cols gb)) (h (group-builder-content gb))
         (raw 0))
    (declare (type (unsigned-byte 64) h) (type fixnum raw))
    (unless (eql width (or (group-builder-width gb) width))
      (error "~A: a ~D-field row in a group of ~D-field rows" (group-builder-kind gb) width (group-builder-width gb)))
    (setf (group-builder-width gb) width)
    (dotimes (i width)
      (let* ((b (svref cols i)) (s (buf-fill b)))
        (encode-field! b (svref types i) (svref src (+ start i)))
        (setf h (fnv64-bytes h (buf-data b) s (buf-fill b)))
        (incf raw (- (buf-fill b) s))))
    (setf (group-builder-content gb) h)
    (incf (group-builder-raw-bytes gb) raw)
    (let ((blk (svref src start)))
      (unless (group-builder-first-block gb) (setf (group-builder-first-block gb) blk))
      (setf (group-builder-last-block gb) blk))
    (when (group-builder-key-addrs gb)
      (vector-push-extend (svref src (+ start 2)) (group-builder-key-addrs gb))
      (when (group-builder-key-slots gb) (vector-push-extend (svref src (+ start 3)) (group-builder-key-slots gb))))
    (incf (group-builder-rows gb))))

(defun builder-push! (gb row)
  "Append ROW (a list of field values in column order, as wide as the table or an older
   width of it: a row read back from an older group) to the pending group."
  (let ((n (length row)) (kind (group-builder-kind gb)))
    (unless (cols-at kind n) (error "~A: row has ~D fields, the table ~D" kind n (length (table-cols kind))))
    (builder-push-fields! gb (coerce row 'simple-vector) 0 n)))

(defun builder-content (gb) "The content hash (hex) of every row pushed so far." (hex64 (group-builder-content gb)))

(defun builder-drop-pending! (gb)
  "Forget the pending (unflushed) rows' bytes; the content hash and keys continue."
  (loop for b across (group-builder-cols gb) do (buf-reset! b))
  (setf (group-builder-rows gb) 0 (group-builder-raw-bytes gb) 0 (group-builder-width gb) nil
        (group-builder-first-block gb) nil (group-builder-last-block gb) nil))

(defun builder-finish (gb &key (codec :zstd))
  "The pending rows as one group (an octet vector), or NIL when none; the builder's columns
   are emptied (its content hash and keys continue — they are per shard)."
  (when (plusp (group-builder-rows gb))
    (let* ((cols (group-builder-cols gb)) (ncols (group-builder-width gb))
           (payloads (loop for i below ncols
                           for b = (svref cols i)
                           for raw-len = (buf-fill b)
                           for z = (and (eq codec :zstd) (plusp raw-len) (zstd-compress (buf-data b) 0 raw-len))
                           collect (if (and z (< (length z) raw-len))
                                       (list 1 raw-len z)
                                       (list 0 raw-len (subseq (buf-data b) 0 raw-len)))))
           (pay-len (reduce #'+ payloads :key (lambda (p) (length (third p)))))
           (total (+ +header-fixed+ (* +dir-entry+ ncols) pay-len))
           (out (make-buf total)))
      (unless (< total (ash 1 32)) (error "group of ~D bytes exceeds the format" total))
      (put-bytes! out +magic+) (put-le! out total 4) (put-le! out (group-builder-rows gb) 4)
      (put-le! out (group-builder-first-block gb) 8) (put-le! out (group-builder-last-block gb) 8)
      (put-le! out ncols 1)
      (dolist (p payloads) (put-le! out (first p) 1) (put-le! out (second p) 4) (put-le! out (length (third p)) 4))
      (dolist (p payloads) (put-bytes! out (third p)))
      (builder-drop-pending! gb)
      (subseq (buf-data out) 0 (buf-fill out)))))

(defun write-group! (gb stream &key (codec :zstd))
  "Flush the pending group to the binary STREAM; returns the bytes written (0 when none)."
  (let ((g (builder-finish gb :codec codec)))
    (if g (progn (write-sequence g stream) (length g)) 0)))

;;; --- The history index (History.lean) -------------------------------------------------
(defun be-bytes (n k)
  (let ((v (make-array k :element-type '(unsigned-byte 8))))
    (dotimes (i k v) (setf (aref v i) (ldb (byte 8 (* 8 (- k 1 i))) n)))))

(defun key-bytes (kind key)
  "KEY = (addr slot) for storage_diff, (addr) for account_diff."
  (if (string= (table-name kind) "storage_diff")
      (concatenate 'octets (be-bytes (first key) 20) (be-bytes (second key) 32))
      (be-bytes (first key) 20)))

(defun bytes< (a b)
  (declare (type octets a b))
  (loop for i below (min (length a) (length b))
        do (cond ((< (aref a i) (aref b i)) (return t)) ((> (aref a i) (aref b i)) (return nil)))
        finally (return (< (length a) (length b)))))

(defun bloom-bits-for (distinct)
  "The smallest power of two holding ten bits per distinct key, at least 64."
  (let ((want (* 10 distinct)) (m 64)) (loop while (< m want) do (setf m (* 2 m))) m))

(defun bloom-positions (m k key)
  (let* ((h (fnv64-bytes +fnv-basis+ key 0 (length key)))
         (h1 (ldb (byte 32 0) h)) (h2 (logior (ldb (byte 32 32) h) 1)))
    (loop for i below k collect (mod (+ h1 (* i h2)) m))))

(defun bloom-may-contain (bloom k key)
  (let ((m (* 8 (length bloom))))
    (every (lambda (p) (logbitp (logand p 7) (aref bloom (ash p -3)))) (bloom-positions m k key))))

(defun build-index (gb)
  "The index of the rows GB has seen since its shard began (its key columns, row order).
   (values perm bloom distinct): perm = row positions sorted by key then position, bloom =
   the filter's bytes. Keys compare as integers — address, then slot — which is the order of
   their fixed-width big-endian bytes (History.lean's key order)."
  (let* ((as (coerce (group-builder-key-addrs gb) 'simple-vector))
         (ss (and (group-builder-key-slots gb) (coerce (group-builder-key-slots gb) 'simple-vector)))
         (n (length as)) (perm (make-array n)))
    (dotimes (i n) (setf (svref perm i) i))
    (flet ((key< (i j)
             (let ((a (aref as i)) (b (aref as j)))
               (cond ((< a b) t) ((> a b) nil)
                     ((and ss (/= (aref ss i) (aref ss j))) (< (aref ss i) (aref ss j)))
                     (t (< i j))))))
      (setf perm (stable-sort perm #'key<)))
    (let ((firsts '()) (prev -1) (kb (make-buf 52)))
      ;; the first row of each distinct key, in key order
      (loop for i across perm
            do (unless (and (>= prev 0) (= (aref as i) (aref as prev)) (or (null ss) (= (aref ss i) (aref ss prev))))
                 (push i firsts))
               (setf prev i))
      (let* ((distinct (length firsts)) (m (bloom-bits-for distinct))
             (bloom (make-array (floor m 8) :element-type '(unsigned-byte 8) :initial-element 0)))
        (dolist (i firsts)
          ;; the key's canonical bytes: big-endian address (20), then slot (32)
          (buf-reset! kb)
          (put-le! kb (aref as i) 20)
          (when ss (put-le! kb (aref ss i) 32))
          (let ((d (buf-data kb)))
            (setf (subseq d 0 20) (reverse (subseq d 0 20)))
            (when ss (setf (subseq d 20 52) (reverse (subseq d 20 52))))
            (dolist (p (bloom-positions m +bloom-k+ (subseq d 0 (buf-fill kb))))
              (setf (aref bloom (ash p -3)) (logior (aref bloom (ash p -3)) (ash 1 (logand p 7)))))))
        (values perm bloom distinct)))))

(defun encode-index (perm bloom)
  "The index section bytes (History.lean encodeIndex)."
  (let ((out (make-buf (+ +index-header+ (* 4 (length perm)) (length bloom)))))
    (put-bytes! out +index-magic+) (put-le! out (+ +index-header+ (* 4 (length perm)) (length bloom)) 4)
    (put-le! out (length perm) 4) (put-le! out +bloom-k+ 1) (put-le! out (length bloom) 4)
    (loop for p across perm do (put-le! out p 4))
    (put-bytes! out bloom)
    (subseq (buf-data out) 0 (buf-fill out))))

(defun decode-index (buf off)
  "(values perm k bloom) of the index section at OFF."
  (unless (equalp (subseq buf off (+ off 4)) +index-magic+) (error "no index section at ~D" off))
  (let* ((n (get-le buf (+ off 8) 4)) (k (aref buf (+ off 12))) (bl (get-le buf (+ off 13) 4))
         (p0 (+ off +index-header+)) (perm (make-array n)))
    (dotimes (i n) (setf (svref perm i) (get-le buf (+ p0 (* 4 i)) 4)))
    (values perm k (subseq buf (+ p0 (* 4 n)) (+ p0 (* 4 n) bl)))))

(defun index-section (gb)
  "The index section for the shard whose rows GB has seen (its key columns):
   (values bytes bloom-bits distinct)."
  (multiple-value-bind (perm bloom distinct) (build-index gb)
    (values (encode-index perm bloom) (* 8 (length bloom)) distinct)))

(defun fct-builder (path kind)
  "A builder that continues binary shard PATH: every row of it decoded and pushed, so its
   content hash and index keys cover them, with nothing pending (a resume inside a range;
   group by group: a range begun by an older writer holds narrower groups)."
  (let ((gb (make-group-builder kind)))
    (map-fct-groups (lambda (columns next) (declare (ignore next))
                      (dolist (row (columns->rows columns)) (builder-push! gb row))
                      (builder-drop-pending! gb))
                    (read-file-bytes path) kind)
    gb))

(defun key-columns (kind) (if (string= (table-name kind) "storage_diff") '(2 3) '(2)))
(defun value-columns (kind) (if (string= (table-name kind) "storage_diff") '((4) (5)) '((3 5 7) (4 6 8))))

(defun shard-changes (path kind key &optional footer)
  "The changes of KEY in one shard, in file order: list of (block tx pre post), pre/post the
   value (storage) or (nonce balance code) list (account). Binary shards go through their
   index (the filter first) once their bytes match the footer's digest — a corrupt filter
   would otherwise answer \"never changed\" without a word; text shards are scanned."
  (let ((kc (key-columns kind)) (pre-c (first (value-columns kind))) (post-c (second (value-columns kind))))
    (flet ((val (row cs) (if (null (cdr cs)) (nth (car cs) row) (mapcar (lambda (c) (nth c row)) cs))))
      (if (and (string= (pathname-type path) "fct") footer (getf footer :index))
          (let* ((buf (read-file-bytes path)) (kb (key-bytes kind key)))
            (when (and (getf footer :fnv)            ; a footer without a digest: taken at its word
                       (not (and (= (length buf) (getf footer :bytes))
                                 (string= (hex64 (fnv64-bytes +fnv-basis+ buf 0 (length buf))) (getf footer :fnv)))))
              (error "~A does not match its footer's digest (~D bytes, footer ~D ~A): refusing its index" path
                     (length buf) (getf footer :bytes) (getf footer :fnv)))
            (multiple-value-bind (perm k bloom) (decode-index buf (getf footer :index))
              (unless (bloom-may-contain bloom k kb) (return-from shard-changes '()))
              (let ((want (remove-duplicates (append '(0 1) kc pre-c post-c))) (cols (make-hash-table)))
                (map-fct-groups (lambda (columns next) (declare (ignore next))
                                  (dolist (i want) (push (svref columns i) (gethash i cols))))
                                buf kind :cols want)
                (let ((col (make-hash-table)))
                  (dolist (i want) (setf (gethash i col) (apply #'concatenate 'simple-vector (nreverse (gethash i cols)))))
                  (flet ((key-at (p) (concatenate 'octets (be-bytes (svref (gethash 2 col) p) 20)
                                                  (if (cdr kc) (be-bytes (svref (gethash 3 col) p) 32) #())))
                         (field (i p) (svref (gethash i col) p)))
                    ;; binary search the key's run in perm
                    (let ((lo 0) (hi (length perm)))
                      (loop while (< lo hi)
                            do (let ((mid (floor (+ lo hi) 2)))
                                 (if (bytes< (key-at (svref perm mid)) kb) (setf lo (1+ mid)) (setf hi mid))))
                      (loop for j from lo below (length perm)
                            for p = (svref perm j)
                            while (equalp (key-at p) kb)
                            collect (list (field 0 p) (field 1 p)
                                          (if (cdr pre-c) (mapcar (lambda (c) (field c p)) pre-c) (field (car pre-c) p))
                                          (if (cdr post-c) (mapcar (lambda (c) (field c p)) post-c) (field (car post-c) p))))))))))
          (loop for row in (read-shard path kind)
                when (equal (mapcar (lambda (c) (nth c row)) kc) key)
                  collect (list (first row) (second row) (val row pre-c) (val row post-c)))))))

(defun read-blooms (dir kind)
  "lo -> (k offset . nbytes) from <dir>/<kind>/blooms.idx (scripts/factlog.py index), read in
   place: the 13-byte record headers only, the filters stay on disk (`bloom-at`), so memory is
   one entry per shard however large the history. An empty table when absent."
  (let ((tbl (make-hash-table)) (p (merge-pathnames (format nil "~(~A~)/blooms.idx" kind) (as-dir dir)))
        (head (make-array 13 :element-type '(unsigned-byte 8))))
    (with-open-file (in p :element-type '(unsigned-byte 8) :if-does-not-exist nil)
      (when in
        (let ((size (file-length in)) (off 0))
          (loop while (<= (+ off 13) size)
                do (file-position in off)
                   (read-sequence head in)
                   (let ((lo (get-le head 0 8)) (bl (floor (get-le head 8 4) 8)) (k (aref head 12)))
                     (when (> (+ off 13 bl) size) (return))   ; torn tail of an interrupted build
                     (setf (gethash lo tbl) (list* k (+ off 13) bl))
                     (incf off (+ 13 bl)))))))
    tbl))

(defun bloom-at (in entry)
  "The filter bytes of a read-blooms ENTRY, from the open blooms.idx stream IN."
  (let ((v (make-array (cddr entry) :element-type '(unsigned-byte 8))))
    (file-position in (cadr entry))
    (read-sequence v in)
    v))

(defun call-with-key-changes (dir kind key fn)
  "(FN ranges changes): RANGES the shards of KIND, (lo hi path) in block order; (CHANGES range)
   KEY's changes in that shard, (block tx pre post) in chain order — a shard whose filter in
   blooms.idx excludes KEY is skipped unread, else its own index is searched."
  (let* ((ranges (shard-ranges dir kind)) (blooms (read-blooms dir kind)) (kb (key-bytes kind key)))
    (with-open-file (bin (merge-pathnames (format nil "~(~A~)/blooms.idx" kind) (as-dir dir))
                         :element-type '(unsigned-byte 8) :if-does-not-exist nil)
      (funcall fn ranges
               (lambda (r)
                 (let ((bl (and bin (gethash (first r) blooms))))
                   (if (and bl (not (bloom-may-contain (bloom-at bin bl) (car bl) kb)))
                       '()
                       (shard-changes (third r) kind key (read-footer (shard-file dir kind (first r) (second r) "sealed"))))))))))

(defun state-at (dir kind key block)
  "The value of KEY at the end of BLOCK — storage: the slot value; account: (nonce balance
   code-hash) — through the shards' history indexes (History.lean `lookup`): the last change at
   or before BLOCK gives its post, else the first change after it gives its pre. :unknown when
   the log never changed the key."
  (call-with-key-changes
   dir kind key
   (lambda (ranges changes)
     (let* ((below (remove-if-not (lambda (r) (<= (first r) block)) ranges))
            (here (car (last below))))
       (when (and here (>= (second here) block))
         (let* ((c (funcall changes here)) (before (remove-if-not (lambda (x) (<= (first x) block)) c)))
           (cond (before (return-from state-at (fourth (car (last before)))))
                 (c (return-from state-at (third (first c)))))
           (setf below (butlast below))))
       (dolist (r (reverse below))
         (let ((c (funcall changes r))) (when c (return-from state-at (fourth (car (last c)))))))
       (dolist (r ranges)
         (when (> (first r) block)
           (let ((c (funcall changes r))) (when c (return-from state-at (third (first c)))))))
       :unknown))))

(defun key-history (dir kind key lo hi)
  "Every change of KEY with LO <= block <= HI, in chain order: ((block tx pre post) …), pre and
   post as `state-at` gives them. Through the history index: only the shards overlapping
   [LO, HI] whose filter may hold KEY are read; in each, the key and value columns only are
   decoded and KEY's rows found by binary search in the index."
  (call-with-key-changes
   dir kind key
   (lambda (ranges changes)
     (loop for r in ranges
           when (and (<= (first r) hi) (>= (second r) lo))
             append (remove-if-not (lambda (c) (<= lo (first c) hi)) (funcall changes r))))))

;;; --- Prefixes: the rows of blocks <= N (the resume pull-back) --------------------------
(defun fct-prefix-end (path kind n)
  "(values offset rows min max straddler) for the binary rows file PATH: OFFSET ends the last
   whole group of blocks <= N; STRADDLER is the rows (<= N) of a group that also holds later
   blocks (a converted shard's groups span blocks), or NIL."
  (let ((buf (read-file-bytes path)) (off 0) (rows 0) (mn nil) (mx nil) (straddler nil))
    (loop
      (multiple-value-bind (columns next) (decode-group buf off kind)
        (when (or (null columns) (eq columns :index)) (return))
        (let ((blocks (svref columns 0)) (n-rows (length (svref columns 0))))
          (cond ((and (plusp n-rows) (> (svref blocks 0) n)) (return))
                ((and (plusp n-rows) (> (svref blocks (1- n-rows)) n))
                 (setf straddler (remove-if-not (lambda (row) (<= (first row) n)) (columns->rows columns)))
                 (dolist (row straddler) (incf rows) (setf mn (if mn (min mn (first row)) (first row)) mx (if mx (max mx (first row)) (first row))))
                 (return))
                (t (incf rows n-rows)
                   (when (plusp n-rows)
                     (setf mn (if mn (min mn (svref blocks 0)) (svref blocks 0))
                           mx (if mx (max mx (svref blocks (1- n-rows))) (svref blocks (1- n-rows)))))
                   (setf off next))))))
    (values off rows mn mx straddler)))

;;; --- Converting text shards (the one encoder, applied to the old form) -------------------
(defun cut-blocks (dir kind lo hi)
  "The blocks of LO..HI a resume can pull this shard back to: every anchor in anchors.sexp
   and every `.at-N` checkpoint prefix of the shard. A group must end at each of them."
  (let ((anchors (with-open-file (in (merge-pathnames "anchors.sexp" (truename dir)) :if-does-not-exist nil)
                   (and in (let ((*read-eval* nil))
                             (loop for form = (read in nil nil) while form
                                   when (and (consp form) (integerp (first form))) collect (first form))))))
        (ats (loop for at in (directory (shard-file dir kind lo hi "at-*"))
                   for rec = (read-footer at) when (and rec (getf rec :block)) collect (getf rec :block))))
    (remove-if-not (lambda (b) (<= lo b hi)) (append anchors ats))))

(defun convert-shard! (dir kind lo hi &key (group-rows 16384) delete)
  "Encode KIND's text shard LO-HI as .fct (groups of GROUP-ROWS rows, zstd per column, the
   history index for diff tables), then write the footer with :content/:index and verify
   by decoding the result: its rows must equal the text rows, fact for fact, and its
   content hash the one the builder computed. Returns the footer; with DELETE the text
   rows file is removed after the gate passes. A group also ends after every block a
   resume can pull the shard back to (CUT-BLOCKS), as the writer's commit flushes do."
  (let* ((text (or (probe-file (shard-file dir kind lo hi "sexp")) (probe-file (shard-file dir kind lo hi "sexp.gz"))))
         (fct (namestring (shard-file dir kind lo hi "fct"))) (tmp (concatenate 'string fct ".tmp"))
         (sealed (shard-file dir kind lo hi "sealed")) (ft (read-footer sealed)))
    (unless text (error "no text shard ~A ~D-~D" kind lo hi))
    (let* ((rows (read-shard text kind)) (gb (make-group-builder kind)) (index-off nil) (bloom-bits nil) (keys nil)
           (cuts (cut-blocks dir kind lo hi)))
      (with-open-file (out tmp :direction :output :element-type '(unsigned-byte 8) :if-exists :supersede :if-does-not-exist :create)
        (loop for (row . more) on rows
              do (builder-push! gb row)
                 ;; a group ends at a block boundary once it holds GROUP-ROWS rows: no group
                 ;; straddles a block, so the resume pull-back cuts at group boundaries only
                 (when (and (or (>= (group-builder-rows gb) group-rows) (member (first row) cuts))
                            (or (null more) (/= (first (car more)) (first row))))
                   (write-group! gb out)))
        (write-group! gb out)
        (when (indexed-p kind)
          (setf index-off (file-position out))
          (multiple-value-bind (section bits distinct) (index-section gb)
            (write-sequence section out) (setf bloom-bits bits keys distinct)))
        (finish-output out))
      ;; the gate: decode what was written and compare fact for fact
      (let ((back (read-fct-rows tmp kind)))
        (unless (equal back rows)
          (delete-file tmp)
          (error "convert ~A ~D-~D: decoded rows differ from the text rows (~D vs ~D)" kind lo hi (length back) (length rows))))
      (sb-posix:rename tmp fct)
      (multiple-value-bind (bytes fnv) (digest fct)
        (let ((new (append (list :kind (intern (string-upcase (table-name kind)) :keyword) :lo lo :hi hi
                                 :rows (length rows)
                                 :first-block (getf ft :first-block (and rows (first (first rows))))
                                 :last-block (getf ft :last-block (and rows (first (car (last rows)))))
                                 :min-block (and rows (reduce #'min rows :key #'first))
                                 :max-block (and rows (reduce #'max rows :key #'first))
                                 :bytes bytes :fnv fnv :content (builder-content gb))
                           (and index-off (list :index index-off :bloom-bits bloom-bits :bloom-k +bloom-k+ :keys keys))
                           (list :version (getf ft :version) :versions (getf ft :versions)))))
          (when ft
            (with-open-file (f sealed :direction :output :if-exists :supersede)
              (let ((*print-pretty* nil)) (prin1 new f) (terpri f))))
          ;; a live (unsealed) shard: its checkpoint prefix records `.at-N` digest the text
          ;; prefix; re-digest the binary one so a resume inside the range keeps its rows
          (dolist (at (directory (shard-file dir kind lo hi "at-*")))
            (let ((rec (read-footer at)))
              (when (and rec (getf rec :block))
                (multiple-value-bind (off nrows) (fct-prefix-end fct kind (getf rec :block))
                  (multiple-value-bind (pbytes pfnv) (digest fct :limit off)
                    (declare (ignorable nrows))
                    (setf (getf rec :bytes) pbytes (getf rec :fnv) pfnv)
                    (with-open-file (f at :direction :output :if-exists :supersede)
                      (let ((*print-pretty* nil)) (prin1 rec f) (terpri f))))))))
          (when delete (delete-file text))
          new)))))

(defun convert-dir! (dir &key kinds delete (group-rows 16384))
  "Convert every text shard of DIR (all tables, or KINDS), sealed or live (the replay must
   be stopped). Prints one line per shard; returns the count."
  (let ((n 0))
    (dolist (kind (or kinds +kinds+))
      (dolist (r (shard-ranges dir kind))
        (destructuring-bind (lo hi path) r
          (when (not (string= (pathname-type path) "fct"))
            (let ((t0 (get-internal-real-time)))
              (convert-shard! dir kind lo hi :group-rows group-rows :delete delete)
              (format t "~&[convert] ~(~A~) ~D-~D ~,1F s~%" kind lo hi
                      (/ (- (get-internal-real-time) t0) internal-time-units-per-second))
              (force-output) (incf n))))))
    n))

;;; --- Scans ------------------------------------------------------------------------
(defstruct factlog dir (shards (make-hash-table :test 'eq)))

(defun open-factlog (dir)
  "Index the shard directory (no rows are read yet)."
  (let ((fl (make-factlog :dir (as-dir dir))))
    (dolist (kind +kinds+)
      (setf (gethash kind (factlog-shards fl)) (shard-ranges (factlog-dir fl) kind)))
    fl))

(defun factlog-coverage (fl)
  "(lo . hi) of the blocks the log covers, from the block shards' footers."
  (let ((lo nil) (hi nil))
    (dolist (r (gethash :block (factlog-shards fl)))
      (let ((ft (read-footer (shard-file (factlog-dir fl) :block (first r) (second r) "sealed"))))
        (when (getf ft :first-block)
          (setf lo (if lo (min lo (getf ft :first-block)) (getf ft :first-block))
                hi (if hi (max hi (getf ft :last-block)) (getf ft :last-block))))))
    (cons lo hi)))

(defun map-rows (fn dir kind lo hi &key cols where)
  "Call FN on each row of KIND with LO <= block <= HI, in chain order, one group in memory at
   a time. COLS: the columns to decode (NIL: all); the others are NIL in the row and cost
   nothing but their bytes on disk. WHERE (column . predicate): that column is decoded first
   and the others only at the rows whose value it accepts (a group with none is skipped)."
  (let ((cols (and cols (union (list 0) (if where (cons (car where) cols) cols)))))
    (dolist (r (shard-ranges dir kind))
      (destructuring-bind (slo shi path) r
        (when (and (<= slo hi) (>= shi lo))
          (if (string= (pathname-type path) "fct")
              (let ((buf (read-file-bytes path)) (off 0))
                (loop
                  (multiple-value-bind (columns next mask)
                      (decode-group buf off kind
                                    :cols cols :mask-cols (and where (list (car where)))
                                    :mask-fn (and where
                                                  (lambda (columns n)
                                                    (let ((m (make-array n :element-type 'bit))
                                                          (c (svref columns (car where))))
                                                      (dotimes (i n m)
                                                        (setf (sbit m i) (if (funcall (cdr where) (svref c i)) 1 0)))))))
                    (when (or (null columns) (eq columns :index)) (return))
                    (setf off next)
                    (when (or (null mask) (find 1 mask))
                      (dotimes (i (length (or (svref columns 0) (svref columns (car where)))))
                        (when (or (null mask) (= 1 (sbit mask i)))
                          (let ((row (loop for c across columns collect (and c (svref c i)))))
                            (when (<= lo (first row) hi) (funcall fn row)))))))))
              (dolist (row (read-shard path kind))
                (when (and (<= lo (first row) hi)
                           (or (null where) (funcall (cdr where) (nth (car where) row))))
                  (funcall fn row)))))))))

(defun fact-scan (fl kind lo hi)
  "All rows of KIND with LO <= block <= HI, in (block, tx, emission) order."
  (let ((out '()))
    (map-rows (lambda (row) (push row out)) (factlog-dir fl) kind lo hi)
    (nreverse out)))

(defun fact-logs (fl addr topic0 lo hi)
  "Logs emitted by ADDR whose topic0 is TOPIC0, LO <= block <= HI: the address column is
   decoded first, the rest only at ADDR's logs."
  (let ((out '()))
    ;; (block tx log-index addr (topics...) data)
    (map-rows (lambda (row) (let ((tps (fifth row))) (when (and tps (= (first tps) topic0)) (push row out))))
              (factlog-dir fl) :log lo hi :where (cons 3 (lambda (a) (= a addr))))
    (nreverse out)))

;;; --- CLI ---------------------------------------------------------------------

(defun check-vectors (path)
  "The Lean-emitted vectors: decode each group to its rows, re-encode the rows (raw codec) to
   the same bytes, hash them to the content hash; build the index of the indexed tables'
   sample keys and compare perm, bloom and the section bytes. Exits 1 on a mismatch."
  (let ((bad 0) (*read-eval* nil))
    (with-open-file (in path)
      (loop for v = (read in nil :eof) until (eq v :eof)
            do (let* ((kind (intern (string-upcase (getf v :table)) :keyword))
                      (rows (getf v :rows)) (group (hex->bytes (getf v :group)))
                      (gb (make-group-builder kind)) (ok t))
                 (multiple-value-bind (columns next) (decode-group (concatenate 'octets group #(170)) 0 kind)
                   (unless (and columns (equal (columns->rows columns) rows) (= next (length group)))
                     (setf ok nil)))
                 (dolist (row rows) (builder-push! gb row))
                 (unless (string= (builder-content gb) (getf v :content)) (setf ok nil))
                 (let ((re (builder-finish gb :codec :raw)))
                   (unless (equalp re group) (setf ok nil))
                   (when (getf v :index)
                     (multiple-value-bind (perm bloom) (build-index gb)
                       (unless (and (equal (coerce perm 'list) (getf v :perm))
                                    (string= (bytes->hex bloom) (getf v :bloom))
                                    (= (* 8 (length bloom)) (getf v :bloom-bits))
                                    (equalp (encode-index perm bloom) (hex->bytes (getf v :index))))
                         (setf ok nil)))))
                 (format t "~(~13A~) ~A (~D rows)~%" kind (if ok "OK" "MISMATCH") (length rows))
                 (unless ok (incf bad)))))
    bad))

(let ((args (cdr sb-ext:*posix-argv*)))
  (when (>= (length args) 2)
    (cond ((and (>= (length args) 3) (string= (second args) "vectors"))
           (sb-ext:exit :code (if (zerop (check-vectors (third args))) 0 1)))
          ((string= (second args) "convert")
           (let* ((rest (cddr args)) (delete (member "--delete" rest :test #'string=))
                  (kinds (remove "--delete" rest :test #'string=)))
             (format t "~&converted ~D shards~%"
                     (convert-dir! (first args) :delete (and delete t)
                                   :kinds (mapcar (lambda (k) (intern (string-upcase k) :keyword)) kinds))))))))
