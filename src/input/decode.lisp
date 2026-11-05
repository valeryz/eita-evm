;;;; input/decode.lisp — how a replay receives its blocks: the decoder (and, in source.lisp, the
;;;; block source).
;;;;
;;;; Every block the replay runs is a CHAIN-BLOCK decoded here, once, from the bytes of its
;;;; JSON-RPC block object (eth_getBlockByNumber with full transactions). Where the bytes
;;;; come from is a BLOCK SOURCE (below): the one seam between execution and acquisition.
;;;; The driver (chains/driver.lisp), the chain specs and the header gates only ever call
;;;; fetch-block / fetch-verified-block / fetch-block-hash / fetch-receipts / fetch-uncles,
;;;; which ask *block-source*.
;;;;
;;;; This repository ships one source, DIRECTORY-BLOCK-SOURCE: a directory of per-block JSON
;;;; files you produce with your own node or tools (docs/block-input.md gives the format).
;;;; Any other source (an RPC follower, an archive reader) is a MAKE-BLOCK-SOURCE with its
;;;; own functions, installed before the driver runs: set EITA_SOURCE to a Lisp file that
;;;; defines it and sets *block-source* (the driver loads it), or set *block-source* from
;;;; your own entry script.

(in-package #:eita.input)

;;; --- Source configuration a chain spec carries (read by sources, not by execution) ----
(defvar *cache-dir* nil
  "Directory of this chain's block files (a pathname ending in /), from its chain spec.")
(defvar *rpc-url* nil
  "This chain's JSON-RPC endpoint, from its chain spec; used by sources that speak RPC.")
(defparameter *rpc-calls* 0 "RPC calls made by the source (reported in the run summary).")
(defparameter *offline-misses* 0
  "Lazy-state reads the source could not answer (a run with misses is suspect).")

;;; A source that gives up waiting for input signals INPUT-OUTAGE; replay-main exits with
;;; +exit-input-outage+ (EX_TEMPFAIL), which a supervisor can treat as "retry", not a crash.
(defparameter +exit-input-outage+ 75 "EX_TEMPFAIL: the replay's exit code after an INPUT-OUTAGE.")
(define-condition input-outage (error)
  ((what :initarg :what :reader outage-what) (secs :initarg :secs :reader outage-secs))
  (:report (lambda (c s) (format s "input outage: gave up waiting for ~A after ~D s"
                                 (outage-what c) (outage-secs c)))))

(defun addr-hex (addr) (format nil "0x~(~40,'0x~)" addr))
(defun blk-hex (n) (format nil "0x~(~x~)" n))

;;; --- Files ---------------------------------------------------------------------------

(defun jnonnull (v) (and v (not (eq v :null)) v))

;; zlib's gz* API (libz: native/libraries.lisp): inflate in-process instead of forking
;; `gzip -dc` (a fork of a multi-GB image per file) and decoding its pipe character by
;; character.
(cffi:defcfun ("gzopen" %gzopen) :pointer (path :string) (mode :string))
(cffi:defcfun ("gzread" %gzread) :int (f :pointer) (buf :pointer) (len :unsigned-int))
(cffi:defcfun ("gzclose" %gzclose) :int (f :pointer))

(defun gzip-size-hint (path)
  "The inflated size of file PATH: a gzip member's ISIZE trailer (its size mod 2^32), else
   the file's length."
  (with-open-file (in path :element-type '(unsigned-byte 8))
    (let ((len (file-length in)))
      (if (and (>= len 18) (= (read-byte in) #x1f) (= (read-byte in) #x8b))
          (progn (file-position in (- len 4))
                 (loop for k below 4 sum (ash (read-byte in) (* 8 k))))
          len))))

(defun read-file-octets (path)
  "The bytes of file PATH, inflated when it is gzip (zlib reads a plain file as it is), into
   one buffer of the size the file announces (one byte over: the read that finds the end),
   shrunk in place — no doubling, no copy (a wrong hint only costs one)."
  (let ((f (%gzopen (namestring path) "rb"))
        (buf (make-array (1+ (gzip-size-hint path)) :element-type '(unsigned-byte 8))) (len 0))
    (when (cffi:null-pointer-p f) (error "gzopen failed: ~A" path))
    (unwind-protect
         (loop (when (= len (length buf)) (setf buf (replace (make-array (* 2 len) :element-type '(unsigned-byte 8)) buf)))
               (let ((n (cffi:with-pointer-to-vector-data (p buf) (%gzread f (cffi:inc-pointer p len) (- (length buf) len)))))
                 (cond ((minusp n) (error "gzread failed: ~A" path))
                       ((zerop n) (return (sb-kernel:%shrink-vector buf len)))
                       (t (incf len n)))))
      (%gzclose f))))

(defun read-file-string (path)
  "The contents of file PATH as text, inflated when it is gzip. As octets, not through the
   per-character UTF-8 stream decoder, which was 11 % of the Arc replay (sb-sprof,
   2026-10-17): the files are RPC JSON."
  (sb-ext:octets-to-string (read-file-octets path) :external-format :latin-1))

;;; --- Decoding: a block's JSON bytes straight to values ---------------------------------
;;; Every block the replay runs is decoded ONCE, here, from the bytes of its JSON-RPC result
;;; object — whatever the block source (below) read it from — into a CHAIN-BLOCK: header
;;; fields as integers and octets, the txs as TX structs, the withdrawals, and (when the
;;; source has them) the receipts and ommer headers. The
;;; replay reads values only. No JSON tree is built: a value the replay does not use (a
;;; receipt's logs, a tx's blockHash) is skipped over. The header hash keccak(rlp(header))
;;; is computed from the same bytes, for fetch-verified-block's check. The verifier
;;; re-encodes the txs (transactionsRoot) from these TX structs, so the root ties the values
;;; that execute to the header.

(defun json-error (b i what)
  (error "block JSON: ~A at byte ~D~@[: ~S~]" what i
         (and (< i (length b)) (map 'string #'code-char (subseq b i (min (length b) (+ i 40)))))))

(declaim (inline jbyte jws))
(defun jbyte (b i)
  "Byte I of B, 0 past its end (0 matches nothing the reader expects)."
  (declare (type octets b) (type fixnum i) (optimize speed (safety 0)))
  (if (< i (length b)) (aref b i) 0))

(defun jws (b i)
  "The first index at or after I that is not blank."
  (declare (type octets b) (type fixnum i) (optimize speed (safety 0)))
  (loop while (and (< i (length b)) (<= (aref b i) 32)) do (incf i))
  i)

(defun jstring-end (b i)
  "I at a string's opening quote: the index after its closing one."
  (declare (type octets b) (type fixnum i) (optimize speed (safety 0)))
  (let ((n (length b)) (j (1+ i)))
    (declare (type fixnum n j))
    (loop (when (>= j n) (json-error b i "unterminated string"))
          (let ((c (aref b j)))
            (cond ((= c 34) (return (1+ j)))
                  ((= c 92) (incf j 2))
                  (t (incf j)))))))

(defun jskip (b i)
  "I at a value: the index after it (an object or array skipped whole)."
  (declare (type octets b) (type fixnum i) (optimize speed (safety 0)))
  (let ((n (length b)) (c (jbyte b i)))
    (declare (type fixnum n))
    (cond ((= c 34) (jstring-end b i))
          ((or (= c 123) (= c 91))
           (let ((depth 0) (j i))
             (declare (type fixnum depth j))
             (loop (when (>= j n) (json-error b i "unterminated value"))
                   (let ((c (aref b j)))
                     (cond ((= c 34) (setf j (jstring-end b j)))
                           ((or (= c 123) (= c 91)) (incf depth) (incf j))
                           ((or (= c 125) (= c 93)) (incf j) (when (zerop (decf depth)) (return j)))
                           (t (incf j)))))))
          ((zerop c) (json-error b i "value expected"))
          (t (loop for j of-type fixnum from i
                   while (and (< j n) (let ((c (aref b j))) (not (or (= c 44) (= c 125) (= c 93) (<= c 32)))))
                   finally (return j))))))

(defmacro do-jobject ((b i key-start key-end) &body body)
  "Iterate the object at index I of B: per member, KEY-START..KEY-END bound to its key's
   bytes and I to its value; BODY returns the index after the value. The index after the
   object."
  `(progn
     (unless (= (jbyte ,b ,i) 123) (json-error ,b ,i "object expected"))
     (setf ,i (jws ,b (1+ ,i)))
     (if (= (jbyte ,b ,i) 125)
         (1+ ,i)
         (loop
           (unless (= (jbyte ,b ,i) 34) (json-error ,b ,i "key expected"))
           (let* ((,key-start (1+ ,i)) (,key-end (1- (setf ,i (jstring-end ,b ,i)))))
             (declare (type fixnum ,key-start ,key-end) (ignorable ,key-start ,key-end))
             (setf ,i (jws ,b ,i))
             (unless (= (jbyte ,b ,i) 58) (json-error ,b ,i "colon expected"))
             (setf ,i (jws ,b (1+ ,i)))
             (setf ,i (jws ,b (progn ,@body)))
             (case (jbyte ,b ,i)
               (44 (setf ,i (jws ,b (1+ ,i))))
               (125 (return (1+ ,i)))
               (t (json-error ,b ,i "comma or } expected"))))))))

(defmacro jkey-case ((b i key-start key-end) &body clauses)
  "In DO-JOBJECT: the clause (\"name\" form...) whose name is the key (compared by length,
   then byte by byte, unrolled); its forms return the index after the value at I. A key
   with no clause has its value skipped."
  (let ((by-len '()))
    (dolist (c clauses) (push c (getf by-len (length (first c)))))
    `(case (- ,key-end ,key-start)
       ,@(loop for (len cs) on by-len by #'cddr
               collect `(,len (cond ,@(loop for (name . forms) in (reverse cs)
                                            collect `((and ,@(loop for ch across name for k from 0
                                                                   collect `(= (aref ,b (+ ,key-start ,k)) ,(char-code ch))))
                                                      ,@forms))
                                    (t (jskip ,b ,i)))))
       (t (jskip ,b ,i)))))

;;; Header fields in consensus order (the RLP header); from baseFeePerGas on a header
;;; carries a prefix of them, by fork. The quantities are encoded minimally.
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter +header-fields+
    #("parentHash" "sha3Uncles" "miner" "stateRoot" "transactionsRoot" "receiptsRoot" "logsBloom"
      "difficulty" "number" "gasLimit" "gasUsed" "timestamp" "extraData" "mixHash" "nonce"
      "baseFeePerGas" "withdrawalsRoot" "blobGasUsed" "excessBlobGas" "parentBeaconBlockRoot" "requestsHash")))
(defconstant +header-required+ 15)
(defparameter +header-quantities+ '(7 8 9 10 11 15 17 18))

(defmacro defdecoder (name lambda-vars fields &body result)
  "(defun NAME (b i) ...): the JSON object at I of B; per FIELDS entry (\"key\" place reader
   . args) the key's value read by (READER b i . ARGS) into PLACE, a LAMBDA-VARS variable
   (NIL when the key is absent); other keys skipped. (values RESULT index-after); an entry
   (:header HF) reads every header field into the vector HF."
  `(defun ,name (b i)
     (let* ,lambda-vars
       (let ((next (do-jobject (b i ks ke)
                     (jkey-case (b i ks ke)
                       ,@(loop for f in fields
                               append (if (eq (first f) :header)
                                          (loop for name across +header-fields+ for k from 0
                                                collect `(,name (jread (svref ,(second f) ,k) jbytes)))
                                          (destructuring-bind (key place reader &rest args) f
                                            `((,key (jread ,place ,reader ,@args))))))))))
         (values (progn ,@result) next)))))

(defmacro jread (place reader &rest args)
  "PLACE := the value at I of B read by READER; the index after it."
  (let ((v (gensym "V")) (next (gensym "NEXT")))
    `(multiple-value-bind (,v ,next) (,reader b i ,@args) (setf ,place ,v) ,next)))

(defparameter +hex-nibbles+
  (let ((v (make-array 256 :element-type '(signed-byte 8) :initial-element -1)))
    (loop for c across "0123456789abcdef" for k from 0
          do (setf (aref v (char-code c)) k (aref v (char-code (char-upcase c))) k))
    v))

(declaim (inline nibble))
(defun nibble (b j)
  (declare (type octets b) (type fixnum j) (optimize speed (safety 0)))
  (let ((d (aref (the (simple-array (signed-byte 8) (256)) (load-time-value +hex-nibbles+ t)) (aref b j))))
    (when (minusp d) (json-error b j "hex digit expected"))
    d))

(defun jhex-span (b i)
  "I at a string: (values first-digit end next), past an 0x prefix."
  (declare (type octets b) (type fixnum i) (optimize speed (safety 0)))
  (let* ((next (jstring-end b i)) (end (1- next)) (s (1+ i)))
    (declare (type fixnum next end s))
    (when (and (<= (+ s 2) end) (= (aref b s) 48) (= (aref b (1+ s)) 120)) (incf s 2))
    (values s end next)))

(defun jint (b i)
  "The value at I as an integer — a hex quantity string, or a decimal number — or NIL for
   anything else (null; jsown writes a NIL as []); (values n index-after)."
  (declare (type octets b) (type fixnum i) (optimize speed (safety 0)))
  (case (jbyte b i)
    (34 (multiple-value-bind (s end next) (jhex-span b i)
          (declare (type fixnum s end))
          (let ((acc 0))                ; 15 digits per fixnum step, as hex->int
            (declare (type unsigned-byte acc))
            (loop for k of-type fixnum = s then (+ k 15) while (< k end)
                  do (let ((e (min end (+ k 15))) (f 0))
                       (declare (type fixnum e) (type (unsigned-byte 60) f))
                       (loop for j of-type fixnum from k below e do (setf f (logior (ash f 4) (nibble b j))))
                       (setf acc (logior (ash acc (* 4 (- e k))) f))))
            (values acc next))))
    ((48 49 50 51 52 53 54 55 56 57)
     (let ((j (jskip b i))) (values (parse-integer (map 'string #'code-char (subseq b i j))) j)))
    (t (values nil (jskip b i)))))

(defun jbytes (b i)
  "The hex string at I as octets (an odd digit count: a leading zero nibble), NIL for
   anything else (null)."
  (declare (type octets b) (type fixnum i) (optimize speed (safety 0)))
  (case (jbyte b i)
    (34 (multiple-value-bind (s end next) (jhex-span b i)
          (declare (type fixnum s end))
          (let* ((odd (logand (- end s) 1))
                 (out (make-array (ash (+ (- end s) 1) -1) :element-type '(unsigned-byte 8))))
            (declare (type fixnum odd))
            (dotimes (k (length out) (values out next))
              (let ((a (- (+ s (* 2 k)) odd)))
                (declare (type fixnum a))
                (setf (aref out k) (logior (if (< a s) 0 (ash (nibble b a) 4)) (nibble b (1+ a)))))))))
    (t (values nil (jskip b i)))))

(defun jaddr (b i)
  "An address at I: an integer, NIL for null or an empty string (a creation's `to`)."
  (multiple-value-bind (v next) (jbytes b i)
    (values (and v (plusp (length v)) (octets-int v)) next)))

(defun jbool (b i) (values (= (jbyte b i) 116) (jskip b i)))   ; true

(defun jlist (b i fn)
  "The array at I as the list of its elements read by FN ((b i) -> (values v next)); NIL
   for null."
  (declare (type octets b) (type fixnum i))
  (case (jbyte b i)
    (91 (setf i (jws b (1+ i)))
     (if (= (jbyte b i) 93)
         (values nil (1+ i))
         (let ((items '()))
           (loop (multiple-value-bind (v next) (funcall fn b i) (push v items) (setf i (jws b next)))
                 (case (jbyte b i)
                   (44 (setf i (jws b (1+ i))))
                   (93 (return (values (nreverse items) (1+ i))))
                   (t (json-error b i "comma or ] expected")))))))
    (110 (values nil (jskip b i)))
    (t (json-error b i "array expected"))))

(defun octets-int (v)
  "The big-endian integer of the octets V."
  (declare (type octets v))
  (let ((acc 0)) (loop for x across v do (setf acc (logior (ash acc 8) x))) acc))

;;; The decoded objects.
(defstruct (chain-block (:conc-name blk-))
  "A decoded block (or ommer header). Hash-like header fields the replay compares are
   octets; the ones it uses as numbers are integers (NIL where the header lacks them)."
  (number 0) (hash 0) (parent-hash 0) (timestamp 0) (miner 0) (gas-limit 0) (gas-used 0)
  base-fee (mix-hash 0) (difficulty 0) excess-blob-gas blob-gas-used parent-beacon-root
  state-root                            ; text: what anchors.sexp records
  receipts-root transactions-root logs-bloom sha3-uncles extra-data nonce requests-hash withdrawals-root
  header-rlp (header-hash 0)            ; rlp(header) and its keccak, from the fields as given
  txs withdrawals (uncle-count 0)       ; withdrawals: (index validator-index address amount)
  receipts                              ; the receipts file's (parse plists), or NIL: none at hand
  uncles)                               ; the uncles file's headers (CHAIN-BLOCKs), or NIL

(defdecoder decode-access-entry (addr keys)
    (("address" addr jint) ("storageKeys" keys jlist #'jint))
  (cons addr keys))

;; An EIP-7702 authorization tuple, as spec-tx-effect reads it (Evm.CL.EffectTx:
;; Evm.Frontier.Vm.Tx.authorize).
(defdecoder decode-authorization (chain-id addr nonce y-parity v r s)
    (("chainId" chain-id jint) ("address" addr jint) ("nonce" nonce jint) ("yParity" y-parity jint)
     ("v" v jint) ("r" r jint) ("s" s jint))
  ;; the authority's ecrecover here, on the decoder thread (recover-authority takes it)
  (recover-authority-ahead! chain-id addr nonce (or y-parity v) r s)
  (list :chain-id chain-id :address addr :nonce nonce :y-parity (or y-parity v) :r r :s s))

;; The tx object at I as a TX — an RPC tx, or a fixture's (gasLimit, data, sender, a typed
;; tx's v as its parity). EIP-4844: the versioned hashes are BLOBHASH's table for the tx
;; (install-blob-env!), their count prices the blob fee; EIP-7702: the authorizations are
;; processed by spec-tx-effect.
(defdecoder decode-tx-object (type from to nonce gas gas-price max-fee max-priority value data access-list
                              blob-hashes max-blob-fee mint auths hash chain-id v y-parity r s source-hash system-p)
    (("type" type jint) ("from" from jint) ("sender" from jint) ("to" to jaddr) ("nonce" nonce jint)
     ("gas" gas jint) ("gasLimit" gas jint) ("gasPrice" gas-price jint) ("maxFeePerGas" max-fee jint)
     ("maxPriorityFeePerGas" max-priority jint) ("value" value jint) ("input" data jbytes) ("data" data jbytes)
     ("accessList" access-list jlist #'decode-access-entry) ("blobVersionedHashes" blob-hashes jlist #'jint)
     ("maxFeePerBlobGas" max-blob-fee jint) ("mint" mint jint) ("authorizationList" auths jlist #'decode-authorization)
     ("hash" hash jint) ("chainId" chain-id jint) ("v" v jint) ("yParity" y-parity jint) ("r" r jint) ("s" s jint)
     ("sourceHash" source-hash jint) ("isSystemTx" system-p jbool))
  (let ((type (or type 0)))
    ;; the data's zero / nonzero byte counts here, on the decoder thread, not on the replay's
    (let ((tx (make-tx :type type :sender from :to to :nonce (or nonce 0) :gas-limit (or gas 0) :gas-price (or gas-price 0)
             :max-fee max-fee :max-priority max-priority :value (or value 0)
             :data (or data (make-array 0 :element-type '(unsigned-byte 8))) :access-list access-list
             :blob-hashes blob-hashes :max-blob-fee max-blob-fee :mint (or mint 0) :auth-count (length auths)
             :auth-list auths :hash (or hash 0) :chain-id chain-id :v (if (plusp type) (or y-parity v) v) :r r :s s
             :source-hash source-hash :system-p system-p)))
      (calldata-byte-counts tx)
      tx)))

(defun decode-tx (b i)
  "A block's tx at I: its object as a TX, a bare hash (a block fetched without txs) as NIL."
  (if (= (jbyte b i) 34) (values nil (jskip b i)) (decode-tx-object b i)))

;; The receipt object at I as the plist the gates read; its logs are skipped. NIL where
;; absent: no status before Byzantium, an exported source may carry no effectiveGasPrice;
;; the OP fields (the Isthmus operator fee: scalar per gas /1e6, a flat constant) 0.
(defdecoder decode-receipt (gas-used status egp l1-fee scalar constant deposit-nonce)
    (("gasUsed" gas-used jint) ("status" status jint) ("effectiveGasPrice" egp jint) ("l1Fee" l1-fee jint)
     ("operatorFeeScalar" scalar jint) ("operatorFeeConstant" constant jint) ("depositNonce" deposit-nonce jint))
  (list :gas-used gas-used :status status :effective-gas-price egp :l1-fee (or l1-fee 0)
        :operator-fee-scalar (or scalar 0) :operator-fee-constant (or constant 0) :deposit-nonce deposit-nonce))

(defdecoder decode-withdrawal (index validator addr amount)
    (("index" index jint) ("validatorIndex" validator jint) ("address" addr jint) ("amount" amount jint))
  (list index validator addr amount))

(defun header-rlp (hf)
  "rlp(header) of the header field bytes HF (+header-fields+ order), as octets."
  (let ((items (loop for k below (length hf)
                     for v = (svref hf k)
                     while (or v (< k +header-required+))
                     collect (progn
                               (unless v (error "block header lacks ~A" (svref +header-fields+ k)))
                               (rlp-encode-bytes (if (member k +header-quantities+)
                                                     (subseq v (or (position 0 v :test-not #'eql) (length v)))
                                                     v))))))
    (coerce (rlp-encode-list items) 'octets)))

(defun jskip-value (b i) (values nil (jskip b i)))

;; The block (or ommer header) object at I as a CHAIN-BLOCK.
(defdecoder decode-block ((hf (make-array (length +header-fields+) :initial-element nil)) hash txs withdrawals uncles)
    ((:header hf) ("hash" hash jint) ("transactions" txs jlist #'decode-tx)
     ("withdrawals" withdrawals jlist #'decode-withdrawal) ("uncles" uncles jlist #'jskip-value))
  (flet ((int (k) (let ((v (svref hf k))) (and v (octets-int v)))))
    (let ((rlp (header-rlp hf)))
      (make-chain-block
       :number (int 8) :hash (or hash 0) :parent-hash (int 0) :timestamp (int 11) :miner (int 2)
       :gas-limit (int 9) :gas-used (int 10) :base-fee (int 15) :mix-hash (or (int 13) 0)
       :difficulty (or (int 7) 0) :excess-blob-gas (int 18) :blob-gas-used (int 17) :parent-beacon-root (int 19)
       :state-root (and (svref hf 3) (bytes->hex-string (svref hf 3) "0x"))
       :receipts-root (svref hf 5) :transactions-root (svref hf 4) :logs-bloom (svref hf 6)
       :sha3-uncles (svref hf 1) :extra-data (svref hf 12) :nonce (svref hf 14) :requests-hash (svref hf 20) :withdrawals-root (svref hf 16)
       :header-rlp rlp :header-hash (octets-int (keccak256-bytes rlp))
       :txs (delete nil txs) :withdrawals withdrawals :uncle-count (length uncles)))))


(defun json-octets (text)
  "TEXT (a JSON-RPC reply, a cached file's contents) as the octets the decoder reads."
  (sb-ext:string-to-octets text :external-format :utf-8))

(defun decode-json-text (text fn)
  "The JSON value TEXT read by FN."
  (let ((b (json-octets text))) (values (funcall fn b (jws b 0)))))

(defun decode-block-json (obj)
  "The jsown block object OBJ decoded (a fixture's block, a test's mutated one)."
  (decode-json-text (jsown:to-json obj) #'decode-block))

(defun decode-rpc-reply (b i fn)
  "The JSON-RPC reply object at I: (values result-read-by-FN next result-start result-end),
   the result NIL when null or absent (an error reply)."
  (let (res (rs 0) (re 0))
    (let ((next (do-jobject (b i ks ke)
                  (jkey-case (b i ks ke)
                    ("result" (setf rs i) (setf re (jread res (lambda (b i) (if (= (jbyte b i) 110) (values nil (jskip b i)) (funcall fn b i))))))))))
      (values res next rs re))))
