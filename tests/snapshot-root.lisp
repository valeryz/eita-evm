;;;; test-snapshot-root.lisp — proof-by-oracle for the streaming state root
;;;; (src/state/root.lisp) against the from-scratch trie (src/state/mpt.lisp).
;;;;
;;;;   1. stack trie == trie-root: random key sets (random 32-byte keys, and keys sharing
;;;;      long prefixes so extensions appear at every depth), every size 0..64 and some
;;;;      large ones, pushed in sorted order, with a base depth of 0 and 1.
;;;;   2. snapshot == account-state-root: random accounts (storage, code, empty ones)
;;;;      written as a binary snapshot and checked with 1 and 4 threads — the parallel
;;;;      top-nibble path —, with 2048 buckets (the large-state layout), and a set whose
;;;;      hashed keys share the top nibble (the single-trie path).
;;;;      The same sets as version 2 bases (hashed key order, `make-writer`, the address
;;;;      field zero as an import writes it): the streaming hashed-order root.
;;;;      And `import-reth` over such a set streamed as rust/reth-export streams it: published
;;;;      with :root-checked under the right header root, quarantined under a wrong one.
;;;;   3. giant-root == storage-root: random storages (0..70,000 slots, so both the 256-way
;;;;      split and the degenerate single-trie path) read in place at an offset, alone
;;;;      and with a random layer composition laid over them (rewrites, tombstones, new
;;;;      slots), with 256 and 2048 bucket files (none left behind); then the snapshot oracles again with every storage built by giant-root.
;;;;
;;;; Run: (eita.test:run-all :only '("snapshot-root")), or (asdf:test-system "eita") for all suites.

(defpackage :eita.test.snapshot-root (:use :cl :eita.state.root))
(in-package :eita.test.snapshot-root)

(defvar *failures* 0)
(defvar *rng* (sb-ext:seed-random-state 20261025))

(defun check (ok what &rest args)
  (unless ok
    (incf *failures*)
    (format t "FAIL: ~?~%" what args)))

(defun random-key (prefix-of plen)
  "A random 32-byte key; with PREFIX-OF, its first PLEN nibbles are PREFIX-OF's."
  (let ((k (make-array 32 :element-type '(unsigned-byte 8))))
    (dotimes (i 32) (setf (aref k i) (random 256 *rng*)))
    (when prefix-of
      (dotimes (d plen)
        (let ((b (floor d 2)) (src (aref prefix-of (floor d 2))))
          (setf (aref k b) (if (evenp d)
                               (logior (logand (aref k b) #x0f) (logand src #xf0))
                               (logior (logand (aref k b) #xf0) (logand src #x0f)))))))
    k))

(defun random-keys (n)
  "N distinct keys; about half share a random-length prefix with an earlier one."
  (let ((keys '()) (seen (make-hash-table :test #'equalp)))
    (loop while (< (hash-table-count seen) n)
          do (let ((k (if (and keys (zerop (random 2 *rng*)))
                          (random-key (nth (random (length keys) *rng*) keys) (random 64 *rng*))
                          (random-key nil 0))))
               (unless (gethash k seen)
                 (setf (gethash k seen) t)
                 (push k keys))))
    keys))

(defun random-value ()
  (let ((v (make-array (1+ (random 40 *rng*)) :element-type '(unsigned-byte 8))))
    (dotimes (i (length v) v) (setf (aref v i) (random 256 *rng*)))))

(defun key< (a b) (loop for x across a for y across b do (cond ((< x y) (return t)) ((> x y) (return nil)))))

(defun stack-root (items base)
  "The streaming root over ITEMS ((key . value) ...), sorted here, pushed in order."
  (let ((st (make-stack-trie base)))
    (dolist (kv (sort (copy-list items) #'key< :key #'car))
      (st-push st (car kv) 0 (cdr kv)))
    (st-finish st)))

(defun oracle-stack-trie ()
  (format t "~&--- stack trie vs trie-root~%")
  (let ((cases 0))
    (dolist (n (append (loop for i from 0 to 64 collect i) '(100 500 2000 20000)))
      (dotimes (rep (if (< n 65) 20 2))
        (let* ((items (mapcar (lambda (k) (cons k (random-value))) (random-keys n)))
               (want (eita.mpt:trie-root items))
               (got (st-root-bytes (stack-root items 0))))
          (incf cases)
          (check (equalp want got) "n=~D rep=~D base 0: ~A vs ~A" n rep
                 (eita.mpt:bytes->hex want) (eita.mpt:bytes->hex got))
          ;; base 1: the subtrie of keys sharing a top nibble equals patricialise at depth
          ;; 1 — checked through the whole trie: keys with top nibble 0 (forced) plus one
          ;; with top nibble 1, root = branch[ref(sub0), ref(leaf1)]
          (when (plusp n)
            (let* ((sub (remove-duplicates
                         (mapcar (lambda (kv) (let ((k (copy-seq (car kv)))) (setf (aref k 0) (logand (aref k 0) #x0f)) (cons k (cdr kv))))
                                 items)
                         :key #'car :test #'equalp))
                   (other (cons (let ((k (random-key nil 0))) (setf (aref k 0) (logior #x10 (logand (aref k 0) #x0f))) k)
                                (random-value)))
                   (want (eita.mpt:trie-root (cons other sub)))
                   (sub-item (stack-root sub 1))
                   (leaf1 (stack-root (list other) 1))
                   (got (st-root-bytes
                         (eita.mpt::rlp-list* (append (list (eita.mpt::node-ref sub-item) (eita.mpt::node-ref leaf1))
                                                      (make-list 15 :initial-element eita.state.root::*empty-item*))))))
              (incf cases)
              (check (equalp want got) "n=~D rep=~D base 1: ~A vs ~A" (length sub) rep
                     (eita.mpt:bytes->hex want) (eita.mpt:bytes->hex got)))))))
    (format t "~D cases~%" cases)))

;;; ---------------------------------------------------------------- snapshots

(defun random-account (&key top-nibble)
  "An (addr nonce balance storage-alist code-bytes . exists-empty) account; with
   TOP-NIBBLE, keccak(addr) starts with that nibble."
  (let ((addr (loop for a = (random (expt 2 160) *rng*)
                    when (or (null top-nibble)
                             (= top-nibble (ash (aref (eita.mpt::%keccak (eita.mpt::int->be-bytes-fixed a 20)) 0) -4)))
                      return a))
        (kind (random 10 *rng*)))
    (case kind
      (0 (list addr 0 0 '() nil t))                                      ; empty, in the trie
      ((1 2 3) (list addr (random 1000 *rng*) (random (expt 2 100) *rng*) '() nil nil))
      (t (let* ((nslots (1+ (random (if (= kind 9) 3000 20) *rng*)))
                (slots (sort (remove-duplicates
                              (loop repeat nslots collect (if (zerop (random 2 *rng*)) (random 64 *rng*) (random (expt 2 256) *rng*)))
                              :test #'=)
                             #'<))
                (code (random-value)))
           (list addr (1+ (random 5 *rng*)) (random (expt 2 64) *rng*)
                 (mapcar (lambda (s) (cons s (if (zerop (random 2 *rng*)) (1+ (random 255 *rng*)) (1+ (random (expt 2 256) *rng*))))) slots)
                 code nil))))))

(defun write-snapshot (dir accounts)
  (let ((m (eita.state.snapshot:make-merge dir 1 7 nil nil)) (codes '()))
    (dolist (a (sort (copy-list accounts) #'< :key #'first))
      (destructuring-bind (addr nonce balance storage code empty) a
        (let ((ch (if code (eita.state.snapshot:octets->int (eita.mpt::%keccak code)) eita.state.snapshot:+empty-code-hash+)))
          (when code (push (cons ch code) codes))
          (eita.state.snapshot:merge-account m addr :fields (list nonce balance ch empty) :slots storage))))
    (eita.state.snapshot:merge-finish m codes)))

(defun write-snapshot-2 (dir accounts)
  "ACCOUNTS as a version 2 base (`make-writer`), by hashed key, with the address field zero
   as an import from reth's hashed tables writes it."
  (let ((w (eita.state.snapshot:make-writer dir 1 7 "0x00")) (codes '()))
    (flet ((h (n width) (eita.mpt::%keccak (eita.mpt::int->be-bytes-fixed n width))))
      (dolist (a (sort (mapcar (lambda (a) (cons (h (first a) 20) a)) accounts) #'key< :key #'car))
        (destructuring-bind (hkey addr nonce balance storage code empty) a
          (declare (ignore addr))
          (dolist (kv (sort (mapcar (lambda (kv) (cons (h (car kv) 32) (cdr kv))) storage) #'key< :key #'car))
            (eita.state.snapshot:writer-slot w hkey (car kv) (cdr kv)))
          (let ((ch (if code (eita.state.snapshot:octets->int (eita.mpt::%keccak code)) eita.state.snapshot:+empty-code-hash+)))
            (when code (push (cons ch code) codes))
            (eita.state.snapshot:writer-account w hkey 0 (if empty 1 0) nonce balance ch)))))
    (eita.state.snapshot:writer-finish w codes)))

(defvar *v2* nil "Write the snapshots in format version 2 (hashed key order).")

(defun oracle-snapshot (name accounts threads &key buckets)
  (let* ((parent (format nil "/tmp/eita-test-snapshot-root-~D/" (sb-posix:getpid)))
         (dir (concatenate 'string parent "snap-7/"))
         (want (eita.mpt:bytes->hex
                (eita.mpt:account-state-root
                 (mapcar (lambda (a) (list (first a) (second a) (third a) (fourth a) (fifth a))) accounts)))))
    (funcall (if *v2* #'write-snapshot-2 #'write-snapshot) dir accounts)
    (dolist (th threads)
      (multiple-value-bind (got expected na ns) (snapshot-root dir :threads th :buckets buckets)
        (declare (ignore expected))
        (check (string= got want) "~A, ~D threads: ~A vs ~A" name th got want)
        (check (= na (length accounts)) "~A: ~D accounts in the snapshot, ~D given" name na (length accounts))
        (check (= ns (reduce #'+ accounts :key (lambda (a) (length (fourth a))))) "~A: ~D slots in the snapshot" name ns)
        (format t "~A: ~D accounts, ~D slots, ~D threads: ~A~%" name na ns th (if (string= got want) "ok" "MISMATCH"))))
    (sb-ext:run-program "rm" (list "-rf" parent) :search t)))

(defun oracle-snapshots ()
  (format t "~&--- snapshots vs account-state-root~%")
  (oracle-snapshot "empty" '() '(1))
  (oracle-snapshot "one" (list (random-account)) '(1 4))
  (oracle-snapshot "random" (loop repeat 500 collect (random-account)) '(1 4))
  (oracle-snapshot "wide" (loop repeat 9000 collect (random-account)) '(4))
  (oracle-snapshot "2048 buckets" (loop repeat 3000 collect (random-account)) '(1 4) :buckets 2048)
  (oracle-snapshot "one top nibble" (loop repeat 40 collect (random-account :top-nibble 3)) '(1 4)))

;;; ---------------------------------------------------------------- giant storages

(defun slot-records (alist pad)
  "ALIST ((slot . value) ...), ascending by slot, as 88-byte storage records after a
   header and PAD unrelated records, in a malloc'd buffer (as a mapping or a composition
   buffer holds them)."
  (let* ((n (+ pad (length alist)))
         (sap (cffi:foreign-alloc :uint8 :count (+ 4096 (* 88 (max 1 n))))))
    (loop for (slot . value) in (append (loop for i below pad collect (cons i (1+ i))) alist)
          for i from 0
          do (let ((o (+ 4096 (* 88 i))))
               (dotimes (j 20) (setf (sb-sys:sap-ref-8 sap (+ o j)) 7))
               (dotimes (j 32)
                 (setf (sb-sys:sap-ref-8 sap (+ o 20 j)) (ldb (byte 8 (* 8 (- 31 j))) slot)
                       (sb-sys:sap-ref-8 sap (+ o 52 j)) (ldb (byte 8 (* 8 (- 31 j))) value)))
               (dotimes (j 4) (setf (sb-sys:sap-ref-8 sap (+ o 84 j)) 0))))
    sap))

(defun random-slot () (if (zerop (random 2 *rng*)) (random 100000 *rng*) (random (expt 2 256) *rng*)))
(defun random-word () (if (zerop (random 2 *rng*)) (1+ (random 255 *rng*)) (1+ (random (1- (expt 2 256)) *rng*))))

(defun random-overlay (base n-new)
  "A layer composition over BASE: a quarter of its slots rewritten (half of those to zero:
   tombstones) and N-NEW other slots (a quarter zero), ascending."
  (let ((seen (make-hash-table)) (out '()))
    (dolist (kv base) (setf (gethash (car kv) seen) t)
      (when (zerop (random 4 *rng*))
        (push (cons (car kv) (if (zerop (random 2 *rng*)) 0 (random-word))) out)))
    (loop repeat n-new
          do (let ((s (random-slot)))
               (unless (gethash s seen)
                 (setf (gethash s seen) t)
                 (push (cons s (if (zerop (random 4 *rng*)) 0 (random-word))) out))))
    (sort out #'< :key #'car)))

(defun oracle-giant ()
  "giant-root over base records (and a layer composition laid over them) against the
   from-scratch storage root of the model."
  (format t "~&--- giant-root vs storage-root~%")
  (let ((cases 0) (scratch (format nil "/tmp/eita-test-giant-root-~D/" (sb-posix:getpid))))
    (ensure-directories-exist scratch)
    (dolist (n '(0 1 2 3 5 17 40 300 5000 70000))
      (dotimes (rep (if (> n 5000) 1 3))
        (let* ((base (let ((h (make-hash-table)))
                       (loop while (< (hash-table-count h) n) do (setf (gethash (random-slot) h) (random-word)))
                       (sort (loop for k being the hash-keys of h using (hash-value v) collect (cons k v)) #'< :key #'car)))
               (delta (random-overlay base (1+ (floor n 8))))
               (model (let ((h (make-hash-table)))
                        (dolist (kv base) (setf (gethash (car kv) h) (cdr kv)))
                        (dolist (kv delta) (if (zerop (cdr kv)) (remhash (car kv) h) (setf (gethash (car kv) h) (cdr kv))))
                        (loop for k being the hash-keys of h using (hash-value v) collect (cons k v))))
               (pad (random 3 *rng*))
               (bsap (slot-records base pad)) (dsap (slot-records delta 0)))
          (unwind-protect
               (loop for (what want-alist d nd) in (list (list "base" base nil 0)
                                                          (list "base+layers" model dsap (length delta)))
                     do (loop for (th nb) in '((1 nil) (4 nil) (4 2048))
                              do (multiple-value-bind (root count)
                                     (eita.state.root::giant-root th scratch bsap pad (length base)
                                                                  :dsap d :nd nd :buckets nb)
                                   (let ((want (eita.mpt:storage-root want-alist)))
                                     (incf cases)
                                     (check (equalp root want) "giant n=~D rep=~D ~A, ~D threads, ~A buckets: ~A vs ~A"
                                            n rep what th nb (eita.mpt:bytes->hex root) (eita.mpt:bytes->hex want))
                                     (check (= count (length want-alist)) "giant n=~D rep=~D ~A: ~D slots, want ~D"
                                            n rep what count (length want-alist))
                                     (check (null (directory (concatenate 'string scratch "*.*")))
                                            "giant n=~D: bucket files left behind" n)))))
            (cffi:foreign-free bsap) (cffi:foreign-free dsap)))))
    (sb-posix:rmdir (string-right-trim "/" scratch))
    (format t "~D cases~%" cases)))

(defun oracle-snapshots-giant ()
  "The snapshot oracles with every non-empty storage built by giant-root."
  (format t "~&--- snapshots, every storage by giant-root~%")
  (let ((big eita.state.root::*big*))
    (setf eita.state.root::*big* 0)      ; global: the pool threads read it
    (unwind-protect (oracle-snapshots) (setf eita.state.root::*big* big))))

(defun oracle-snapshots-2 ()
  "The snapshot oracles over version 2 bases: the hashed-order root (`snapshot-root-2`)."
  (format t "~&--- version 2 snapshots~%")
  (let ((*v2* t)) (oracle-snapshots)))

(defun write-export-stream (path accounts root)
  "ACCOUNTS as rust/reth-export would stream them, header stateRoot ROOT (hex)."
  (with-open-file (o path :direction :output :element-type '(unsigned-byte 8) :if-exists :supersede)
    (flet ((int (n w) (write-sequence (eita.mpt::int->be-bytes-fixed n w) o))
           (tag (c) (write-byte (char-code c) o))
           (h (n w) (eita.mpt::%keccak (eita.mpt::int->be-bytes-fixed n w))))
      (write-sequence (map 'vector #'char-code "EITARETH") o)
      (int 1 4) (int 1 8) (int 7 8) (int 0 32) (int (parse-integer root :radix 16) 32)
      (int (length accounts) 8) (int 0 8) (int 4 2) (write-sequence (map 'vector #'char-code "test") o)
      (let ((codes '()) (ns 0))
        (dolist (a (sort (mapcar (lambda (a) (cons (h (first a) 20) a)) accounts) #'key< :key #'car))
          (destructuring-bind (hkey addr nonce balance storage code empty) a
            (declare (ignore addr))
            (dolist (kv (sort (mapcar (lambda (kv) (cons (h (car kv) 32) (cdr kv))) storage) #'key< :key #'car))
              (tag #\S) (write-sequence hkey o) (write-sequence (car kv) o) (int (cdr kv) 32) (incf ns))
            (let ((ch (if code (eita.mpt::%keccak code) (eita.mpt::int->be-bytes-fixed eita.state.snapshot:+empty-code-hash+ 32))))
              (when code (pushnew (cons ch code) codes :key #'car :test #'equalp))
              (tag #\A) (write-sequence hkey o) (int 0 20) (int (if empty 1 0) 4) (int nonce 8) (int balance 32)
              (write-sequence ch o))))
        (dolist (c (setf codes (sort codes #'key< :key #'car)))
          (tag #\C) (write-sequence (car c) o) (int (length (cdr c)) 4) (write-sequence (cdr c) o))
        (tag #\E) (int (length accounts) 8) (int ns 8) (int (length codes) 8)))))

(defun oracle-import ()
  "`import-reth` over a stream of random accounts: published and root-checked when the header
   root is the state's, quarantined in .tmp-snap-7/ when it is not."
  (format t "~&--- import-reth~%")
  (let* ((parent (format nil "/tmp/eita-test-import-~D/" (sb-posix:getpid)))
         (stream (concatenate 'string parent "s.stream"))
         (accounts (loop repeat 700 collect (random-account)))
         (want (eita.mpt:bytes->hex (eita.mpt:account-state-root
                                     (mapcar (lambda (a) (list (first a) (second a) (third a) (fourth a) (fifth a))) accounts)))))
    (ensure-directories-exist parent)
    (unwind-protect
         (progn
           (write-export-stream stream accounts want)
           (let ((dir (with-open-file (in stream :element-type '(unsigned-byte 8)) (import-reth parent in :threads 4))))
             (check dir "import: a matching root was not published")
             (check (and dir (getf (eita.state.snapshot:read-manifest dir) :root-checked)) "import: no :root-checked")
             (check (and dir (= (length (remove-duplicates (remove nil (mapcar #'fifth accounts)) :test #'equalp))
                                (getf (getf (eita.state.snapshot:read-manifest dir) :counts) :codes)))
                    "import: code count"))
           (sb-ext:run-program "rm" (list "-rf" (concatenate 'string parent "snap-7")) :search t)
           (write-export-stream stream accounts (concatenate 'string (if (char= (char want 0) #\0) "1" "0") (subseq want 1)))
           (check (null (with-open-file (in stream :element-type '(unsigned-byte 8)) (import-reth parent in :threads 4)))
                  "import: a wrong root was published")
           (check (and (probe-file (concatenate 'string parent ".tmp-snap-7/"))
                       (not (probe-file (concatenate 'string parent "snap-7/"))))
                  "import: a mismatch is not quarantined"))
      (sb-ext:run-program "rm" (list "-rf" parent) :search t))))

(defun main ()
  (oracle-stack-trie)
  (oracle-snapshots)
  (oracle-snapshots-2)
  (oracle-import)
  (oracle-giant)
  (oracle-snapshots-giant)
  (format t "~%==============================~%")
  (if (zerop *failures*)
      (format t "ALL ORACLES PASS~%")
      (progn (format t "~D FAILURE(S)~%" *failures*)
             (eita.test:finish :code 1))))

(main)
