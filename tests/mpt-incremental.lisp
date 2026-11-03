;;;; test-mpt-incremental.lisp — proof-by-oracle for the INCREMENTAL
;;;; mutable account trie in src/state/mpt.lisp (#20).
;;;;
;;;; Oracles:
;;;;   1. Genesis match: insert all genesis accounts one-by-one into an
;;;;      empty mtrie; root must equal the canonical genesis stateRoot.
;;;;   2. Incremental == full-rebuild: hundreds of randomized insert/delete
;;;;      sequences; mtrie-root must equal the from-scratch trie-root of the
;;;;      resulting key->value set after each op.
;;;;   3. Delete inverts insert: insert+delete an extra key returns the root.
;;;;
;;;; Run: (eita.test:run-all :only '("mpt-incremental")), or (asdf:test-system "eita") for all suites.

(in-package #:eita.mpt)

(load (merge-pathnames "genesis-alloc.lisp" *load-truename*))

(defparameter *genesis-target*
  "d7f8974fb5ac78d9ac099b9ad5018bedc2ce0a72dad1827a1709da30580f0544")


(defun strip-hex (s)
  (if (and (>= (length s) 2) (string= "0x" (subseq s 0 2))) (subseq s 2) s))

(defun hex->bytes (s)
  (let* ((s (strip-hex s))
         (s (if (oddp (length s)) (concatenate 'string "0" s) s))
         (n (floor (length s) 2))
         (bs (make-array n :element-type '(unsigned-byte 8))))
    (loop for i from 0 below n do
      (setf (aref bs i)
            (parse-integer s :radix 16 :start (* 2 i) :end (* 2 (+ i 1)))))
    bs))

;;; --------------------------------------------------------------------
;;; Test harness state + helpers
;;; --------------------------------------------------------------------

(defvar *failures* 0)

(defun check (cond fmt &rest args)
  (unless cond
    (incf *failures*)
    (format t "  FAIL: ~A~%" (apply #'format nil fmt args))))

;; Reproducible RNG (fixed seed).
(defparameter *rng* (sb-ext:seed-random-state 20260619))

(defun rand-int (n) (random n *rng*))

(defun rand-bytes (len)
  (let ((v (make-array len :element-type '(unsigned-byte 8))))
    (dotimes (i len) (setf (aref v i) (rand-int 256)))
    v))

(defun bytes-key= (a b)
  (and (= (length a) (length b)) (every #'= a b)))

;; A reference model: alist of (key-bytes . value-bytes), used to build the
;; from-scratch trie-root for comparison.
(defun model-set (model key value)
  "Insert/overwrite KEY->VALUE in MODEL (an alist), returning new alist."
  (cons (cons key value)
        (remove-if (lambda (kv) (bytes-key= (car kv) key)) model)))

(defun model-del (model key)
  (remove-if (lambda (kv) (bytes-key= (car kv) key)) model))

(defun model-root (model)
  "From-scratch trie-root of the current model key set."
  (trie-root model))

;;; --------------------------------------------------------------------
;;; Oracle 1: genesis one-by-one insert
;;; --------------------------------------------------------------------

(defun oracle-genesis ()
  (format t "~&== Oracle 1: genesis one-by-one insert ==~%")
  (let ((trie (make-mtrie))
        (count 0))
    (progn
      (loop for acct in (genesis-alloc)
            do (let* ((addr (getf acct :addr))
                      (balance (getf acct :balance))
                      (nonce (getf acct :nonce))
                      (code-str (getf acct :code))
                      (code (when (and code-str (plusp (length code-str)))
                              (hex->bytes code-str)))
                      (chash (if code (%keccak code) (empty-code-hash)))
                      (key (%keccak (int->be-bytes-fixed addr 20)))
                      (val (account-leaf-value nonce balance
                                               (empty-root-bytes) chash)))
                 (mtrie-insert trie key val)
                 (incf count))))
    (let* ((got (bytes->hex (mtrie-root trie)))
           (pass (string-equal got *genesis-target*)))
      (format t "  accounts inserted : ~D~%" count)
      (format t "  computed root     : ~A~%" got)
      (format t "  canonical root    : ~A~%" *genesis-target*)
      (check pass "genesis root mismatch")
      (format t "  ~A~%" (if pass "PASS" "FAIL")))))

;;; --------------------------------------------------------------------
;;; Oracle 2: incremental == full-rebuild, randomized
;;; --------------------------------------------------------------------

(defun random-key (keylen prefix-pool)
  "Either a fresh random key or one built from a shared long prefix to
   force ext/branch splits."
  (if (and prefix-pool (< (rand-int 100) 55))
      (let* ((base (nth (rand-int (length prefix-pool)) prefix-pool))
             (share (rand-int (1+ (length base))))
             (v (copy-seq base)))
        ;; keep SHARE bytes of BASE, randomize the rest
        (loop for i from share below keylen do (setf (aref v i) (rand-int 256)))
        v)
    (rand-bytes keylen)))

(defun run-random-round (round keylen nops vallen)
  "One randomized sequence. Keep an mtrie and a model alist in lockstep;
   after every op compare mtrie-root to the from-scratch model-root."
  (let ((trie (make-mtrie))
        (model '())
        (prefix-pool '())
        (live-keys '()))
    (dotimes (op nops)
      (let ((action (rand-int 100)))
        (cond
          ;; ~55%: insert (fresh or overwrite, with prefix-sharing)
          ((< action 55)
           (let ((key (random-key keylen prefix-pool))
                 (val (rand-bytes (max 1 (rand-int vallen)))))
             (mtrie-insert trie key val)
             (setf model (model-set model key val))
             (pushnew key prefix-pool :test #'bytes-key=)
             (when (> (length prefix-pool) 8)
               (setf prefix-pool (subseq prefix-pool 0 8)))
             (pushnew key live-keys :test #'bytes-key=)))
          ;; ~20%: delete a present key (forces collapse)
          ((and (< action 75) live-keys)
           (let ((key (nth (rand-int (length live-keys)) live-keys)))
             (mtrie-delete trie key)
             (setf model (model-del model key))
             (setf live-keys (remove key live-keys :test #'bytes-key=))))
          ;; ~15%: delete an absent (random) key — must be a no-op
          ((< action 90)
           (let ((key (rand-bytes keylen)))
             (mtrie-delete trie key)
             (setf model (model-del model key))))
          ;; ~10%: overwrite a present key
          (live-keys
           (let ((key (nth (rand-int (length live-keys)) live-keys))
                 (val (rand-bytes (max 1 (rand-int vallen)))))
             (mtrie-insert trie key val)
             (setf model (model-set model key val))))))
      ;; Compare after every op.
      (let ((inc (bytes->hex (mtrie-root trie)))
            (full (bytes->hex (model-root model))))
        (unless (string= inc full)
          (check nil "round ~D op ~D: inc ~A /= full ~A (model size ~D)"
                 round op inc full (length model))
          (return-from run-random-round nil))))
    t))

(defun oracle-property ()
  (format t "~&== Oracle 2: incremental == full-rebuild (randomized) ==~%")
  (let ((before *failures*)
        (rounds 0))
    ;; A spread of configurations: short keys (more collisions/collapses),
    ;; account-sized 32-byte keys, varied op counts and value sizes.
    ;; Short keys + heavy prefix sharing maximize ext-splits, branch
    ;; collapses, and ext/leaf merges — the fiddly delete paths.
    (dolist (cfg '((2 . 40) (3 . 60) (4 . 80) (32 . 60) (32 . 120)
                   (1 . 30) (2 . 120) (3 . 150)))
      (let ((keylen (car cfg)) (nops (cdr cfg)))
        (dotimes (r 60)
          (incf rounds)
          (run-random-round rounds keylen nops 40))))
    (format t "  rounds run        : ~D~%" rounds)
    (let ((pass (= before *failures*)))
      (format t "  ~A~%" (if pass "PASS" "FAIL")))))

;;; --------------------------------------------------------------------
;;; Oracle 2b: delete down to empty -> empty-trie root
;;; --------------------------------------------------------------------

(defun oracle-empty ()
  (format t "~&== Oracle 2b: delete down to empty ==~%")
  (let ((before *failures*))
    (dotimes (r 50)
      (let ((trie (make-mtrie))
            (keys '())
            (keylen (+ 1 (rand-int 6))))
        ;; insert a handful of keys (some sharing prefixes)
        (let ((pool '()))
          (dotimes (i (+ 2 (rand-int 12)))
            (let ((k (random-key keylen pool)))
              (mtrie-insert trie k (rand-bytes (+ 1 (rand-int 30))))
              (pushnew k keys :test #'bytes-key=)
              (pushnew k pool :test #'bytes-key=))))
        ;; delete all in random order
        (let ((order (sort (copy-seq keys) (lambda (a b) (declare (ignore a b))
                                             (zerop (rand-int 2))))))
          (dolist (k order) (mtrie-delete trie k)))
        (let ((got (bytes->hex (mtrie-root trie)))
              (want (bytes->hex (empty-root-bytes))))
          (check (string= got want)
                 "round ~D: empty root ~A /= ~A" r got want))))
    (format t "  ~A~%" (if (= before *failures*) "PASS" "FAIL"))))

;;; --------------------------------------------------------------------
;;; Oracle 3: delete inverts insert
;;; --------------------------------------------------------------------

(defun oracle-invert ()
  (format t "~&== Oracle 3: delete inverts insert ==~%")
  (let ((before *failures*))
    (dotimes (r 100)
      (let ((trie (make-mtrie))
            (keylen (+ 1 (rand-int 6)))
            (pool '()))
        ;; insert a base set
        (dotimes (i (+ 1 (rand-int 15)))
          (let ((k (random-key keylen pool)))
            (mtrie-insert trie k (rand-bytes (+ 1 (rand-int 30))))
            (pushnew k pool :test #'bytes-key=)))
        (let ((snapshot (bytes->hex (mtrie-root trie)))
              ;; an EXTRA key not already present
              (extra (loop for k = (random-key keylen pool)
                           unless (member k pool :test #'bytes-key=)
                             return k)))
          (mtrie-insert trie extra (rand-bytes (+ 1 (rand-int 30))))
          (mtrie-delete trie extra)
          (let ((after (bytes->hex (mtrie-root trie))))
            (check (string= snapshot after)
                   "round ~D: root ~A /= snapshot ~A" r after snapshot)))))
    (format t "  ~A~%" (if (= before *failures*) "PASS" "FAIL"))))

;;; --------------------------------------------------------------------
;;; Oracle 5: PER-SLOT storage maintenance == from-scratch storage-root
;;;
;;; This is the invariant the incremental validator now rests on: a contract's
;;; storage trie kept up to date one slot at a time must equal
;;; `storage-root` over the resulting slot map. It matters because the
;;; alternative — rebuilding on every touch — costs 93 s and 7.6 GB for Arc's
;;; largest contract (14 618 285 slots), which is touched in 10-46% of blocks.
;;;
;;; The slot key/value encoding here is deliberately the same expression
;;; `storage-root` uses (keccak(32-byte BE slot) -> RLP(rlp-uint val)); if
;;; mpt-live.lisp's copy ever drifts from it, this oracle is what catches it.
;;; --------------------------------------------------------------------

(defun slot-key (slot) (%keccak (int->be-bytes-fixed slot 32)))
(defun slot-val (val) (rlp-encode (rlp-uint val)))

(defun storage-model-root (model)
  "`storage-root` over an alist of (slot . value); 0-valued slots are absent."
  (storage-root model))

(defun oracle-storage-incremental ()
  (format t "~&== Oracle 5: per-slot storage == from-scratch storage-root ==~%")
  (let ((before *failures*) (rounds 0) (ops 0))
    (dotimes (r 120)
      (let ((trie (make-mtrie))
            (model '())                       ; alist (slot . value), non-zero only
            ;; a small slot space so deletes, re-adds and collisions actually happen
            (space (+ 4 (rand-int 24))))
        (incf rounds)
        (dotimes (i (+ 2 (rand-int 30)))
          (incf ops)
          (let* ((slot (rand-int space))
                 ;; zero 30% of the time: that is a DELETE in storage semantics
                 (val (if (< (rand-int 10) 3) 0 (+ 1 (rand-int (expt 2 200))))))
            (if (zerop val)
                (progn (mtrie-delete trie (slot-key slot))
                       (setf model (remove slot model :key #'car)))
                (progn (mtrie-insert trie (slot-key slot) (slot-val val))
                       (setf model (cons (cons slot val)
                                         (remove slot model :key #'car)))))
            ;; after EVERY op: incremental root == from-scratch root
            (let ((inc (if (null (eita.mpt::mtrie-top trie))
                           (bytes->hex (empty-root-bytes))
                           (bytes->hex (mtrie-root trie))))
                  (ref (bytes->hex (storage-model-root model))))
              (check (string= inc ref)
                     "round ~D op ~D (slot ~D val ~D): incremental ~A /= rebuild ~A"
                     r i slot val inc ref))))
        ;; delete every remaining slot: must land exactly on the empty root
        (dolist (kv (copy-list model))
          (mtrie-delete trie (slot-key (car kv))))
        (let ((inc (if (null (eita.mpt::mtrie-top trie))
                       (bytes->hex (empty-root-bytes))
                       (bytes->hex (mtrie-root trie)))))
          (check (string= inc (bytes->hex (empty-root-bytes)))
                 "round ~D: emptied trie root ~A /= empty root" r inc))))
    (format t "  ~D rounds, ~D ops — ~A~%" rounds ops
            (if (= before *failures*) "PASS" "FAIL"))))

(defun oracle-storage-readd ()
  "A deleted slot re-added must give the same root as never having deleted it."
  (format t "~&== Oracle 6: delete-then-re-add a slot ==~%")
  (let ((before *failures*))
    (dotimes (r 80)
      (let ((trie (make-mtrie)) (model '()) (space (+ 3 (rand-int 12))))
        (dotimes (i (+ 2 (rand-int 10)))
          (let ((slot (rand-int space)) (val (+ 1 (rand-int (expt 2 180)))))
            (mtrie-insert trie (slot-key slot) (slot-val val))
            (setf model (cons (cons slot val) (remove slot model :key #'car)))))
        (let* ((victim (car (nth (rand-int (length model)) model)))
               (vval (cdr (assoc victim model)))
               (snapshot (bytes->hex (mtrie-root trie))))
          (mtrie-delete trie (slot-key victim))
          (mtrie-insert trie (slot-key victim) (slot-val vval))
          (check (string= snapshot (bytes->hex (mtrie-root trie)))
                 "round ~D: re-adding slot ~D did not restore the root" r victim))))
    (format t "  ~A~%" (if (= before *failures*) "PASS" "FAIL"))))

;;; --------------------------------------------------------------------

(defun main ()
  (oracle-genesis)
  (oracle-property)
  (oracle-empty)
  (oracle-invert)
  (oracle-storage-incremental)
  (oracle-storage-readd)
  (format t "~%==============================~%")
  (if (zerop *failures*)
      (format t "ALL ORACLES PASS~%")
      (progn (format t "~D FAILURE(S)~%" *failures*)
             (eita.test:finish :code 1))))

(main)
