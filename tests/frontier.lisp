;;;; frontier.lisp — the frontier mirrors of lean/Evm/Trie/Frontier.lean (src/state/root.lisp:
;;;; `frontier-subref` = `subRef`, `dense-above-p` = `DenseAbove`, `assemble` = `assemble` over
;;;; `refAt`) against the trie (`eita.mpt:trie-root`, `eita.mpt:storage-root`), and over
;;;; snapshot v2's key ranges (`compose-range`) as blocks of writes arrive.
;;;;
;;;;   1. Random tries (random keys, and keys sharing long prefixes so that DenseAbove fails
;;;;      at some depth), 0..600 keys, depths 1..3: `dense-above-p` over the frontier's shape
;;;;      is Lean `DenseAbove` computed from the keys, and when it holds the root assembled
;;;;      over the frontier is the trie's root (Lean `patricialise_assemble`, stated there).
;;;;   2. One contract's storage trie in a v2 stack, between two other contracts: the
;;;;      frontier at depth 1 and 2, each entry the stack trie over `compose-range` of its key
;;;;      range (base and layers, tombstones and a wipe among them), assembles to the model's
;;;;      storage root. After each block (a layer) only the dirty prefixes are rebuilt and the
;;;;      clean ones kept (Lean `stepFrontier`, `frontierOK_update`): the result equals the
;;;;      frontier rebuilt from scratch, and assembles to the post-state's root.
;;;;
;;;; Run: (eita.test:run-all :only '("frontier")), or (asdf:test-system "eita") for all suites.

(in-package #:eita.state.snapshot)

(defvar *frng* (sb-ext:seed-random-state 20261121))
(defvar *ffails* 0)
(defvar *roots-checked* 0)

(defun fcheck (what got want)
  (unless (equalp got want)
    (incf *ffails*)
    (when (<= *ffails* 20) (format t "FAIL ~S~%   got  ~S~%   want ~S~%" what got want))))

(defun f-oct< (a b) (dotimes (i (length a) nil) (cond ((< (aref a i) (aref b i)) (return t)) ((> (aref a i) (aref b i)) (return nil)))))
(defun top-nibbles (key d) (ash (octets->int key) (- (* 4 d) 256)))
(defun nibble (key j) (ldb (byte 4 (- 252 (* 4 j))) (octets->int key)))
(defun leaf-value (v) (eita.mpt:rlp-encode (eita.mpt:rlp-uint v)))

(defun frontier-of (d keyvals)
  "The depth-D frontier of KEYVALS ((key . value) sorted by key): a stack trie per prefix."
  (let ((refs (make-array (expt 16 d) :initial-element nil)) (st (eita.state.root:make-stack-trie d)))
    (loop with rest = keyvals
          for p below (expt 16 d)
          do (eita.state.root:st-reset st d)
             (loop while (and rest (= (top-nibbles (car (first rest)) d) p))
                   do (let ((kv (pop rest))) (eita.state.root:st-push st (car kv) 0 (cdr kv))))
             (setf (aref refs p) (eita.state.root:frontier-subref st)))
    refs))

(defun lean-dense-above (d keys)
  "Lean `DenseAbove d`, from its definition: every key, at every level j < d, has another key
   sharing its first j nibbles and differing in nibble j."
  (every (lambda (k)
           (loop for j below d
                 always (some (lambda (o) (and (= (top-nibbles o j) (top-nibbles k j)) (/= (nibble o j) (nibble k j))))
                              keys)))
         keys))

(defun assembled-root (d refs)
  (eita.mpt:%keccak (eita.mpt:rlp-encode (eita.state.root:assemble d refs))))

(defun random-keys (n)
  "N distinct 32-byte keys, some sharing a long prefix with an earlier one."
  (let ((keys '()) (seen (make-hash-table :test 'equalp)))
    (loop while (< (hash-table-count seen) n)
          do (let ((k (make-array 32 :element-type '(unsigned-byte 8))))
               (dotimes (i 32) (setf (aref k i) (random 256 *frng*)))
               (when (and keys (zerop (random 3 *frng*)))
                 (let ((src (nth (random (length keys) *frng*) keys)) (l (random 6 *frng*)))
                   (replace k src :end2 (floor l 2))
                   (when (oddp l)
                     (setf (aref k (floor l 2)) (logior (logand (aref src (floor l 2)) #xf0) (logand (aref k (floor l 2)) #x0f))))))
               (unless (gethash k seen) (setf (gethash k seen) t) (push k keys))))
    (sort keys #'f-oct<)))

(defun random-tries ()
  (dotimes (round 300)
    (let* ((n (if (< round 40) round (random 600 *frng*)))
           (keys (random-keys n))
           (kvs (mapcar (lambda (k) (cons k (leaf-value (1+ (random 1000 *frng*))))) keys)))
      (loop for d from 1 to 3
            do (let* ((refs (frontier-of d kvs)) (dense (eita.state.root:dense-above-p d refs)))
                 (fcheck (list :dense-above round n d) dense (lean-dense-above d keys))
                 (when (and dense keys)
                   (incf *roots-checked*)
                   (fcheck (list :assemble round n d) (assembled-root d refs) (eita.mpt:trie-root kvs))))))))

;;; 2. a contract's storage trie over a v2 stack

(defvar *fdir* (format nil "/tmp/test-frontier-~D/" (sb-posix:getpid)))
(defun fk (n width) (eita.mpt:%keccak (int->octets n width)))

(defun write-stack-2 (tmp n accounts &key parent)
  "ACCOUNTS: (addr flags balance slots), SLOTS ((slot . value) ...); written in hashed order."
  (let ((w (make-writer tmp 1 n "0x00" :parent parent)))
    (dolist (a (sort (copy-list accounts) #'f-oct< :key (lambda (a) (fk (first a) 20))))
      (destructuring-bind (addr flags balance slots) a
        (dolist (kv (sort (copy-list slots) #'f-oct< :key (lambda (kv) (fk (car kv) 32))))
          (writer-slot w (fk addr 20) (fk (car kv) 32) (cdr kv)))
        (writer-account w (fk addr 20) addr flags 1 balance +empty-code-hash+)))
    (writer-finish w '())))

(defun range-frontier (d layers base ha &key (prefixes (loop for p below (expt 16 d) collect p)) refs)
  "The depth-D frontier of the storage trie of the account HA (32 octets) in the stack, at
   PREFIXES (the others kept from REFS): each entry the stack trie over `compose-range` of
   the prefix's key range, tombstones dropped."
  (let ((refs (if refs (copy-seq refs) (make-array (expt 16 d) :initial-element nil)))
        (st (eita.state.root:make-stack-trie d)) (key (make-array 32 :element-type '(unsigned-byte 8))))
    (dolist (p prefixes refs)
      (eita.state.root:st-reset st d)
      (multiple-value-bind (lo hi) (key-range (logior (ash (octets->int ha) (* 4 d)) p) (+ 256 (* 4 d)) 64)
        (compose-range (slot-runs layers base ha lo hi)
                       (lambda (sap off)
                         (dotimes (i 32) (setf (aref key i) (sb-sys:sap-ref-8 sap (+ off 32 i))))
                         (eita.state.root:st-push st key 0 (leaf-value (sap-be sap (+ off 64) 32))))
                       :drop-zero 64))
      (setf (aref refs p) (eita.state.root:frontier-subref st)))))

(defun storage-stack ()
  (sb-ext:run-program "rm" (list "-rf" *fdir*) :search t)
  (ensure-directories-exist *fdir*)
  (let* ((c #xC0FFEE) (ha (fk c 20)) (others '(#xB0B #xCAFE))
         (model (make-hash-table)) (open '()))
    (flet ((rand-slots (k) (remove-duplicates (loop repeat k collect (cons (random 3000 *frng*) (1+ (random 1000 *frng*))))
                                              :key #'car))
           (opened (path) (car (push (snap-open path) open))))
      (dolist (kv (rand-slots 700)) (setf (gethash (car kv) model) (cdr kv)))
      (let* ((tmp (snap-tmp-path *fdir* 100))
             (base (progn (write-stack-2 tmp 100 (cons (list c 0 5 (loop for k being the hash-keys of model using (hash-value v)
                                                                       collect (cons k v)))
                                                       (mapcar (lambda (o) (list o 0 1 (rand-slots 50))) others)))
                          (snap-publish *fdir* 100 tmp)
                          (opened (snap-path *fdir* 100))))
             (layers '()) (blk 100)
             (fronts (loop for d from 1 to 2 collect (range-frontier d '() base ha))))
        (flet ((check-step (tag)
                 (let ((want (eita.mpt:storage-root (loop for k being the hash-keys of model using (hash-value v) collect (cons k v)))))
                   (loop for d from 1 to 2 for refs in fronts
                         do (fcheck (list tag d :incremental-is-fresh) refs (range-frontier d layers base ha))
                            (when (eita.state.root:dense-above-p d refs)
                              (incf *roots-checked*)
                              (fcheck (list tag d :root) (assembled-root d refs) want))))))
          (check-step :base)
          (dotimes (b 8)
            ;; a block: writes to C (new slots, overwrites, deletions), a wipe in block 5,
            ;; and writes to the other contracts (their ranges must not leak into C's)
            (let* ((wipe (= b 5))
                   (writes (remove-duplicates
                            (append (rand-slots (1+ (random 40 *frng*)))
                                    (loop repeat (random 15 *frng*)
                                          collect (cons (let ((ks (loop for k being the hash-keys of model collect k)))
                                                          (if ks (nth (random (length ks) *frng*) ks) 0))
                                                        (if (zerop (random 2 *frng*)) 0 (1+ (random 9 *frng*))))))
                            :key #'car :from-end t))
                   (n (+ blk 10)) (tmp (layer-tmp-path *fdir* blk n)))
              (when wipe (clrhash model))
              (dolist (kv writes) (if (zerop (cdr kv)) (remhash (car kv) model) (setf (gethash (car kv) model) (cdr kv))))
              (write-stack-2 tmp n (cons (list c (if wipe +flag-wiped+ 0) 7 writes)
                                         (mapcar (lambda (o) (list o 0 2 (rand-slots 5))) others))
                             :parent blk)
              (snap-publish *fdir* n tmp :final (layer-path *fdir* blk n))
              (push (opened (layer-path *fdir* blk n)) layers)
              (setf blk n)
              ;; the step: the dirty prefixes rebuilt (all of them after a wipe), the rest kept
              (setf fronts
                    (loop for d from 1 to 2 for refs in fronts
                          collect (range-frontier d layers base ha :refs refs
                                                  :prefixes (if wipe
                                                                (loop for p below (expt 16 d) collect p)
                                                                (remove-duplicates
                                                                 (mapcar (lambda (kv) (top-nibbles (fk (car kv) 32) d)) writes))))))
              (check-step (list :block b))))))
      (mapc #'snap-close open))
    (sb-ext:run-program "rm" (list "-rf" *fdir*) :search t)))

(random-tries)
(storage-stack)
(fcheck :roots-checked (> *roots-checked* 100) t)
(format t "frontier: ~D assembled roots checked, ~D failures~%" *roots-checked* *ffails*)
(eita.test:finish :code (if (zerop *ffails*) 0 1))
