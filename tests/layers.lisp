;;;; test-layers.lisp — layered snapshots (src/state/snapshot.lisp) against the Lean model
;;;; (lean/Evm/Persist/Layered.lean), on random states.
;;;;
;;;; Run: (eita.test:run-all :only '("layers")), or (asdf:test-system "eita") for all suites.
;;;;
;;;; Each round: a random base (written by the merge writer, so materialized), 1-6 random
;;;; FieldsCover layers written by the layer writer, then
;;;;   lookup  `view-account` / `view-slot` / `view-map-account-storage` through the stack
;;;;           = `mat (applyAll layers base)` computed here on hash tables;
;;;;   minor   the oldest run of layers composed into one (`write-composed` :parent): the
;;;;           view through the new stack is unchanged (Lean `compose_run_view`);
;;;;   major   base + all layers merged into a new base (`write-composed`): its records are
;;;;           exactly the model's materialized state (Lean `compaction_correct`);
;;;;   root    the layered root check (state/root.lisp over base + layers) equals the
;;;;           root of the compacted base.
;;;; Addresses and slots come from small ranges so that collisions, wipes over earlier
;;;; writes, tombstones over base slots and empty-but-marked accounts all occur.

(in-package #:eita.state.snapshot)

(defvar *rng* (sb-ext:seed-random-state 20261026))
(defun rnd (n) (random n *rng*))
(defparameter +ec+ +empty-code-hash+)
(defparameter *codes* (list +ec+ (+ +ec+ 1) (+ +ec+ 2)))   ; fake codehashes: the root check takes them as given

;;; The model: accounts addr -> (nonce balance codehash mark); storage (addr . slot) -> v.
(defun model-copy (m) (let ((h (make-hash-table :test 'equal))) (maphash (lambda (k v) (setf (gethash k h) v)) m) h))

(defun rand-addr () (+ #x1000 (rnd 40)))
(defun rand-slot () (rnd 12))
(defun rand-fields ()
  (case (rnd 5)
    (0 (list 0 0 +ec+ nil))              ; deleted / empty
    (1 (list 0 0 +ec+ t))                ; empty but marked
    (t (list (rnd 3) (rnd 3) (nth (rnd 3) *codes*) (zerop (rnd 4))))))

(defun has-storage (sto addr)
  (loop for k being the hash-keys of sto using (hash-value v)
        thereis (and (= (car k) addr) (plusp v))))

(defun mat (acc sto)
  "Lean `mat`: the base the writer would produce."
  (let ((a (make-hash-table)) (s (make-hash-table :test 'equal)))
    (maphash (lambda (k v) (when (plusp v) (setf (gethash k s) v))) sto)
    (let ((addrs (remove-duplicates (append (loop for k being the hash-keys of acc collect k)
                                            (loop for k being the hash-keys of s collect (car k))))))
      (dolist (addr addrs)
        (let ((f (gethash addr acc)) (hs (has-storage s addr)))
          (if (null f)
              (when hs (setf (gethash addr a) (list 0 0 +ec+ t)))
              (destructuring-bind (n b c mark) f
                (when (s1-included-p n b c hs mark)
                  (setf (gethash addr a) (list n b c (and (zerop n) (zerop b) (= c +ec+))))))))))
    (values a s)))

(defun apply-delta (acc sto d)
  "Lean `apply`. D: list of (addr fields wiped slots)."
  (dolist (e d)
    (destructuring-bind (addr fields wiped slots) e
      (setf (gethash addr acc) fields)
      (when wiped
        (loop for k in (loop for k being the hash-keys of sto when (= (car k) addr) collect k)
              do (remhash k sto)))
      (dolist (kv slots) (setf (gethash (cons addr (car kv)) sto) (cdr kv))))))

(defun rand-delta ()
  (let ((addrs (remove-duplicates (loop repeat (1+ (rnd 12)) collect (rand-addr)))))
    (sort (mapcar (lambda (addr)
                    (list addr (rand-fields) (zerop (rnd 5))
                          (sort (remove-duplicates (loop repeat (rnd 5) collect (cons (rand-slot) (if (zerop (rnd 3)) 0 (1+ (rnd 9)))))
                                                   :key #'car)
                                #'< :key #'car)))
                  addrs)
          #'< :key #'first)))

(defvar *dir* (format nil "/tmp/test-layers-~D/" (sb-posix:getpid)))
(defvar *open* '() "Snaps opened this round (closed at its end).")
(defun open-snap (path) (car (push (snap-open path) *open*)))

(defun write-base (n acc sto)
  "A base from the model (materialized by the writer)."
  (let* ((tmp (snap-tmp-path *dir* n))
         (m (make-merge tmp 1 n "0x00" nil))
         (addrs (sort (remove-duplicates (append (loop for k being the hash-keys of acc collect k)
                                                 (loop for k being the hash-keys of sto collect (car k))))
                      #'<)))
    (dolist (addr addrs)
      (merge-account m addr :fields (gethash addr acc)
                            :slots (sort (loop for k being the hash-keys of sto using (hash-value v)
                                               when (= (car k) addr) collect (cons (cdr k) v))
                                         #'< :key #'car)))
    (merge-finish m '())
    (snap-publish *dir* n tmp)
    (open-snap (snap-path *dir* n))))

(defun write-layer (p n d)
  (let* ((tmp (layer-tmp-path *dir* p n))
         (m (make-merge tmp 1 n "0x00" nil :parent p)))
    (dolist (e d)
      (destructuring-bind (addr fields wiped slots) e
        (merge-account m addr :fields fields :wiped wiped :slots slots)))
    (merge-finish m '())
    (snap-publish *dir* n tmp :final (layer-path *dir* p n))
    (open-snap (layer-path *dir* p n))))

(defvar *fails* 0)
(defun check (what got want)
  (unless (equalp got want)
    (incf *fails*)
    (when (<= *fails* 20) (format t "FAIL ~A~%   got  ~S~%   want ~S~%" what got want))))

(defun check-view (tag layers base acc sto)
  "Every address in range: view-account, view-slot and the storage map vs the model."
  (multiple-value-bind (ma ms) (mat acc sto)
    (loop for addr from #x1000 below (+ #x1000 40)
          do (multiple-value-bind (found n b c flag code) (view-account layers base addr)
               (check (list tag :account addr) (and found (list n b c flag)) (gethash addr ma))
               ;; CODE is the protocol's code vector or NIL, never a disk layer's WIPED flag
               (check (list tag :code addr) (typep code '(or null (vector (unsigned-byte 8)))) t))
             (loop for slot below 12
                   do (check (list tag :slot addr slot) (view-slot layers base addr slot)
                             (gethash (cons addr slot) ms 0)))
             (let ((got '()))
               (view-map-account-storage layers base addr (lambda (k v) (push (cons k v) got)))
               (check (list tag :map addr) (sort got #'< :key #'car)
                      (sort (loop for k being the hash-keys of ms using (hash-value v)
                                  when (= (car k) addr) collect (cons (cdr k) v))
                            #'< :key #'car))))))

(defun check-base (tag s acc sto)
  "S's records are exactly the model's materialized state."
  (multiple-value-bind (ma ms) (mat acc sto)
    (let ((got-a (make-hash-table)) (got-s (make-hash-table :test 'equal)))
      (snap-map-accounts s (lambda (addr n b c flag) (setf (gethash addr got-a) (list n b c flag))))
      (snap-map-storage s (lambda (addr slot v) (setf (gethash (cons addr slot) got-s) v)))
      (check (list tag :accounts) (sort (loop for k being the hash-keys of got-a using (hash-value v) collect (cons k v)) #'< :key #'car)
             (sort (loop for k being the hash-keys of ma using (hash-value v) collect (cons k v)) #'< :key #'car))
      (check (list tag :storage)
             (sort (loop for k being the hash-keys of got-s using (hash-value v) collect (list (car k) (cdr k) v)) #'< :key (lambda (x) (+ (* 100 (first x)) (second x))))
             (sort (loop for k being the hash-keys of ms using (hash-value v) collect (list (car k) (cdr k) v)) #'< :key (lambda (x) (+ (* 100 (first x)) (second x))))))))

(defun round-1 (r)
  (mapc #'snap-close *open*)
  (setf *open* '())
  (sb-ext:run-program "rm" (list "-rf" *dir*) :search t)
  (ensure-directories-exist *dir*)
  (let ((acc (make-hash-table)) (sto (make-hash-table :test 'equal)))
    ;; a base: a random state, materialized
    (apply-delta acc sto (mapcar (lambda (e) (list (first e) (second e) nil (remove 0 (fourth e) :key #'cdr))) (rand-delta)))
    (multiple-value-bind (ma ms) (mat acc sto) (setf acc ma sto ms))
    (let* ((base (write-base 100 acc sto)) (layers '()) (blk 100) (k (1+ (rnd 6))))
      (check-view (list r :base) '() base acc sto)
      (dotimes (i k)
        (let ((d (rand-delta)) (n (+ blk 10)))
          (apply-delta acc sto d)
          (push (write-layer blk n d) layers)
          (setf blk n)))
      (check-view (list r :stack k) layers base acc sto)
      ;; minor: the oldest run composed into one layer
      (when (>= k 2)
        (let* ((j (+ 2 (rnd (1- k))))                ; how many of the oldest
               (run (last layers j))
               (p (snap-parent (car (last run)))) (n (snap-block (first run)))
               (tmp (layer-tmp-path *dir* p n)))
          (write-composed tmp 1 n "0x00" run base :parent p)
          (let ((fin (layer-path *dir* p n)))
            (snap-publish *dir* n tmp :final fin)
            (let ((stack (append (butlast layers j) (list (open-snap fin)))))
              (check-view (list r :minor j) stack base acc sto)))))
      ;; major: everything into a new base
      (let ((tmp (snap-tmp-path *dir* blk)))
        (write-composed tmp 1 blk "0x00" layers base)
        (snap-publish *dir* blk tmp)
        (let ((nb (open-snap (snap-path *dir* blk))))
          (check-base (list r :major) nb acc sto)
          (check-view (list r :major-view) '() nb acc sto)
          ;; root: layered check over base + layers = check over the compacted base
          (let ((want (eita.state.root:snapshot-root (snap-path *dir* blk) :threads 2))
                (got (eita.state.root:snapshot-root (snap-path *dir* 100) :threads 2
                                                   :layers (mapcar #'snap-dir (reverse layers)))))
            (check (list r :root) got want)
            ;; and with every base storage a giant: the layers laid over it in place
            (let ((big eita.state.root::*big*))
              (setf eita.state.root::*big* 0)   ; global: the pool threads read it
              (unwind-protect
                   (check (list r :root-giant)
                          (eita.state.root:snapshot-root (snap-path *dir* 100) :threads 2
                                                        :layers (mapcar #'snap-dir (reverse layers)))
                          want)
                (setf eita.state.root::*big* big)))))))))

(defun gc-spares-frozen-layer ()
  "A frozen RAM layer whose layer-P-N/ the writer has published but not yet swapped into the
   stack: no resume point names it, and the replay's GC (prune-dumps!: run-gc pinned by
   live-components) must leave it (2026-11-08: it deleted it under the writer)."
  (let ((dir (format nil "~Agc/" *dir*)))
    (ensure-directories-exist (merge-pathnames "layer-117-118/" dir))
    (let ((eita.state::*layers* (list (eita.state::make-ram-layer :block 118 :parent 117)))
          (eita.state::*base* nil) (eita.state::*pending-root* nil)
          (eita.state::*compacting-base* nil) (eita.state::*compactor-job* nil))
      (let ((*standard-output* (make-broadcast-stream)))
        (eita.state.recovery:run-gc dir :pinned (eita.state::live-components))))
    (check :gc-spares-frozen-layer (and (probe-file (merge-pathnames "layer-117-118/" dir)) t) t)))

(defun tip-freezes-stay-bounded ()
  "Every block a layer, as at the tip: a world over a base, each block's hot set frozen and
   written by the writer thread, `collect-written!` polled between blocks. The tables the
   written layers still hold never pass a quarter of the state budget plus one block's,
   and are dropped (cut loose) when it is reached. The hot-budget check sees a large hot
   set and not a small one. The stack's specials are set globally (the writer thread
   reads the global values) and restored, the hooks `back-world!` installs with them."
  (let* ((dir (format nil "~Atip/" *dir*))
         (old-env (sb-ext:posix-getenv "EITA_STATE_DIR"))
         (saved (list eita.state::*hot-budget-bytes* eita.state::*written* eita.state::*layers* eita.state::*base*
                      eita.state::*current-world* eita.state::*keep-zero-slots* eita.state::*fault-account-hook*
                      eita.state::*fault-slot-hook* eita.state::*storage-wipe-hook* eita.state::*cold-storage-map-hook*))
         (world (eita.state:make-world))
         (most 0) (one 0) (drops 0) (dropped '()))
    (ensure-directories-exist dir)
    (sb-posix:setenv "EITA_STATE_DIR" dir 1)
    (setf eita.state::*hot-budget-bytes* (* 1024 1024) eita.state::*written* '()
          eita.state::*current-world* world)
    (unwind-protect
         (let ((*standard-output* (make-broadcast-stream)))
           (let ((tmp (snap-tmp-path dir 100)))
             (let ((m (make-merge tmp 1 100 "0x00" nil)))
               (merge-account m #x1000 :fields (list 1 1 +ec+ nil) :slots (list (cons 1 1)))
               (merge-finish m '()))
             (snap-publish dir 100 tmp))
           (eita.state::back-world! world (snap-open (snap-path dir 100)) '())
           (loop for b from 101 to 140
                 do (loop for a from 0 below 20
                          do (loop for k below 50
                                   do (eita.state::world-storage-set world (+ #x2000 a) (+ (* 1000 b) k) (1+ k))))
                    (let ((l (eita.state::freeze! world b "0x00")))
                      (setf one (max one (eita.state::ram-layer-bytes l))))
                    (eita.state::writer-drain!)
                    (let ((before (cdr eita.state::*written*)))
                      (eita.state::collect-written!)
                      (when (and before (null eita.state::*written*))
                        (incf drops) (setf dropped (append before dropped))))
                    (setf most (max most (or (car eita.state::*written*) 0)))))
      (eita.state::stop-background!)
      (mapc #'snap-close (remove-if-not #'snap-p (cons eita.state::*base* eita.state::*layers*)))
      ;; back-world! installed the snapshot hooks: the suites after this one run on plain worlds
      (destructuring-bind (budget written layers base cw kz fa fs sw cs) saved
        (setf eita.state::*hot-budget-bytes* budget eita.state::*written* written eita.state::*layers* layers
              eita.state::*base* base eita.state::*current-world* cw eita.state::*keep-zero-slots* kz
              eita.state::*fault-account-hook* fa eita.state::*fault-slot-hook* fs
              eita.state::*storage-wipe-hook* sw eita.state::*cold-storage-map-hook* cs))
      (if old-env (sb-posix:setenv "EITA_STATE_DIR" old-env 1) (sb-posix:unsetenv "EITA_STATE_DIR")))
    (check :tip-one-block-measured (plusp one) t)
    (check :tip-written-bounded (<= most (+ (floor (* 1024 1024) 4) one)) t)
    (check :tip-written-dropped (plusp drops) t)
    (check :tip-dropped-tables-cut (every (lambda (l) (null (eita.state::ram-layer-accts l))) dropped) t)
    ;; the hot-budget check (replay thread only: bindings are fine): a hot set of 20,000
    ;; slots is over 1 MB, an empty one is not
    (let ((eita.state::*hot-budget-bytes* (* 1024 1024))
          (eita.state::*base* t) (eita.state::*layers* '())
          (w (eita.state:make-world)))
      (let ((eita.state::*current-world* w))
        (check :hot-budget-empty (eita.state:hot-over-budget-p 1000) nil)
        (loop for k below 20000 do (eita.state::world-storage-set w #x3000 k 1))
        (check :hot-budget-over (and (eita.state:hot-over-budget-p 1000) t) t)
        (check :hot-budget-only-every-1000 (eita.state:hot-over-budget-p 1001) nil)
        (multiple-value-bind (lisp native) (eita.state::acct-table-bytes (eita.state::world-accts w))
          ;; 20,000 slots: at least 65 bytes each in native memory, and the table's arrays in the heap
          (check :table-bytes-native (>= native (* 65 20000)) t)
          (check :table-bytes-lisp (plusp lisp) t))))))

(let ((rounds (if eita.test:*argument* (parse-integer eita.test:*argument*) 200)))
  (dotimes (r rounds) (round-1 r))
  (gc-spares-frozen-layer)
  (tip-freezes-stay-bounded)
  (sb-ext:run-program "rm" (list "-rf" *dir*) :search t)
  (format t "~D rounds, ~D failures~%" rounds *fails*)
  (eita.test:finish :code (if (zerop *fails*) 0 1)))
