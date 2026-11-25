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
;;;; Then the same rounds in snapshot v2 (hashed key order): the view by hashed key, the
;;;; major compaction, the persisted fences and the state root, with mutants that must fail
;;;; (see "v2" below).
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
                (setf eita.state.root::*big* big)))
            ;; the converter (state/convert.lisp): the v1 stack as a v2 base, every storage a
            ;; giant in even rounds; its records are the model's, its root the v1 stack's
            (let ((big eita.state.root::*big*) (tmp (snap-tmp-path (format nil "~Av2/" *dir*) blk)))
              (setf eita.state.root::*big* (if (evenp r) 0 big))
              (unwind-protect (eita.state.root:convert-stack base layers tmp (format nil "~Aconv/" *dir*) :threads (1+ (rnd 3)))
                (setf eita.state.root::*big* big))
              (let ((v2 (open-snap tmp)))
                (check-base-2 (list r :convert) v2 acc sto)
                (check-fences (list r :convert) v2)
                (check (list r :convert-view) (view-mismatches '() v2 acc sto) 0)
                (check (list r :convert-root) (eita.state.root:snapshot-root tmp :threads 2) want)))))))))

(defun convert-gate ()
  "`convert-snapshot` from a state directory, over many chunks (12,000 accounts, a layer
   across them): it takes the composition the anchor names, publishes the v2 base and its
   anchor when the root is the header's, and quarantines it when it is not."
  (mapc #'snap-close *open*)
  (setf *open* '())
  (sb-ext:run-program "rm" (list "-rf" *dir*) :search t)
  (let ((acc (make-hash-table)) (sto (make-hash-table :test 'equal)) (d '()))
    (dotimes (i 12000)
      (let ((addr (* 7919 (1+ i))))
        (setf (gethash addr acc) (if (zerop (mod i 11)) (list 0 0 +ec+ t) (list (rnd 3) (1+ (rnd 9)) +ec+ nil)))
        (dotimes (k (if (zerop (mod i 5)) (rnd 40) 0)) (setf (gethash (cons addr (rnd 100)) sto) (1+ (rnd 1000))))))
    (dotimes (i 400)                    ; the layer: changes, wipes, new accounts across the range
      (let ((addr (if (evenp i) (* 7919 (1+ (rnd 12000))) (+ 3 (* 7919 (rnd 12000))))))
        (push (list addr (list (rnd 3) (rnd 3) +ec+ (zerop (rnd 3))) (zerop (rnd 7))
                    (sort (remove-duplicates (loop repeat (rnd 6) collect (cons (rnd 100) (rnd 3))) :key #'car) #'< :key #'car))
              d)))
    (setf d (sort (remove-duplicates d :key #'first) #'< :key #'first))
    (let* ((base (write-base 100 acc sto)) (layer (write-layer 100 200 d))
           (root (eita.state.root:snapshot-root (snap-path *dir* 100) :threads 2 :layers (list (layer-path *dir* 100 200))))
           (comps (mapcar #'component-of (list base layer)))
           (out (format nil "~Aout/" *dir*)) (bad (format nil "~Abad/" *dir*)))
      (with-open-file (a (merge-pathnames "anchors.sexp" *dir*) :direction :output :if-exists :supersede)
        (let ((*print-pretty* nil)) (prin1 (list 200 (concatenate 'string "0x" root) root t (composition-string comps)) a)) (terpri a))
      ;; the layer's manifest given the header root (the content hash covers the files only)
      (let ((m (read-manifest (layer-path *dir* 100 200))))
        (setf (getf m :state-root) (concatenate 'string "0x" root))
        (with-open-file (f (merge-pathnames "MANIFEST.sexp" (layer-path *dir* 100 200)) :direction :output :if-exists :supersede)
          (let ((*print-pretty* nil) (*print-case* :downcase)) (prin1 m f) (terpri f))))
      (let ((got (let ((big eita.state.root::*big*))   ; storages over 20 slots as giants (global: the pool reads it)
                   (setf eita.state.root::*big* 20)
                   (unwind-protect (eita.state.root:convert-snapshot *dir* out :threads 3)
                     (setf eita.state.root::*big* big)))))
        (check :convert-published (and got (probe-file (snap-path out 200)) t) t)
        (when got
          (let ((v2 (open-snap (snap-path out 200))))
            (check :convert-root (eita.state.root:snapshot-root (snap-path out 200) :threads 2) root)
            (check :convert-version (snap-version v2) 2)
            (check :convert-anchor (eita.state.recovery:read-anchors out)
                   (list (list 200 t (getf (snap-manifest v2) :content-hash)))))))
      ;; and a header root it does not have: quarantined, no anchor
      (with-open-file (a (merge-pathnames "anchors.sexp" *dir*) :direction :output :if-exists :supersede)
        (prin1 (list 100 "0x00" "00" t (composition-string (list (component-of base)))) a) (terpri a))
      (check :convert-gate (eita.state.root:convert-snapshot *dir* bad :threads 2) nil)
      (check :convert-quarantined (and (probe-file (snap-tmp-path bad 100)) (not (probe-file (snap-path bad 100)))
                                       (not (probe-file (merge-pathnames "anchors.sexp" bad))) t)
             t))))

(defun gc-spares-frozen-layer ()
  "A frozen RAM layer whose layer-P-N/ the writer has published but not yet swapped into the
   stack: no resume point names it, and the replay's GC (prune-dumps!: run-gc pinned by
   live-components) must leave it (deleting it under the writer breaks the writer's rename)."
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
                      eita.state::*fault-slot-hook* eita.state::*storage-wipe-hook*))
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
      (destructuring-bind (budget written layers base cw kz fa fs sw) saved
        (setf eita.state::*hot-budget-bytes* budget eita.state::*written* written eita.state::*layers* layers
              eita.state::*base* base eita.state::*current-world* cw eita.state::*keep-zero-slots* kz
              eita.state::*fault-account-hook* fa eita.state::*fault-slot-hook* fs
              eita.state::*storage-wipe-hook* sw))
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

(defun big-delta (k)
  "Every address in range, with slots: a layer that outweighs a one-account base (a major
   compaction is due over it). Block K's layer has one more slot per address than the one
   before: a base of the wrong block under a layer shows through the storage map."
  (loop for addr from #x1000 below (+ #x1000 40)
        collect (list addr (list 1 (+ k addr) +ec+ nil) nil
                      (loop for slot below (+ 12 (floor (- k 100) 10)) collect (cons slot (+ 1 k slot))))))

(defun rollback-discards-pending-base (sub)
  "A major compaction finished (snap-120 over base 100 and layers 110, 120) and waits for its
   own root check (SUB :due — not started; :running — a checker process in flight; :above —
   the rollback stays at M; :guard — the check passes after a rollback the pending base
   missed: `compaction-swap!` refuses it). A reorg rolls back to 115, below M = 120 (the Veil model
   CompactionDeepReorg, 17 steps): the pending base must go with the abandoned branch —
   its check stopped, snap-120 deleted, nothing waiting on it — so that compaction and GC
   resume, `finish-anchors!` returns, and a later pass of that check cannot install the old
   branch's snap-120 under the kept layers. At or above M it stays and swaps in as before.
   The stack's specials are set globally (`finish-anchors!` runs on a thread) and restored."
  (let* ((dir (format nil "~Areorg-~(~A~)/" *dir* sub))
         (old-env (sb-ext:posix-getenv "EITA_STATE_DIR"))
         (vars '(eita.state::*base* eita.state::*layers* eita.state::*compacting-base* eita.state::*base-check-due*
                 eita.state::*pending-root* eita.state::*anchor-queue* eita.state::*compactor* eita.state::*compactor-job*
                 eita.state::*compactor-result* eita.state::*retired* eita.state::*current-world*
                 eita.state::*keep-zero-slots* eita.state::*fault-account-hook* eita.state::*fault-slot-hook*
                 eita.state::*storage-wipe-hook*))
         (saved (mapcar #'symbol-value vars))
         (world (eita.state:make-world))
         (tag (list :reorg sub))
         (proc nil))
    (sb-ext:run-program "rm" (list "-rf" dir) :search t)
    (ensure-directories-exist dir)
    (sb-posix:setenv "EITA_STATE_DIR" dir 1)
    (unwind-protect
         (let ((*dir* dir) (*open* '())
               (acc (make-hash-table)) (sto (make-hash-table :test 'equal)))
           (apply-delta acc sto (list (list #x1000 (list 1 1 +ec+ nil) nil (list (cons 1 1)))))
           (let* ((base (write-base 100 acc sto))
                  (models '()) (layers '()))
             (loop for (p n) in '((100 110) (110 120) (120 130))
                   for d = (big-delta n)
                   do (apply-delta acc sto d)
                      (push (write-layer p n d) layers)
                      (push (cons n (cons (model-copy acc) (model-copy sto))) models))
             ;; snap-120 = base + layers 110, 120: the finished major compaction
             (let ((tmp (snap-tmp-path dir 120)))
               (write-composed tmp 1 120 "0x00" (rest layers) base)
               (snap-publish dir 120 tmp))
             (eita.state::back-world! world base layers)
             (setf eita.state::*compacting-base* (snap-open (snap-path dir 120))
                   eita.state::*base-check-due* nil eita.state::*pending-root* nil eita.state::*anchor-queue* '()
                   eita.state::*compactor* nil eita.state::*compactor-job* nil eita.state::*compactor-result* nil
                   eita.state::*retired* '())
             (ecase sub
               ((:due :above :guard) (setf eita.state::*base-check-due* 120))
               (:running
                (setf proc (sb-ext:run-program "/bin/sleep" '("600") :wait nil)
                      eita.state::*pending-root*
                      (list 120 "0x00" proc (namestring (merge-pathnames "state-120.rootout" dir))
                            (list (list :base 120 "")) :base (get-universal-time)))))
             (let* ((target (if (eq sub :above) 125 115))
                    ;; :guard — the rollback is not seen by the pending base (as if a path
                    ;; bypassed `rollback-to!`'s discard): the swap itself must refuse it
                    (top (if (eq sub :guard)
                             (let ((cb (shiftf eita.state::*compacting-base* nil)))
                               (prog1 (eita.state::rollback-to! world target)
                                 (setf eita.state::*compacting-base* cb)))
                             (eita.state::rollback-to! world target)))
                    (m (if (eq sub :above) 120 110))
                    (model (cdr (assoc m models))))
               (check (list tag :top) top m)
               (if (eq sub :above)
                   ;; at or above M: the pending base stays, its check goes on, the swap installs it
                   (progn
                     (check (list tag :pending-kept) (and eita.state::*compacting-base* (snap-block eita.state::*compacting-base*)) 120)
                     (check (list tag :check-due-kept) eita.state::*base-check-due* 120)
                     (eita.state::compaction-swap! 120)
                     (check (list tag :base-is-120) (snap-block eita.state::*base*) 120))
                   (progn
                     (when (eq sub :guard)
                       (check (list tag :swap-refused) (eita.state::compaction-swap! 120) nil))
                     (check (list tag :pending-discarded) eita.state::*compacting-base* nil)
                     (check (list tag :check-due-cleared) eita.state::*base-check-due* nil)
                     (check (list tag :root-check-stopped) eita.state::*pending-root* nil)
                     (when proc (check (list tag :checker-dead) (sb-ext:process-alive-p proc) nil))
                     (check (list tag :snap-120-deleted) (probe-file (snap-path dir 120)) nil)
                     ;; the old check passing later must not install snap-120
                     (let ((s eita.state::*compacting-base*))
                       (when s (eita.state::compaction-swap! 120)))
                     (check (list tag :base-still-100) (snap-block eita.state::*base*) 100)
                     ;; no stall: a bounded run's end returns, a compaction starts again
                     (let ((th (sb-thread:make-thread (lambda () (handler-case (progn (eita.state::finish-anchors! 115) :returned)
                                                                (error (e) (list :error (princ-to-string e))))))))
                       (let ((r (sb-thread:join-thread th :timeout 20 :default :timeout)))
                         (when (eq r :timeout) (sb-thread:terminate-thread th) (sb-thread:join-thread th :default nil))
                         (check (list tag :finish-anchors-returns) r :returned)))
                     (when proc (ignore-errors (sb-ext:process-kill proc 9)) (sb-ext:process-wait proc))
                     (setf eita.state::*pending-root* nil)
                     (unless eita.state::*compacting-base*
                       (eita.state::compaction-step! 1000 nil)
                       (check (list tag :compaction-restarts) (and eita.state::*compactor* t) t)
                       (when eita.state::*compactor*
                         (sb-thread:join-thread eita.state::*compactor* :default nil)
                         (check (list tag :compacted-to-110) (eita.state::compaction-step! 1000 nil) 110)
                         (check-base (list tag :compacted-110) eita.state::*compacting-base* (car model) (cdr model))
                         (snap-close (shiftf eita.state::*compacting-base* nil))))))
               (check-view (list tag :view) eita.state::*layers* eita.state::*base* (car model) (cdr model))
               (mapc #'snap-close eita.state::*retired*)
               (mapc #'snap-close (remove-if-not #'snap-p (cons eita.state::*base* eita.state::*layers*)))
               (when (and eita.state::*compacting-base* (not (eq sub :above))) (snap-close eita.state::*compacting-base*)))))
      (when (and proc (sb-ext:process-alive-p proc)) (ignore-errors (sb-ext:process-kill proc 9)) (sb-ext:process-wait proc))
      (loop for v in vars for x in saved do (setf (symbol-value v) x))
      (if old-env (sb-posix:setenv "EITA_STATE_DIR" old-env 1) (sb-posix:unsetenv "EITA_STATE_DIR")))))

;;; ---------------------------------------------------------------- v2 (hashed key order)
;;;
;;; The same random states and layers, written in v2 (`make-writer`): the view by hashed key
;;; (`view-account-h`, `view-slot-h`, `view-map-storage-h`: `compose-range`, Lean
;;; `viewRange_acct` / `viewRange_slot`) and the major compaction (`write-composed-2`) equal
;;; the model; every fence read from a .fnc equals the one built over the file at open; the
;;; compacted base's state root, a stack trie streamed over its records in file order, equals
;;; the v1 root of the same state. Three mutants of the layers (their WIPED flags, their
;;; tombstones, their existence marks dropped) must each make some view differ from the
;;; model, and the writer must refuse records out of order or against S2 / S5.

(defvar *hk* (make-hash-table))
(defun hk (addr) (or (gethash addr *hk*) (setf (gethash addr *hk*) (eita.mpt:%keccak (int->octets addr 20)))))
(defvar *hs* (make-hash-table))
(defun hs (slot) (or (gethash slot *hs*) (setf (gethash slot *hs*) (eita.mpt:%keccak (int->octets slot 32)))))
(defun oct< (a b) (minusp (cmp-octets a b)))
(defun cmp-octets (a b) (dotimes (i (length a) 0) (cond ((< (aref a i) (aref b i)) (return -1)) ((> (aref a i) (aref b i)) (return 1)))))

(defun write-2 (tmp n entries &key parent (expect '(0 0)))
  "ENTRIES: (addr fields flags slots) in any order, SLOTS ((slot . value) ...): written in
   hashed order, each account's slots before it."
  (let ((w (make-writer tmp 1 n "0x00" :parent parent :expect expect)))
    (dolist (e (sort (copy-list entries) #'oct< :key (lambda (e) (hk (first e)))))
      (destructuring-bind (addr fields flags slots) e
        (dolist (kv (sort (copy-list slots) #'oct< :key (lambda (kv) (hs (car kv)))))
          (writer-slot w (hk addr) (hs (car kv)) (cdr kv)))
        (destructuring-bind (nonce balance codehash mark) fields
          (declare (ignore mark))
          (writer-account w (hk addr) addr flags nonce balance codehash))))
    (writer-finish w '())))

(defun write-base-2 (n acc sto)
  (multiple-value-bind (ma ms) (mat acc sto)
    (let ((tmp (snap-tmp-path *dir* n)))
      (write-2 tmp n (loop for addr being the hash-keys of ma using (hash-value f)
                           collect (list addr f (if (fourth f) +flag-exists-empty+ 0)
                                         (loop for k being the hash-keys of ms using (hash-value v)
                                               when (= (car k) addr) collect (cons (cdr k) v))))
               :expect (list (hash-table-count ma) (hash-table-count ms)))
      (snap-publish *dir* n tmp)
      (open-snap (snap-path *dir* n)))))

(defun write-layer-2 (p n d &key (mutant nil))
  "D as `rand-delta` gives it; MUTANT :wipe, :tombstone or :mark drops that from the layer."
  (let ((tmp (layer-tmp-path *dir* p n)))
    (write-2 tmp n (mapcar (lambda (e)
                             (destructuring-bind (addr fields wiped slots) e
                               (list addr fields
                                     (logior (if (and (fourth fields) (not (eq mutant :mark))) +flag-exists-empty+ 0)
                                             (if (and wiped (not (eq mutant :wipe))) +flag-wiped+ 0))
                                     (if (eq mutant :tombstone) (remove 0 slots :key #'cdr) slots))))
                           d)
             :parent p)
    (snap-publish *dir* n tmp :final (layer-path *dir* p n))
    (open-snap (layer-path *dir* p n))))

(defun view-mismatches (layers base acc sto)
  "How many of the view's answers by hashed key differ from the model (`mat`)."
  (let ((bad 0))
    (multiple-value-bind (ma ms) (mat acc sto)
      (loop for addr from #x1000 below (+ #x1000 40)
            do (multiple-value-bind (found a n b c flag) (view-account-h layers base (hk addr))
                 (unless (equalp (and found (list a n b c flag)) (let ((f (gethash addr ma))) (and f (cons addr f))))
                   (incf bad)))
               (loop for slot below 12
                     do (unless (= (view-slot-h layers base (hk addr) (hs slot)) (gethash (cons addr slot) ms 0))
                          (incf bad)))
               (let ((got '()))
                 (view-map-storage-h layers base (hk addr) (lambda (k v) (push (cons k v) got)))
                 (unless (equalp (nreverse got)
                                 (sort (loop for k being the hash-keys of ms using (hash-value v)
                                             when (= (car k) addr) collect (cons (hs (cdr k)) v))
                                       #'oct< :key #'car))
                   (incf bad)))))
    bad))

(defun records-2 (s table)
  "Every record of the v2 snap S's TABLE, decoded, in file order (a one-source compose-range)."
  (let ((out '()))
    (compose-range (list (snap-run s table nil nil))
                   (lambda (sap off)
                     (push (if (eq table :accounts)
                               (list (sap-be sap off 32) (sap-be sap (+ off 32) 20) (sap-be sap (+ off 52) 4)
                                     (sap-be sap (+ off 56) 8) (sap-be sap (+ off 64) 32) (sap-be sap (+ off 96) 32))
                               (list (sap-be sap off 32) (sap-be sap (+ off 32) 32) (sap-be sap (+ off 64) 32)))
                           out)))
    (nreverse out)))

(defun check-base-2 (tag s acc sto)
  (multiple-value-bind (ma ms) (mat acc sto)
    (check (list tag :accounts) (records-2 s :accounts)
           (sort (loop for addr being the hash-keys of ma using (hash-value f)
                       collect (destructuring-bind (n b c e) f
                                 (list (octets->int (hk addr)) addr (if e +flag-exists-empty+ 0) n b c)))
                 #'< :key #'first))
    (check (list tag :storage) (records-2 s :storage)
           (sort (loop for k being the hash-keys of ms using (hash-value v)
                       collect (list (octets->int (hk (car k))) (octets->int (hs (cdr k))) v))
                 (lambda (x y) (or (< (first x) (first y)) (and (= (first x) (first y)) (< (second x) (second y)))))))))

(defun fence-equal (a b)
  (or (and (null a) (null b))
      (and a b (= (fence-bit a) (fence-bit b)) (= (fence-r a) (fence-r b)) (equalp (fence-a a) (fence-a b))
           (= (if (fence-kids a) (hash-table-count (fence-kids a)) 0) (if (fence-kids b) (hash-table-count (fence-kids b)) 0))
           (or (null (fence-kids a))
               (loop for p being the hash-keys of (fence-kids a) using (hash-value k)
                     always (fence-equal k (gethash p (fence-kids b))))))))

(defun check-fences (tag s)
  "S's fences, read from its .fnc files, are the ones `build-fence` builds over its files."
  (check (list tag :acct-fence)
         (fence-equal (snap-acct-fence s) (build-fence (snap-acct s) +acct-rec-2+ 32 (snap-n-accounts s))) t)
  (check (list tag :slot-fence)
         (fence-equal (snap-slot-fence s) (build-fence (snap-slot-map s) +slot-rec-2+ 64 (snap-n-slots s))) t))

(defun v2-state-root (s)
  "The state root of the v2 base S in one pass over its records: each account's slots (a
   contiguous run, in hslot order) streamed into its storage trie, the accounts (in hkey
   order) into the account trie. Codehashes are taken as given."
  (let ((st (eita.state.root:make-stack-trie)) (sst (eita.state.root:make-stack-trie))
        (slots (records-2 s :storage)) (key (make-array 32 :element-type '(unsigned-byte 8))))
    (dolist (a (records-2 s :accounts))
      (destructuring-bind (h addr flags nonce balance codehash) a
        (declare (ignore addr flags))
        (eita.state.root:st-reset sst 0)
        (loop while (and slots (= (first (first slots)) h))
              do (destructuring-bind (ha hsl v) (pop slots)
                   (declare (ignore ha))
                   (eita.state.root:st-push sst (int->octets hsl 32) 0 (eita.mpt:rlp-encode (eita.mpt:rlp-uint v)))))
        (replace key (int->octets h 32))
        (eita.state.root:st-push st key 0 (eita.mpt:account-leaf-value nonce balance
                                                                       (eita.state.root:st-root-bytes (eita.state.root:st-finish sst))
                                                                       (int->octets codehash 32)))))
    (eita.mpt:bytes->hex (eita.state.root:st-root-bytes (eita.state.root:st-finish st)))))

;;; The replay's reader over a version 2 stack: by address and slot (`view-account`,
;;; `view-slot`, `view-has-storage-p`), the hashes computed on demand, with a frozen RAM
;;; layer (keyed by address, as the world is) above the disk layers.

(defun ram-layer-of (d)
  "A frozen RAM layer holding the delta D (`rand-delta`'s shape; codehashes empty)."
  (let ((tb (eita.state::make-acct-table)))
    (dolist (e d)
      (destructuring-bind (addr (nonce balance codehash mark) wiped slots) e
        (declare (ignore codehash))
        (let ((a (eita.state::acct-table-intern tb addr)))
          (setf (eita.state::acct-nonce tb a) nonce (eita.state::acct-balance tb a) balance)
          (eita.state::acct-set-flag! tb a eita.state::+acct-faulted+)
          (when mark (eita.state::acct-set-flag! tb a eita.state::+acct-marked+))
          (when wiped (eita.state::acct-set-flag! tb a eita.state::+acct-wiped+))
          (dolist (kv slots) (eita.state::acct-slot-put! tb a (car kv) (cdr kv))))))
    (eita.state::make-ram-layer :block 999 :accts tb)))

(defun mixed-mismatches (layers base acc sto)
  "How many of the address-keyed reader's answers differ from the model (`mat`)."
  (let ((bad 0))
    (multiple-value-bind (ma ms) (mat acc sto)
      (loop for addr from #x1000 below (+ #x1000 40)
            do (multiple-value-bind (found n b c flag) (view-account layers base addr (lambda () (hk addr)) #'hs)
                 (unless (equalp (and found (list n b c flag)) (gethash addr ma)) (incf bad)))
               (loop for slot below 12
                     do (unless (= (view-slot layers base addr slot (lambda () (hk addr)) (hs slot)) (gethash (cons addr slot) ms 0))
                          (incf bad)))
               (unless (eq (view-has-storage-p layers base addr (hk addr) #'hs) (has-storage ms addr))
                 (incf bad))))
    bad))

(defvar *mutants-caught* (list :wipe 0 :tombstone 0 :mark 0))

(defun round-2 (r)
  (mapc #'snap-close *open*)
  (setf *open* '())
  (sb-ext:run-program "rm" (list "-rf" *dir*) :search t)
  (ensure-directories-exist *dir*)
  (let ((acc (make-hash-table)) (sto (make-hash-table :test 'equal)))
    (apply-delta acc sto (mapcar (lambda (e) (list (first e) (second e) nil (remove 0 (fourth e) :key #'cdr))) (rand-delta)))
    (multiple-value-bind (ma ms) (mat acc sto) (setf acc ma sto ms))
    (let* ((base (write-base-2 100 acc sto)) (deltas '()) (layers '()) (blk 100) (k (1+ (rnd 6)))
           (acc0 (model-copy acc)) (sto0 (model-copy sto)))
      (check-fences (list r :v2-base) base)
      (check (list r :v2-base-view) (view-mismatches '() base acc sto) 0)
      (dotimes (i k)
        (let ((d (rand-delta)) (n (+ blk 10)))
          (apply-delta acc sto d)
          (push (cons blk d) deltas)
          (push (write-layer-2 blk n d) layers)
          (setf blk n)))
      (dolist (l layers) (check-fences (list r :v2-layer) l))
      (check (list r :v2-stack-view k) (view-mismatches layers base acc sto) 0)
      (check (list r :v2-stack-mixed k) (mixed-mismatches layers base acc sto) 0)
      (let ((d (mapcar (lambda (e) (list* (first e) (append (subseq (second e) 0 2) (list +ec+ (fourth (second e)))) (cddr e)))
                       (rand-delta)))
            (acc2 (model-copy acc)) (sto2 (model-copy sto)))
        (apply-delta acc2 sto2 d)
        (check (list r :v2-ram-over-stack k) (mixed-mismatches (cons (ram-layer-of d) layers) base acc2 sto2) 0))
      ;; minor: the oldest run composed into one layer (Lean `compose_run_view`)
      (when (>= k 2)
        (let* ((j (+ 2 (rnd (1- k)))) (run (last layers j))
               (p (snap-parent (car (last run)))) (n (snap-block (first run)))
               (tmp (layer-tmp-path *dir* p n)) (fin (layer-path *dir* p n)))
          (write-composed tmp 1 n "0x00" run base :parent p)
          (snap-publish *dir* n tmp :final fin)
          (let ((stack (append (butlast layers j) (list (open-snap fin)))))
            (check-fences (list r :v2-minor) (car (last stack)))
            (check (list r :v2-minor j) (view-mismatches stack base acc sto) 0))))
      ;; the mutants: the same deltas with one rule dropped from the layers
      (dolist (mutant '(:wipe :tombstone :mark))
        (let ((ml (loop for (p . d) in deltas
                        collect (let ((*dir* (format nil "~Am-~(~A~)/" *dir* mutant)))
                                  (ensure-directories-exist *dir*)
                                  (write-layer-2 p (+ p 10) d :mutant mutant)))))
          (when (plusp (view-mismatches ml base acc sto)) (incf (getf *mutants-caught* mutant)))))
      ;; major: everything into a new v2 base
      (let ((tmp (snap-tmp-path *dir* blk)))
        (write-composed tmp 1 blk "0x00" layers base)
        (snap-publish *dir* blk tmp)
        (let ((nb (open-snap (snap-path *dir* blk))))
          (check-base-2 (list r :v2-major) nb acc sto)
          (check-fences (list r :v2-major) nb)
          (check (list r :v2-major-view) (view-mismatches '() nb acc sto) 0)
          ;; the same state in v1: its root (state/root.lisp) is the v2 base's
          (let ((tmp1 (snap-tmp-path *dir* 1)))
            (multiple-value-bind (ma ms) (mat acc sto)
              (let ((m (make-merge tmp1 1 1 "0x00" nil)))
                (dolist (addr (sort (loop for a being the hash-keys of ma collect a) #'<))
                  (merge-account m addr :fields (gethash addr ma)
                                        :slots (sort (loop for kk being the hash-keys of ms using (hash-value v)
                                                           when (= (car kk) addr) collect (cons (cdr kk) v))
                                                     #'< :key #'car)))
                (merge-finish m '())))
            (snap-publish *dir* 1 tmp1)
            (check (list r :v2-root) (v2-state-root nb)
                   (eita.state.root:snapshot-root (snap-path *dir* 1) :threads 1))
            ;; the streaming root of the v2 base, and of the stack it was compacted from
            (check (list r :v2-root-base) (eita.state.root:snapshot-root (snap-path *dir* blk) :threads 2) (v2-state-root nb))
            (dolist (threads '(1 3))
              (check (list r :v2-root-stack threads)
                     (eita.state.root:snapshot-root (snap-path *dir* 100) :threads threads
                                                   :layers (mapcar #'snap-dir (reverse layers)))
                     (v2-state-root nb))))))
      ;; the base before the layers: compose-range over it alone is the model's base
      (check (list r :v2-base-kept) (view-mismatches '() base acc0 sto0) 0))))

(defun fences-at-scale ()
  "Fences over enough records to have deep top levels and kids (a contract of 3,000 slots:
   its buckets exceed +fence-split+), written with EXPECT exact, four times too high (the
   top level subsampled), too low and absent (kids built from the records written): each
   equals the fence `build-fence` builds over the files, and finds every key and no other."
  (let ((dir (format nil "~Afences/" *dir*)) (n 20000)
        (keys (make-hash-table :test 'equalp)))
    (loop while (< (hash-table-count keys) n)
          do (let ((k (make-array 32 :element-type '(unsigned-byte 8))))
               (dotimes (i 32) (setf (aref k i) (rnd 256)))
               (setf (gethash k keys) t)))
    (let* ((accts (sort (loop for k being the hash-keys of keys collect k) #'oct<))
           (big (nth 777 accts))
           (slots (lambda (a) (if (eq a big) 3000 (if (zerop (rnd 4)) (rnd 3) 0))))
           (plan (mapcar (lambda (a) (cons a (sort (loop repeat (funcall slots a) collect (int->octets (rnd (ash 1 60)) 32)) #'oct<)))
                         accts))
           (ns (reduce #'+ plan :key (lambda (e) (length (remove-duplicates (cdr e) :test #'equalp))))))
      (dolist (expect (list (list n ns) (list (* 4 n) (* 4 ns)) (list 100 100) (list 0 0)))
        (sb-ext:run-program "rm" (list "-rf" dir) :search t)
        (let ((w (make-writer dir 1 1 "0x00" :expect expect)))
          (dolist (e plan)
            (dolist (sl (remove-duplicates (cdr e) :test #'equalp)) (writer-slot w (car e) sl 1))
            (writer-account w (car e) 0 0 1 0 +ec+))
          (writer-finish w '()))
        (let ((s (snap-open dir)))
          (check-fences (list :fences-at-scale expect) s)
          (check (list :fences-at-scale expect :kids) (and (fence-kids (snap-slot-fence s)) t) t)
          (check (list :fences-at-scale expect :finds)
                 (loop for a in accts for i from 0
                       always (eql (find-record (snap-acct s) (snap-acct-fence s) (snap-n-accounts s) +acct-rec-2+ a 32) i))
                 t)
          (check (list :fences-at-scale expect :finds-slots)
                 (loop for (a . sls) in plan
                       always (loop for sl in sls
                                    always (find-record (snap-slot-map s) (snap-slot-fence s) (snap-n-slots s) +slot-rec-2+
                                                        (concatenate '(simple-array (unsigned-byte 8) (*)) a sl) 64)))
                 t)
          (check (list :fences-at-scale expect :absent)
                 (loop repeat 2000
                       never (let ((k (make-array 32 :element-type '(unsigned-byte 8))))
                               (dotimes (i 32) (setf (aref k i) (rnd 256)))
                               (and (not (gethash k keys))
                                    (find-record (snap-acct s) (snap-acct-fence s) (snap-n-accounts s) +acct-rec-2+ k 32))))
                 t)
          (snap-close s))))
    (sb-ext:run-program "rm" (list "-rf" dir) :search t)))

(defun writer-refuses ()
  "The v2 writer signals on keys out of order (S4), a slot without its account (S5) and a
   zero slot in a base (S2), and accepts a zero slot in a layer."
  (let ((dir (format nil "~Awriter/" *dir*)) (k1 (int->octets 1 32)) (k2 (int->octets 2 32)))
    (flet ((refuses (tag fn &key parent)
             (sb-ext:run-program "rm" (list "-rf" dir) :search t)
             (let ((w (make-writer dir 1 1 "0x00" :parent parent)))
               (check (list :writer tag)
                      (handler-case (progn (funcall fn w) (writer-finish w '()) :accepted)
                        (error () :refused))
                      (if (eq tag :layer-tombstone) :accepted :refused)))))
      (refuses :account-order (lambda (w) (writer-account w k2 2 0 1 0 +ec+) (writer-account w k1 1 0 1 0 +ec+)))
      (refuses :account-duplicate (lambda (w) (writer-account w k1 1 0 1 0 +ec+) (writer-account w k1 1 0 1 0 +ec+)))
      (refuses :slot-order (lambda (w) (writer-slot w k1 k2 1) (writer-slot w k1 k1 1) (writer-account w k1 1 0 1 0 +ec+)))
      (refuses :slot-orphan (lambda (w) (writer-slot w k1 k1 1) (writer-account w k2 2 0 1 0 +ec+)))
      (refuses :slot-after-account (lambda (w) (writer-account w k1 1 0 1 0 +ec+) (writer-slot w k1 k1 1)))
      (refuses :base-zero-slot (lambda (w) (writer-slot w k1 k1 0) (writer-account w k1 1 0 1 0 +ec+)))
      (refuses :layer-tombstone (lambda (w) (writer-slot w k1 k1 0) (writer-account w k1 1 0 0 0 +ec+)) :parent 0))
    (sb-ext:run-program "rm" (list "-rf" dir) :search t)))

(defun page-range-stays-inside ()
  "A release never names a page past the mapping (MADV_DONTNEED there zeroes another one)."
  (let ((pg (sb-posix:getpagesize)))
    (dolist (len (list 4096 pg (* 2 pg) (1+ pg) (+ 4096 88) (* 3 pg) (1- (* 3 pg))))
      (let ((top (* pg (ceiling len pg))))
        (dolist (end (list len (+ len 1) (+ len pg) (* 2 top)))
          (check (format nil "page-range ~D 0 ~D" len end)
                 (multiple-value-list (page-range len 0 end)) (list 0 top)))
        (check (format nil "page-range ~D inside" len)
               (multiple-value-list (page-range len (1+ pg) (1- len)))
               (list pg (* pg (floor (1- len) pg))))))))

(let ((rounds (if eita.test:*argument* (parse-integer eita.test:*argument*) 200)))
  (page-range-stays-inside)
  (dotimes (r rounds) (round-1 r))
  (dotimes (r rounds) (round-2 r))
  (loop for (mutant n) on *mutants-caught* by #'cddr
        do (check (list :mutant-caught mutant) (plusp n) t))
  (format t "v2 mutants caught (rounds): ~{~(~A~) ~D~^, ~}~%" *mutants-caught*)
  (convert-gate)
  (fences-at-scale)
  (writer-refuses)
  (gc-spares-frozen-layer)
  (tip-freezes-stay-bounded)
  (dolist (sub '(:due :running :above :guard)) (rollback-discards-pending-base sub))
  (sb-ext:run-program "rm" (list "-rf" *dir*) :search t)
  (format t "~D rounds, ~D failures~%" rounds *fails*)
  (eita.test:finish :code (if (zerop *fails*) 0 1)))
