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
                 eita.state::*storage-wipe-hook* eita.state::*cold-storage-map-hook*))
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
                     ;; the old check passing later (old code: it installed snap-120 here)
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
  (gc-spares-frozen-layer)
  (tip-freezes-stay-bounded)
  (dolist (sub '(:due :running :above :guard)) (rollback-discards-pending-base sub))
  (sb-ext:run-program "rm" (list "-rf" *dir*) :search t)
  (format t "~D rounds, ~D failures~%" rounds *fails*)
  (eita.test:finish :code (if (zerop *fails*) 0 1)))
