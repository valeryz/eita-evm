;;;; evm/observe-tx.lisp — what a tx did, for observers: pre-images, transfers, logs, call frames.

(in-package #:eita.evm)

(defvar *obs-acct-pre* (make-hash-table :test 'eql)
  "addr -> T once ADDR's pre-image is in *obs-acct-pres* (this tx).")
(defvar *obs-acct-pres* (make-array 64 :adjustable t :fill-pointer 0)
  "addr nonce balance code, per account at its first write in this tx; code is the object,
   hashed only when a diff is emitted.")
(defvar *obs-events* (make-array 64 :adjustable t :fill-pointer 0)
  "Pending events of this tx, in execution order, flat: :xfer kind depth from to value, and
   :log addr topics data. Frames mark/truncate it (see below).")

(defun obs-code-hash (code)
  (if (and code (plusp (length code))) (code-hash-int code) 0))
(defun obs-acct-fields (addr)
  "(values nonce balance code) of ADDR now."
  (let ((w *current-world*))
    ;; raw tables: an observer's pre-image is not a read of the tx (storage view)
    (with-acct (tb a) w addr (values (acct-nonce tb a) (acct-balance tb a) (acct-code-entry tb a)))))

(defun observe-acct-touch! (addr)
  "First write to ADDR in this tx snapshots its pre-image, faulted in first so it is
   the authoritative value. Called by the storage view's account writers."
  (when (and *current-world*
             (not (gethash addr *obs-acct-pre*)))
    (fault-account! addr)
    (setf (gethash addr *obs-acct-pre*) t)
    (multiple-value-bind (n b c) (obs-acct-fields addr)
      (let ((v *obs-acct-pres*))
        (vector-push-extend addr v) (vector-push-extend n v) (vector-push-extend b v) (vector-push-extend c v)))))
(defun observe-slot-touch! (addr slot)
  "First touch of (ADDR, SLOT) in this tx snapshots its pre-image. Called from
   fault-slot! after the fault hook, on every storage access of the Lisp path; the native
   path's hits enter the same log (c/storage_host.h, the observers' first-touch log: one
   owner, so the order is the tx's first-touch order whichever path touched)."
  (when *current-world*
    (let ((v (world-storage-get *current-world* addr slot)))
      (with-acct (tb a) *current-world* addr
        (%sh-touch a (eita.state::u256-word addr 0) (eita.state::u256-word addr 1) (eita.state::u256-word addr 2)
                   (eita.state::u256-word slot 0) (eita.state::u256-word slot 1)
                   (eita.state::u256-word slot 2) (eita.state::u256-word slot 3)
                   (eita.state::u256-word v 0) (eita.state::u256-word v 1)
                   (eita.state::u256-word v 2) (eita.state::u256-word v 3))))))

(declaim (inline observe-transfer! observe-log! observe-mark observe-revert!))
(defun observe-transfer! (kind depth from to value)
  "Record a native value move of KIND at DEPTH (pending until tx end)."
  (when *observer*
    (let ((v *obs-events*))
      (vector-push-extend :xfer v) (vector-push-extend kind v) (vector-push-extend depth v)
      (vector-push-extend from v) (vector-push-extend to v) (vector-push-extend value v))))
(defun observe-log! (addr topics data)
  "Record a LOG (pending until tx end; same revert scoping as transfers). Always: the
   committed logs feed the receipts root and the bloom, armed or not."
  (let ((v *obs-events*))
    (vector-push-extend :log v) (vector-push-extend addr v) (vector-push-extend topics v)
    (vector-push-extend data v)))
(defun observe-mark ()
  "Frame mark — taken where the frame snapshots parent-jsnap."
  (fill-pointer *obs-events*))
(defun observe-revert! (mark)
  "Drop the events recorded since MARK — the frame called revert-journal-to."
  (setf (fill-pointer *obs-events*) mark))

;; Call frames: one record per EXECUTED frame, top frame included, in pre-order: frame
;; (pre-order index in the tx, 0 = the top frame), parent (-1 for the top frame), depth,
;; kind (0 CALL, 1 CALLCODE, 2 DELEGATECALL, 3 STATICCALL, 4 CREATE, 5 CREATE2), from (the
;; calling context), to (the code address; CREATE: the new address), value (0 for
;; DELEGATECALL/STATICCALL), selector (the first 4 input bytes, -1 when shorter), input
;; length, gas (the frame's budget, stipend included), gas used, status (0 return, 1
;; revert, 2 exceptional halt). Frames inside a failed tx or a reverted parent are recorded
;; too (they ran); a CALL/CREATE refused before a frame exists is not.
(defvar *observe-calls* nil
  "Record call frames (an observer that wants them sets it).")
(defvar *obs-frame* -1 "Pre-order index of the executing frame in this tx; -1 outside one.")
(defvar *obs-frame-next* 0)
(defconstant +call-stride+ 12 "A call frame record: frame … status.")
(defvar *obs-calls* (make-array (* 16 +call-stride+))
  "This tx's call frames, flat and indexed by frame: frame K's fields
   at K·stride, written when it starts (all but gas-used and status) and when it ends — so
   the rows are in frame (pre-)order by construction.")

(defun obs-call-base (frame)
  "Where FRAME's row starts in *obs-calls* (grown to hold it)."
  (let ((base (* frame +call-stride+)) (v *obs-calls*))
    (when (> (+ base +call-stride+) (length v))
      (setf *obs-calls* (replace (make-array (* 2 (+ base +call-stride+))) v)))
    base))

(defun input-selector (input len)
  "The first four bytes of INPUT (a foreign pointer or a byte vector) as an integer; -1
   when LEN < 4."
  (if (< len 4)
      -1
      (let ((v 0))
        (dotimes (i 4 v)
          (setf v (logior (ash v 8) (if (pointerp input) (mem-aref input :uint8 i) (aref input i))))))))

(defmacro with-observed-frame ((&key kind depth from to value selector input-len gas gas-used status)
                              &body body)
  "Run BODY as the next frame of this tx (nested frames see it as their parent), then
   record its call frame. The row fields are evaluated before BODY except GAS-USED and
   STATUS (:return / :revert / :halt), which are evaluated after it. Recorded in an
   unwind-protect, because cb-create leaves its frame by RETURN-FROM."
  (let ((idx (gensym "IDX")) (parent (gensym "PARENT")) (base (gensym "BASE"))
        (pre (loop repeat 8 collect (gensym "F"))))
    `(if (not *observe-calls*)
         (progn ,@body)
         (let* ((,parent *obs-frame*)
                (,idx (prog1 *obs-frame-next* (incf *obs-frame-next*)))
                ,@(mapcar #'list pre (list depth kind from to value selector input-len gas))
                (,base (obs-call-base ,idx)))
           (let ((v *obs-calls*))
             (setf (svref v ,base) ,idx (svref v (+ ,base 1)) ,parent
                   ,@(loop for p in pre for k from 2 append `((svref v (+ ,base ,k)) ,p))))
           (unwind-protect (let ((*obs-frame* ,idx)) ,@body)
             (let ((v *obs-calls*))   ; a nested frame may have grown it
               (setf (svref v (+ ,base 10)) ,gas-used
                     (svref v (+ ,base 11)) (case ,status (:return 0) (:revert 1) (t 2)))))))))

(defvar *last-tx-logs* '()
  "The last tx's COMMITTED logs, in order, as (address topics data) — empty when it
   failed. Set by observe-tx-end!; the receipts-root check (receipts.lisp) reads it.")

(defun observe-tx-begin! ()
  "Driver hook before a tx's first account fault; opens the tx's read/write stream when a
   subscriber wants it (the storage view)."
  (setf *last-tx-logs* '()
        *view-log* *capture-reads*
        (fill-pointer *obs-events*) 0)
  (when *observer*
    (setf *observe-capture* t)
    ;; clrhash costs the table's capacity, not its count: one big tx left every later tx
    ;; paying for its size (0.8 % of the near-tip replay); a grown table is dropped instead
    (flet ((fresh (h) (if (> (hash-table-size h) 1024) (make-hash-table :test (hash-table-test h)) (clrhash h))))
      (setf *obs-acct-pre* (fresh *obs-acct-pre*)))
    (%sh-touch-reset)
    (setf (fill-pointer *obs-acct-pres*) 0
          *obs-frame-next* 0)))

(defmacro do-account-changes ((addr n0 n1 b0 b1 h0 h1) &body body)
  "Inside an observer's tx-end: each account whose nonce, balance or code the tx changed
   (net), in first-write order — nonce and balance before and after, code hashes before and
   after (0: no code; when the code object did not change, both are its hash)."
  (let ((v (gensym "V")) (i (gensym "I")) (c0 (gensym "C0")) (c1 (gensym "C1")))
    `(let ((,v *obs-acct-pres*))
       (loop for ,i from 0 below (fill-pointer ,v) by 4
             do (let ((,addr (aref ,v ,i)) (,n0 (aref ,v (+ ,i 1))) (,b0 (aref ,v (+ ,i 2))) (,c0 (aref ,v (+ ,i 3))))
                  (multiple-value-bind (,n1 ,b1 ,c1) (obs-acct-fields ,addr)
                    (let ((,h0 (if (eq ,c0 ,c1) 0 (obs-code-hash ,c0)))
                          (,h1 (if (eq ,c0 ,c1) 0 (obs-code-hash ,c1))))
                      (unless (and (= ,n0 ,n1) (= ,b0 ,b1) (= ,h0 ,h1))
                        (when (eq ,c0 ,c1) (setf ,h0 (obs-code-hash ,c0) ,h1 ,h0))
                        ,@body))))))))

(defmacro do-storage-changes ((addr slot pre post) &body body)
  "Inside an observer's tx-end: each storage slot the tx changed (net), in first-touch order
   (the first-touch log, c/storage_host.h: address, slot, value at first touch)."
  (let ((p (gensym "P")) (i (gensym "I")) (w (gensym "W")))
    `(let ((,w *current-world*))
       (dotimes (,i (%sh-touch-count))
         (let* ((,p (%sh-touch-at ,i))
                (,addr (words-u256 (mem-ref ,p :uint64 0) (mem-ref ,p :uint64 8) (mem-ref ,p :uint64 16) 0))
                (,slot (words-u256 (mem-ref ,p :uint64 32) (mem-ref ,p :uint64 40) (mem-ref ,p :uint64 48) (mem-ref ,p :uint64 56)))
                (,pre (words-u256 (mem-ref ,p :uint64 64) (mem-ref ,p :uint64 72) (mem-ref ,p :uint64 80) (mem-ref ,p :uint64 88)))
                (,post (world-storage-get ,w ,addr ,slot)))
           (unless (= ,pre ,post) ,@body))))))

(defmacro do-call-frames ((frame parent depth kind from to value selector input-len gas gas-used status)
                          &body body)
  "Inside an observer's tx-end, with *observe-calls*: each executed frame, in pre-order."
  (let ((v (gensym "V")) (k (gensym "K")) (b (gensym "B")))
    `(let ((,v *obs-calls*))
       (dotimes (,k *obs-frame-next*)
         (let* ((,b (* ,k +call-stride+))
                ,@(loop for var in (list frame parent depth kind from to value selector input-len gas gas-used status)
                        for j from 0 collect `(,var (svref ,v (+ ,b ,j)))))
           ,@body)))))

(defmacro do-tx-events ((&key transfer log) &body body)
  "Inside an observer's tx-end of a SUCCESSFUL tx: its committed native transfers and logs,
   in execution order. TRANSFER is (kind depth from to value) — kind 0 tx envelope, 1 CALL
   value, 2 CREATE endowment, 3 SELFDESTRUCT sweep, 4 a chain's native move; depth 0 for the
   envelope / top frame, the callee frame for 1/2 — and LOG is (index addr topics data);
   BODY is (:transfer forms…) (:log forms…)."
  (let ((v (gensym "V")) (i (gensym "I")) (n (gensym "N"))
        (tb (cdr (assoc :transfer body))) (lb (cdr (assoc :log body))))
    (destructuring-bind (kind depth from to value) transfer
      (destructuring-bind (index addr topics data) log
        `(let ((,v *obs-events*) (,i 0) (,n 0))
           (loop while (< ,i (fill-pointer ,v))
                 do (if (eq (aref ,v ,i) :xfer)
                        (let ((,kind (aref ,v (+ ,i 1))) (,depth (aref ,v (+ ,i 2))) (,from (aref ,v (+ ,i 3)))
                              (,to (aref ,v (+ ,i 4))) (,value (aref ,v (+ ,i 5))))
                          ,@tb (incf ,i 6))
                        (let ((,index ,n) (,addr (aref ,v (+ ,i 1))) (,topics (aref ,v (+ ,i 2))) (,data (aref ,v (+ ,i 3))))
                          ,@lb (incf ,n) (incf ,i 4)))))))))

(defun observe-tx-end! (block tx success)
  "Driver hook after the tx's fee settlement + end-of-tx deletions: the observer's tx-end
   sees the tx's touched-state summary (do-account-changes, do-storage-changes,
   do-call-frames, and iff SUCCESS do-tx-events); the committed logs become *last-tx-logs*
   (the receipts gate), observer or not. Then reset."
  (observe tx-end block tx success)
  (when success
    (let ((v *obs-events*) (i 0))
      (loop while (< i (fill-pointer v))
            do (if (eq (aref v i) :xfer)
                   (incf i 6)
                   (progn (push (list (aref v (+ i 1)) (aref v (+ i 2)) (aref v (+ i 3))) *last-tx-logs*)
                          (incf i 4))))))
  (let ((logs (nreverse *last-tx-logs*)))
    (observe-tx-begin!)
    (setf *last-tx-logs* logs *observe-capture* nil))
  (setf *view-log* nil))

(declaim (inline read-addr))
