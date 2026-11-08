;;;; evm/interp.lisp — running a frame on a tier (JIT chunks, the threaded interpreter), and the
;;;; differential tier replay.

(in-package #:eita.evm)

;; Defined in evm/frames.lisp (the tier dispatch below runs inside a frame).
(declaim (special *cur-block* *current-address* *tx-arena-root*))

;; One frame's EvmState (c/evm_state.h), the unit the substate arena is sliced in
;; (evm/frames.lisp) and the differential tier replay below snapshots.
(defconstant +substate-bytes+ 608)   ; sizeof(EvmState), c/evm_state.h

(declaim (ftype function storage-host-sync!))

(defun run-frame (state code)
  "Run one frame natively: JIT chunk dispatch by default (threshold
   1), the threaded interp as the logged fallback tier."
  (storage-host-sync!)
  (multiple-value-bind (run-chunk entries aoff alen)
      (when (plusp (length code)) (jit-for-code code))
    (cond
      (run-chunk
       (incf *frames-jit*)
       ;; Hang probe: from EITA_LASTFRAME_FROM on, OVERWRITE one file with the
       ;; code of the frame about to run. When a JIT frame infinite-loops, the
       ;; file is left holding exactly the culprit's bytecode. Gated by block so
       ;; the per-frame write doesn't slow the warm 0→region replay.
       (let ((from *lastframe-from*))
         (when (and from (>= *cur-block* from))
           (with-open-file (s "/tmp/eita_lastframe.hex" :direction :output
                              :if-exists :supersede :if-does-not-exist :create)
             (format s "~D~%" *cur-block*)
             (loop for b across code do (format s "~2,'0X" b)))))
       ;; #259: pin this chunk's arena range while it executes, so a JIT triggered
       ;; by a sub-CALL cannot evict/overwrite the chunk we're running (proved
       ;; safe by Evm.CL.CodeArena.place_safe). aoff is nil on the clang/dlopen
       ;; path (separate dylibs, not arena-managed) — nothing to pin.
       (let ((*code-exec-pinned* (if aoff
                                     (cons (cons aoff alen) *code-exec-pinned*)
                                     *code-exec-pinned*)))
         (run-jit-frame state run-chunk entries (length code))))
      (t
       (when (plusp (length code))
         (incf *frames-interp*))
       (eita-run state)))))

;;; --- Differential tier replay (#241) --------------------------------
;;;
;;; EITA_DIFF_TIERS: run each top-level tx frame on BOTH tiers (JIT, then the
;;; whole tx on the interp) from the SAME pre-state, and compare the observables
;;; (gas_left, halted, reverted, output bytes). The first divergence is logged
;;; loudly with block + address + code. The interp result is kept as canonical.
;;; A single JIT frame can't hang (per-dispatch fuel in eita_execute_program),
;;; so tier-A always returns. State isolation: snapshot the EvmState +
;;; journal cursor before tier A, restore + revert-journal-to before tier B.
(defstartup *diff-tiers*
  (let ((v (sb-posix:getenv "EITA_DIFF_TIERS"))) (and v (string/= v "0")))
  "When set, every top-level tx frame is cross-checked JIT-vs-interp (#241).")
(defparameter *diff-stats* (list :txs 0 :checked 0 :divergences 0))
(defstartup *diff-every*
  (let ((v (sb-posix:getenv "EITA_DIFF_TIERS"))) (max 1 (or (and v (parse-integer v :junk-allowed t)) 1))))
(defstartup *diff-snap* nil)   ; lazy EvmState scratch (foreign, per process) (+substate-bytes+)

(defun %frame-output (state)
  "Copy the frame's output bytes (ptr@112, size@120) to a Lisp vector."
  (let ((p (mem-ref state :pointer 112)) (n (mem-ref state :uint64 120)))
    (if (or (null-pointer-p p) (zerop n)) #()
        (foreign->bytes p n))))

(defun %frame-memory (state)
  "The frame's memory (ptr@40, size@48) as a Lisp vector."
  (let ((p (mem-ref state :pointer 40)) (n (mem-ref state :uint64 48)))
    (if (or (null-pointer-p p) (zerop n)) #() (foreign->bytes p n))))

(defun %journal-bytes (arena from)
  "ARENA's journal entries from index FROM to its count, as bytes (c/tx_arena.h, 104 B each)."
  (let ((n (mem-ref arena :uint64 0)))
    (if (<= n from) #()
        (foreign->bytes (inc-pointer (mem-ref arena :pointer 16) (* from 104)) (* (- n from) 104)))))

(defun diff-run-tiers (state code)
  "Run the top-level frame on JIT then interp from the same pre-state, compare,
   log the first divergence. Leaves the INTERP (trusted) result in STATE.
   Compared: gas, halted/reverted, output, the frame's final memory, the refund counter
   and every journal entry the tx wrote (its storage, balance, nonce, warm-up and created
   effects). The restore between the tiers is what run-tx-frame! does after a frame (the
   memory arena scrubbed, the last returndata freed) plus the journal rewind and tier A's
   logs, transfers and frame records dropped (tests/diff-tiers.lisp).
   EITA_DIFF_TIERS=N cross-checks every Nth tx (1 = all)."
  (unless *diff-snap* (setf *diff-snap* (foreign-alloc :uint8 :count +substate-bytes+)))
  (incf (getf *diff-stats* :txs))
  (unless (zerop (mod (getf *diff-stats* :txs) *diff-every*))
    (return-from diff-run-tiers (run-frame state code)))
  (incf (getf *diff-stats* :checked))
  (let ((jsnap (mem-ref *tx-arena-root* :uint64 0))
        (esnap (fill-pointer *obs-events*)) (fsnap *obs-frame-next*))
    (dotimes (i +substate-bytes+) (setf (mem-aref *diff-snap* :uint8 i) (mem-aref state :uint8 i)))
    (run-frame state code)                                   ; tier A: JIT
    (let ((ag (mem-ref state :uint64 8)) (ah (mem-ref state :uint8 128))
          (ar (mem-ref state :uint8 129)) (ao (%frame-output state))
          (am (%frame-memory state)) (aj (%journal-bytes *tx-arena-root* jsnap)) (af (ts-refund)))
      ;; as run-tx-frame! after a frame: tier B's memory must read zero where it expands
      (zero-bytes *memory-arena* 0 (mem-ref state :uint64 48))
      (free-frame-returndata state)
      (dotimes (i +substate-bytes+) (setf (mem-aref state :uint8 i) (mem-aref *diff-snap* :uint8 i)))
      (revert-journal-to *tx-arena-root* jsnap)              ; restore pre-state
      (setf (fill-pointer *obs-events*) esnap *obs-frame-next* fsnap)   ; drop tier A's logs, transfers, frames
      (let ((*force-interp* t)) (run-frame state code))     ; tier B: interp
      (let ((bg (mem-ref state :uint64 8)) (bh (mem-ref state :uint8 128))
            (br (mem-ref state :uint8 129)) (bo (%frame-output state))
            (bm (%frame-memory state)) (bj (%journal-bytes *tx-arena-root* jsnap)) (bf (ts-refund)))
        (unless (and (= ag bg) (= ah bh) (= ar br) (equalp ao bo) (equalp am bm) (equalp aj bj) (= af bf))
          (incf (getf *diff-stats* :divergences))
          (format *error-output*
                  "TIERDIFF block ~D addr ~X: JIT(gas=~D halt=~D rev=~D out=~D mem=~D jrnl=~D refund=~D) /= INTERP(gas=~D halt=~D rev=~D out=~D mem=~D jrnl=~D refund=~D) same out/mem/journal ~A/~A/~A code=~A~%"
                  *cur-block* *current-address* ag ah ar (length ao) (length am) (length aj) af
                  bg bh br (length bo) (length bm) (length bj) bf
                  (equalp ao bo) (equalp am bm) (equalp aj bj) (code-tag code))
          (finish-output *error-output*))))))
