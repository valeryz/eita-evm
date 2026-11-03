;;;; evm/observe.lisp — the observation seam (observers), and the engine's code version.

(in-package #:eita.evm)

;;; --- Observation seam ------------------------------------------------------------------
;;; What execution did, for whoever wants to record it (a data writer, a fold, a debugger),
;;; without any say in what it does. *OBSERVER* is NIL by default: every hook site then costs
;;; one special-variable test, nothing is captured, and results are identical either way
;;; (observers see, never steer). An observer is a MAKE-OBSERVER, installed in *OBSERVER*
;;; before a run (`EITA_OBSERVER` names a Lisp file that does it; replay-run loads it):
;;;   attach ()              once per run, before the verifier: attach its subscribers to the
;;;                          event stream (below), which delivers block begin (:block-begin
;;;                          n), block end (:commit n …), layer points (:checkpoint n sem),
;;;                          reorgs (:rollback n) and the end of the run (:finalize)
;;;   start (start)          a full-state run starts at START (its resume point is known)
;;;   block (blk fork-ord)   a block's header, as it executes (before its pre-block work)
;;;   tx-end (block tx success)  a tx ended — user, system or a chain's own; during the call
;;;                          its touched-state summary is readable: do-account-changes,
;;;                          do-storage-changes, do-call-frames (when *observe-calls*), and
;;;                          iff SUCCESS do-tx-events (committed transfers and logs)
;;;   tx-result (n idx tx gas-used status egp)  a block's tx as the driver settled it
;;; The summary is NET PER TX, derived from the fault seam: every account / slot access is
;;; preceded by fault-account! / fault-slot!, so the first touch of a key within a tx
;;; snapshots its pre-image (after the fault hook: the authoritative loaded value) and at tx
;;; end every touched key whose value differs is a change; writes inside frames that later
;;; revert net out. Transfers and logs are EVENTS and follow the journal's frame scoping:
;;; pending in a per-tx vector, a frame marks it where it snapshots the journal and
;;; truncates to the mark where it reverts; the survivors are the committed ones.
(defstruct observer name attach start block tx-end tx-result)
(defmacro observe (hook &rest args)
  "Call the installed observer's HOOK with ARGS (evaluated only when there is one)."
  (let ((acc (intern (format nil "OBSERVER-~A" (symbol-name hook)) :eita.evm)) (o (gensym "O")) (f (gensym "F")))
    `(let ((,o *observer*)) (when ,o (let ((,f (,acc ,o))) (when ,f (funcall ,f ,@args)))))))
(defun load-observer! ()
  "EITA_OBSERVER: a Lisp file that installs an observer (once)."
  (let ((f (sb-ext:posix-getenv "EITA_OBSERVER")))
    (when (and f (plusp (length f)) (null *observer*)) (load f))))

;;; --- The engine's code version -------------------------------------------------------
;;; A content hash of the code that runs (native/code-version.lisp: the Lisp sources,
;;; libeita, the emitJIT daemon): what persisted state and observers record as its provenance.
(defvar *engine-code-version* nil)
(defun engine-code-version ()
  (or *engine-code-version*
      (setf *engine-code-version*
            (code-version :home (eita-home)
                          :extra (list (or (nonempty-env "EITA_LIB") (native-path "libeita" :error nil))
                                       *emit-jit*)))))
