;;;; tests/diff-tiers.lisp — the differential mode (EITA_DIFF_TIERS, interp.lisp diff-run-tiers)
;;;; must not diverge against itself.
;;;;
;;;; The differential runs a tx's top frame on tier A, restores the pre-state, runs it on tier B
;;;; and compares. With both tiers the bytecode interpreter, every comparison must agree; a
;;;; divergence is a hole in the restore, which would also show up as a false TIERDIFF (or a
;;;; wrong kept result) against the JIT. The restore missed two things (2026-11-06): tier A's
;;;; memory arena was left dirty, so tier B's memory expansion read tier A's bytes instead of
;;;; zeros, and tier A's logs and transfers stayed in the tx's event buffer (16 divergences and
;;;; 11 receipt mismatches in 30 mainnet blocks).
;;;;
;;;; Then the memory rule: tier A's final memory is made to differ from tier B's (byte 0 of every
;;;; top frame that has memory flipped after tier A). A frame both tiers end in an exceptional halt
;;;; (frame-status :halt: out of gas and the like, the frame's memory discarded) must NOT diverge
;;;; -- the JIT's per-chunk gas check legitimately leaves other bytes there than the interpreter
;;;; (203 such TIERDIFFs on the 30k bundle); every other flipped frame (RETURN, STOP, REVERT) must.
;;;; Run: (eita.test:run-all :only '("diff-tiers")).

(defpackage #:eita.test.diff-tiers (:use #:cl))
(in-package #:eita.test.diff-tiers)

(defparameter *ok* t)

(let ((root (eita.test::fixtures-dir)))
  (dolist (sub '("bcExample/" "bcStateTests/"))
    (let* ((dir (concatenate 'string root sub))
           (eita.evm::*force-interp* t)
           (eita.evm::*diff-tiers* t)
           (eita.evm::*diff-every* 1)
           (eita.evm::*diff-stats* (list :txs 0 :checked 0 :divergences 0))
           (out (with-output-to-string (*standard-output*)
                  (let ((*error-output* *standard-output*)) (eita.fixtures:main (list dir)))))
           (line (find-if (lambda (l) (eql 0 (search "summary:" l)))
                          (uiop:split-string out :separator '(#\Newline))))
           (st eita.evm::*diff-stats*)
           (pass (and line (search " fail=0 " line) (not (search "pass=0 " line))
                      (plusp (or (getf st :checked) (getf st :txs))) (zerop (getf st :divergences)))))
      (format t "  ~A: ~A; differential ~S~%" sub line st)
      (unless pass
        (setf *ok* nil)
        (dolist (l (uiop:split-string out :separator '(#\Newline)))
          (when (search "TIERDIFF" l)
            (format t "    ~A~%" (subseq l 0 (min 200 (length l))))))))))

;;; The memory rule: flip byte 0 of tier A's memory in every top frame (tier A is the first of
;;; diff-run-tiers' two top-level run-frame calls; nested frames' run-frame calls are left alone).
(defvar *depth* 0)
(defvar *top-calls* 0)
(defparameter *flipped* (list :halt 0 :other 0))
(sb-int:encapsulate 'eita.evm::run-frame 'flip-tier-a-memory
                    (lambda (f state code)
                      (prog1 (let ((*depth* (1+ *depth*))) (funcall f state code))
                        (when (and (= *depth* 0) (oddp (incf *top-calls*)))          ; tier A's top frame
                          (let ((p (cffi:mem-ref state :pointer 40)) (n (cffi:mem-ref state :uint64 48)))
                            (when (plusp n)
                              (setf (cffi:mem-aref p :uint8 0) (logxor #xff (cffi:mem-aref p :uint8 0)))
                              (incf (getf *flipped* (if (eq (eita.evm::frame-status state) :halt) :halt :other)))))))))
(unwind-protect
     (let* ((dir (concatenate 'string (eita.test::fixtures-dir) "bcStateTests/"))
            (eita.evm::*force-interp* t)
            (eita.evm::*diff-tiers* t)
            (eita.evm::*diff-every* 1)
            (eita.evm::*diff-stats* (list :txs 0 :checked 0 :divergences 0))
            (st (progn (with-output-to-string (*standard-output*)
                         (let ((*error-output* *standard-output*)) (eita.fixtures:main (list dir))))
                       eita.evm::*diff-stats*))
            (pass (and (plusp (getf *flipped* :halt)) (plusp (getf *flipped* :other))
                       (= (getf st :divergences) (getf *flipped* :other)))))
       (format t "  bcStateTests/, tier A's memory flipped in ~D exceptional-halt and ~D other top frames: ~D TIERDIFFs (want ~D) ~:[FAIL~;ok~]~%"
               (getf *flipped* :halt) (getf *flipped* :other) (getf st :divergences) (getf *flipped* :other) pass)
       (unless pass (setf *ok* nil)))
  (sb-int:unencapsulate 'eita.evm::run-frame 'flip-tier-a-memory))

(eita.test:finish :code (if *ok* 0 1))
