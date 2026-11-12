;;;; recovery.lisp — the recovery decisions over the durable artifacts (P0, rev. 2 §2.4).
;;;;
;;;; One owner for what used to be split between arc-follow.sh (latest_anchor,
;;;; prune_dumps, the genesis guard) and state/anchors.lisp (prune-dumps!):
;;;;
;;;;   eita recovery resume <state-dir>   prints N | genesis | refuse
;;;;   eita recovery gc <state-dir>       deletes the GC set, prints it
;;;;   eita recovery peek <state-dir>     `resume` without the sync (observers)
;;;;
;;;; Also loaded by the replay (state/anchors.lisp) for the same GC rule. No libeita, no
;;;; replay code: it starts in milliseconds and reads only anchors.sexp and the directory.
;;;;
;;;; The decisions are pure functions of a VIEW of the durable state, so the Lean model
;;;; (P1, lean/Evm/Persist/Recovery.lean; layered files: lean/Evm/Persist/Layered.lean,
;;;; Part D) can state and prove them over the same inputs:
;;;;   anchors : list of (block ok hash-or-nil)      from anchors.sexp (torn lines skipped)
;;;;   files   : list of (component . status)        status :sealed | :torn | :corrupt
;;;;   points  : list of (block . components)        what a resume from the block loads
;;;; A component is a base snapshot snap-B/ — (:base B) — or a delta layer layer-P-N/ —
;;;; (:layer P N) (docs/layered-snapshots.md): :sealed when its manifest exists and every
;;;; file has its recorded size (snapshot.lisp), :torn otherwise, :corrupt once a resume
;;;; refused it (renamed *.corrupt/). The points: every anchor's composition (its hash
;;;; field), every sealed base by itself, and every sealed layer with its chain down to a
;;;; base (`resolve`). The Part 1 view ("dumps") is one (block . status) per point:
;;;; :sealed when all its components are.


(in-package #:eita.state.recovery)

;;; --- Pure decisions -----------------------------------------------------------
;;; Each function mirrors the Lean definition named in its docstring, clause for clause;
;;; `tests/recovery-vectors.lisp` checks them against `lake exe recoveryVectors`.

(defun verified-blocks (anchors)
  "Lean `verified`."
  (loop for (b ok) in anchors when ok collect b))

(defun usable-p (b dumps)
  "Lean `usable`: block B has a sealed dump."
  (and (member (cons b :sealed) dumps :test #'equal) t))

(defun resume-point (anchors dumps)
  "Lean `resumePoint` (I1): the highest verified block with a sealed dump — or :genesis
   when no block has ever been verified, or :refuse when verified blocks exist but none
   has a usable dump (I2: going behind them needs the operator). Proved:
   resume_sound, resume_max, resume_genesis_iff, resume_mono."
  (let* ((ver (verified-blocks anchors))
         (cands (remove-if-not (lambda (b) (usable-p b dumps)) ver)))
    (cond (cands (reduce #'max cands))
          ((null ver) :genesis)
          (t :refuse))))

(defun sealed-blocks (dumps)
  "Lean `sealedBlocks`."
  (loop for (b . st) in dumps when (eq st :sealed) collect b))

(defun keep-verified (anchors dumps)
  "Lean `keepVerified`: the two highest verified sealed dumps."
  (let ((ver (verified-blocks anchors)))
    (let ((l (sort (remove-if-not (lambda (b) (member b ver)) (sealed-blocks dumps)) #'>)))
      (subseq l 0 (min 2 (length l))))))

(defun keep-above (anchors dumps)
  "Lean `keepAbove`: up to two unverified sealed dumps above the highest kept one."
  (let* ((ver (verified-blocks anchors))
         (top (first (keep-verified anchors dumps)))
         (l (sort (remove-if-not (lambda (b) (and (not (member b ver)) (or (null top) (< top b))))
                                 (sealed-blocks dumps))
                  #'>)))
    (subseq l 0 (min 2 (length l)))))

(defun gc-set (anchors dumps)
  "Lean `gcSet` (I2): every non-corrupt dump outside keepVerified ++ keepAbove; :corrupt
   ones are kept for inspection. Proved: resume_not_gc, gc_preserves_resume, gc_bounded."
  (let ((keep (append (keep-verified anchors dumps) (keep-above anchors dumps))))
    (sort (loop for (b . st) in dumps
                when (and (not (eq st :corrupt)) (not (member b keep))) collect b)
          #'<)))

;;; Layered files (Lean Part D, Evm.Persist.Layered).

(defun point-status (files comps)
  "Lean `pointStatus`: :sealed iff the point has components and all are sealed."
  (if (and comps (every (lambda (c) (member (cons c :sealed) files :test #'equal)) comps))
      :sealed
      :torn))

(defun dumps-of (files points)
  "Lean `dumpsOf`: the Part 1 view, one (block . status) per point."
  (loop for (b . comps) in points collect (cons b (point-status files comps))))

(defun keep-files (anchors files points)
  "Lean `keepFiles`: every component of every point at a kept block."
  (let* ((dumps (dumps-of files points))
         (keep (append (keep-verified anchors dumps) (keep-above anchors dumps))))
    (loop for (b . comps) in points when (member b keep) append comps)))

(defun gc-files (anchors files points)
  "Lean `gcFiles`: the non-corrupt files no kept point names. Proved:
   gcFiles_preserves_resume (the resume point does not move)."
  (let ((keep (keep-files anchors files points)))
    (loop for (c . st) in files
          when (and (not (eq st :corrupt)) (not (member c keep :test #'equal))) collect c)))

;;; --- Reading the durable state ------------------------------------------------

(defun state-file (dir name) (merge-pathnames name (pathname dir)))

(defun read-anchors (dir)
  (let ((path (state-file dir "anchors.sexp")))
    (when (probe-file path)
      (with-open-file (a path)
        (loop for line = (read-line a nil nil) while line
              for form = (ignore-errors (let ((*read-eval* nil)) (read-from-string line)))
              when (and (consp form) (integerp (first form)) (>= (length form) 4))
                collect (list (first form) (eq (fourth form) t)
                              (and (stringp (fifth form)) (fifth form))))))))

(defun component-of-dir (name)
  "(:base B) for snap-B, (:layer P N) for layer-P-N, else NIL; and whether it is .corrupt."
  (flet ((num (start end) (ignore-errors (parse-integer name :start start :end end))))
    (let ((corrupt (and (search ".corrupt" name) t))
          (end (or (search ".corrupt" name) (length name))))
      (values
       (cond ((and (> end 5) (string= "snap-" name :end2 5))
              (let ((b (num 5 end))) (and b (list :base b))))
             ((and (> end 6) (string= "layer-" name :end2 6))
              (let* ((dash (position #\- name :start 6 :end end))
                     (p (and dash (num 6 dash))) (n (and dash (num (1+ dash) end))))
                (and p n (list :layer p n)))))
       corrupt))))

(defun read-files (dir)
  "The view's files: base snapshots snap-B/ and layers layer-P-N/, each :sealed, :torn or
   :corrupt."
  (loop for p in (directory (merge-pathnames "*/" (pathname dir)))
        for name = (car (last (pathname-directory p)))
        for (comp corrupt) = (multiple-value-list (component-of-dir name))
        when comp collect (cons comp (cond (corrupt :corrupt)
                                           ((eita.state.snapshot:snap-sealed-p p) :sealed)
                                           (t :torn)))))

(defun strip-hash (c) (if (eq (first c) :base) (list :base (second c)) (list :layer (second c) (third c))))

(defun verified-base-p (anchors b files)
  "A sealed snap-B whose own root check passed (an anchor at B naming the base alone)."
  (and (member (cons (list :base b) :sealed) files :test #'equal)
       (some (lambda (a)
               (and (eql (first a) b) (second a)
                    (let ((c (eita.state.snapshot:parse-composition (third a) b)))
                      (and (= (length c) 1) (eq (first (first c)) :base)))))
             anchors)))

(defun resolve (anchors files n)
  "The chain a resume from the sealed layer ending at N loads: that layer (the widest one
   ending there), then down to a verified base, through the widest layer ending at each
   parent. Unverified bases are used only where no layer continues the chain. May name a
   missing component (the point is then :torn)."
  (labels ((layers-ending (b)
             (sort (loop for (c . st) in files
                         when (and (eq st :sealed) (eq (first c) :layer) (= (third c) b)) collect c)
                   #'< :key #'second))
           (down (b acc depth)
             (cond ((> depth 100000) (cons (list :base b) acc))   ; a cycle cannot occur; bound anyway
                   ((verified-base-p anchors b files) (cons (list :base b) acc))
                   ((layers-ending b) (let ((l (first (layers-ending b)))) (down (second l) (cons l acc) (1+ depth))))
                   (t (cons (list :base b) acc)))))
    (let ((l (first (layers-ending n))))
      (and l (down (second l) (list l) 0)))))

(defun read-points (anchors files)
  "One point per block: the first sealed of its candidate compositions — its anchors'
   (passed checks first, the fewest components first: a compacted base before the stack it
   replaced), the base snap at the block, the chain of the widest layer ending there — else
   the first of them. (One per block keeps `keepVerified` two distinct blocks.)"
  (let ((cands (make-hash-table)))
    (flet ((add (b comps) (setf (gethash b cands) (append (gethash b cands) (list comps)))))
      (loop for (b nil comps) in (stable-sort
                                  (loop for (b ok hash) in anchors
                                        collect (list b ok (mapcar #'strip-hash (eita.state.snapshot:parse-composition hash b))))
                                  (lambda (x y) (or (and (second x) (not (second y)))
                                                    (and (eq (second x) (second y))
                                                         (< (length (third x)) (length (third y)))))))
            do (add b comps))
      (loop for (c . st) in files
            when (and (eq st :sealed) (eq (first c) :base)) do (add (second c) (list c)))
      (loop for (c . st) in files
            when (and (eq st :sealed) (eq (first c) :layer))
              do (add (third c) (resolve anchors files (third c)))))
    (sort (loop for b being the hash-keys of cands using (hash-value cs)
                collect (cons b (or (find-if (lambda (c) (eq (point-status files c) :sealed)) cs) (first cs))))
          #'< :key #'car)))

(defun read-view (dir)
  "(values anchors dumps files points): the Part 1 view and the layered files under it."
  (let* ((anchors (read-anchors dir)) (files (read-files dir)) (points (read-points anchors files)))
    (values anchors (dumps-of files points) files points)))

;;; --- Effects ------------------------------------------------------------------

(defun fsync-path (path)
  (let ((fd (ignore-errors (sb-posix:open (namestring path) sb-posix:o-rdonly))))
    (when fd
      (unwind-protect (ignore-errors (sb-posix:fsync fd)) (sb-posix:close fd)))))

(defun sync-view (dir)
  "Make the view durable before deciding on it. The decisions are proved over the durable
   state (Lean `resume_ge`), but they read the live one: a verdict appended by a process
   killed before its fsync is readable and not yet durable. Acting on it (resuming from
   it, or GC'ing older dumps because of it) and then losing it to a power loss would move
   R backwards and could GC the dump R falls back to. Found by the fault-injection twin
   (the fault-injection twin, seed 10: R 2600 -> 0)."
  (fsync-path (state-file dir "anchors.sexp"))
  (fsync-path (pathname dir)))

(defun run-resume (dir &key (sync t))
  (when sync (sync-view dir))
  (multiple-value-bind (anchors dumps) (read-view dir)
    (let ((r (resume-point anchors dumps)))
      (format t "~(~A~)~%" r)
      r)))

(defun component-name (c)
  (if (eq (first c) :base) (format nil "snap-~D" (second c)) (format nil "layer-~D-~D" (second c) (third c))))

(defun run-gc (dir &key pinned)
  "Delete `gc-files` (directories are removed with rm -rf; a symlinked base loses only
   its link), except PINNED components: the running replay's own stack, which may hold
   layers no resume point names yet (one being replaced by its rewrite after a restart,
   say). Deleting less never moves the resume point (Lean `gcFiles_preserves_resume`
   holds for any subset). Prints and returns their names."
  (sync-view dir)
  (multiple-value-bind (anchors dumps files points) (read-view dir) ; @veil run-gc/scan
    (declare (ignore dumps))
    (let ((gone (set-difference (gc-files anchors files points) pinned :test #'equal))) ; @veil run-gc/victims
      (dolist (c gone)
        (let ((sp (eita.state.snapshot:component-path dir c)))
          (when (probe-file sp)
            (sb-ext:run-program "rm" (list "-rf" (string-right-trim "/" (namestring sp))) :search t)))) ; @veil run-gc/rm
      (format t "~{~A~^ ~}~%" (mapcar #'component-name gone))
      (mapcar #'component-name gone))))
