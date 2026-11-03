;;;; native/code-version.lisp — the version of the code a replay runs (see
;;;; docs/layered-snapshots.md).
;;;;
;;;; A persisted result is equal to what a later run would produce only if both ran the
;;;; same code. The version is a content hash, not a git hash (a deployed tree need not carry
;;;; .git), over everything that decides the results:
;;;;   - every Lisp source file of the loaded eita systems, and their .asd;
;;;;   - libeita and the emitJIT binary (as the run finds them: native/libraries.lisp);
;;;;   - ocicl.csv, the pinned versions of the Lisp libraries under the engine.
;;;; A docs-only change does not move it; any code change does, even one that leaves the
;;;; results unchanged. That is safe and cheap: a resume replays every block past R anyway,
;;;; and a shard of another version is rewritten instead of skipped, then compared with
;;;; what it replaced (`rewrites.sexp`). EITA_CODE_SALT is mixed in for tests only.
;;;;
;;;; The Lisp part is hashed while the sources are at hand: at the first CODE-VERSION call of
;;;; a process that loaded them, or, for the executable, when it is built
;;;; (FREEZE-LISP-MANIFEST!, before the image is saved).

(in-package #:eita.native)

(defvar *version* nil)
(defvar *manifest* nil)
(defvar *lisp-manifest* nil
  "((relative-path . sha256) …) of the Lisp sources (and .asd files, ocicl.csv), once known.")

(defun sha256-files (paths)
  "Alist path -> sha256 hex, by one sha256sum (Linux) or shasum -a 256 (macOS) call."
  (when paths
    (let* ((cmd (if (probe-file "/usr/bin/sha256sum") "/usr/bin/sha256sum" "shasum"))
           (args (if (string= cmd "shasum") (list* "-a" "256" paths) paths))
           (out (with-output-to-string (s)
                  (sb-ext:run-program cmd args :search t :output s :error nil))))
      (with-input-from-string (in out)
        (loop for line = (read-line in nil) while line
              for sp = (position #\Space line)
              when sp collect (cons (string-left-trim " *" (subseq line (1+ sp))) (subseq line 0 sp)))))))

(defun sha256-text (text)
  (let* ((cmd (if (probe-file "/usr/bin/sha256sum") "/usr/bin/sha256sum" "shasum"))
         (out (with-output-to-string (s)
                (with-input-from-string (in text)
                  (sb-ext:run-program cmd (if (string= cmd "shasum") '("-a" "256") '())
                                      :search t :input in :output s :error nil)))))
    (subseq out 0 (position #\Space out))))

(defun asdf-call (name &rest args)
  (apply (find-symbol name :asdf) args))

(defun lisp-source-files ()
  "The source files of every loaded system named eita or eita/…, their .asd, and ocicl.csv:
   absolute namestrings."
  (let ((files '()))
    (dolist (name (asdf-call "REGISTERED-SYSTEMS"))
      (when (and (or (string= name "eita") (eql 0 (search "eita/" name)))
                 (asdf-call "COMPONENT-LOADED-P" name))
        (let ((sys (asdf-call "FIND-SYSTEM" name)))
          (push (namestring (asdf-call "SYSTEM-SOURCE-FILE" sys)) files)
          (labels ((walk (c)
                     (if (typep c (find-symbol "PARENT-COMPONENT" :asdf))
                         (mapc #'walk (asdf-call "COMPONENT-CHILDREN" c))
                         (when (typep c (find-symbol "CL-SOURCE-FILE" :asdf))
                           (push (namestring (asdf-call "COMPONENT-PATHNAME" c)) files)))))
            (walk sys)))))
    (let ((csv (source-file "ocicl.csv")))
      (when (probe-file csv) (push csv files)))
    (remove-duplicates files :test #'string=)))

(defun freeze-lisp-manifest! ()
  "Hash the Lisp sources now (the executable's build, before the image is saved)."
  (let ((home (namestring (truename (source-file "")))))
    (setf *lisp-manifest*
          (mapcar (lambda (e) (cons (if (eql 0 (search home (car e))) (subseq (car e) (length home)) (car e))
                                    (cdr e)))
                  (sha256-files (lisp-source-files))))))

(defun code-version (&key home extra)
  "The 16-hex-digit version of the running code, computed once. HOME is the root native
   paths are shown relative to; EXTRA, the native artifacts (missing ones are skipped)."
  (or *version*
      (let* ((home (namestring (truename home)))
             (lisp (or *lisp-manifest* (freeze-lisp-manifest!)))
             (native (mapcar (lambda (p) (namestring (truename p)))
                             (remove-if-not #'probe-file (remove nil extra))))
             (sums (sha256-files native))
             (rel (lambda (p) (if (string= home p :end2 (min (length p) (length home)))
                                  (subseq p (length home)) p)))
             (lines (sort (append (mapcar (lambda (e) (format nil "~A ~A" (cdr e) (car e))) lisp)
                                  (mapcar (lambda (p) (format nil "~A ~A" (or (cdr (assoc p sums :test #'string=)) "missing")
                                                              (funcall rel p)))
                                          native))
                          #'string<))
             (salt (sb-ext:posix-getenv "EITA_CODE_SALT"))
             (text (format nil "~{~A~%~}~@[salt ~A~%~]" lines (and salt (plusp (length salt)) salt)))
             (h (sha256-text text)))
        (setf *manifest* text
              *version* (subseq h 0 16)))))

(defun code-version-manifest () *manifest*)
