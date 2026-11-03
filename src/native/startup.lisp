;;;; native/startup.lisp — what a saved image redoes when it starts.
;;;;
;;;; Loading the engine opens shared libraries, allocates foreign buffers, caches pointers into
;;;; libeita and reads the environment (EITA_NO_JIT, EITA_TRACE_*, …) into variables. A process
;;;; that loads the sources does all of that as it starts. The executable (bin/eita) was
;;;; loaded when it was BUILT: when it starts, its libraries are closed, its foreign memory is
;;;; gone and the environment is the run's, not the build's. So every such load-time
;;;; initialization is declared here, in one of two forms, and is redone, in load order, by
;;;; RUN-STARTUP! when the image starts (eita.cli:main):
;;;;   (defstartup *x* init "doc")   a DEFPARAMETER whose INIT is evaluated again at startup
;;;;   (at-startup name form…)       forms run at load and again at startup ((name var…):
;;;;                                 the forms set the variables VAR)
;;;; Loaded from source, each is evaluated once, at load, exactly as a DEFPARAMETER or a
;;;; top-level form would be.

(in-package #:eita.native)

(defvar *startup* '()
  "The startup entries, newest first: (key . thunk), KEY the variable or action name.")

(defvar *image-p* nil
  "True in the saved executable (set by RUN-STARTUP!): native artifacts are searched next to
   it before the build tree.")

(defun register-startup (key thunk)
  "Add (or, on a reload, replace in place) the startup entry KEY."
  (let ((e (assoc key *startup*)))
    (if e (setf (cdr e) thunk) (push (cons key thunk) *startup*)))
  key)

(defmacro defstartup (name init &optional doc)
  "DEFPARAMETER NAME INIT, re-initialized when a saved image starts."
  `(progn (defparameter ,name ,init ,@(when doc (list doc)))
          (register-startup ',name (lambda () (setf ,name ,init)))
          ',name))

(defvar *startup-set* '()
  "Variables an AT-STARTUP action sets (outside DEFSTARTUP: another library's).")

(defmacro at-startup (name &body body)
  "Run BODY now, and again when a saved image starts. NAME is a symbol, or (NAME VAR…)
   when BODY sets the variables VAR (re-initialized at startup, like a DEFSTARTUP's)."
  (destructuring-bind (key &rest vars) (if (listp name) name (list name))
    `(progn (register-startup ',key (lambda () ,@body))
            (setf *startup-set* (union *startup-set* ',vars))
            ,@body)))

(defun run-startup! ()
  "Redo every load-time initialization, in load order (the image has just started)."
  (setf *image-p* t)
  (dolist (e (reverse *startup*))
    (funcall (cdr e))))

;; The image's random state is the build's: every start would draw the same sequence (the
;; WebSocket key and masks, node/acquire/ws-rpc.lisp). Seeded from the OS at each start.
(at-startup random-state
  (setf *random-state* (make-random-state t)))

;;; --- The save-time check: nothing of the build process survives in a variable -----------
;;; A value tied to the process that computed it — a SAP or alien value (a foreign pointer),
;;; an open stream or socket, a thread or child process, or an integer that is an address in
;;; a shared library or the malloc heap (on Linux, from /proc/self/maps) — is wrong in every
;;; other process: libraries map elsewhere (ASLR), foreign memory and descriptors are gone.
;;; The 2026-11-02 Arc deploy died on one (the factlog writer's syncfs address, an integer
;;; computed at load). FORGET-SHARED-OBJECTS! refuses to let the image be saved while any
;;; variable not re-initialized at startup (DEFSTARTUP) holds such a value, anywhere in its
;;; conses, vectors, hash tables or structures.

(defun process-address-ranges ()
  "(lo . hi) of every mapping of a shared object and of the brk heap, on Linux; else NIL."
  (with-open-file (in "/proc/self/maps" :if-does-not-exist nil)
    (when in
      (loop for line = (read-line in nil) while line
            for dash = (position #\- line)
            for sp = (position #\Space line)
            when (and dash sp (or (search ".so" line) (search "[heap]" line)))
              collect (cons (parse-integer line :end dash :radix 16)
                            (parse-integer line :start (1+ dash) :end sp :radix 16))))))

(defun process-bound-p (x ranges)
  "The kind of process-bound value X is, or NIL."
  (typecase x
    (sb-sys:system-area-pointer (and (/= 0 (sb-sys:sap-int x)) "a foreign pointer (SAP)"))   ; NULL is NULL anywhere
    (sb-alien-internals:alien-value "an alien value")
    ;; fds 0-2 are the standard streams, which SBCL and UIOP re-create at startup
    (stream (and (typep x 'sb-sys:fd-stream) (> (sb-sys:fd-stream-fd x) 2) "an open fd-stream"))
    (sb-thread:thread "a thread")
    (sb-impl::process "a child process")
    (integer (and (find-if (lambda (r) (<= (car r) x (cdr r))) ranges) "an address in a mapped library or the heap"))
    (t (and (find-package :sb-bsd-sockets)
            (typep x (find-symbol "SOCKET" :sb-bsd-sockets))
            "a socket"))))

(defun image-state-violations ()
  "(symbol kind) of every bound variable outside SBCL whose value reaches a process-bound
   value, the DEFSTARTUP variables excepted."
  (let ((ranges (process-address-ranges))
        (seen (make-hash-table :test 'eq))
        (out '()))
    (labels ((walk (x)
               (cond ((process-bound-p x ranges))
                     ((or (typep x '(or number character symbol function package pathname string stream))
                          (gethash x seen))
                      nil)
                     (t (setf (gethash x seen) t)
                        (typecase x
                          (cons (loop for c = x then (cdr c)
                                      thereis (walk (car c))
                                      while (consp (cdr c))
                                      finally (return (walk (cdr c)))))
                          ((array t) (loop for i below (array-total-size x) thereis (walk (row-major-aref x i))))
                          (hash-table (block nil
                                        (maphash (lambda (k v) (let ((r (or (walk k) (walk v)))) (when r (return r)))) x)))
                          (structure-object
                           (let ((dd (sb-kernel:find-defstruct-description (type-of x) nil)))
                             (and dd (some (lambda (dsd)
                                             (and (eq (sb-kernel:dsd-raw-type dsd) t)
                                                  (walk (sb-kernel:%instance-ref x (sb-kernel:dsd-index dsd)))))
                                           (sb-kernel:dd-slots dd)))))))))
             (walk-value (x) (or (process-bound-p x ranges) (walk x))))
      (dolist (p (list-all-packages))
        (unless (or (member (package-name p) '("COMMON-LISP" "KEYWORD") :test #'string=)
                    (eql 0 (search "SB-" (package-name p))))
          (do-symbols (s p)
            (when (and (eq (symbol-package s) p) (boundp s)
                       (not (assoc s *startup*)) (not (member s *startup-set*)))
              (let ((kind (walk-value (symbol-value s))))
                (when kind (push (list s kind) out))))))))
    out))

(defun forget-shared-objects! ()
  "Before the image is saved: refuse when a variable carries a value of this (the build)
   process (IMAGE-STATE-VIOLATIONS: declare it with DEFSTARTUP, or compute it on use); then
   the shared objects loaded so far are not reopened by the runtime at startup (their
   build-tree paths may not exist there): RUN-STARTUP! opens them from where the executable
   finds them."
  (let ((bad (image-state-violations)))
    (when bad
      (error "not saving the image: these variables hold values of the build process, ~
              stale in every other one (make them DEFSTARTUP, native/startup.lisp):~%~
              ~:{  ~S: ~A~%~}" bad)))
  (dolist (obj sb-alien::*shared-objects*)
    (setf (sb-alien::shared-object-dont-save obj) t)))
