;;;; cli.lisp — bin/eita, the one executable.
;;;;
;;;;   eita replay --chain C --from N [--to M | --to tip] [--blocks DIR] [--state DIR]
;;;;               [--checkpoint-every N] [--source FILE] [--observer FILE]
;;;;               [--resume N] [--genesis FILE] [--lazy | --full-state]
;;;;   eita fixtures PATH...                    BlockchainTests (a file or a flat directory)
;;;;   eita repl [--load FILE]...               a REPL in the EITA package
;;;;   eita check-root [--parent PID] SNAP-DIR [LAYER-DIR...] [THREADS]
;;;;   eita recovery resume|peek|gc STATE-DIR
;;;;   eita version
;;;;
;;;; The heap is an SBCL runtime option, given before the command:
;;;;   eita --dynamic-space-size 16GB --end-runtime-options fixtures …
;;;; (the image's default is the heap it was built with: build.sh, EITA_HEAP_MB). Every
;;;; environment variable the engine reads (EITA_NO_JIT, EITA_TRACE_*, …) works as with the
;;;; sources: the image reads them when it starts (native/startup.lisp).

(in-package #:eita.cli)

(defparameter +usage+
  "usage: eita <command> [arguments]
  replay --chain ethereum|arc|arc-testnet|arc-mainnet|base|opt|world --from N [--to M|tip]
         [--blocks DIR] [--state DIR] [--checkpoint-every N] [--source FILE]
         [--observer FILE] [--resume N] [--genesis FILE] [--lazy | --full-state]
  fixtures PATH...                 run BlockchainTests (files or flat directories)
  repl [--load FILE]...            a REPL in the EITA package
  check-root [--parent PID] SNAP-DIR [LAYER-DIR...] [THREADS]
  recovery resume|peek|gc DIR      the resume point / garbage collection of a state directory
  version                          the engine version and code version
Heap: eita --dynamic-space-size 16GB --end-runtime-options <command> ...  (docs/quickstart.md)")

(define-condition usage-error (simple-error) ())

(defun usage-error (fmt &rest args)
  (error 'usage-error :format-control fmt :format-arguments args))

(defun parse-options (args spec)
  "ARGS against SPEC, a list of (\"--name\" :value | :flag). Returns (values plist rest):
   options as keywords (values strings, flags T), and the other arguments in order."
  (let ((opts '()) (rest '()))
    (loop while args
          do (let* ((a (pop args)) (s (assoc a spec :test #'string=)))
               (cond ((null s)
                      (when (and (> (length a) 2) (string= "--" a :end2 2))
                        (usage-error "unknown option ~A" a))
                      (push a rest))
                     ((eq (second s) :flag)
                      (setf (getf opts (intern (string-upcase (subseq a 2)) :keyword)) t))
                     (t (unless args (usage-error "~A needs a value" a))
                        (let ((k (intern (string-upcase (subseq a 2)) :keyword)))
                          (if (eq (third s) :many)
                              (setf (getf opts k) (append (getf opts k) (list (pop args))))
                              (setf (getf opts k) (pop args))))))))
    (values opts (nreverse rest))))

(defun int-arg (s name)
  (or (and s (ignore-errors (parse-integer s)))
      (usage-error "~A: not a number: ~A" name s)))

(defun cmd-replay (args)
  (multiple-value-bind (o rest)
      (parse-options args '(("--chain" :value) ("--from" :value) ("--to" :value) ("--blocks" :value)
                            ("--state" :value) ("--checkpoint-every" :value) ("--source" :value)
                            ("--observer" :value) ("--resume" :value) ("--genesis" :value)
                            ("--lazy" :flag) ("--full-state" :flag)))
    (when rest (usage-error "replay: unexpected ~{~A~^ ~}" rest))
    (unless (getf o :chain) (usage-error "replay: --chain is required"))
    (unless (or (getf o :from) (getf o :resume)) (usage-error "replay: --from is required"))
    (when (and (getf o :lazy) (getf o :full-state)) (usage-error "replay: --lazy or --full-state, not both"))
    (let ((to (getf o :to)))
      (apply #'eita:replay (getf o :chain) (if (getf o :from) (int-arg (getf o :from) "--from") 0)
             :to (cond ((null to) nil) ((string-equal to "tip") :tip) (t (int-arg to "--to")))
             :blocks (getf o :blocks) :source (getf o :source) :observer (getf o :observer)
             :state (getf o :state) :genesis (getf o :genesis)
             :checkpoint-every (and (getf o :checkpoint-every) (int-arg (getf o :checkpoint-every) "--checkpoint-every"))
             :resume (and (getf o :resume) (int-arg (getf o :resume) "--resume"))
             (cond ((getf o :lazy) '(:full-state nil))
                   ((getf o :full-state) '(:full-state t))))))
  t)

(defun cmd-fixtures (args)
  (when (null args) (usage-error "fixtures: give a BlockchainTests file or directory"))
  (eita.fixtures:main args)
  t)

(defun cmd-repl (args)
  (multiple-value-bind (o rest) (parse-options args '(("--load" :value :many)))
    (when rest (usage-error "repl: unexpected ~{~A~^ ~}" rest))
    (format t "~&;; Eita ~A — (in-package :eita) is current: (new-world), (transact …), (call …); docs/quickstart.md~%"
            (eita-version))
    (sb-ext:enable-debugger)
    (let ((*package* (find-package :eita)))
      (handler-bind ((serious-condition #'invoke-debugger))
        (dolist (f (getf o :load)) (load f))
        (sb-impl::toplevel-repl nil))))
  t)

(defun cmd-check-root (args)
  (eita.state.root:main args))

(defun cmd-recovery (args)
  (destructuring-bind (&optional what dir &rest more) args
    (unless (and dir (null more) (member what '("resume" "peek" "gc") :test #'string=))
      (usage-error "recovery resume|peek|gc DIR"))
    (cond ((string= what "resume") (eita.state.recovery:run-resume dir))
          ((string= what "peek") (eita.state.recovery:run-resume dir :sync nil))
          (t (eita.state.recovery:run-gc dir)))
    t))

(defparameter *eita-version*
  (funcall (find-symbol "COMPONENT-VERSION" :asdf) (funcall (find-symbol "FIND-SYSTEM" :asdf) "eita"))
  "The version of the eita system this was built from (eita.asd).")

(defun eita-version () *eita-version*)

(defun cmd-version (args)
  (declare (ignore args))
  (format t "eita ~A~%code version ~A~%" (eita-version) (eita.evm:engine-code-version))
  t)

(defparameter +commands+
  '(("replay" . cmd-replay) ("fixtures" . cmd-fixtures) ("repl" . cmd-repl)
    ("check-root" . cmd-check-root) ("recovery" . cmd-recovery) ("version" . cmd-version)))

(defun register-command (name function)
  "Add the subcommand NAME, run as (FUNCTION args) after the engine started: a program that
   builds its own executable on this CLI (with more ASDF systems) adds its commands here."
  (setf +commands+ (cons (cons name function) (remove name +commands+ :key #'car :test #'string=)))
  name)

(defun main ()
  "The executable's entry point: start the engine (native/startup.lisp), run a command."
  (let* ((args (let ((a (uiop:command-line-arguments)))   ; the runtime leaves its end marker
                 (if (equal (first a) "--end-runtime-options") (rest a) a)))
         (cmd (assoc (first args) +commands+ :test #'equal)))
    (cond ((member (first args) '("help" "-h" "--help") :test #'equal)
           (format t "~A~%" +usage+)
           t)
          ((null cmd)
           (format *error-output* "~@[eita: unknown command ~A~%~]~A~%" (first args) +usage+)
           (finish-output *error-output*)
           (sb-ext:exit :code 2 :abort t))
          (t
           (eita.native:run-startup!)
           (handler-case (funcall (cdr cmd) (rest args))
             (usage-error (e)
               (format *error-output* "eita: ~A~%~A~%" e +usage+)
               (finish-output *error-output*)
               (sb-ext:exit :code 2 :abort t)))))))
