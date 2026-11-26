;;;; cli.lisp — bin/eita, the one executable.
;;;;
;;;;   eita replay --chain C --from N [--to M | --to tip] [--blocks DIR] [--state DIR]
;;;;               [--checkpoint-every N] [--source FILE] [--observer FILE]
;;;;               [--resume N] [--genesis FILE] [--lazy | --full-state]
;;;;   eita engine --chain C --state DIR --jwt FILE [--engine-listen ADDR] [--genesis FILE]
;;;;               [--blocks DIR]               the Engine API for a consensus client
;;;;   eita fixtures PATH...                    BlockchainTests (a file or a flat directory)
;;;;   eita repl [--load FILE]...               a REPL in the EITA package
;;;;   eita check-root [--parent PID] SNAP-DIR [LAYER-DIR...] [THREADS]
;;;;   eita import-reth --state DIR [--threads N] FILE|-   a base from rust/reth-export's stream
;;;;   eita convert-snapshot --from DIR --to DIR [--tmp DIR] [--threads N] [--block N]
;;;;   eita recovery resume|peek|gc STATE-DIR
;;;;   eita version
;;;;
;;;; The heap is an SBCL runtime option, given before the command:
;;;;   eita --dynamic-space-size 16GB --end-runtime-options fixtures …
;;;; (the image's default is the heap it was built with: build.sh, EITA_HEAP_MB). Every
;;;; environment variable the engine reads (EITA_TRACE_*, …) works as with the
;;;; sources: the image reads them when it starts (native/startup.lisp).
;;;;
;;;; EITA_SWANK_PORT=N: `replay`, `engine` and `repl` serve a Swank REPL on 127.0.0.1:N
;;;; (src/swank.lisp; docs/hooks.md, "Developing hooks live from Emacs").

(in-package #:eita.cli)

(defparameter +usage+
  "usage: eita <command> [arguments]
  replay --chain ethereum|hoodi|devnet|arc|arc-testnet|arc-mainnet|base|opt|world|avalanche|avalanche-fuji --from N [--to M|tip]
         [--blocks DIR] [--state DIR] [--checkpoint-every N] [--source FILE]
         [--observer FILE] [--resume N] [--genesis FILE] [--lazy | --full-state]
  engine --chain ethereum|hoodi|devnet --state DIR --jwt FILE [--engine-listen 127.0.0.1:8551]
         [--genesis FILE] [--blocks DIR]
                                   an execution client for a consensus client (docs/run-a-node.md)
  fixtures PATH...                 run BlockchainTests (files or flat directories)
  repl [--load FILE]...            a REPL in the EITA package
  check-root [--parent PID] SNAP-DIR [LAYER-DIR...] [THREADS]
  import-reth --state DIR [--threads N] FILE|-
                                   a root-checked base from a reth node (rust/reth-export)
  convert-snapshot --from DIR --to DIR [--tmp DIR] [--threads N] [--block N]
                                   a verified v1 state as a root-checked v2 base and anchor
  recovery resume|peek|gc DIR      the resume point / garbage collection of a state directory
  version                          the engine version and code version
Swank: EITA_SWANK_PORT=4005 serves a REPL on 127.0.0.1:4005 to replay, engine and repl
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

;;; --- Swank: a live REPL into a running command (src/swank.lisp) ---------------------------
;;; Loopback only: from another host, forward the port (ssh -L). Started by the long-running
;;; commands (replay, engine, repl), never at build time and never by the short ones, which
;;; run beside a replay and would take its port. Swank's threads serve it; the replay never
;;; waits on a client. Never walk the world or the JIT cache from it while blocks run (they
;;; mutate on the replay thread without locks): ask a fold (docs/hooks.md).

(defvar *swank-default-port* nil
  "When EITA_SWANK_PORT is unset, for `replay` and `engine`: NIL (no Swank), or a function of
   the chain name (a string, or NIL) returning the port or NIL. A program built on this CLI
   sets its own default.")

;; Swank loads its contribs at run time from its source tree, which it records when it is
;; loaded: the build's. In the executable that is the ocicl/ beside bin/, wherever the tree
;; has moved since the build.
(eita.native:at-startup (swank-paths swank-loader::*source-directory* swank-loader::*fasl-directory* swank::*load-path*)
  (let ((src (and (eita.native:executable-dir)
                  (first (directory (merge-pathnames "../ocicl/slime-*/swank.asd" (eita.native:executable-dir)))))))
    (when src
      (let ((dir (make-pathname :name nil :type nil :defaults src)))
        (setf swank-loader::*source-directory* dir
              swank-loader::*fasl-directory* (asdf:apply-output-translations dir)
              swank::*load-path* (list (swank-loader::contrib-dir swank-loader::*fasl-directory*)
                                       (swank-loader::contrib-dir dir)))))))

(defun swank-port (chain default)
  "EITA_SWANK_PORT (0: none), else, with DEFAULT, *swank-default-port*'s for CHAIN."
  (let ((v (eita.native:nonempty-env "EITA_SWANK_PORT")))
    (cond (v (let ((p (or (ignore-errors (parse-integer v)) (usage-error "EITA_SWANK_PORT: not a number: ~A" v))))
               (and (plusp p) p)))
          ((and default *swank-default-port*) (funcall *swank-default-port* chain)))))

(defun start-swank (chain &key (default t))
  "Start the Swank server for a command on CHAIN: its port, or NIL (none configured, or it
   could not start: a replay does not die of a REPL)."
  (let ((port (swank-port chain default)))
    (when port
      (handler-case
          (let ((swank::*log-output* (make-broadcast-stream)))
            (eita-swank:serve port)
            (format t "~&[swank] live REPL on 127.0.0.1:~D (ssh -L ~D:localhost:~D …)~%" port port port)
            (finish-output)
            port)
        (error (e) (format *error-output* "~&[swank] not started on 127.0.0.1:~D: ~A~%" port e) nil)))))

(defmacro with-swank ((chain &key (default t)) &body body)
  "BODY with the Swank server of CHAIN's command running; closed when BODY returns."
  (let ((port (gensym "PORT")))
    `(let ((,port (start-swank ,chain :default ,default)))
       (unwind-protect (progn ,@body)
         (when ,port (ignore-errors (eita-swank:stop ,port)))))))

(defun option (args name)
  (second (member name args :test #'string=)))

(defun cmd-replay (args)
  (with-swank ((option args "--chain"))
    (replay-command args)))

(defun replay-command (args)
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

(defun cmd-engine (args)
  (with-swank ((option args "--chain"))
    (engine-command args)))

(defun engine-command (args)
  (multiple-value-bind (o rest)
      (parse-options args '(("--chain" :value) ("--state" :value) ("--jwt" :value)
                            ("--engine-listen" :value) ("--genesis" :value) ("--blocks" :value)))
    (when rest (usage-error "engine: unexpected ~{~A~^ ~}" rest))
    (dolist (k '(:chain :state :jwt))
      (unless (getf o k) (usage-error "engine: --~(~A~) is required" k)))
    (when (and (string-equal (getf o :chain) "devnet") (null (getf o :genesis)))
      (usage-error "engine: a devnet needs --genesis FILE (its genesis.json)"))
    (eita.engine:run (getf o :chain) :state (getf o :state) :jwt (getf o :jwt)
                     :listen (getf o :engine-listen)
                     :genesis (getf o :genesis) :blocks (getf o :blocks)))
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
    (with-swank (nil :default nil)
      (let ((*package* (find-package :eita)))
        (handler-bind ((serious-condition #'invoke-debugger))
          (dolist (f (getf o :load)) (load f))
          (sb-impl::toplevel-repl nil)))))
  t)

(defun cmd-check-root (args)
  (eita.state.root:main args))

(defun cmd-import-reth (args)
  (eita.state.root:import-main args))

(defun cmd-convert-snapshot (args)
  (multiple-value-bind (o rest)
      (parse-options args '(("--from" :value) ("--to" :value) ("--tmp" :value) ("--threads" :value) ("--block" :value)))
    (when rest (usage-error "convert-snapshot: unexpected ~{~A~^ ~}" rest))
    (unless (and (getf o :from) (getf o :to)) (usage-error "convert-snapshot: --from and --to are required"))
    (sb-ext:exit :code (if (eita.state.root:convert-snapshot
                            (getf o :from) (getf o :to) :tmp (getf o :tmp)
                            :threads (if (getf o :threads) (int-arg (getf o :threads) "--threads") (eita.state.snapshot:hardware-threads))
                            :block (and (getf o :block) (int-arg (getf o :block) "--block")))
                           0 1))))

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
  '(("replay" . cmd-replay) ("engine" . cmd-engine) ("fixtures" . cmd-fixtures) ("repl" . cmd-repl)
    ("check-root" . cmd-check-root) ("import-reth" . cmd-import-reth)
    ("convert-snapshot" . cmd-convert-snapshot) ("recovery" . cmd-recovery) ("version" . cmd-version)))

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
