;;;; swank.lisp — a Swank server (SLIME's) in a long-running process, on 127.0.0.1 only.
;;;;
;;;; Standalone: it needs Swank loaded and nothing of the engine, so a process outside
;;;; bin/eita (an `sbcl --script` that loads Swank itself) serves its REPL with the same
;;;; code. bin/eita starts it from `replay`, `engine` and `repl` when EITA_SWANK_PORT is set
;;;; (src/cli.lisp); docs/hooks.md, "Developing hooks live from Emacs".

(defpackage #:eita-swank
  (:use #:cl)
  (:export #:serve #:stop))
(in-package #:eita-swank)

(defun serve (port)
  "Listen on 127.0.0.1:PORT and serve each connection on a thread of its own (Swank's
   `:spawn` style), returning PORT. An error on one connection (a failed accept, a
   connection that drops during authentication) is logged and the server goes on
   listening: Swank's own accept loop lets it escape its thread, and in a process with the
   debugger disabled an error that escapes a thread ends the process. The thread registers
   itself as Swank's does, so `stop` (swank:stop-server) closes the socket and ends it.
   Signals an error when the port cannot be bound (in use, or not permitted)."
  (swank::init-log-output)
  (let ((socket (let ((swank::*loopback-interface* "127.0.0.1")) (swank::socket-quest port nil))))
    (sb-thread:make-thread
     (lambda ()
       (swank::add-server socket port sb-thread:*current-thread*)
       (loop (handler-case (swank::accept-connections socket :spawn t)
               (error (e)
                 (unless (find socket swank::*servers* :key #'car) (return))   ; stopped
                 (format *error-output* "~&[swank] a connection failed (still listening): ~A~%" e)
                 (finish-output *error-output*)))))
     :name (format nil "Swank ~D" port))
    port))

(defun stop (port)
  "Close the server on PORT; its connections end with it."
  (swank:stop-server port))
