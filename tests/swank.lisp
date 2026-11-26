;;;; tests/swank.lisp — the Swank server (src/swank.lisp) and how bin/eita starts it (src/cli.lisp):
;;;;   1. it listens on 127.0.0.1 only and answers an eval over Swank's wire protocol;
;;;;;   2. a connection that fails in accept (the client gone first: ECONNABORTED) is logged and
;;;;      the server goes on; stop closes it and its thread ends, also right after the start;
;;;;   3. EITA_SWANK_PORT starts it, 0 or unset (with no default) does not, and a port in use
;;;;      leaves the command running without a server.

(defpackage #:eita.test.swank (:use #:cl))
(in-package #:eita.test.swank)

(defvar *fails* 0)
(defun fail (fmt &rest args) (incf *fails*) (format t "  FAIL: ~?~%" fmt args))
(defmacro check (form fmt &rest args) `(unless ,form (fail ,fmt ,@args)))

(defun connect (port)
  (let ((s (make-instance 'sb-bsd-sockets:inet-socket :type :stream :protocol :tcp)))
    (sb-bsd-sockets:socket-connect s #(127 0 0 1) port)
    s))

(defun swank-eval (port)
  "One Swank request, (+ 1 2), over the wire protocol (6 hex digits of length); the reply."
  (let* ((s (connect port))
         (io (sb-bsd-sockets:socket-make-stream s :input t :output t :element-type 'character
                                                  :external-format :utf-8 :buffering :full))
         (msg "(:emacs-rex (cl:+ 1 2) \"COMMON-LISP-USER\" t 1)"))
    (unwind-protect
         (sb-sys:with-deadline (:seconds 10)
           (format io "~6,'0x~A" (length msg) msg) (finish-output io)
           (loop for len = (parse-integer (let ((h (make-string 6))) (read-sequence h io) h) :radix 16)
                 for body = (let ((b (make-string len))) (read-sequence b io) b)
                 when (search "(:return" body) return body))
      (close io :abort t))))

(defun server (port) (find port swank::*servers* :key #'second))
(defun server-thread (port)
  (loop repeat 200 for s = (server port) when s return (third s) do (sleep 0.01)))
(defun free-port () (+ 30000 (random 9000 (make-random-state t))))
(defun setenv (name value)
  (if value (sb-posix:setenv name value 1) (sb-posix:unsetenv name)))

;;; 1 and 2: the server itself, its first accept made to fail as the kernel's ECONNABORTED does
(let ((port (free-port)) (failed 0) (swank::*log-output* (make-broadcast-stream)))
  (sb-int:encapsulate 'swank/backend:accept-connection 'econnaborted
                      (lambda (f &rest args)
                        (if (plusp failed)
                            (apply f args)
                            (progn (incf failed)
                                   (close (apply f args) :abort t)
                                   (error 'sb-bsd-sockets:socket-error :errno 53 :syscall "accept")))))
  (unwind-protect
       (progn
         (eita-swank:serve port)
         (let ((thread (server-thread port)))
           (check thread "no Swank server on ~D" port)
           (when thread
             (let ((name (multiple-value-list (sb-bsd-sockets:socket-name (first (server port))))))
               (check (equalp (first name) #(127 0 0 1)) "bound to ~S, not 127.0.0.1" name))
             (sb-bsd-sockets:socket-close (connect port))           ; the connection that fails
             (sleep 0.5)
             (check (= failed 1) "the injected accept failure did not run (~D)" failed)
             (check (sb-thread:thread-alive-p thread) "the accept thread died of the failed connection")
             (let ((reply (swank-eval port)))
               (check (search "(:return (:ok 3) 1)" reply) "no (+ 1 2) after the failed accept: ~S" reply)
               (format t "  127.0.0.1:~D: after a failed accept, (+ 1 2) answers ~A~%" port reply))
             (eita-swank:stop port)
             (sb-thread:join-thread thread :default nil :timeout 5)
             (check (not (sb-thread:thread-alive-p thread)) "the accept thread outlived stop"))))
    (sb-int:unencapsulate 'swank/backend:accept-connection 'econnaborted)
    (when (server port) (ignore-errors (eita-swank:stop port)))))

;;; a stop right after the start (a command that fails at once) closes the server
(let ((port (free-port)) (swank::*log-output* (make-broadcast-stream)))
  (eita-swank:serve port)
  (let ((thread (third (server port))))
    (eita-swank:stop port)
    (check (and thread (not (server port))) "the server outlived a stop right after its start")
    (when thread (sb-thread:join-thread thread :default nil :timeout 5))
    (check (not (and thread (sb-thread:thread-alive-p thread))) "its thread outlived the stop")))

;;; 3: EITA_SWANK_PORT, as the commands read it
(let ((saved (sb-posix:getenv "EITA_SWANK_PORT")) (port (free-port))
      (*error-output* (make-broadcast-stream)) (*standard-output* (make-broadcast-stream)))
  (unwind-protect
       (let ((eita.cli:*swank-default-port* nil))
         (setenv "EITA_SWANK_PORT" nil)
         (check (null (eita.cli::start-swank "ethereum")) "a server with EITA_SWANK_PORT unset and no default")
         (setenv "EITA_SWANK_PORT" "0")
         (check (null (eita.cli::start-swank "ethereum")) "a server with EITA_SWANK_PORT=0")
         (setenv "EITA_SWANK_PORT" (princ-to-string port))
         (check (eql port (eita.cli::start-swank "ethereum")) "no server on EITA_SWANK_PORT=~D" port)
         (check (null (eita.cli::start-swank "ethereum")) "a second server on the port in use")
         (check (search "(:return (:ok 3) 1)" (swank-eval port)) "the first server stopped answering")
         (eita-swank:stop port)
         (setenv "EITA_SWANK_PORT" nil)
         (let ((eita.cli:*swank-default-port* (lambda (chain) (and (equal chain "ethereum") port))))
           (check (null (eita.cli::start-swank "ethereum" :default nil)) "the default used where it does not apply")
           (check (eql port (eita.cli::start-swank "ethereum")) "the default port not used")
           (eita-swank:stop port)))
    (setenv "EITA_SWANK_PORT" saved)
    (when (server port) (ignore-errors (eita-swank:stop port)))))

(format t "~&swank: ~:[FAIL~;127.0.0.1 only, a failed accept is survived, EITA_SWANK_PORT starts it~]~%" (zerop *fails*))
(eita.test:finish :code (if (zerop *fails*) 0 1))
