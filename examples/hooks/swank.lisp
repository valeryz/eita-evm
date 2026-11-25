;;;; examples/hooks/swank.lisp — a Swank (SLIME) or Slynk (SLY) server in this process, for
;;;; developing hooks live from Emacs (docs/hooks.md). It listens on 127.0.0.1 only.
;;;;
;;;;   SWANK_LOADER=/path/to/slime/swank-loader.lisp        SLIME's, the version your Emacs runs
;;;;   SLYNK_LOADER=/path/to/sly/slynk/slynk-loader.lisp    or SLY's
;;;;   EITA_SWANK_PORT=4005                                 the port (default 4005)
;;;;
;;;;   bin/eita repl --load examples/hooks/swank.lisp
;;;;   or, in a hooks file given to `bin/eita replay --observer`: (load "examples/hooks/swank.lisp")

(let* ((port (parse-integer (or (uiop:getenv "EITA_SWANK_PORT") "4005")))
       (swank (uiop:getenv "SWANK_LOADER"))
       (slynk (uiop:getenv "SLYNK_LOADER"))
       (server (cond (swank (load swank) (uiop:symbol-call :swank-loader :init) :swank)
                     (slynk (load slynk) (uiop:symbol-call :slynk-loader :init) :slynk)
                     (t (error "swank.lisp: set SWANK_LOADER (SLIME) or SLYNK_LOADER (SLY)")))))
  (setf (symbol-value (find-symbol "*LOOPBACK-INTERFACE*" server)) "127.0.0.1")
  (uiop:symbol-call server :create-server :port port :dont-close t)
  (format t "~&~(~A~) on 127.0.0.1:~D~%" server port))
