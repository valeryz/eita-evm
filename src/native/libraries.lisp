;;;; native/libraries.lisp — where the native artifacts are, and opening them: the one place.
;;;;
;;;; The engine needs libeita (the Lean-emitted handlers, the precompiles, keccak),
;;;; libkeccak_batch (the trie's batched keccak), libz (block files), libeita_pq (Arc's PQ
;;;; precompile, opened on first use) and the Lean `emitJIT` daemon (the JIT tier). A library
;;;; is found, in order:
;;;;   EITA_LIB (libeita only: a full path, so a side-built libeita can be tried without
;;;;   overwriting the one a live replay holds mapped — overwriting it SIGBUSes that process)
;;;;   $EITA_LIB_DIR/<lib>
;;;;   next to the executable (bin/: build.sh copies the libraries there, so bin/ moves whole)
;;;;   <home>/c/<lib> (the build directory)
;;;; Resolution is at RUN time, never read time: nothing of the build machine's layout is
;;;; baked into a fasl or the image (native/startup.lisp reopens everything at startup).

(in-package #:eita.native)

(defun eita-lib-ext () #+darwin "dylib" #-darwin "so")

(defun nonempty-env (name)
  (let ((v (sb-ext:posix-getenv name))) (and v (plusp (length v)) v)))

(defun dir-of (path)
  (and path (make-pathname :name nil :type nil :version nil :defaults (pathname path))))

(defun executable-dir ()
  "The directory of the running executable (bin/), in the saved image; else NIL."
  (and *image-p* sb-ext:*runtime-pathname* (dir-of sb-ext:*runtime-pathname*)))

(defun eita-home ()
  "The install / repository root: EITA_HOME; in the saved image the directory above bin/;
   else the source directory of the ASDF system \"eita\"."
  (let ((env (nonempty-env "EITA_HOME")))
    (cond
      (env (truename (concatenate 'string (string-right-trim "/" env) "/")))
      ((executable-dir) (truename (merge-pathnames "../" (executable-dir))))
      ((and (find-package :asdf) (funcall (find-symbol "FIND-SYSTEM" :asdf) "eita" nil))
       (funcall (find-symbol "SYSTEM-SOURCE-DIRECTORY" :asdf) "eita"))
      (t *default-pathname-defaults*))))

(defun eita-file (rel) (namestring (merge-pathnames rel (eita-home))))

(defun home-relative (path)
  "PATH as given when it names a file (absolute, or relative to the working directory), else
   under the home: a chain's data (chains/<chain>/genesis.json) from any directory."
  (if (or (probe-file path) (eq :absolute (first (pathname-directory (pathname path)))))
      path
      (eita-file path)))

(defun source-file (rel)
  "REL under the ASDF system's source directory, at LOAD time: for data the engine reads
   while it loads (and an image carries from its build)."
  (namestring (funcall (find-symbol "SYSTEM-RELATIVE-PATHNAME" :asdf) "eita" rel)))

(defun native-candidates (file)
  (remove nil (list (let ((d (nonempty-env "EITA_LIB_DIR")))
                      (and d (concatenate 'string (string-right-trim "/" d) "/" file)))
                    (and (executable-dir) (namestring (merge-pathnames file (executable-dir))))
                    (eita-file (concatenate 'string "c/" file)))))

(defun native-path (stem &key (error t))
  "The path of the native library STEM (\"libeita\", …) by the search above."
  (let* ((file (format nil "~A.~A" stem (eita-lib-ext)))
         (cands (native-candidates file)))
    (or (find-if #'probe-file cands)
        (and error (error "~A not found (searched: ~{~A~^, ~}); build it (./build.sh) or set EITA_LIB_DIR"
                          file cands)))))

(defun open-native (stem)
  (load-foreign-library (native-path stem)))

(defun open-libeita ()
  (load-foreign-library (or (nonempty-env "EITA_LIB") (native-path "libeita"))))

(define-foreign-library libz
  (:darwin "libz.dylib")
  (t (:default "libz" "libz.so.1")))

;; zlib's gz* API (block files: input/decode.lisp) — a system library, found by name.
(at-startup native-libraries
  (open-libeita)
  (open-native "libkeccak_batch")
  (use-foreign-library libz))

(defun emit-jit-path ()
  "The Lean emit daemon (the JIT tier): EITA_EMITJIT, else next to the executable, else
   <home>/lean/.lake/build/bin/emitJIT. A deploy ships it with libeita (and its libmcl)."
  (or (nonempty-env "EITA_EMITJIT")
      (let ((p (and (executable-dir) (merge-pathnames "emitJIT" (executable-dir)))))
        (and p (probe-file p) (namestring p)))
      (eita-file "lean/.lake/build/bin/emitJIT")))
