;;;; state/import.lisp — `eita import-reth`: a base snapshot from a reth node's state.
;;;;
;;;;   eita-reth-export --datadir DIR --chain-id N | eita import-reth --state STATE-DIR -
;;;;
;;;; rust/reth-export walks reth's hashed state tables and writes them as a stream of
;;;; version 2 records already in key order (its header comment gives the stream). Here the
;;;; records go through the version 2 writer, which checks S2, S4 and S5 and builds the
;;;; fences as they pass, into STATE-DIR/.tmp-snap-H/; every code is re-hashed. Then the
;;;; root gate, the honesty boundary of an import (docs/state-snapshot-format.md §10): the
;;;; state root is recomputed from the written records alone (`snapshot-root`, never reth's
;;;; trie tables or stored roots) and compared with the stateRoot of header H. On a match the
;;;; manifest gains `:root-checked t` and the directory is published as snap-H/; on a
;;;; mismatch it stays in .tmp-snap-H/ (quarantined: a replay deletes it at startup) and the
;;;; command exits 1.
;;;;
;;;; The address field of every account record is zero: reth's hashed tables do not hold
;;;; addresses. A record whose address is zero and whose hkey is not keccak(0x00…00) is an
;;;; address not yet known; the replay learns it at the account's first touch.

(in-package #:eita.state.root)

(defun read-exact (in buf n)
  (unless (= n (read-sequence buf in :end n))
    (error "import: the stream ends early (the exporter failed? see its output)"))
  buf)

(defun read-be (in buf n)
  (eita.state.snapshot:octets->int (read-exact in buf n) 0 n))

(defun mark-root-checked (dir)
  "Rewrite DIR's manifest with :root-checked t (the content hash, over the files, is unchanged)."
  (let* ((m (eita.state.snapshot:read-manifest dir))
         (ch (getf m :content-hash))
         (m (append (loop for (k v) on m by #'cddr unless (member k '(:content-hash :root-checked)) append (list k v))
                    (list :root-checked t :content-hash ch)))
         (path (merge-pathnames "MANIFEST.sexp" dir)))
    (with-open-file (f path :direction :output :if-exists :supersede)
      (let ((*print-pretty* nil) (*print-case* :downcase)) (prin1 m f) (terpri f))
      (finish-output f)
      (sb-posix:fsync (sb-sys:fd-stream-fd f)))))

(defun import-reth (state-dir in &key (threads (eita.state.snapshot:hardware-threads)))
  "Read the exporter's stream IN (octets) into a base under STATE-DIR and gate it on its
   root. Returns the published directory, or NIL on a root mismatch."
  (let ((b (make-array 128 :element-type '(unsigned-byte 8)))
        (state-dir (eita.state.snapshot::as-dir state-dir)))
    (unless (string= "EITARETH" (map 'string #'code-char (subseq (read-exact in b 8) 0 8)))
      (error "import: not an eita-reth-export stream"))
    (unless (= 1 (read-be in b 4)) (error "import: stream version ~D, this reads 1" (eita.state.snapshot:octets->int b 0 4)))
    (let* ((chain-id (read-be in b 8)) (block (read-be in b 8))
           (hash (format nil "0x~(~64,'0X~)" (read-be in b 32)))
           (root (format nil "0x~(~64,'0X~)" (read-be in b 32)))
           (expect (list (read-be in b 8) (read-be in b 8)))
           (provenance (let ((p (make-array (read-be in b 2) :element-type '(unsigned-byte 8))))
                         (sb-ext:octets-to-string (read-exact in p (length p)) :external-format :utf-8)))
           (tmp (eita.state.snapshot:snap-tmp-path state-dir block))
           (final (eita.state.snapshot:snap-path state-dir block))
           (t0 (get-internal-real-time)))
      (flet ((elapsed () (/ (- (get-internal-real-time) t0) internal-time-units-per-second)))
        (format t "~&import: chain ~D block ~D ~A, stateRoot ~A; about ~D accounts, ~D slots~%"
                chain-id block hash root (first expect) (second expect))
        (when (probe-file final) (error "import: ~A exists" final))
        (when (probe-file tmp) (sb-ext:run-program "rm" (list "-rf" (namestring tmp)) :search t))
        (let ((w (eita.state.snapshot:make-writer tmp chain-id block root :expect expect))
              (tag 0) (manifest nil))
          (sb-sys:with-pinned-objects (b)
            (loop (setf tag (read-be in b 1))
                  (case tag
                    (#.(char-code #\S) (read-exact in b 96) (eita.state.snapshot:writer-record w :storage (sb-sys:vector-sap b) 0))
                    (#.(char-code #\A) (read-exact in b 128) (eita.state.snapshot:writer-record w :accounts (sb-sys:vector-sap b) 0))
                    (t (return)))))
          (format t "~&import: records written at ~,1Fs~%" (elapsed)) (finish-output)
          (setf manifest
                (eita.state.snapshot:writer-finish
                 w (lambda ()
                     (when (= tag (char-code #\C))
                       (let* ((h (read-be in b 32))
                              (code (make-array (read-be in b 4) :element-type '(unsigned-byte 8))))
                         (read-exact in code (length code))
                         (unless (= h (eita.state.snapshot:octets->int (eita.mpt:%keccak code)))
                           (error "import: code ~(~64,'0X~) does not hash to its key" h))
                         (setf tag (read-be in b 1))
                         (cons h code))))
                 :provenance provenance))
          (unless (= tag (char-code #\E)) (error "import: unexpected record tag ~D" tag))
          (let ((counts (list :accounts (read-be in b 8) :slots (read-be in b 8) :codes (read-be in b 8))))
            (unless (equal counts (getf manifest :counts))
              (error "import: the exporter wrote ~S, the snapshot holds ~S" counts (getf manifest :counts))))
          (format t "~&import: ~S written in ~,1Fs; checking the root~%" (getf manifest :counts) (elapsed))
          (finish-output))
        (multiple-value-bind (got expected) (snapshot-root tmp :threads threads)
          (format t "~&CL trie root : ~A~%header root  : ~A~%" got expected)
          (cond ((and expected (string-equal got expected))
                 (mark-root-checked tmp)
                 (eita.state.snapshot:snap-publish state-dir block tmp)
                 (format t "MATCH: published ~A (root-checked) in ~,1Fs~%" final (elapsed))
                 final)
                (t (format t "MISMATCH: the import stays quarantined in ~A~%" tmp)
                   nil)))))))

(defun import-main (args)
  "eita import-reth --state DIR [--threads N] FILE|-"
  (let* ((p (position "--state" args :test #'string=)) (dir (and p (nth (1+ p) args)))
         (q (position "--threads" args :test #'string=)) (threads (and q (parse-integer (nth (1+ q) args))))
         (file (car (last args))))
    (unless (and dir (= (length args) (if q 5 3)) (or (string= file "-") (probe-file file)))
      (format t "usage: eita import-reth --state STATE-DIR [--threads N] FILE|-~%") (sb-ext:exit :code 2))
    (ensure-directories-exist (eita.state.snapshot::as-dir dir))
    (let ((ok (if (string= file "-")
                  (import-reth dir (sb-sys:make-fd-stream 0 :input t :element-type '(unsigned-byte 8) :buffering :full)
                               :threads (or threads (eita.state.snapshot:hardware-threads)))
                  (with-open-file (in file :element-type '(unsigned-byte 8))
                    (import-reth dir in :threads (or threads (eita.state.snapshot:hardware-threads)))))))
      (sb-ext:exit :code (if ok 0 1)))))
