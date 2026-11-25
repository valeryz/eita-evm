;;;; examples/history/backfill.lisp — fold a past range from the fact log, then follow the chain
;;;; with the same subscription: the past is read, not executed again.
;;;;
;;;;   (load "examples/hooks/gas-per-block.lisp")        ; any subscription: it subscribes
;;;;   (load "examples/history/backfill.lisp")
;;;;   (history.backfill:catch-up "factlog/" 24000000 "ethereum" :to :tip :blocks "blocks/" :factlog "factlog/")
;;;;
;;;; `eita:backfill` hands the subscriptions the records of each logged block (the replay's
;;;; own, rebuilt from the facts; the block hash, parent hash, tx nonce and gas limit are not
;;;; in the log and are NIL), then the replay delivers the blocks after the log's last one: the
;;;; handlers see one run, with one :start. A fold gives the same state either way.

(defpackage #:history.backfill (:use #:cl) (:export #:catch-up #:committed))
(in-package #:history.backfill)

(defun committed (dir)
  "The fact log's newest block whose rows are all on disk."
  (with-open-file (in (merge-pathnames "committed" (uiop:ensure-directory-pathname dir)))
    (parse-integer (read-line in))))

(defun catch-up (dir from chain &rest replay-keys)
  "Fold blocks FROM..committed of the fact log at DIR into the subscriptions, then replay
   CHAIN from the next block with REPLAY-KEYS (eita:replay's)."
  (let* ((to (committed dir)) (n (eita:backfill dir from to)))
    (format t "~&backfill: blocks ~D..~D (~D) from ~A~%" from to n dir)
    (apply #'eita:replay chain (1+ to) replay-keys)))
