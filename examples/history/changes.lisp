;;;; examples/history/changes.lisp — a value's history: every change of a storage slot, or of an
;;;; account's balance, nonce or code, over a block range, with the block and tx of each.
;;;;
;;;;   (load "examples/history/changes.lisp")
;;;;   (history.changes:changes "factlog/" "0xC02a…6Cc2" 24000000 24538111 :slot 3)
;;;;   (history.changes:changes "factlog/" "0xd8dA…6045" 24000000 24538111 :kind :balance)
;;;;
;;;; Through the history index, like a lookup: only the shards whose filter may hold the key
;;;; are read, and in each only the key and value columns are decoded. tx is the tx's index
;;;; in its block, -1 for the system work before the txs, 10^9 for the work after them.

(defpackage #:history.changes (:use #:cl) (:export #:changes))
(in-package #:history.changes)

(defun changes (dir address from to &key slot (kind (if slot :storage :balance)))
  "Every change of ADDRESS's storage SLOT (KIND :storage) or of its :balance, :nonce or
   :code hash in blocks FROM..TO, in chain order: plists (:block :tx :pre :post)."
  (let ((addr (eita:addr address)))
    (if (eq kind :storage)
        (loop for (block tx pre post) in (eita-factlog:key-history dir :storage_diff (list addr slot) from to)
              collect (list :block block :tx tx :pre pre :post post))
        (let ((i (position kind '(:nonce :balance :code))))
          ;; an account row carries all three: keep the rows where this one moved
          (loop for (block tx pre post) in (eita-factlog:key-history dir :account_diff (list addr) from to)
                unless (= (nth i pre) (nth i post))
                  collect (list :block block :tx tx :pre (nth i pre) :post (nth i post)))))))
