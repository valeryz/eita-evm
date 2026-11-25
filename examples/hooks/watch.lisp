;;;; examples/hooks/watch.lisp — a state watch: call a function when a storage slot or an
;;;; account's balance, nonce or code changes (docs/hooks.md).
;;;;
;;;;   (load "examples/hooks/watch.lisp")
;;;;   (hooks.watch:watch "0xA0b8…eB48" :slot 3)                 ; print each change
;;;;   (hooks.watch:watch "0xd8dA…6045" :kind :balance :notify #'my-function)
;;;;
;;;; A change is a tx's NET change (pre and post value), after the block verified; one
;;;; subscription serves every watch through one hash lookup per state change.

(defpackage #:hooks.watch (:use #:cl) (:export #:watch #:unwatch #:print-change))
(in-package #:hooks.watch)

(defvar *watches* (make-hash-table :test 'equal)
  "(address kind slot) -> the functions to call with each change of it; kind :storage
   (slot: the slot) or :balance / :nonce / :code (slot NIL).")

(defun key (address kind slot) (list (eita:addr address) kind (and (eq kind :storage) slot)))

(defun print-change (change)
  "The default NOTIFY: one line per change."
  (format t "~&[watch] block ~D tx ~A: ~(~A~) of ~A~@[ slot ~A~] ~A -> ~A~%"
          (getf change :block) (getf change :tx) (getf change :kind) (eita:hex (getf change :address))
          (and (getf change :slot) (eita:hex (getf change :slot)))
          (getf change :pre) (getf change :post)))

(defun watch (address &key (kind :storage) slot (notify 'print-change))
  "Call NOTIFY with each change of ADDRESS's slot SLOT (KIND :storage) or of its balance,
   nonce or code hash (KIND :balance, :nonce, :code), and with (:kind :rollback :block n)
   when the chain is rolled back to block N (what it reported above N is retracted)."
  (eita:with-fold-state ()                     ; the table is read by the handler's thread
    (pushnew notify (gethash (key address kind slot) *watches*)))
  (list address kind slot))

(defun unwatch (address &key (kind :storage) slot)
  (eita:with-fold-state () (remhash (key address kind slot) *watches*)))

(defun on-change (change)
  (let ((fns (gethash (list (getf change :address) (getf change :kind) (getf change :slot)) *watches*)))
    (dolist (f fns) (funcall f change))))

(defun on-rollback (n)
  (let ((all '()))
    (maphash (lambda (k fns) (declare (ignore k)) (setf all (union fns all))) *watches*)
    (dolist (f all) (funcall f (list :kind :rollback :block n)))))

(eita:subscribe "watch" :state-change 'on-change :rollback 'on-rollback)
