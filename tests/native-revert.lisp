;;;; tests/native-revert.lisp — a reverted frame's SSTOREs to accounts that collide in the
;;;; native address -> id cache (c/storage_host.c: 64 entries, keyed by the address's low
;;;; limb mod 64) are all restored by the native revert alone (eita_sh_revert_storage), as a
;;;; host with no second pass needs; the Lisp loop of revert-journal-to finds no SSTORE entry
;;;; left. The tx: O calls R; R calls A, B, A, C (each increments its slot 1 and sets slot 2)
;;;; and reverts; O records the call's result. After it, the world must be the pre-state plus
;;;; O's record and the sender's nonce: the same storage and the same state root.
;;;; Run: (eita.test:run-all :only '("native-revert")).

(defpackage #:eita.test.native-revert (:use #:cl))
(in-package #:eita.test.native-revert)

(defparameter *ok* t)
(defun check (ok fmt &rest args)
  (format t "  ~:[FAIL~;PASS~]  ~?~%" ok fmt args)
  (unless ok (setf *ok* nil)))

(defun addr-bytes (a) (loop for i from 19 downto 0 collect (ldb (byte 8 (* 8 i)) a)))
(defun call-code (a)
  "CALL A with all gas, no value, no data; pop the result."
  `(#x60 0 #x60 0 #x60 0 #x60 0 #x60 0 #x73 ,@(addr-bytes a) #x5a #xf1 #x50))

;; Equal low limbs mod 64 (one native cache entry), different accounts.
(defparameter +a+ #xaa00000000000000000000000000000000000005)
(defparameter +b+ #xbb00000000000000000000000000000000000045)
(defparameter +c+ #xcc00000000000000000000000000000000000085)
(defparameter +r+ #x00000000000000000000000000000000000000f1)
(defparameter +o+ #x00000000000000000000000000000000000000f2)
(defparameter +from+ #x00000000000000000000000000000000000000e0)
(defparameter +counter+                 ; slot 1 += 1; slot 2 := 7
  '(#x60 1 #x54 #x60 1 #x01 #x60 1 #x55 #x60 7 #x60 2 #x55 #x00))
(defparameter +reverter+
  (append (call-code +a+) (call-code +b+) (call-code +a+) (call-code +c+) '(#x60 0 #x60 0 #xfd)))
(defparameter +outer+                   ; slot 9 := CALL R's result + 1
  `(#x60 0 #x60 0 #x60 0 #x60 0 #x60 0 #x73 ,@(addr-bytes +r+) #x5a #xf1 #x60 1 #x01 #x60 9 #x55 #x00))

(defun alloc (&key (o-slot9 nil) (nonce 0))
  `((,+from+ :balance ,(expt 10 18) :nonce ,nonce)
    (,+o+ :code ,(coerce +outer+ 'vector) ,@(and o-slot9 `(:storage ((9 . ,o-slot9)))))
    (,+r+ :code ,(coerce +reverter+ 'vector))
    (,+a+ :code ,(coerce +counter+ 'vector) :storage ((1 . 100)))
    (,+b+ :code ,(coerce +counter+ 'vector) :storage ((1 . 200)))
    (,+c+ :code ,(coerce +counter+ 'vector) :storage ((1 . 300)))))

;;; The SSTORE entries above the first un-create: before the native pass (each SSTORE writes
;;; the effect's entry when the value changes and the handler's, old = the value written),
;;; and after it, those left for the Lisp loop.
(defvar *entries* 0)
(defvar *left* 0)
(defvar *restored* 0)
(defun count-left (arena target)
  (let ((count (cffi:mem-ref arena :uint64 0)) (jdata (cffi:mem-ref arena :pointer 16)) (n 0))
    (loop for i downfrom (1- count) to target
          for type = (cffi:mem-ref jdata :uint64 (* i eita.evm::+journal-entry-bytes+))
          until (= type 10) do (when (zerop type) (incf n)))
    n))

(let ((w (eita:new-world :fork "Prague" :alloc (alloc)))
      (want (eita:new-world :fork "Prague" :alloc (alloc :o-slot9 1 :nonce 1))))
  (sb-int:encapsulate 'eita.native:%sh-revert-storage 'native-revert-test
                      (lambda (f arena target)
                        (incf *entries* (count-left arena target))
                        (let ((n (funcall f arena target)))
                          (incf *restored* n)
                          (incf *left* (count-left arena target))
                          n)))
  (unwind-protect
       (let ((r (eita:transact w :from +from+ :to +o+ :gas 1000000)))
         (check (eql 1 (getf r :status)) "the tx succeeds (status ~A)" (getf r :status))
         (check (= 1 (eita:storage w +o+ 9)) "R reverted (O's slot 9 = ~D)" (eita:storage w +o+ 9))
         (check (and (plusp *entries*) (= *restored* *entries*))
                "the native revert restored ~D of the slice's ~D SSTORE entries" *restored* *entries*)
         (check (zerop *left*) "no SSTORE entry left for the Lisp loop (~D)" *left*)
         (loop for (a v) in (list (list +a+ 100) (list +b+ 200) (list +c+ 300))
               do (check (and (= v (eita:storage w a 1)) (zerop (eita:storage w a 2)))
                         "~X: slot 1 = ~D, slot 2 = ~D" a (eita:storage w a 1) (eita:storage w a 2)))
         (let ((got (eita:state-root w)) (exp (eita:state-root want)))
           (check (string= got exp) "state root ~A = the pre-state's plus O's record ~A" got exp)))
    (sb-int:unencapsulate 'eita.native:%sh-revert-storage 'native-revert-test)))

(eita.test:finish :code (if *ok* 0 1))
