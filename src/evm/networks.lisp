;;;; evm/networks.lisp — running a world at a network's rules by name.

(in-package #:eita.evm)

(defparameter *network-fork-ords*
  '(("Frontier" . 0) ("Homestead" . 1) ("EIP150" . 3) ("EIP158" . 4)
    ("Byzantium" . 5) ("Constantinople" . 6) ("ConstantinopleFix" . 7)
    ("Istanbul" . 8) ("Berlin" . 10) ("London" . 11) ("Paris" . 14)
    ("Merge" . 14) ("Shanghai" . 15) ("Cancun" . 16) ("Prague" . 17) ("Osaka" . 18)
    ("BPO1" . 19) ("BPO2" . 20)))
;; Not listed, so skipped by run-test: the transition networks ("ShanghaiToCancunAtTime15k", ...).

(defun set-fork! (network)
  "Point both the host (*fork-ord*) and the native dispatch table at
   NETWORK's fork. Unknown networks are a hard error — no silent
   Cancun fallback."
  (let ((ord (cdr (assoc network *network-fork-ords* :test #'string=))))
    (unless ord (error "set-fork!: unknown network ~A" network))
    (setf *fork-ord* ord)
    (%set-fork ord)))
