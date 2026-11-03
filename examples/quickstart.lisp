;;;; examples/quickstart.lisp — a first session with Eita, as a script.
;;;;
;;;;   bin/eita repl --load examples/quickstart.lisp < /dev/null     (after ./build.sh)
;;;;
;;;; or in an SBCL that loaded the engine, (asdf:load-system "eita") (docs/quickstart.md),
;;;; then (load "examples/quickstart.lisp"). The same forms work typed into `bin/eita repl`.

(in-package :eita)

(defparameter *alice* "0x00000000000000000000000000000000000a11ce")
(defparameter *bob*   "0x0000000000000000000000000000000000000b0b")

;; A world at Prague rules, Alice holding 10 ETH.
(defparameter *w* (new-world :fork "Prague" :alloc `((,*alice* :balance ,(* 10 (expt 10 18))))))
(format t "~&alice: ~D wei~%" (balance *w* *alice*))

;; 1. A plain transfer: 1 ETH to Bob. Gas price 0, so Alice pays only the value.
(let ((r (transact *w* :from *alice* :to *bob* :value (expt 10 18) :gas 21000)))
  (format t "transfer: status ~D, gas used ~D~%" (getf r :status) (getf r :gas-used)))
(format t "alice: ~D wei, bob: ~D wei, alice's nonce ~D~%"
        (balance *w* *alice*) (balance *w* *bob*) (nonce *w* *alice*))

;; 2. Deploy a counter. Runtime (24 bytes): slot0 += 1; LOG1(topic = the new value); return it.
;;    60 00 54 60 01 01 80 60 00 55 80 60 00 52 60 20 60 00 a1 60 20 60 00 f3
;;    Init code: CODECOPY the runtime to memory, RETURN it.
(defparameter *counter*
  (deploy *w* :from *alice*
              :code "0x6018600c60003960186000f3600054600101806000558060005260206000a160206000f3"))
(format t "counter deployed at ~A, ~D bytes of code~%" (hex *counter*) (length (code *w* *counter*)))

;; 3. Call it in a transaction (state changes), then with CALL (on a copy: nothing changes).
(let ((r (transact *w* :from *alice* :to *counter*)))
  (format t "tx:   status ~D, gas ~D, output ~A~%" (getf r :status) (getf r :gas-used) (hex (getf r :output)))
  (dolist (l (getf r :logs))
    (destructuring-bind (address topics data) l
      (format t "      log from ~A topics ~A data ~A~%" (hex address) (mapcar #'hex topics) (hex data)))))
(let ((r (call *w* :from *bob* :to *counter*)))
  (format t "call: output ~A (what a second tx would return)~%" (hex (getf r :output))))
(format t "slot 0 after one tx and one call: ~D~%" (storage *w* *counter* 0))

;; 4. The state root a block header would commit to.
(format t "state root: ~A~%" (state-root *w*))
