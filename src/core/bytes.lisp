;;;; core/bytes.lisp — keccak, big-endian bytes, RLP, CREATE addresses.

(in-package #:eita.core)

(defun keccak256-bytes (bytes)
  "Hash BYTES (a sequence of u8), return a 32-byte vector; a u8 vector is hashed in place."
  (let ((in (coerce bytes '(simple-array (unsigned-byte 8) (*))))
        (out (make-array 32 :element-type '(unsigned-byte 8))))
    (cffi:with-pointer-to-vector-data (i in)
      (cffi:with-pointer-to-vector-data (o out) (eita-keccak256 i (length in) o)))
    out))

(defun int-to-be-bytes (n)
  "Minimal big-endian byte list for non-negative N. Zero → empty list."
  (if (zerop n) '()
      (loop with bs = '()
            for v = n then (ash v -8)
            while (plusp v)
            do (push (logand v 255) bs)
            finally (return bs))))

(defun rlp-encode-bytes (bs)
  "RLP-encode a sequence of bytes as a string."
  (let ((n (length bs)))
    (cond
      ((and (= n 1) (< (elt bs 0) 128)) (list (elt bs 0)))
      ((<= n 55) (cons (+ 128 n) (coerce bs 'list)))
      (t (let ((lb (int-to-be-bytes n)))
           (append (cons (+ 183 (length lb)) lb) (coerce bs 'list)))))))

(defun rlp-encode-list (items)
  "ITEMS is a list of RLP-encoded byte-lists; wrap with list header."
  (let* ((payload (apply #'append items))
         (n (length payload)))
    (if (<= n 55)
        (cons (+ 192 n) payload)
        (let ((lb (int-to-be-bytes n)))
          (append (cons (+ 247 (length lb)) lb) payload)))))

(defun addr-to-bytes (addr)
  "20-byte big-endian representation of a u160 address."
  (loop for i from 19 downto 0
        collect (logand 255 (ash addr (* -8 i)))))

(defun derive-create-address (sender nonce)
  "EIP-2: new contract address = keccak256(rlp([sender, nonce]))[12..32]."
  (let* ((rlp (rlp-encode-list
                (list (rlp-encode-bytes (addr-to-bytes sender))
                      (rlp-encode-bytes (int-to-be-bytes nonce)))))
         (hash (keccak256-bytes (coerce rlp 'vector)))
         (addr 0))
    (loop for i from 12 to 31
          do (setf addr (logior (ash addr 8) (aref hash i))))
    addr))
