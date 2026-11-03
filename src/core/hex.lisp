;;;; core/hex.lisp — hex text to integers and octets.

(in-package #:eita.core)

;;; --- Hex helpers ---

(declaim (inline hex-start))
(defun hex-start (s) (if (and (>= (length s) 2) (char= (char s 0) #\0) (char= (char s 1) #\x)) 2 0))

(declaim (inline hex-digit))
(defun hex-digit (c)
  (let ((code (char-code c)))
    (cond ((<= 48 code 57) (- code 48)) ((<= 97 code 102) (- code 87)) ((<= 65 code 70) (- code 55))
          (t (error "not a hex digit: ~S" c)))))

(defun hex->int (s)
  "S (0x optional) as an integer, 0 for no digits. Block input does not come through here
   (input/ decodes it from its bytes)."
  (let ((i (hex-start s))) (if (= i (length s)) 0 (parse-integer s :start i :radix 16))))

(defun hex->bytes (s)
  "S (0x optional) as octets; an odd digit count has a leading zero nibble."
  (let* ((i (hex-start s)) (odd (if (oddp (- (length s) i)) 1 0))
         (bs (make-array (ceiling (- (length s) i) 2) :element-type '(unsigned-byte 8))))
    (dotimes (k (length bs) bs)
      (let ((a (- (+ i (* 2 k)) odd)))
        (setf (aref bs k) (logior (if (< a i) 0 (ash (hex-digit (char s a)) 4)) (hex-digit (char s (1+ a)))))))))
