;;;; examples/hooks/notify.lisp — a notification service: conditions on verified blocks →
;;;; a bounded queue → a worker thread that delivers, rate-limited (docs/hooks.md).
;;;;
;;;;   bin/eita replay --chain ethereum --blocks DIR --from 1 --to 1000 --observer examples/hooks/notify.lisp
;;;;
;;;; prints one JSON line per notification. (hooks.notify:start :deliver f) delivers through
;;;; your F instead (a webhook, a chat bot); the handlers only queue, so a slow or failing
;;;; delivery never holds the replay back.

(defpackage #:hooks.notify (:use #:cl)
  (:export #:make-notifier #:notify #:stop-notifier #:notifier-stats #:json-line
           #:start #:stop #:*notifier* #:*large-value*))
(in-package #:hooks.notify)

;;; --- The notifier: a bounded queue, a token bucket, one worker thread ----------------------
(defstruct (notifier (:constructor %make-notifier))
  deliver capacity rate burst
  (tokens 0d0) (stamp (get-internal-real-time))
  (head '()) (tail '()) (count 0) (busy nil) (stopping nil)
  (lock (sb-thread:make-mutex :name "notifier")) (cv (sb-thread:make-waitqueue))
  (sent 0) (rate-limited 0) (full 0) (failed 0) thread)

(defun make-notifier (&key (deliver 'json-line) (capacity 1024) (rate 1) (burst 10))
  "A notifier that calls DELIVER (message) on its own thread for each queued message: at
   most BURST at once, then RATE a second on average; at most CAPACITY waiting."
  (let ((n (%make-notifier :deliver deliver :capacity capacity :rate rate :burst burst
                           :tokens (float burst 1d0))))
    (setf (notifier-thread n) (sb-thread:make-thread (lambda () (worker n)) :name "notifier"))
    n))

(defun notify (n message)
  "Queue MESSAGE (a plist) for delivery; never waits. :queued, or :rate-limited / :full
   (dropped and counted)."
  (sb-thread:with-mutex ((notifier-lock n))
    (let ((now (get-internal-real-time)))    ; refill the bucket for the time passed
      (setf (notifier-tokens n) (min (float (notifier-burst n) 1d0)
                                     (+ (notifier-tokens n) (* (notifier-rate n) (/ (- now (notifier-stamp n)) internal-time-units-per-second))))
            (notifier-stamp n) now))
    (cond ((< (notifier-tokens n) 1) (incf (notifier-rate-limited n)) :rate-limited)
          ((>= (notifier-count n) (notifier-capacity n)) (incf (notifier-full n)) :full)
          (t (decf (notifier-tokens n))
             (let ((cell (list message)))
               (if (notifier-tail n) (setf (cdr (notifier-tail n)) cell) (setf (notifier-head n) cell))
               (setf (notifier-tail n) cell))
             (incf (notifier-count n))
             (sb-thread:condition-broadcast (notifier-cv n))
             :queued))))

(defun worker (n)
  (loop
    (let ((message (sb-thread:with-mutex ((notifier-lock n))
                     (loop until (or (notifier-head n) (notifier-stopping n))
                           do (sb-thread:condition-wait (notifier-cv n) (notifier-lock n)))
                     (unless (notifier-head n) (return))
                     (decf (notifier-count n))
                     (setf (notifier-busy n) t)
                     (prog1 (pop (notifier-head n))
                       (unless (notifier-head n) (setf (notifier-tail n) nil))))))
      (handler-case (progn (funcall (notifier-deliver n) message)
                           (sb-thread:with-mutex ((notifier-lock n)) (incf (notifier-sent n))))
        (error (e)
          (sb-thread:with-mutex ((notifier-lock n)) (incf (notifier-failed n)))
          (format *error-output* "~&[notify] delivery failed: ~A~%" e)))
      (sb-thread:with-mutex ((notifier-lock n))
        (setf (notifier-busy n) nil)
        (sb-thread:condition-broadcast (notifier-cv n))))))

(defun drain (n)
  "Wait until every queued message is delivered."
  (sb-thread:with-mutex ((notifier-lock n))
    (loop while (or (notifier-head n) (notifier-busy n))
          do (sb-thread:condition-wait (notifier-cv n) (notifier-lock n)))))

(defun stop-notifier (n)
  "Deliver what is queued, then end the worker."
  (sb-thread:with-mutex ((notifier-lock n))
    (setf (notifier-stopping n) t)
    (sb-thread:condition-broadcast (notifier-cv n)))
  (sb-thread:join-thread (notifier-thread n) :default nil))

(defun notifier-stats (n)
  (sb-thread:with-mutex ((notifier-lock n))
    (list :sent (notifier-sent n) :queued (notifier-count n) :rate-limited (notifier-rate-limited n)
          :full (notifier-full n) :failed (notifier-failed n))))

(defun json-line (message &optional (stream *standard-output*))
  "MESSAGE as one line of JSON."
  (write-line (jsown:to-json (cons :obj (loop for (k v) on message by #'cddr
                                              collect (cons (string-downcase (symbol-name k)) v))))
              stream)
  (finish-output stream))

;;; --- Conditions: what is worth a notification ---------------------------------------------
(defvar *notifier* nil)
(defparameter *large-value* (expt 10 20) "A native value move at least this large (wei) is notified.")

(defun on-transfer (x)
  (when (>= (getf x :value) *large-value*)
    (notify *notifier* (list :event "large-transfer" :block (getf x :block) :tx (getf x :tx)
                             :from (eita:hex (getf x :from)) :to (eita:hex (getf x :to))
                             :value (princ-to-string (getf x :value))))))

(defun on-block (block)
  (when (> (* 100 (getf block :gas-used)) (* 95 (getf block :gas-limit)))
    (notify *notifier* (list :event "full-block" :block (getf block :number)
                             :gas-used (getf block :gas-used) :gas-limit (getf block :gas-limit)))))

(defun on-rollback (n)
  (notify *notifier* (list :event "rollback" :block n)))

(defun on-finalize ()
  (drain *notifier*))                    ; a bounded run ends with its notifications out

(defun start (&rest options &key deliver capacity rate burst)
  "Subscribe the conditions above, delivering through a new notifier (OPTIONS: make-notifier's)."
  (declare (ignore deliver capacity rate burst))
  (when *notifier* (stop))
  (setf *notifier* (apply #'make-notifier (loop for (k v) on options by #'cddr when v append (list k v))))
  (eita:subscribe "notify" :transfer 'on-transfer :block 'on-block :rollback 'on-rollback :finalize 'on-finalize))

(defun stop ()
  (eita:unsubscribe "notify")
  (when *notifier* (stop-notifier (shiftf *notifier* nil))))

(start)
