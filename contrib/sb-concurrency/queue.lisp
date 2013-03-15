;;;; Written by James M. Lawrence for SBCL.
;;;; API and docstrings by Nikodemus Siivola.
;;;;
;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was written at
;;;; Carnegie Mellon University and released into the public domain. The
;;;; software is in the public domain and is provided with absolutely no
;;;; warranty. See the COPYING and CREDITS files for more information.

;;; Singly-linked queue with compare-and-swap operations.
;;;
;;; The following invariants hold except during updates:
;;;
;;;   (car (queue-head queue)) == +dummy+
;;;
;;;   (cdr (queue-tail queue)) == nil
;;;
;;;   If the queue is empty, (queue-head queue) == (queue-tail queue).
;;;
;;;   If the queue is non-empty, (cadr (queue-head queue)) is the next
;;;   value to be dequeued and (car (queue-tail queue)) is the most
;;;   recently enqueued value.
;;;
;;; The CDR of a discarded node is set to +DEAD-END+. This flag must
;;; be checked at each traversal.

(in-package :sb-concurrency)

(defconstant +dummy+ '.dummy.)
(defconstant +dead-end+ '.dead-end.)

(declaim (inline %make-queue))
(defstruct (queue (:constructor %make-queue (head tail name))
                  (:copier nil)
                  (:predicate queuep))
  "Lock-free thread safe FIFO queue.

Use ENQUEUE to add objects to the queue, and DEQUEUE to remove them."
  (head (error "No HEAD.") :type cons)
  (tail (error "No TAIL.") :type cons)
  (name nil))

(setf (documentation 'queuep 'function)
      "Returns true if argument is a QUEUE, NIL otherwise."
      (documentation 'queue-name 'function)
      "Name of a QUEUE. Can be assingned to using SETF. Queue names
can be arbitrary printable objects, and need not be unique.")

(defun make-queue (&key name initial-contents)
  "Returns a new QUEUE with NAME and contents of the INITIAL-CONTENTS
sequence enqueued."
  (let* ((dummy (cons +dummy+ nil))
         (queue (%make-queue dummy dummy name)))
    (flet ((enc-1 (x)
             (enqueue x queue)))
      (declare (dynamic-extent #'enc-1))
      (map nil #'enc-1 initial-contents))
    queue))

(defun enqueue (value queue)
  "Adds VALUE to the end of QUEUE. Returns VALUE."
  ;; Attempt CAS, repeat upon failure. Upon success update QUEUE-TAIL.
  (declare (optimize speed))
  (let ((new (cons value nil)))
    (loop (when (eq nil (sb-ext:compare-and-swap (cdr (queue-tail queue))
                                                 nil new))
            (setf (queue-tail queue) new)
            (return value)))))

(defun dequeue (queue)
  "Retrieves the oldest value in QUEUE and returns it as the primary value,
and T as secondary value. If the queue is empty, returns NIL as both primary
and secondary value."
  ;; Attempt to CAS QUEUE-HEAD with the next node, repeat upon
  ;; failure. Upon success, clear the discarded node and set the CAR
  ;; of QUEUE-HEAD to +DUMMY+.
  (declare (optimize speed))
  (loop (let* ((head (queue-head queue))
               (next (cdr head)))
          ;; NEXT could be +DEAD-END+, whereupon we try again.
          (typecase next
            (null (return (values nil nil)))
            (cons (when (eq head (sb-ext:compare-and-swap (queue-head queue)
                                                          head next))
                    (let ((value (car next)))
                      ;; Clear the CDR, otherwise the conservative GC could
                      ;; hoard long lists. (car head) is always +dummy+.
                      (setf (cdr head) +dead-end+
                            (car next) +dummy+)
                      (return (values value t)))))))))

(defun try-walk-queue (fun queue)
  ;; This isn't /quite/ as bad as it looks. We're in danger of needing
  ;; to restart only as long as we're close to the head of the queue.
  (let ((node (queue-head queue)))
    (loop
       (let ((value (car node)))
         (unless (eq value +dummy+)
           (funcall fun value)))
       (setf node (cdr node))
       (cond ((eq node +dead-end+)
              (return nil))
             ((null node)
              (return t))))))

(defun list-queue-contents (queue)
  "Returns the contents of QUEUE as a list without removing them from the
QUEUE. Mainly useful for manual examination of queue state, as the list may be
out of date by the time it is returned, and concurrent dequeue operations may
in the worse case force the queue-traversal to be restarted several times."
  (tagbody
   :retry
     (collect ((result))
       (unless (try-walk-queue (lambda (elem) (result elem)) queue)
         (go :retry))
       (return-from list-queue-contents (result)))))

(defun queue-count (queue)
  "Returns the number of objects in QUEUE. Mainly useful for manual
examination of queue state, and in PRINT-OBJECT methods: inefficient as it
must walk the entire queue."
  (tagbody
   :retry
     (let ((count 0))
       (unless (try-walk-queue (lambda (elem)
                                 (declare (ignore elem))
                                 (incf count))
                               queue)
         (go :retry))
       (return-from queue-count count))))

(defun queue-empty-p (queue)
  "Returns T if QUEUE is empty, NIL otherwise."
  (null (cdr (queue-head queue))))
