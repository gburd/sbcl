;;;; parts of the loader which make sense in the cross-compilation
;;;; host (and which are useful in the host, because they're used by
;;;; GENESIS)
;;;;
;;;; based on the CMU CL load.lisp code, written by Skef Wholey and
;;;; Rob Maclachlan

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!FASL")

;;;; There looks to be an exciting amount of state being modified
;;;; here: certainly enough that I (dan, 2003.1.22) don't want to mess
;;;; around deciding how to thread-safetify it.  So we use a Big Lock.
;;;; Because this code is mutually recursive with the compiler, we use
;;;; the **WORLD-LOCK**.

;;;; miscellaneous load utilities

;;; Output the current number of semicolons after a fresh-line.
;;; FIXME: non-mnemonic name
(defun load-fresh-line ()
  (fresh-line)
  (let ((semicolons ";;;;;;;;;;;;;;;;"))
    (do ((count *load-depth* (- count (length semicolons))))
        ((< count (length semicolons))
         (write-string semicolons *standard-output* :end count))
      (declare (fixnum count))
      (write-string semicolons))
    (write-char #\space)))

;;; If VERBOSE, output (to *STANDARD-OUTPUT*) a message about how
;;; we're loading from STREAM-WE-ARE-LOADING-FROM.
(defun maybe-announce-load (stream-we-are-loading-from verbose)
  (when verbose
    (load-fresh-line)
    (let ((name #-sb-xc-host (file-name stream-we-are-loading-from)
                #+sb-xc-host nil))
      (if name
          (format t "loading ~S~%" name)
          (format t "loading stuff from ~S~%" stream-we-are-loading-from)))))

;;;; utilities for reading from fasl files

#!-sb-fluid (declaim (inline read-byte))

;;; This expands into code to read an N-byte unsigned integer using
;;; FAST-READ-BYTE.
(defmacro fast-read-u-integer (n)
  (let (bytes)
    `(let ,(loop for i from 0 below n
                 collect (let ((name (gensym "B")))
                           (push name bytes)
                           `(,name ,(if (zerop i)
                                        `(fast-read-byte)
                                        `(ash (fast-read-byte) ,(* i 8))))))
       (logior ,@bytes))))

;;; like FAST-READ-U-INTEGER, but the size may be determined at run time
(defmacro fast-read-var-u-integer (n)
  (let ((n-pos (gensym))
        (n-res (gensym))
        (n-cnt (gensym)))
    `(do ((,n-pos 8 (+ ,n-pos 8))
          (,n-cnt (1- ,n) (1- ,n-cnt))
          (,n-res
           (fast-read-byte)
           (dpb (fast-read-byte) (byte 8 ,n-pos) ,n-res)))
         ((zerop ,n-cnt) ,n-res)
       (declare (type index ,n-pos ,n-cnt)))))

;;; Read a signed integer.
(defmacro fast-read-s-integer (n)
  (declare (optimize (speed 0)))
  (let ((n-last (gensym)))
    (do ((res `(let ((,n-last (fast-read-byte)))
                 (if (zerop (logand ,n-last #x80))
                     ,n-last
                     (logior ,n-last #x-100)))
              `(logior (fast-read-byte)
                       (ash (the (signed-byte ,(* cnt 8)) ,res) 8)))
         (cnt 1 (1+ cnt)))
        ((>= cnt n) res))))

;;; Read an N-byte unsigned integer from the *FASL-INPUT-STREAM*.
(defmacro read-arg (n)
  (declare (optimize (speed 0)))
  (if (= n 1)
      `(the (unsigned-byte 8) (read-byte *fasl-input-stream*))
      `(with-fast-read-byte ((unsigned-byte 8) *fasl-input-stream*)
         (fast-read-u-integer ,n))))

(declaim (inline read-byte-arg read-halfword-arg read-word-arg))
(defun read-byte-arg ()
  (declare (optimize (speed 0)))
  (read-arg 1))

(defun read-halfword-arg ()
  (declare (optimize (speed 0)))
  (read-arg #.(/ sb!vm:n-word-bytes 2)))

(defun read-word-arg ()
  (declare (optimize (speed 0)))
  (read-arg #.sb!vm:n-word-bytes))

(defun read-unsigned-byte-32-arg ()
  (declare (optimize (speed 0)))
  (read-arg 4))


;;;; the fop table

;;; The table is implemented as a simple-vector indexed by the table
;;; offset. The offset is kept in at index 0 of the vector.
;;;
;;; FOPs use the table to save stuff, other FOPs refer to the table by
;;; direct indexes via REF-FOP-TABLE.

(defvar *fop-table*)
(declaim (simple-vector *fop-table*))

(declaim (inline ref-fop-table))
(defun ref-fop-table (index)
  (declare (type index index))
  (svref *fop-table* (the index (+ index 1))))

(defun get-fop-table-index ()
  (svref *fop-table* 0))

(defun reset-fop-table ()
  (setf (svref *fop-table* 0) 0))

(defun push-fop-table (thing)
  (let* ((table *fop-table*)
         (index (+ (the index (aref table 0)) 1)))
    (declare (fixnum index)
             (simple-vector table))
    (when (eql index (length table))
      (setf table (grow-fop-vector table index)
            *fop-table* table))
    (setf (aref table 0) index
          (aref table index) thing)))

;;; These three routines are used for both the stack and the table.
(defun make-fop-vector (size)
  (declare (type index size))
  (let ((vector (make-array size)))
    (setf (aref vector 0) 0)
    vector))

(defun grow-fop-vector (old-vector old-size)
  (declare (simple-vector old-vector)
           (type index old-size))
  (let* ((new-size (* old-size 2))
         (new-vector (make-array new-size)))
    (declare (fixnum new-size)
             (simple-vector new-vector old-vector))
    (replace new-vector old-vector)
    (nuke-fop-vector old-vector)
    new-vector))

(defun nuke-fop-vector (vector)
  (declare (simple-vector vector)
           #!-gencgc (ignore vector)
           (optimize speed))
  ;; Make sure we don't keep any garbage.
  #!+gencgc
  (fill vector 0))


;;;; the fop stack

;;; Much like the table, this is bound to a simple vector whose first
;;; element is the current index.
(defvar *fop-stack*)
(declaim (simple-vector *fop-stack*))

(defun fop-stack-empty-p ()
  (eql 0 (svref *fop-stack* 0)))

(defun pop-fop-stack ()
  (let* ((stack *fop-stack*)
         (top (svref stack 0)))
    (declare (type index top))
    (when (eql 0 top)
      (error "FOP stack empty"))
    (setf (svref stack 0) (1- top))
    (svref stack top)))

(defun push-fop-stack (value)
  (let* ((stack *fop-stack*)
         (next (1+ (the index (svref stack 0)))))
    (declare (type index next))
    (when (eql (length stack) next)
      (setf stack (grow-fop-vector stack next)
            *fop-stack* stack))
    (setf (svref stack 0) next
          (svref stack next) value)))

;;; Define a local macro to pop from the stack. Push the result of evaluation
;;; if PUSHP.
(defmacro with-fop-stack (pushp &body forms)
  (aver (member pushp '(nil t :nope)))
  `(macrolet ((pop-stack ()
                `(pop-fop-stack))
              (push-stack (value)
                `(push-fop-stack ,value)))
     ,(if pushp
          `(push-fop-stack (progn ,@forms))
          `(progn ,@forms))))

;;; Call FUN with N arguments popped from STACK.
(defmacro call-with-popped-args (fun n)
  ;; N's integer value must be known at macroexpansion time.
  (declare (type index n))
  (with-unique-names (n-stack old-top new-top)
    (let ((argtmps (make-gensym-list n)))
      `(let* ((,n-stack *fop-stack*)
              (,old-top (svref ,n-stack 0))
              (,new-top (- ,old-top ,n))
              ,@(loop for i from 1 upto n collecting
                      `(,(nth (1- i) argtmps)
                        (aref ,n-stack (+ ,new-top ,i)))))
         (declare (simple-vector ,n-stack))
         (setf (svref ,n-stack 0) ,new-top)
        ;; (For some applications it might be appropriate to FILL the
        ;; popped area with NIL here, to avoid holding onto garbage. For
        ;; sbcl-0.8.7.something, though, it shouldn't matter, because
        ;; we're using this only to pop stuff off *FOP-STACK*, and the
        ;; entire *FOP-STACK* can be GCed as soon as LOAD returns.)
        (,fun ,@argtmps)))))

;;;; Conditions signalled on invalid fasls (wrong fasl version, etc),
;;;; so that user code (esp. ASDF) can reasonably handle attempts to
;;;; load such fasls by recompiling them, etc. For simplicity's sake
;;;; make only condition INVALID-FASL part of the public interface,
;;;; and keep the guts internal.

(define-condition invalid-fasl (error)
  ((stream :reader invalid-fasl-stream :initarg :stream)
   (expected :reader invalid-fasl-expected :initarg :expected))
  (:report
   (lambda (condition stream)
     (format stream "~S is an invalid fasl file."
             (invalid-fasl-stream condition)))))

(define-condition invalid-fasl-header (invalid-fasl)
  ((byte :reader invalid-fasl-byte :initarg :byte)
   (byte-nr :reader invalid-fasl-byte-nr :initarg :byte-nr))
  (:report
   (lambda (condition stream)
     (format stream "~@<~S contains an illegal byte in the FASL header at ~
                     position ~A: Expected ~A, got ~A.~:@>"
             (invalid-fasl-stream condition)
             (invalid-fasl-byte-nr condition)
             (invalid-fasl-expected condition)
             (invalid-fasl-byte condition)))))

(define-condition invalid-fasl-version (invalid-fasl)
  ((version :reader invalid-fasl-version :initarg :version))
  (:report
   (lambda (condition stream)
     (format stream "~@<~S is a fasl file compiled with SBCL ~W, and ~
                      can't be loaded into SBCL ~W.~:@>"
             (invalid-fasl-stream condition)
             (invalid-fasl-version condition)
             (invalid-fasl-expected condition)))))

(define-condition invalid-fasl-implementation (invalid-fasl)
  ((implementation :reader invalid-fasl-implementation
                   :initarg :implementation))
  (:report
   (lambda (condition stream)
     (format stream "~S was compiled for implementation ~A, but this is a ~A."
             (invalid-fasl-stream condition)
             (invalid-fasl-implementation condition)
             (invalid-fasl-expected condition)))))

(define-condition invalid-fasl-features (invalid-fasl)
  ((potential-features :reader invalid-fasl-potential-features
                       :initarg :potential-features)
   (features :reader invalid-fasl-features :initarg :features))
  (:report
   (lambda (condition stream)
     (format stream "~@<incompatible ~S in fasl file ~S: ~2I~_~
                     Of features affecting binary compatibility, ~4I~_~S~2I~_~
                     the fasl has ~4I~_~A,~2I~_~
                     while the runtime expects ~4I~_~A.~:>"
             '*features*
             (invalid-fasl-stream condition)
             (invalid-fasl-potential-features condition)
             (invalid-fasl-features condition)
             (invalid-fasl-expected condition)))))

;;; Skips past the shebang line on stream, if any.
(defun maybe-skip-shebang-line (stream)
  (let ((p (file-position stream)))
    (flet ((next () (read-byte stream nil)))
      (unwind-protect
           (when (and (eq (next) (char-code #\#))
                      (eq (next) (char-code #\!)))
             (setf p nil)
             (loop for x = (next)
                   until (or (not x) (eq x (char-code #\newline)))))
        (when p
          (file-position stream p))))
    t))

;;; Returns T if the stream is a binary input stream with a FASL header.
(defun fasl-header-p (stream &key errorp)
  (unless (and (member (stream-element-type stream) '(character base-char))
               ;; give up if it's not a file stream, or it's an
               ;; fd-stream but it's either not bivalent or not
               ;; seekable (doesn't really have a file)
               (or (not (typep stream 'file-stream))
                   (and (typep stream 'fd-stream)
                        (or (not (sb!impl::fd-stream-bivalent-p stream))
                            (not (sb!impl::fd-stream-file stream))))))
    (let ((p (file-position stream)))
      (unwind-protect
           (let* ((header *fasl-header-string-start-string*)
                  (buffer (make-array (length header) :element-type '(unsigned-byte 8)))
                  (n 0))
             (flet ((scan ()
                      (maybe-skip-shebang-line stream)
                      (setf n (read-sequence buffer stream))))
               (if errorp
                   (scan)
                   (or (ignore-errors (scan))
                       ;; no a binary input stream
                       (return-from fasl-header-p nil))))
             (if (mismatch buffer header
                           :test #'(lambda (code char) (= code (char-code char))))
                 ;; Immediate EOF is valid -- we want to match what
                 ;; CHECK-FASL-HEADER does...
                 (or (zerop n)
                     (when errorp
                       (error 'fasl-header-missing
                              :stream stream
                              :fhsss buffer
                              :expected header)))
                 t))
        (file-position stream p)))))


;;;; LOAD-AS-FASL
;;;;
;;;; Note: LOAD-AS-FASL is used not only by LOAD, but also (with
;;;; suitable modification of the fop table) in GENESIS. Therefore,
;;;; it's needed not only in the target Lisp, but also in the
;;;; cross-compilation host.

;;; a helper function for LOAD-FASL-GROUP
;;;
;;; Return true if we successfully read a FASL header from the stream, or NIL
;;; if EOF was hit before anything except the optional shebang line was read.
;;; Signal an error if we encounter garbage.
(defun check-fasl-header (stream)
  (maybe-skip-shebang-line stream)
  (let ((byte (read-byte stream nil)))
    (when byte
      ;; Read and validate constant string prefix in fasl header.
      (let* ((fhsss *fasl-header-string-start-string*)
             (fhsss-length (length fhsss)))
        (unless (= byte (char-code (schar fhsss 0)))
          (error 'invalid-fasl-header
                 :stream stream
                 :byte-nr 0
                 :byte byte
                 :expected (char-code (schar fhsss 0))))
        (do ((byte (read-byte stream) (read-byte stream))
             (count 1 (1+ count)))
            ((= byte +fasl-header-string-stop-char-code+)
             t)
          (declare (fixnum byte count))
          (when (and (< count fhsss-length)
                     (not (eql byte (char-code (schar fhsss count)))))
            (error 'invalid-fasl-header
                   :stream stream
                   :byte-nr count
                   :byte byte
                   :expected (char-code (schar fhsss count))))))
      ;; Read and validate version-specific compatibility stuff.
      (flet ((string-from-stream ()
               (let* ((length (read-unsigned-byte-32-arg))
                      (result (make-string length)))
                 (read-string-as-bytes stream result)
                 result)))
        ;; Read and validate implementation and version.
        (let ((implementation (keywordicate (string-from-stream)))
              (expected-implementation +backend-fasl-file-implementation+))
          (unless (string= expected-implementation implementation)
            (error 'invalid-fasl-implementation
                   :stream stream
                   :implementation implementation
                   :expected expected-implementation)))
        (let* ((fasl-version (read-word-arg))
               (sbcl-version (if (<= fasl-version 76)
                                 "1.0.11.18"
                                 (string-from-stream)))
               (expected-version (sb!xc:lisp-implementation-version)))
          (unless (string= expected-version sbcl-version)
            (restart-case
                (error 'invalid-fasl-version
                       :stream stream
                       :version sbcl-version
                       :expected expected-version)
              (continue () :report "Load the fasl file anyway"))))
        ;; Read and validate *FEATURES* which affect binary compatibility.
        (let ((faff-in-this-file (string-from-stream)))
          (unless (string= faff-in-this-file *features-affecting-fasl-format*)
            (error 'invalid-fasl-features
                   :stream stream
                   :potential-features *features-potentially-affecting-fasl-format*
                   :expected *features-affecting-fasl-format*
                   :features faff-in-this-file)))
        ;; success
        t))))

;; Setting this variable gives you a trace of fops as they are loaded and
;; executed.
#!+sb-show
(defvar *show-fops-p* nil)

;;;
;;; a helper function for LOAD-AS-FASL
;;;
;;; Return true if we successfully load a group from the stream, or
;;; NIL if EOF was encountered while trying to read from the stream.
;;; Dispatch to the right function for each fop.
(defun load-fasl-group (stream)
  (when (check-fasl-header stream)
    (catch 'fasl-group-end
      (reset-fop-table)
      (let ((*skip-until* nil))
        (declare (special *skip-until*))
        (loop
          (let ((byte (read-byte stream)))
            ;; Do some debugging output.
            #!+sb-show
            (when *show-fops-p*
              (let* ((stack *fop-stack*)
                     (ptr (svref stack 0)))
                (fresh-line *trace-output*)
                ;; The FOP operations are stack based, so it's sorta
                ;; logical to display the operand before the operator.
                ;; ("reverse Polish notation")
                (unless (= ptr 0)
                  (write-char #\space *trace-output*)
                  (prin1 (aref stack ptr) *trace-output*)
                  (terpri *trace-output*))
                ;; Display the operator.
                (format *trace-output*
                        "~&~S (#X~X at ~D) (~S)~%"
                        (aref *fop-names* byte)
                        byte
                        (1- (file-position stream))
                        (svref *fop-funs* byte))))

            ;; Actually execute the fop.
            (funcall (the function (svref *fop-funs* byte)))))))))

(defun load-as-fasl (stream verbose print)
  ;; KLUDGE: ANSI says it's good to do something with the :PRINT
  ;; argument to LOAD when we're fasloading a file, but currently we
  ;; don't. (CMU CL did, but implemented it in a non-ANSI way, and I
  ;; just disabled that instead of rewriting it.) -- WHN 20000131
  (declare (ignore print))
  (when (zerop (file-length stream))
    (error "attempt to load an empty FASL file:~%  ~S" (namestring stream)))
  (maybe-announce-load stream verbose)
  (let* ((*fasl-input-stream* stream)
         (*fop-table* (make-fop-vector 1000))
         (*fop-stack* (make-fop-vector 100)))
    (unwind-protect
         (loop while (load-fasl-group stream))
      ;; Nuke the table and stack to avoid keeping garbage on
      ;; conservatively collected platforms.
      (nuke-fop-vector *fop-table*)
      (nuke-fop-vector *fop-stack*)))
  t)

(declaim (notinline read-byte)) ; Why is it even *declaimed* inline above?

;;;; stuff for debugging/tuning by collecting statistics on FOPs (?)

#|
(defvar *fop-counts* (make-array 256 :initial-element 0))
(defvar *fop-times* (make-array 256 :initial-element 0))
(defvar *print-fops* nil)

(defun clear-counts ()
  (fill (the simple-vector *fop-counts*) 0)
  (fill (the simple-vector *fop-times*) 0)
  t)

(defun analyze-counts ()
  (let ((counts ())
        (total-count 0)
        (times ())
        (total-time 0))
    (macrolet ((breakdown (lvar tvar vec)
                 `(progn
                   (dotimes (i 255)
                     (declare (fixnum i))
                     (let ((n (svref ,vec i)))
                       (push (cons (svref *fop-names* i) n) ,lvar)
                       (incf ,tvar n)))
                   (setq ,lvar (subseq (sort ,lvar (lambda (x y)
                                                     (> (cdr x) (cdr y))))
                                       0 10)))))

      (breakdown counts total-count *fop-counts*)
      (breakdown times total-time *fop-times*)
      (format t "Total fop count is ~D~%" total-count)
      (dolist (c counts)
        (format t "~30S: ~4D~%" (car c) (cdr c)))
      (format t "~%Total fop time is ~D~%" (/ (float total-time) 60.0))
      (dolist (m times)
        (format t "~30S: ~6,2F~%" (car m) (/ (float (cdr m)) 60.0))))))
|#

