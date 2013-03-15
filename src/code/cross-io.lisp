;;;; cross-compiler-only versions of I/O-related stuff

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!FASL")

;;;; fast-read operations
;;;;
;;;; (Portable versions of these are needed at cross-compile time because
;;;; genesis implements some of its cold fops by cloning ordinary fop
;;;; implementations, and the ordinary fop implementations are defined in terms
;;;; of fast-read operations.)

(defmacro with-fast-read-byte ((type stream &optional (eof-error-p t) eof-value)
                               &body body)
  (let ((f-stream (gensym "STREAM"))
        (f-eof-error-p (gensym "EOF-ERROR-P"))
        (f-eof-value (gensym "EOF-VALUE")))
    `(let ((,f-stream ,stream)
           (,f-eof-error-p ,eof-error-p)
           (,f-eof-value ,eof-value))
       (flet ((fast-read-byte ()
                  (the ,type (read-byte ,f-stream ,f-eof-error-p ,f-eof-value))))
         ,@body))))
