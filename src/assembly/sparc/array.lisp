;;;; support routines for arrays and vectors

;;;; This software is part of the SBCL system. See the README file for
;;;; more information.
;;;;
;;;; This software is derived from the CMU CL system, which was
;;;; written at Carnegie Mellon University and released into the
;;;; public domain. The software is in the public domain and is
;;;; provided with absolutely no warranty. See the COPYING and CREDITS
;;;; files for more information.

(in-package "SB!VM")

(define-assembly-routine (allocate-vector
                          (:policy :fast-safe)
                          (:translate allocate-vector)
                          (:arg-types positive-fixnum
                                      positive-fixnum
                                      positive-fixnum))
                         ((:arg type any-reg a0-offset)
                          (:arg length any-reg a1-offset)
                          (:arg words any-reg a2-offset)
                          (:res result descriptor-reg a0-offset)

                          (:temp ndescr non-descriptor-reg nl0-offset)
                          (:temp gc-temp non-descriptor-reg nl1-offset)
                          (:temp vector descriptor-reg a3-offset))
  (pseudo-atomic ()
    ;; boxed words == unboxed bytes
    (inst add ndescr words (* (1+ vector-data-offset) n-word-bytes))
    (inst andn ndescr 7)
    (allocation vector ndescr other-pointer-lowtag :temp-tn gc-temp)
    (inst srl ndescr type word-shift)
    (storew ndescr vector 0 other-pointer-lowtag)
    (storew length vector vector-length-slot other-pointer-lowtag))
  ;; This makes sure the zero byte at the end of a string is paged in so
  ;; the kernel doesn't bitch if we pass it the string.
  ;;
  ;; RLT comments in CMUCL about changing the following line to
  ;; store at -1 instead of 0:
  ;;   This used to write to the word after the last allocated word.  I
  ;;   (RLT) made it write to the last allocated word, which is where
  ;;   the zero-byte of the string is.  Look at the deftransform for
  ;;   make-array in array-tran.lisp.  For strings we always allocate
  ;;   enough space to hold the zero-byte.
  ;; Which is most certainly motivated by the fact that this store (if
  ;; performed on gencgc) overwrites the first word of the following
  ;; page -- destroying the first object of an unrelated allocation region!
  ;;
  ;; But the CMUCL fix breaks :ELEMENT-TYPE NIL strings, so we'd need a
  ;; branch to figure out whether to do it.  Until and unless someone
  ;; demonstrates that gencgc actually gives us uncommitted memory, I'm
  ;; just not doing it at all:  -- DFL
  #!-gencgc
  (storew zero-tn alloc-tn 0)
  (move result vector))
