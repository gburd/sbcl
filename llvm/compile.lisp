(in-package :sb-c)

(defun compile-component-to-ir1 (component)

  ;; miscellaneous sanity checks
  ;;
  ;; FIXME: These are basically pretty wimpy compared to the checks done
  ;; by the old CHECK-IR1-CONSISTENCY code. It would be really nice to
  ;; make those internal consistency checks work again and use them.
  (aver-live-component component)
  (do-blocks (block component)
    (aver (eql (block-component block) component)))
  (dolist (lambda (component-lambdas component))
    ;; sanity check to prevent weirdness from propagating insidiously as
    ;; far from its root cause as it did in bug 138: Make sure that
    ;; thing-to-COMPONENT links are consistent.
    (aver (eql (lambda-component lambda) component))
    (aver (eql (node-component (lambda-bind lambda)) component)))

  (let* ((*component-being-compiled* component))

    ;; Record xref information before optimization. This way the
    ;; stored xref data reflects the real source as closely as
    ;; possible.
    (record-component-xrefs component)

    (ir1-phases component)

    (when *loop-analyze*
      (dfo-as-needed component)
      (find-dominators component)
      (loop-analyze component))

    #|
    (when (and *loop-analyze* *compiler-trace-output*)
      (labels ((print-blocks (block)
                 (format *compiler-trace-output* "    ~A~%" block)
                 (when (block-loop-next block)
                   (print-blocks (block-loop-next block))))
               (print-loop (loop)
                 (format *compiler-trace-output* "loop=~A~%" loop)
                 (print-blocks (loop-blocks loop))
                 (dolist (l (loop-inferiors loop))
                   (print-loop l))))
        (print-loop (component-outer-loop component))))
    |#

    ;; FIXME: What is MAYBE-MUMBLE for? Do we need it any more?
    (maybe-mumble "env ")
    (physenv-analyze component)
    (dfo-as-needed component)

    (delete-if-no-entries component)

;    (unless (eq (block-next (component-head component))
;                (component-tail component))
;      (%compile-component component)))

    )
  component)

(defun %compile-to-ir1 (lambda-expression
                 *compile-object*
                 &key
                 name
                 (path
                  ;; This magical idiom seems to be the appropriate
                  ;; path for compiling standalone LAMBDAs, judging
                  ;; from the CMU CL code and experiment, so it's a
                  ;; nice default for things where we don't have a
                  ;; real source path (as in e.g. inside CL:COMPILE).
                  '(original-source-start 0 0)))
  (when name
    (legal-fun-name-or-type-error name))
  (let* ((*lexenv* (make-lexenv
                    :policy *policy*
                    :handled-conditions *handled-conditions*
                    :disabled-package-locks *disabled-package-locks*))
         (*compiler-sset-counter* 0)
         (fun (make-functional-from-toplevel-lambda lambda-expression
                                                    :name name
                                                    :path path)))
    (locall-analyze-clambdas-until-done (list fun))

    (let ((components-from-dfo (find-initial-dfo (list fun))))
      (map 'list 'compile-component-to-ir1 components-from-dfo))))

(defun cleanup-after-compile-to-ir1 (components-from-dfo)
  (clear-constant-info)
  (mapc #'clear-ir1-info components-from-dfo)
  (clear-stuff))


(defun compile-to-ir1 (name definition &optional (*lexenv* (make-null-lexenv)))
  (with-compilation-values
    (with-compilation-unit ()
      ;; FIXME: These bindings were copied from SUB-COMPILE-FILE with
      ;; few changes. Once things are stable, the shared bindings
      ;; probably be merged back together into some shared utility
      ;; macro, or perhaps both merged into one of the existing utility
      ;; macros SB-C::WITH-COMPILATION-VALUES or
      ;; CL:WITH-COMPILATION-UNIT.
      (let* (;; FIXME: Do we need the *INFO-ENVIRONMENT* rebinding
             ;; here? It's a literal translation of the old CMU CL
             ;; rebinding to (OR *BACKEND-INFO-ENVIRONMENT*
             ;; *INFO-ENVIRONMENT*), and it's not obvious whether the
             ;; rebinding to itself is needed now that SBCL doesn't
             ;; need *BACKEND-INFO-ENVIRONMENT*.
             (*info-environment* *info-environment*)
             (form (get-lambda-to-compile definition))
             (*source-info* (make-lisp-source-info form :parent *source-info*))
             (*toplevel-lambdas* ())
             (*block-compile* nil)
             (*allow-instrumenting* nil)
             (*code-coverage-records* nil)
             (*code-coverage-blocks* nil)
             (*compiler-error-bailout*
              (lambda (&optional error)
                (declare (ignore error))
                (compiler-mumble
                 "~2&fatal error, aborting compilation~%")
                (return-from compile-to-ir1 (values nil t nil))))
             (*current-path* nil)
             (*last-source-context* nil)
             (*last-original-source* nil)
             (*last-source-form* nil)
             (*last-format-string* nil)
             (*last-format-args* nil)
             (*last-message-count* 0)
             (*last-error-context* nil)
             (*gensym-counter* 0)
             ;; KLUDGE: This rebinding of policy is necessary so that
             ;; forms such as LOCALLY at the REPL actually extend the
             ;; compilation policy correctly.  However, there is an
             ;; invariant that is potentially violated: future
             ;; refactoring must not allow this to be done in the file
             ;; compiler.  At the moment we're clearly alright, as we
             ;; call %COMPILE with a core-object, not a fasl-stream,
             ;; but caveat future maintainers. -- CSR, 2002-10-27
             (*policy* (lexenv-policy *lexenv*))
             ;; see above
             (*handled-conditions* (lexenv-handled-conditions *lexenv*))
             ;; ditto
             (*disabled-package-locks* (lexenv-disabled-package-locks *lexenv*))
             ;; FIXME: ANSI doesn't say anything about CL:COMPILE
             ;; interacting with these variables, so we shouldn't. As
             ;; of SBCL 0.6.7, COMPILE-FILE controls its verbosity by
             ;; binding these variables, so as a quick hack we do so
             ;; too. But a proper implementation would have verbosity
             ;; controlled by function arguments and lexical variables.
             (*compile-verbose* nil)
             (*compile-print* nil))
        (handler-bind (((satisfies handle-condition-p) #'handle-condition-handler))
          (clear-stuff)
          (find-source-paths form 0)
          (%compile-to-ir1 form (make-core-object)
                           :name name
                           :path '(original-source-start 0 0)))))))

