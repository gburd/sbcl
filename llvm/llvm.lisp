;; HACK! make sigabrt not abort.
(cffi:defcfun "undoably_install_low_level_interrupt_handler" :void
  (signal :int)
  (handler :pointer))

(undoably-install-low-level-interrupt-handler 6 (cffi:null-pointer))

(defun sigabrt-handler (signal info context)
  (declare (ignore signal info))
  (declare (type system-area-pointer context))
  (sb-sys:with-interrupts
         (error "sigabrt at #X~X"
                (with-alien ((context (* sb-sys:os-context-t) context))
                  (sb-sys:sap-int (sb-vm:context-pc context))))))
(sb-sys:enable-interrupt sb-posix:sigabrt #'sigabrt-handler)



(defun LispObjType ()
  (LLVMInt64TypeInContext *llvm-context*))

(defun define-support-fns (mod)
  (LLVMAddFunction mod "call_into_lisp"
                   (LLVMFunctionType* (LispObjType) (list (LispObjType) (LLVMPointerType (LispObjType) 0) (LLVMInt32TypeInContext *llvm-context*)) 0))
)
;  (LLVMAddGlobal mod (LLVMFunctionType* (LispObjType) (list (LLVMPointerType (LispObjType) 0)) 0)
;                 "call_into_lisp"))
;  (CLLLVM_LLVMParseAssemblyString
;"declare i64 @call_into_lisp(i64, i64*, i32)
;"
;     *jit-module* *llvm-context*))

;; Do it now!
(define-support-fns *jit-module*)
(LLVMDumpModule *jit-module*)

(defvar *lambda-var-hash*)

(defun llvm-compile (lambda)
  (let* ((component (first (sb-c::compile-to-ir1 nil lambda)))
         (fun (second (sb-c::component-lambdas component))))
    (build-function fun *jit-module-provider*)))

(defun build-function (fun mod-provider)
  (let* ((mod (CLLLVM_LLVMModuleProviderGetModule mod-provider))
         (n-args (length (sb-c::lambda-vars fun)))
         (fun-args (loop for n from 0 below n-args
                         collect (LispObjType)))
         (llfun (LLVMAddFunction mod "anonymous"
                               (LLVMFunctionType*
                                (LispObjType)
                                fun-args
                                0)))
         ;; From lambda-var -> llvm var
         (*lambda-var-hash* (make-hash-table :test 'eq))
;         (block-hash (make-hash-table :test 'eq))
         (builder (LLVMCreateBuilderInContext *llvm-context*)))
    (LLVMSetFunctionCallConv llfun (cffi:foreign-enum-value 'LLVMCallConv :LLVMCCallConv))
    (loop for node in (sb-c::lambda-vars fun)
          for n from 0
          do
          (setf (gethash node *lambda-var-hash*) (LLVMGetParam llfun n)))

    (let ((block (sb-c::ctran-block (sb-c::node-prev (sb-c::lambda-bind fun)))))
      (sb-c::do-blocks (block (sb-c::block-component block) :both)
        (setf (sb-c::block-flag block) nil))
      (labels ((walk (block)
                 (unless (sb-c::block-flag block)
                   (setf (sb-c::block-flag block) t)
                   (when (sb-c::block-start block)
                     (build-block llfun builder block))
                   (dolist (block (sb-c::block-succ block))
                     (walk block)))))
        (walk block)))

    (LLVMDumpValue llfun)
    llfun))

;; Run the code!
(defun run-fun (fun a b c)
  (let ((fun-ptr (LLVMGetPointerToGlobal *jit-execution-engine* fun)))
    (cffi:foreign-funcall-pointer fun-ptr () :int64 a :int64 b :int64 c :int64)))

(defun build-block (llfun builder block)
  (format t "block start~%")
  (let ((llblock (LLVMAppendBasicBlockInContext *llvm-context* llfun "blockname")))
    (LLVMPositionBuilderAtEnd builder llblock)
    (do ((ctran (sb-c::block-start block) (sb-c::node-next (sb-c::ctran-next ctran))))
        ((not ctran))
      (let ((node (sb-c::ctran-next ctran)))
        (format t "~s~%" node)
        (etypecase node
          ;; Don't do anything; this is entirely superfluous.
          (sb-c::bind nil)
          (sb-c::ref (llvm-convert-ref llfun builder node))
          (sb-c::combination (llvm-convert-combination llfun builder node))
          (sb-c::creturn (llvm-convert-return llfun builder node)))
        ))))

;;; Convert a REF node. The reference must not be delayed.
(defun llvm-convert-ref (llfun builder node)
  (declare (type sb-c::ref node))
  (let* ((lvar (sb-c::node-lvar node))
         (leaf (sb-c::ref-leaf node)))
    (etypecase leaf
      (sb-c::lambda-var
       (let ((llvm-var (gethash leaf *lambda-var-hash*)))
         (if (sb-c::lambda-var-indirect leaf)
             FIXME #|(vop value-cell-ref node block tn res)|#
             (setf (sb-c::lvar-info lvar) llvm-var))))
      (sb-c::constant
         FIXME #|(emit-move node block (constant-tn leaf) res)|#)
      (sb-c::functional
         FIXME #|(ir2-convert-closure node block leaf res)|#)
      (sb-c::global-var
         FIXME
       #|(let ((unsafe (policy node (zerop safety)))
             (name (leaf-source-name leaf)))
         (ecase (global-var-kind leaf)
           ((:special :unknown)
            (aver (symbolp name))
            (let ((name-tn (emit-constant name)))
              (if (or unsafe (info :variable :always-bound name))
                  (vop fast-symbol-value node block name-tn res)
                  (vop symbol-value node block name-tn res))))
           (:global
            (aver (symbolp name))
            (let ((name-tn (emit-constant name)))
              (if (or unsafe (info :variable :always-bound name))
                  (vop fast-symbol-global-value node block name-tn res)
                  (vop symbol-global-value node block name-tn res))))
           (:global-function
            (let ((fdefn-tn (make-load-time-constant-tn :fdefinition name)))
              (if unsafe
                  (vop fdefn-fun node block fdefn-tn res)
                  (vop safe-fdefn-fun node block fdefn-tn res))))))|#)
         ))
  (values))

(defun llvmconstify (type list)
  (map 'list (lambda (x) (LLVMConstInt type x 0))
       list))

(defun llvm-convert-combination (llfun builder node)
  (let* ((lvar (sb-c::node-lvar node))
         (arg-count (length (sb-c::combination-args node)))
         (arg-count-llc (LLVMConstInt (LLVMInt32TypeInContext *llvm-context*) arg-count 0))
         (arg-mem (LLVMBuildArrayAlloca builder (LispObjType)
                                      arg-count-llc "CIL-array")))
;    (setf (sb-c::lvar-info lvar) (sb-c::lvar-info (sb-c::combination-fun node)))
;    (return-from llvm-convert-combination nil)
    (loop for arg in (sb-c::combination-args node)
          for n from 0
          do
          (let ((GEP (LLVMBuildGEP* builder arg-mem (llvmconstify (LLVMInt32TypeInContext *llvm-context*) (list n)))))
            (LLVMBuildStore builder (sb-c::lvar-info arg) GEP)))

 ; pass array as pointer to first element.
    (let* ((arg-mem-ptr (LLVMBuildGEP* builder arg-mem (llvmconstify (LLVMInt32TypeInContext *llvm-context*) (list 0))))
           (call-into-lisp (LLVMGetNamedFunction *jit-module* "call_into_lisp"))
           (callee (sb-c::lvar-info (sb-c::combination-fun node))))
      (when (cffi:pointer-eq (cffi:null-pointer) call-into-lisp)
        (error "call-into-lisp not found!"))
      (setf (sb-c::lvar-info lvar)
            (LLVMBuildCall* builder call-into-lisp (list callee arg-mem-ptr arg-count-llc) "call_into_lisp")))))

(defun llvm-convert-return (llfun builder node)
  (LLVMBuildRet builder (sb-c::lvar-info (sb-c::return-result node))))



#|
(defun print-nodes (fun block)
  (do ((ctran (block-start block) (node-next (ctran-next ctran))))
      ((not ctran))
    (let ((node (ctran-next ctran)))
      (format t "~3D>~:[    ~;~:*~3D:~] "
              (cont-num ctran)
              (when (and (valued-node-p node) (node-lvar node))
                (cont-num (node-lvar node))))
      (etypecase node
        (ref (print-leaf (ref-leaf node)))
        (basic-combination
           (let ((kind (basic-combination-kind node)))
             (format t "~(~A~A ~A~) "
                     (if (node-tail-p node) "tail " "")
                     kind
                     (type-of node))
             (print-lvar (basic-combination-fun node))
             (dolist (arg (basic-combination-args node))
               (if arg
                   (print-lvar arg)
                   (format t "<none> ")))))
        (cset
           (write-string "set ")
           (print-leaf (set-var node))
           (write-char #\space)
           (print-lvar (set-value node)))
        (cif
           (write-string "if ")
           (print-lvar (if-test node))
           (print-ctran (block-start (if-consequent node)))
           (print-ctran (block-start (if-alternative node))))
        (bind
           (write-string "bind ")
           (print-leaf (bind-lambda node))
           (when (functional-kind (bind-lambda node))
             (format t " ~S ~S" :kind (functional-kind (bind-lambda node)))))
        (creturn
           (write-string "return ")
           (print-lvar (return-result node))
           (print-leaf (return-lambda node)))
        (entry
           (let ((cleanup (entry-cleanup node)))
             (case (cleanup-kind cleanup)
               ((:dynamic-extent)
                  (format t "entry DX~{ v~D~}"
                          (mapcar (lambda (lvar-or-cell)
                                    (if (consp lvar-or-cell)
                                        (cons (car lvar-or-cell)
                                              (cont-num (cdr lvar-or-cell)))
                                        (cont-num lvar-or-cell)))
                                  (cleanup-info cleanup))))
               (t
                  (format t "entry ~S" (entry-exits node))))))
        (exit
           (let ((value (exit-value node)))
             (cond (value
                    (format t "exit ")
                    (print-lvar value))
               ((exit-entry node)
                (format t "exit <no value>"))
               (t
                (format t "exit <degenerate>")))))
        (cast
           (let ((value (cast-value node)))
             (format t "cast v~D ~A[~S -> ~S]" (cont-num value)
                     (if (cast-%type-check node) #\+ #\-)
                     (cast-type-to-check node)
                     (cast-asserted-type node)))))
      (pprint-newline :mandatory)))
|#
