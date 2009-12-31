(eval-when (:compile-toplevel :load-toplevel :execute)
  (use-package :llvm))

(declaim (optimize (debug 3)))

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

;; END HACK

(cffi::defcallback intern :intptr ((name :string) (package :string))
  (sb-kernel:get-lisp-obj-address (intern name package)))

(cffi::defcallback symbol-function :intptr ((symbol :intptr))
  (sb-kernel:get-lisp-obj-address (symbol-function (sb-kernel:make-lisp-obj symbol))))

(defun LispObjType ()
  (LLVMInt64Type))

(defun declare-global-var (mod name type &key value thread-local constant linkage)
  (let ((previous-global (LLVMGetNamedGlobal mod name)))
    (if (cffi:pointer-eq previous-global (cffi:null-pointer))
        (let ((global (LLVMAddGlobal mod type name)))
          (when value
            (LLVMSetInitializer global (LLVMConstInt type value nil)))
          (when constant
            (LLVMSetGlobalConstant global t))
          (when thread-local
            (LLVMSetThreadLocal global t))
          (when linkage
            (LLVMSetLinkage global linkage))))))

(defun declare-intrinsic-function (mod name ret-type arg-types &key global-mapping attrs)
  (let ((previous-fun (LLVMGetNamedFunction mod name)))
    (if (cffi:pointer-eq previous-fun (cffi:null-pointer))
        (let ((function (LLVMAddFunction mod name
                                         (LLVMFunctionType ret-type arg-types nil))))
          (LLVMSetFunctionCallConv function (cffi:foreign-enum-value 'LLVMCallConv :LLVMCCallConv))
          (LLVMSetLinkage function :LLVMExternalLinkage)
          (assert (LLVMIsDeclaration function))
          (when (eql (mismatch "llvm." name) 5) ; name starts with llvm.
            (assert (/= 0 (LLVMGetIntrinsicID function))))
          (when global-mapping
            (LLVMAddGlobalMapping *jit-execution-engine*
                                  function
                                  global-mapping))
          (dolist (attr attrs)
            (LLVMAddFunctionAttr function attr))
          function)
        previous-fun)))

(defun define-support-fns (mod)
  (declare-intrinsic-function mod "intern"
                              (LispObjType) (list (LLVMPointerType (LLVMInt8Type) 0)
                                                  (LLVMPointerType (LLVMInt8Type) 0))
                              :global-mapping (cffi::callback intern))
  (declare-intrinsic-function mod "symbol-function"
                              (LispObjType) (list (LispObjType))
                              :global-mapping (cffi::callback symbol-function))
  (declare-intrinsic-function mod "llvm.atomic.load.sub.i64.p0i64"
                              (LLVMInt64Type)
                              (list (LLVMPointerType (LLVMInt64Type) 0) (LLVMInt64Type)))
  (declare-global-var mod "SBCL_nil" (LispObjType) :constant t :value (sb-kernel:get-lisp-obj-address nil))
  ;; Comes from SBCL runtime.
;  (declare-global-var mod "current_thread" (LispObjType) :thread-local t :linkage :LLVMExternalLinkage)
  (declare-global-var mod "specials" (LLVMInt32Type) :constant t)
  (declare-intrinsic-function mod "call_into_lisp"
    (LispObjType)
    (list (LispObjType) (LLVMPointerType (LispObjType) 0) (LLVMInt32Type)))
  (declare-intrinsic-function mod "alloc"
    (LLVMPointerType (LispObjType) 0)
    (list (LLVMInt64Type)))
  (declare-intrinsic-function mod "do_pending_interrupt"
    (LLVMVoidType)
    nil)
  (declare-intrinsic-function mod "pthread_getspecific"
    (LLVMPointerType (LLVMInt8Type) 0)
    (list (LLVMInt32Type)) :attrs '(:LLVMNoUnwindAttribute :LLVMReadNoneAttribute))
  ;; Function to get the TLS data. It's a bit odd that SBCL isn't using native TLS on
  ;; linux, but lucky for me, because LLVM's JIT doesn't support TLS yet.
  (CLLLVM_LLVMParseAssemblyString
"define i64* @get_thread_data() nounwind readnone {
start:
  %0 = load i32* @specials
  %1 = call i8* @pthread_getspecific(i32 %0)
  %2 = bitcast i8* %1 to i64*
  ret i64* %2
}
" *jit-module* *llvm-context*))




;  (LLVMAddGlobal mod (LLVMFunctionType (LispObjType) (list (LLVMPointerType (LispObjType) 0)) nil)
;                 "call_into_lisp"))
;  (CLLLVM_LLVMParseAssemblyString
;"declare i64 @call_into_lisp(i64, i64*, i32)
;"
;     *jit-module* *llvm-context*))

;; Do it now!
(define-support-fns *jit-module*)
;;(LLVMDumpModule *jit-module*)


;; Function to dump the IR1 nodes of a lambda expression, for debugging.
(defun dump-ir1 (lambda)
  (let* ((component (first (sb-c::compile-to-ir1 nil lambda)))
         (fun (second (sb-c::component-lambdas component))))
    (let ((block (sb-c::ctran-block (sb-c::node-prev (sb-c::lambda-bind fun)))))
      (sb-c::do-blocks (block (sb-c::block-component block) :both)
        (setf (sb-c::block-flag block) nil))
      (labels ((walk (block)
                 (unless (sb-c::block-flag block)
                   (setf (sb-c::block-flag block) t)
                   (when (sb-c::block-start block)
                     (dump-block block))
                   (dolist (block (sb-c::block-succ block))
                     (walk block)))))
        (walk block)))))

(defun dump-block (block)
  (format t "block start ~s~%" (sb-c::block-number block))
  (do ((ctran (sb-c::block-start block) (sb-c::node-next (sb-c::ctran-next ctran))))
      ((not ctran))
    (let ((node (sb-c::ctran-next ctran)))
      (format t "~s~%" node))))

;; Now, the actual LLVM compiler

(defmacro with-entry-block-builder ((builder llfun) &body body)
  (let ((entry-block-v (gensym "entry-block")))
    `(let ((,builder (LLVMCreateBuilder))
           (,entry-block-v (LLVMGetEntryBasicBlock ,llfun)))
       (LLVMPositionBuilderAtEnd ,builder ,entry-block-v)
       (prog1
           (progn ,@body)
         (LLVMDisposeBuilder ,builder)))))

;; Main entry point
(defun llvm-compile (lambda)
  (let* ((component (first (sb-c::compile-to-ir1 nil lambda)))
         (fun (second (sb-c::component-lambdas component))))
    (build-function fun *jit-module-provider*)))

(defun unboxed-type (ctype)
  (cond
    ((csubtypep ctype '(unsigned-byte 64))
     :unsigned-word)
    ((csubtypep ctype '(signed-byte 64))
     :signed-word)
    ;; FIXME: floats, whatever else we want unboxed...
    (t nil)))

    
(defun build-function (fun mod-provider)
  (let* ((mod (CLLLVM_LLVMModuleProviderGetModule mod-provider))
         (n-args (length (sb-c::lambda-vars fun)))
         (fun-args (loop for n from 0 below n-args
                         collect (LispObjType)))
         (llfun (LLVMAddFunction mod "anonymous"
                               (LLVMFunctionType
                                (LispObjType)
                                fun-args
                                nil)))
         (setup-block (LLVMAppendBasicBlock llfun "setup"))
         (builder (LLVMCreateBuilder)))
    (LLVMSetFunctionCallConv llfun (cffi:foreign-enum-value 'LLVMCallConv :LLVMCCallConv))

    (with-entry-block-builder (builder llfun)
      (loop for node in (sb-c::lambda-vars fun)
            for n from 0
            do
            (let ((param-alloca (LLVMBuildAlloca builder (LispObjType) "arg")))
              (setf (sb-c::leaf-info node) param-alloca)
              (LLVMBuildStore builder (LLVMGetParam llfun n) param-alloca))))

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
        (walk block))
      (LLVMPositionBuilderAtEnd builder setup-block)
      (LLVMBuildBr builder (llvm-ensure-block llfun block)))

    (format t ";; Pre-optimization:~%")
    (LLVMDumpValue llfun)
    ;;(LLVMVerifyModule mod :LLVMPrintMessageAction (cffi:null-pointer))
    (LLVMRunFunctionPassManager *jit-pass-manager* llfun)
    (format t ";; Post-optimization:~%")
    (LLVMDumpValue llfun)

    llfun))

;; Call this to run your function!
(defmacro run-fun (fun &rest args)
  (let ((ffp-args (loop for arg in args
                        collect :intptr
                        collect `(sb-kernel:get-lisp-obj-address ,arg)))
        (fun-ptr-v (gensym "fun-ptr")))
  `(let ((,fun-ptr-v (LLVMGetPointerToGlobal *jit-execution-engine* ,fun)))
     (sb-kernel:make-lisp-obj (cffi:foreign-funcall-pointer ,fun-ptr-v () ,@ffp-args :intptr)))))


;;;; Utility functions...

(defun ptr-to-lispobj (builder ptr lowtag)
  (LLVMBuildAdd builder (LLVMBuildPtrToInt builder ptr (LispObjType) "") (LLVMConstInt (LLVMInt64Type) lowtag nil) ""))

(defun fixnumize (val)
  (LLVMConstInt (LispObjType) (* val 8) nil)) ;; FIXME: hardcoded 8...

(defun LLVMBuildGEP* (builder ptr indices name)
  (let ((type (LLVMInt32Type)))
    (LLVMBuildGEP builder ptr
                  (map 'list (lambda (x) (LLVMConstInt type x nil)) indices)
                  name)))

(defun llvm-ensure-block (llfun block)
  "Ensure that the given IR1 block has an associated LLVM block, and return it."
  (let ((existing-block (sb-c::block-info block)))
    (if existing-block
        existing-block
        (setf (sb-c::block-info block)
              (LLVMAppendBasicBlock llfun (format nil "block~d" (sb-c::block-number block)))))))


(defun build-alloca-in-entry (llfun name)
  (with-entry-block-builder (builder llfun)
    (LLVMBuildAlloca builder (LispObjType) name)))

(defun llvm-ensure-lvar (llfun lvar)
  "Ensure that the given IR1 lvar object has an associated LLVM variable, and return it"
  (let ((existing-lvar (sb-c::lvar-info lvar)))
    (if existing-lvar
        existing-lvar
        (setf (sb-c::lvar-info lvar) (build-alloca-in-entry llfun "lvar")))))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *llvm-primitives* (make-hash-table :test 'eq)))

(defmacro def-llvmfun (name args &body body)
  "Sorta the equivalent of defining a VOP.

   NAME should be a known function, and your function will be called to do something
   special instead of building a full call to that function."
  (let ((real-name (intern (concatenate 'string "LLVMFUN-" (symbol-name name)))))
    `(progn
       (defun ,real-name
           ,args
         ,@body)
       (setf (gethash ',name *llvm-primitives*) (function ,real-name)))))

;;;; Creating blocks...

(defun finish-block (llfun builder block)
  (let* ((last (sb-c::block-last block))
         (succ (sb-c::block-succ block)))
    (unless (or (sb-c::if-p last) (sb-c::return-p last))
      (assert (sb-c::singleton-p succ))
      (let ((target (first succ)))
        (cond ((eq target (sb-c::component-tail (sb-c::block-component block)))
               ;; component-tail isn't a real block, so don't emit a branch to it.
               ;; This location ought to be unreachable, so tell LLVM that.
               (LLVMBuildUnreachable builder))
              (t (LLVMBuildBr builder (llvm-ensure-block llfun target))))))))

(defun build-block (llfun builder block)
  (format t "block start ~s~%" (sb-c::block-number block))
  (let ((llblock (llvm-ensure-block llfun block)))
    (LLVMPositionBuilderAtEnd builder llblock)
    (do ((ctran (sb-c::block-start block) (sb-c::node-next (sb-c::ctran-next ctran))))
        ((not ctran))
      (let ((node (sb-c::ctran-next ctran)))
        (format t "~s~%" node)
        (etypecase node
          (sb-c::bind nil) ;; Don't do anything; bind is entirely superfluous.
          (sb-c::ref (llvm-convert-ref llfun builder node))
          (sb-c::combination
             (let ((fun (sb-c::ref-leaf (sb-c::lvar-uses (sb-c::combination-fun node)))))
               (if (and (sb-c::functional-p fun) (eq (sb-c::functional-kind fun) :let)) ; mv-let, assignment?
                   (llvm-convert-let llfun builder node)
                   ;; FIXME: this data should really go into the fun-info struct from
                   ;; combination-fun-info, but for expediency, use a separate datastore
                   ;; for the moment.
                   (let ((llvm-primitive (gethash (sb-c::leaf-source-name fun) *llvm-primitives*)))
                     (if llvm-primitive
                         (llvm-convert-knowncombination llfun builder node llvm-primitive)
                         (llvm-convert-combination llfun builder node))))))
          (sb-c::creturn (llvm-convert-return llfun builder node))
          (sb-c::cif (llvm-convert-if llfun builder node))
          (sb-c::cset (llvm-convert-set llfun builder node)))
        ))
    (finish-block llfun builder block)))

(defmacro with-load-time-builder (builder &body body)
  `(let ((,builder *ltv-builder*))
     ,@body))


;;;; "Constant" support (many lisp constants are not LLVM constants, but rather set at load-time)

(defun llvm-emit-global-string (mod str)
  (let* ((ll-str (LLVMConstString str nil))
         (global (LLVMAddGlobal mod (LLVMTypeOf ll-str) ".str")))
      (LLVMSetInitializer global ll-str)
      (LLVMSetGlobalConstant global t)
      global))

(defun llvm-emit-symbol-ref (builder value)
  ;; Check for staticly-defined symbols?
  (let* ((global (LLVMAddGlobal *jit-module* (LispObjType) (symbol-name value)))
         (name-var (llvm-emit-global-string *jit-module* (symbol-name value)))
         (package-name-var (llvm-emit-global-string *jit-module* (package-name (symbol-package value)))))
    (LLVMSetLinkage global :LLVMInternalLinkage)
    (LLVMSetInitializer global (LLVMConstInt (LispObjType) 0 nil))
    (let ((lt-builder builder)) ;with-load-time-builder (lt-builder)
      (LLVMBuildStore lt-builder
                      (LLVMBuildCall lt-builder (LLVMGetNamedFunction *jit-module* "intern")
                                     (list
                                      (LLVMBuildGEP* lt-builder name-var (list 0 0) "")
                                      (LLVMBuildGEP* lt-builder package-name-var (list 0 0) ""))
                                     "intern")
                      global))
    (LLVMBuildLoad builder global "symbol")))

(defun llvm-emit-symbol-function (builder value)
  (LLVMBuildCall builder (LLVMGetNamedFunction *jit-module* "symbol-function")
                 (list
                  (llvm-emit-symbol-ref builder value))
                 "symbol-function"))

(defun llvm-emit-constant (builder leaf)
  (let ((value (sb-c::constant-value leaf)))
    (etypecase value
      ;; most-*-fixnum should have sb!xc: prefix
      ((integer #.most-negative-fixnum #.most-positive-fixnum)
         (fixnumize value))
      (integer
         (FIXME-BIGINT))
      (character
         (FIXME-CHARACTER))
      (symbol
         (llvm-emit-symbol-ref builder value))
#|
      (when (static-symbol-p value)
        (sc-number-or-lose 'immediate)))
    (single-float
     (sc-number-or-lose
      (if (eql value 0f0) 'fp-single-zero 'fp-single-immediate)))
    (double-float
     (sc-number-or-lose
      (if (eql value 0d0) 'fp-double-zero 'fp-double-immediate)))
    ((complex single-float)
     (sc-number-or-lose
      (if (eql value #c(0f0 0f0))
          'fp-complex-single-zero
          'fp-complex-single-immediate)))
    ((complex double-float)
     (sc-number-or-lose
      (if (eql value #c(0d0 0d0))
          'fp-complex-double-zero
          'fp-complex-double-immediate)))|#)
    ))

;;; Convert a REF node. The reference must not be delayed.
(defun llvm-convert-ref (llfun builder node)
  (declare (type sb-c::ref node))
  (let* ((lvar (sb-c::node-lvar node))
         (leaf (sb-c::ref-leaf node))
         (val
          (etypecase leaf
            (sb-c::lambda-var
               (let ((llvm-var (sb-c::leaf-info leaf)))
                 (if (sb-c::lambda-var-indirect leaf)
                     (FIXME) #|(vop value-cell-ref node block tn res)|#
                     (LLVMBuildLoad builder llvm-var ""))))
            (sb-c::constant
               (or (sb-c::leaf-info leaf)
                   (llvm-emit-constant builder leaf)))
            (sb-c::functional
               (if (eq (sb-c::functional-kind leaf) :let) ;; mv-let, assignment?
                   (return-from llvm-convert-ref nil) ;; Don't need to store anything
                   (FIXME-FUNCTIONAL) #|(ir2-convert-closure node block leaf res)|#))
            (sb-c::global-var
               (let ((unsafe (sb-c::policy node (zerop safety)))
                     (name (sb-c::leaf-source-name leaf)))
                 (declare (ignore unsafe))
                 (ecase (sb-c::global-var-kind leaf)
                   ((:special :unknown)
                      #|(aver (symbolp name))
                      (let ((name-tn (emit-constant name)))
                      (if (or unsafe (info :variable :always-bound name))
                      (vop fast-symbol-value node block name-tn res)
                      (vop symbol-value node block name-tn res)))|#)
                   (:global
                      #|(aver (symbolp name))
                      (let ((name-tn (emit-constant name)))
                      (if (or unsafe (info :variable :always-bound name))
                      (vop fast-symbol-global-value node block name-tn res)
                      (vop symbol-global-value node block name-tn res)))|#)
                   (:global-function
                      (llvm-emit-symbol-function builder name)
                      #|(let ((fdefn-tn (make-load-time-constant-tn :fdefinition name)))
                      (if unsafe
                      (vop fdefn-fun node block fdefn-tn res)
                      (vop safe-fdefn-fun node block fdefn-tn res)))|#))))
            )))
    (assert val)
;    (print (CLLLVM_LLVMDumpValueToString val))
;    (print (CLLLVM_LLVMDumpTypeToString (LLVMTypeOf (llvm-ensure-lvar llfun lvar))))
    ;; Store the value into the lvar.
    (LLVMBuildStore builder val (llvm-ensure-lvar llfun lvar)))
  (values))

(defun llvm-convert-let (llfun builder node)
  (let ((fun (sb-c::ref-leaf (sb-c::lvar-uses (sb-c::combination-fun node))))
        (args (sb-c::combination-args node)))
    (loop for node in (sb-c::lambda-vars fun)
          for arg in args
          for n from 0
          do
          (let ((param-alloca (build-alloca-in-entry llfun "let-var")))
            (setf (sb-c::leaf-info node) param-alloca)
            (LLVMBuildStore builder (LLVMBuildLoad builder (llvm-ensure-lvar llfun arg) "")
                            param-alloca)))))

(defun llvm-convert-combination (llfun builder node)
  (let* ((lvar (sb-c::node-lvar node))
         (arg-count (length (sb-c::combination-args node)))
         (arg-count-llc (LLVMConstInt (LLVMInt32Type) arg-count 0))
         (arg-mem (LLVMBuildArrayAlloca builder (LispObjType)
                                      arg-count-llc "CIL-array")))
    (loop for arg in (sb-c::combination-args node)
          for n from 0
          do
          (let ((GEP (LLVMBuildGEP* builder arg-mem (list n) "")))
            (LLVMBuildStore builder (LLVMBuildLoad builder (llvm-ensure-lvar llfun arg) "") GEP)))

    ;; BuildGEP is because we pass array as pointer to first element.
    (let* ((arg-mem-ptr (LLVMBuildGEP* builder arg-mem (list 0) ""))
           (call-into-lisp (LLVMGetNamedFunction *jit-module* "call_into_lisp"))
           (callee (LLVMBuildLoad builder (llvm-ensure-lvar llfun (sb-c::combination-fun node)) "")))
      (when (cffi:pointer-eq (cffi:null-pointer) call-into-lisp)
        (error "call-into-lisp not found!"))
      (let ((call-result (LLVMBuildCall builder call-into-lisp
                                        (list callee arg-mem-ptr arg-count-llc) "call_into_lisp")))
        ;; When lvar exists, store result of call into it.
        (when lvar
          (LLVMBuildStore builder call-result (llvm-ensure-lvar llfun lvar)))))))

(defun llvm-convert-knowncombination (llfun builder node primitivefun)
  (let* ((lvar (sb-c::node-lvar node))
         (args (sb-c::combination-args node))
         (call-result (funcall primitivefun llfun builder args)))
    ;; When lvar exists, store result of call into it.
    (when lvar
      (LLVMBuildStore builder call-result (llvm-ensure-lvar llfun lvar)))))

(defun llvm-convert-return (llfun builder node)
;  (print (sb-c::lvar-info (sb-c::return-result node)))
  (LLVMBuildRet builder (LLVMBuildLoad builder (llvm-ensure-lvar llfun (sb-c::return-result node)) "")))


(defun llvm-convert-if (llfun builder node)
  (LLVMBuildCondBr builder
                   (LLVMBuildICmp builder :LLVMIntNE
                                  (LLVMBuildLoad builder (llvm-ensure-lvar llfun (sb-c::if-test node)) "")
                                  (LLVMBuildLoad builder (LLVMGetNamedGlobal *jit-module* "SBCL_nil")
                                                                 "")
                                  "nil?")
                   (llvm-ensure-block llfun (sb-c::if-consequent node))
                   (llvm-ensure-block llfun (sb-c::if-alternative node))))

(defun llvm-convert-set (llfun builder node)
  (let* ((lvar (sb-c::node-lvar node))
         (leaf (sb-c::set-var node))
         (val (sb-c::set-value node))
         (ll-val (LLVMBuildLoad builder (llvm-ensure-lvar llfun val) "")))
    (etypecase leaf
      (sb-c::lambda-var
         (let ((llvm-var (sb-c::leaf-info leaf)))
           (if (sb-c::lambda-var-indirect leaf)
               (FIXME) #|(vop value-cell-ref node block tn res)|#
               (LLVMBuildStore builder ll-val llvm-var))))
      (sb-c::global-var
         (ecase (sb-c::global-var-kind leaf)
           ((:special)
              (FIXME) #|(vop set node block (emit-constant (leaf-source-name leaf)) val)|#)
           ((:global)
              (FIXME) #|(vop %set-symbol-global-value node
              block (emit-constant (leaf-source-name leaf)) val)|#))))

    ;; *Also* store into the target lvar of this set node.
    (when lvar
      (LLVMBuildStore builder ll-val (llvm-ensure-lvar llfun lvar)))))




(defun get-current-thread (builder)
  (LLVMBuildCall builder
                 (LLVMGetNamedFunction *jit-module* "get_thread_data")
                 nil ""))

;; FIXME: I don't really want or need to use an atomic op here, what I *really* need is an
;; atomic-against-signal operation.  On X86/X86-64, the tomic sub will by accident do the
;; right thing, since it emits a single load/modify/write LOCK SUB instruction. It might
;; make sense to just emit asm here, but LLVM's JIT doesn't deal with inline
;; target-specific asm at the moment, unfortunately.
(defmacro with-pseudo-atomic ((llfun builder) &body body)
  ;; Store 2 (arbitrary-but-not-1 value) in *pseudo-atomic-bits*
  `(progn
     (LLVMBuildStore ,builder
                     (fixnumize 2)
                     (LLVMBuildGEP* ,builder (get-current-thread ,builder) (list sb-vm::thread-pseudo-atomic-bits-slot) ""))
     ;; Run p-a-protected body
     (prog1
         (progn ,@body)
       ;; Check if we were interrupted
       (let ((orig-value (LLVMBuildCall ,builder
                                        (LLVMGetNamedFunction *jit-module* "llvm.atomic.load.sub.i64.p0i64")
                                        (list (LLVMBuildGEP* ,builder (get-current-thread ,builder) (list sb-vm::thread-pseudo-atomic-bits-slot) "")
                                              (fixnumize 2))
                                        ""))
             (do-interruption-block (LLVMAppendBasicBlock ,llfun "do-interruption"))
             (continue-block (LLVMAppendBasicBlock ,llfun "continue")))
         ;; If we were, ...
         (LLVMBuildCondBr ,builder
                          (LLVMBuildICmp ,builder :LLVMIntEQ orig-value (fixnumize 2) "")
                          do-interruption-block
                          continue-block)
         ;; Handle the interruption.
         (LLVMPositionBuilderAtEnd ,builder do-interruption-block)
         (LLVMBuildCall ,builder (LLVMGetNamedFunction *jit-module* "do_pending_interrupt")
                        nil "")
         (LLVMBuildBr ,builder continue-block)

         ;; Otherwise, or then, ...continue with the rest of our code
         (LLVMPositionBuilderAtEnd ,builder continue-block)))))

(def-llvmfun cons (llfun builder args)
  (assert (= (length args) 2))
  (with-pseudo-atomic (llfun builder)
    (let* ((new-mem (LLVMBuildCall builder (LLVMGetNamedFunction *jit-module* "alloc")
                                   (list (LLVMConstInt (LLVMInt64Type) 16 nil)) ;; FIXME: 16 is number of bytes for a cons
                                   "")))
      (LLVMBuildStore builder (LLVMBuildLoad builder (llvm-ensure-lvar llfun (first args)) "")
                      (LLVMBuildGEP* builder new-mem (list sb-vm::cons-car-slot) ""))
      (LLVMBuildStore builder (LLVMBuildLoad builder (llvm-ensure-lvar llfun (second args)) "")
                      (LLVMBuildGEP* builder new-mem (list sb-vm::cons-cdr-slot) ""))
      ;; returns:
      (ptr-to-lispobj builder new-mem sb-vm::list-pointer-lowtag))))

