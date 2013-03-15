;;; Basics

(defstruct xxx yyy)

(macrolet ((test (init op)
             `(with-test (:name (:cas :basics ,op))
                (let ((x ,init)
                      (y (list 'foo))
                      (z (list 'bar)))
                  (assert (eql nil (compare-and-swap (,op x) nil y)))
                  (assert (eql y (compare-and-swap (,op x) nil z)))
                  (assert (eql y (,op x)))
                  (let ((x "foo"))
                    (multiple-value-bind (res err)
                        (ignore-errors (compare-and-swap (,op x) nil nil))
                      (unless (not res)
                        (error "Wanted NIL and type-error, got: ~S" res))
                      (assert (typep err 'type-error))))))))
  (test (cons nil :no) car)
  (test (cons nil :no) first)
  (test (cons :no nil) cdr)
  (test (cons :no nil) rest)
  (test '.foo. symbol-plist)
  (test (progn (set '.bar. nil) '.bar.) symbol-value)
  (test (make-xxx) xxx-yyy))

(defvar *foo*)

;;; thread-local bindings

(with-test (:name (:cas :tls))
  (let ((*foo* 42))
    (let ((*foo* nil))
      (assert (eql nil (compare-and-swap (symbol-value '*foo*) nil t)))
      (assert (eql t (compare-and-swap (symbol-value '*foo*) nil :foo)))
      (assert (eql t *foo*)))
    (assert (eql 42 *foo*))))

;;; unbound symbols + symbol-value

(assert (not (boundp '*foo*)))

(with-test (:name (:cas :unbound))
  (multiple-value-bind (res err)
      (ignore-errors (compare-and-swap (symbol-value '*foo*) nil t))
    (assert (not res))
    (assert (typep err 'unbound-variable))))

(defvar *bar* t)

(with-test (:name (:cas :unbound 2))
  (let ((*bar* nil))
    (makunbound '*bar*)
    (multiple-value-bind (res err)
        (ignore-errors (compare-and-swap (symbol-value '*bar*) nil t))
      (assert (not res))
      (assert (typep err 'unbound-variable)))))

;;; SVREF

(defvar *v* (vector 1))

;; basics
(with-test (:name (:cas :svref))
  (assert (eql 1 (compare-and-swap (svref *v* 0) 1 2)))
  (assert (eql 2 (compare-and-swap (svref *v* 0) 1 3)))
  (assert (eql 2 (svref *v* 0))))

;; bounds
(with-test (:name (:cas :svref :bounds))
  (multiple-value-bind (res err)
      (ignore-errors (compare-and-swap (svref *v* -1) 1 2))
    (assert (not res))
    (assert (typep err 'type-error)))
  (multiple-value-bind (res err)
      (ignore-errors (compare-and-swap (svref *v* 1) 1 2))
    (assert (not res))
    (assert (typep err 'type-error))))

;; type of the first argument
(with-test (:name (:cas :svref :type))
  (multiple-value-bind (res err)
      (ignore-errors (compare-and-swap (svref "foo" 1) 1 2))
    (assert (not res))
    (assert (typep err 'type-error))))

;; Check that we don't modify constants
(defconstant +a-constant+ 42)
(with-test (:name (:cas :symbol-value :constant-modification))
  (assert
   (eq :error
       (handler-case
           (sb-ext:compare-and-swap (symbol-value '+a-constant+) 42 13)
         (error () :error))))
  (let ((name '+a-constant+))
    (assert
     (eq :error
         (handler-case
             (sb-ext:compare-and-swap (symbol-value name) 42 13)
           (error () :error))))))

;; Check that we don't mess declaimed types
(declaim (boolean *a-boolean*))
(defparameter *a-boolean* t)
(with-test (:name (:cas :symbol-value :type-checking))
  (assert
   (eq :error
       (handler-case
           (sb-ext:compare-and-swap (symbol-value '*a-boolean*) t 42)
         (error () :error))))
  (let ((name '*a-boolean*))
    (assert
     (eq :error
         (handler-case
             (sb-ext:compare-and-swap (symbol-value name) t 42)
           (error () :error))))))

;;;; ATOMIC-INCF and ATOMIC-DECF (we should probably rename this file atomic-ops...)

(defstruct box
  (word 0 :type sb-vm:word))

;; Have the following tests check that CAS access to the superclass
;; works in the presence of a subclass sharing the conc-name.
(defstruct (subbox (:include box) (:conc-name "BOX-")))

(defun inc-box (box n)
  (declare (fixnum n) (box box))
  (loop repeat n
        do (sb-ext:atomic-incf (box-word box))))

(defun dec-box (box n)
  (declare (fixnum n) (box box))
  (loop repeat n
        do (sb-ext:atomic-decf (box-word box))))

(with-test (:name :atomic-incf/decf)
  (let ((box (make-box)))
    (inc-box box 10000)
    (assert (= 10000 (box-word box)))
    (dec-box box 10000)
    (assert (= 0 (box-word box)))))

(with-test (:name :atomic-incf-wraparound)
  (let ((box (make-box :word (1- (ash 1 sb-vm:n-word-bits)))))
    (sb-ext:atomic-incf (box-word box) 2)
    (assert (= 1 (box-word box)))))

(with-test (:name :atomic-decf-wraparound)
  (let ((box (make-box :word 0)))
    (sb-ext:atomic-decf (box-word box) 2)
    (assert (= (- (ash 1 sb-vm:n-word-bits) 2) (box-word box)))))

#+sb-thread
(with-test (:name (:atomic-incf/decf :threads))
  (let* ((box (make-box))
         (threads (loop repeat 64
                        collect (sb-thread:make-thread (lambda ()
                                                         (inc-box box 1000)
                                                         (dec-box box 10000)
                                                         (inc-box box 10000)
                                                         (dec-box box 1000))
                                                       :name "inc/dec thread"))))
    (mapc #'sb-thread:join-thread threads)
    (assert (= 0 (box-word box)))))

;;; STANDARD-INSTANCE-ACCESS, FUNCALLABLE-STANDARD-INSTANCE-ACCESS

(defclass sia-cas-test ()
  ((a :initarg :a)
   (b :initarg :b)))

(with-test (:name (:cas :standard-instance-access))
  (flet ((slot-loc (slot class)
           (sb-mop:slot-definition-location
            (find slot (sb-mop:class-slots class) :key #'sb-mop:slot-definition-name))))
    (let* ((class (find-class 'sia-cas-test))
           (instance (make-instance class :a 'a :b 'b))
           (a-loc (slot-loc 'a class))
           (b-loc (slot-loc 'b class)))
      (assert (eq 'a (slot-value instance 'a)))
      (assert (eq 'a (compare-and-swap (sb-mop:standard-instance-access instance a-loc)
                                       'x 'oops)))
      (assert (eq 'a (sb-mop:standard-instance-access instance a-loc)))
      (assert (eq 'a (compare-and-swap (sb-mop:standard-instance-access instance a-loc)
                                       'a 'a2)))
      (assert (eq 'a2 (sb-mop:standard-instance-access instance a-loc)))
      (assert (eq 'a2 (slot-value instance 'a)))
      (assert (eq 'b (slot-value instance 'b)))
      (assert (eq 'b (sb-mop:standard-instance-access instance b-loc))))))

(defclass fia-cas-test (sb-mop:funcallable-standard-object)
  ((a :initarg :a)
   (b :initarg :b))
  (:metaclass sb-mop:funcallable-standard-class))

(with-test (:name (:cas :standard-instance-access))
  (flet ((slot-loc (slot class)
           (sb-mop:slot-definition-location
            (find slot (sb-mop:class-slots class) :key #'sb-mop:slot-definition-name))))
    (let* ((class (find-class 'fia-cas-test))
           (instance (make-instance class :a 'a :b 'b))
           (a-loc (slot-loc 'a class))
           (b-loc (slot-loc 'b class)))
      (sb-mop:set-funcallable-instance-function instance (lambda () :ok))
      (eq :ok (funcall instance))
      (assert (eq 'a (slot-value instance 'a)))
      (assert (eq 'a (compare-and-swap
                      (sb-mop:funcallable-standard-instance-access instance a-loc)
                      'x 'oops)))
      (assert (eq 'a (sb-mop:funcallable-standard-instance-access instance a-loc)))
      (assert (eq 'a (compare-and-swap
                      (sb-mop:funcallable-standard-instance-access instance a-loc)
                                       'a 'a2)))
      (assert (eq 'a2 (sb-mop:funcallable-standard-instance-access instance a-loc)))
      (assert (eq 'a2 (slot-value instance 'a)))
      (assert (eq 'b (slot-value instance 'b)))
      (assert (eq 'b (sb-mop:funcallable-standard-instance-access instance b-loc))))))

;;; SLOT-VALUE

(defclass standard-thing ()
  ((x :initform 42)
   (y)))

(defmethod slot-unbound ((class standard-class) (obj standard-thing) slot)
  (list :unbound slot))

(defmethod slot-missing ((class standard-class) (obj standard-thing) slot op &optional val)
  (list :missing slot op val))

(with-test (:name (:cas :slot-value :standard-object))
  (let ((x (make-instance 'standard-thing)))
    (assert (eql 42 (slot-value x 'x)))
    (assert (eql 42 (compare-and-swap (slot-value x 'x) 0 :foo)))
    (assert (eql 42 (slot-value x 'x)))
    (assert (eql 42 (compare-and-swap (slot-value x 'x) 42 :foo)))
    (assert (eql :foo (slot-value x 'x)))))

(with-test (:name (:cas :slot-value :slot-unbound))
  (let ((x (make-instance 'standard-thing)))
    (assert (equal '(:unbound y) (slot-value x 'y)))
    (assert (equal '(:unbound y) (compare-and-swap (slot-value x 'y) 0 :foo)))
    (assert (equal '(:unbound y) (slot-value x 'y)))
    (assert (eq sb-pcl:+slot-unbound+
                (compare-and-swap (slot-value x 'y) sb-pcl:+slot-unbound+ :foo)))
    (assert (eq :foo (slot-value x 'y)))))

(with-test (:name (:cas :slot-value :slot-missing))
  (let ((x (make-instance 'standard-thing)))
    (assert (equal '(:missing z slot-value nil) (slot-value x 'z)))
    (assert (equal '(:missing z sb-ext:cas (0 :foo)) (compare-and-swap (slot-value x 'z) 0 :foo)))
    (assert (equal '(:missing z slot-value nil) (slot-value x 'z)))))

(defclass non-standard-class (standard-class)
  ())

(defmethod sb-mop:validate-superclass ((class non-standard-class) (superclass standard-class))
  t)

(defclass non-standard-thing-0 ()
  ((x :initform 13))
  (:metaclass non-standard-class))

(defclass non-standard-thing-1 ()
  ((x :initform 13))
  (:metaclass non-standard-class))

(defclass non-standard-thing-2 ()
  ((x :initform 13))
  (:metaclass non-standard-class))

(defclass non-standard-thing-3 ()
  ((x :initform 13))
  (:metaclass non-standard-class))

(defvar *access-list* nil)

(defmethod sb-mop:slot-value-using-class
    ((class non-standard-class) (obj non-standard-thing-1) slotd)
  (let ((v (call-next-method)))
    (push :read *access-list*)
    v))

(defmethod (setf sb-mop:slot-value-using-class)
    (value (class non-standard-class) (obj non-standard-thing-2) slotd)
  (let ((v (call-next-method)))
    (push :write *access-list*)
    v))

(defmethod sb-mop:slot-boundp-using-class
    ((class non-standard-class) (obj non-standard-thing-3) slotd)
  (let ((v (call-next-method)))
    (push :boundp *access-list*)
    v))

(with-test (:name (:cas :slot-value :non-standard-object :standard-access))
  (let ((x (make-instance 'non-standard-thing-0)))
    (assert (eql 13 (slot-value x 'x)))
    (assert (eql 13 (compare-and-swap (slot-value x 'x) 0 :bar)))
    (assert (eql 13 (slot-value x 'x)))
    (assert (eql 13 (compare-and-swap (slot-value x 'x) 13 :bar)))
    (assert (eql :bar (slot-value x 'x)))))

(with-test (:name (:cas :slot-value :non-standard-object :slot-value-using-class))
  (setf *access-list* nil)
  (let ((x (make-instance 'non-standard-thing-1)))
    (declare (notinline slot-value))
    (assert (null *access-list*))
    (assert (eql 13 (slot-value x 'x)))
    (assert (equal '(:read) *access-list*))
    (assert (eq :error
                (handler-case
                    (compare-and-swap (slot-value x 'x) 0 :bar)
                  (error () :error))))
    (assert (eql 13 (slot-value x 'x)))
    (assert (equal '(:read :read) *access-list*))))

(with-test (:name (:cas :slot-value :non-standard-object :setf-slot-value-using-class))
  (setf *access-list* nil)
  (let ((x (make-instance 'non-standard-thing-2)))
    (assert (equal '(:write) *access-list*))
    (assert (eql 13 (slot-value x 'x)))
    (assert (equal '(:write) *access-list*))
    (assert (eq :error
                (handler-case
                    (compare-and-swap (slot-value x 'x) 0 :bar)
                  (error () :error))))
    (assert (eql 13 (slot-value x 'x)))
    (assert (equal '(:write) *access-list*))))

(with-test (:name (:cas :slot-value :non-standard-object :slot-boundp-using-class))
  (setf *access-list* nil)
  (let ((x (make-instance 'non-standard-thing-3)))
    (assert (equal '(:boundp) *access-list*))
    (assert (eql 13 (slot-value x 'x)))
    (assert (eq :error
                (handler-case
                    (compare-and-swap (slot-value x 'x) 0 :bar)
                  (error () :error))))
    (assert (eql 13 (slot-value x 'x)))))

(defvar *foo* nil)

(defun foo ()
  *foo*)

(defun (cas foo) (old new)
  (cas (symbol-value '*foo*) old new))

(with-test (:name (:cas :defun))
  (assert (null (foo)))
  (assert (null (cas (foo) nil t)))
  (assert (eq t (foo)))
  (assert (eq t (cas (foo) nil :oops)))
  (assert (eq t (foo))))

(with-test (:name (:cas :flet))
  (let (x)
    (flet (((cas x) (old new)
             (let ((tmp x))
               (when (eq tmp old)
                 (setf x new))
               tmp))
           (x ()
             x))
      (assert (null (x)))
      (assert (null (cas (x) nil t)))
      (assert (eq t (x)))
      (assert (eq t (cas (x) nil :oops)))
      (assert (eq t (x))))))

(defgeneric (cas thing) (old new thing))

(defmethod (cas thing) (old new (thing cons))
  (cas (car thing) old new))

(defmethod (cas thing) (old new (thing symbol))
  (cas (symbol-value thing) old new))

(defgeneric thing (thing)
  (:method ((x cons))
    (car x))
  (:method ((x symbol))
    (symbol-value x)))

(with-test (:name (:cas :defgeneric))
  (let ((a (list nil))
        (b (gensym "X")))
    (set b nil)
    (assert (null (thing a)))
    (assert (null (thing b)))
    (assert (null (cas (thing a) nil t)))
    (assert (null (cas (thing b) nil t)))
    (assert (eq t (thing a)))
    (assert (eq t (thing b)))
    (assert (eq t (cas (thing a) nil :oops)))
    (assert (eq t (cas (thing b) nil :oops)))
    (assert (eq t (thing a)))
    (assert (eq t (thing b)))))

;;; SYMBOL-VALUE with a constant argument used to return a bogus read-form
(with-test (:name :symbol-value-cas-expansion)
  (multiple-value-bind (vars vals old new cas-form read-form)
      (get-cas-expansion `(symbol-value t))
    (assert (not vars))
    (assert (not vals))
    (assert (eq t (eval read-form))))
  (multiple-value-bind (vars vals old new cas-form read-form)
      (get-cas-expansion `(symbol-value *))
    (let ((* :foo))
      (assert (eq :foo
                  (eval `(let (,@(mapcar 'list vars vals))
                      ,read-form)))))
    (let ((* :bar))
      (assert (eq :bar
                  (eval `(let (,@(mapcar 'list vars vals))
                      ,read-form)))))))

(let ((foo (cons :foo nil)))
  (defun cas-foo (old new)
    (cas (cdr foo) old new)))

(defcas foo () cas-foo)

(with-test (:name :cas-and-macroexpansion)
  (assert (not (cas (foo) nil t)))
  (assert (eq t (cas (foo) t nil)))
  (symbol-macrolet ((bar (foo)))
    (assert (not (cas bar nil :ok)))
    (assert (eq :ok (cas bar :ok nil)))
    (assert (not (cas bar nil t)))))

(with-test (:name atomic-push
            :skipped-on '(not :sb-thread))
  (let ((store (cons nil nil))
        (n 100000))
    (symbol-macrolet ((x (car store))
                      (y (cdr store)))
      (dotimes (i n)
        (push i y))
      (mapc #'sb-thread:join-thread
            (loop repeat (ecase sb-vm:n-word-bits (32 100) (64 1000))
                  collect (sb-thread:make-thread
                           (lambda ()
                             (loop for z = (atomic-pop y)
                                   while z
                                   do (atomic-push z x)
                                      (sleep 0.00001))))))
      (assert (not y))
      (assert (eql n (length x))))))
