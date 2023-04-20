(in-package :geb.vampir.spec)

;; Here we use the language of vampir to talk about the components

;; Adapted form
;; https://github.com/heliaxdev/ark-plonk/blob/plonk-ir/plonk-ir/src/plonk_ir.pest

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Sum Type Declarations
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; please remove these geb types later

(deftype statement ()
  `(or alias pub constraint))

(deftype constraint ()
  `(or application bind equality expression
       geb.extension.spec:common-sub-expression))

;; called base in the file
;; Values are called over a normal form!?!?!?
(deftype expression ()
  `(or infix application normal-form tuple
       geb.extension.spec:common-sub-expression))

(deftype normal-form ()
  `(or wire constant))

(deftype primitive ()
  `(or (eql :+) (eql :-) (eql :*) (eql :^) (eql :\\) (eql :%) (eql :/)))

(deftype constraint-list ()
  `(satisfies constraint-list))

(deftype normal-form-list ()
  `(satisfies normal-form-list))

(defun constraint-list (list)
  (and (listp list)
       (every (lambda (x) (typep x 'constraint)) list)))

(defun normal-form-list (list)
  (and (listp list)
       (every (lambda (x) (typep x 'normal-form)) list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Statement Product Types
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass mixins (geb.mixins:direct-pointwise-mixin) ())


(defclass alias (mixins)
  ((name :initarg :name
         :type    (or symbol keyword)
         :accessor name
         :documentation "Name of the alias gate")
   (inputs :initarg :inputs
           :type    list
           :accessor inputs
           :documentation "the arguments to the circuit")
   ;; we should move this to an expression instead
   ;; See Issue #38 comment 1 on why.
   ;; (outputs :initarg :outputs
   ;;          :type    list
   ;;          :accessor outputs
   ;;          :documentation "The return wires of the circuit")
   ;; TODO :: layout types
   (body :initarg :body
         :accessor body
         :type     constraint-list))
  (:documentation "An alias gate in vamp-ir"))

(defclass pub (mixins)
  ((wires :initarg :wires
          :type    list
          :accessor wires)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Expression Product Types
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass infix (mixins)
  ((op :initarg :op
       :accessor op
       :type     primitive
       :documentation "the alias we are calling")
   (lhs :initarg  :lhs
        :accessor lhs
        :type     expression
        :documentation "the argument to the left of the op")
   (rhs :initarg  :rhs
        :accessor rhs
        :type     expression
        :documentation "the argument to the right of the op")))

(defclass application (mixins)
  ((func :initarg :func
         :accessor func
         :type     (or symbol keyword)
         :documentation "the alias we are calling")
   (arguments :initarg :arguments
              ;; I assume list of expressions?
              :type     cons
              :accessor arguments
              :documentation "The arguments in which the gate is called upon")))

(defclass bind (mixins)
  ((names :initarg :names
          :accessor names
          :type     normal-form-list)
   (value :initarg :value
          :accessor value
          ;; can't be a constant however!
          :type     expression)))

(defclass equality (mixins)
  ((lhs :initarg  :lhs
        :accessor lhs
        :type     expression
        :documentation "the argument to the left of the =")
   (rhs :initarg  :rhs
        :accessor rhs
        :type     expression
        :documentation "the argument to the rigth of the =")))

(defclass tuple (mixins)
  ((wires :initarg :wires
          :type    list
          :accessor wires)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Normal Form Product Types
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass wire (mixins)
  ((var :initarg :var
        :accessor var
        :type     (or symbol keyword)))
  (:documentation "A reference in vamp-ir"))

(defclass constant (mixins)
  ((const :initarg :const
          :accessor const)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Alias
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(serapeum:-> make-alias
             (&key (:name (or symbol keyword)) (:inputs list) (:body constraint-list))
             alias)
(defun make-alias (&key name inputs body)
  (values
   (make-instance 'alias :name name :inputs inputs :body body)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pub
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-pub (&key wires)
  (make-instance 'pub :wires wires))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Infix
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-infix (&key lhs op rhs)
  (make-instance 'infix :lhs lhs :op op :rhs rhs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Application
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-application (&key func arguments)
  (make-instance 'application :func func :arguments arguments))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Bind
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-bind (&key names value)
  (make-instance 'bind :names names :value value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Equality
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-equality (&key lhs rhs)
  (make-instance 'equality :lhs lhs :rhs rhs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Wire
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-wire (&key var)
  (make-instance 'wire :var var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constant
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-constant (&key const)
  (make-instance 'constant :const const))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Tuples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-tuples (&key wires)
  (make-instance 'tuple :wires wires))
