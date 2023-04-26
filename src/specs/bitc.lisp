(in-package #:geb.bitc.spec)

(deftype bitc ()
  `(or compose fork parallel swap one zero ident drop branch))

(defclass <bitc> (geb.mixins:direct-pointwise-mixin cat-morph) ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructor Morphisms for Bits (Objects are just natural numbers)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass compose (<bitc>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")))

(defclass fork (<bitc>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")))

(defclass parallel (<bitc>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")))

(defclass swap (<bitc>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")))

(defclass one (<bitc>)
  ())

(defclass zero (<bitc>)
  ())

(defclass ident (<bitc>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")))

(defclass drop (<bitc>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")))

(defclass branch (<bitc>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro make-multi (constructor)
  `(defun ,constructor (mcar mcadr &rest args)
     ,(format nil "Creates a multiway constructor for [~A]" constructor)
     (reduce (lambda (x y)
               (make-instance ',constructor :mcar x :mcadr y))
             (list* mcar mcadr args)
             :from-end t)))

(make-multi parallel)
(make-multi compose)

(defun fork (mcar)
  "FORK ARG1"
  (make-instance 'fork :mcar mcar))

(defun swap (mcar mcadr)
  "swap ARG1 and ARG2"
  (make-instance 'swap :mcar mcar :mcadr mcadr))

(defvar one
  (make-instance 'one))

(defvar zero
  (make-instance 'zero))

(defun ident (mcar)
  "ident ARG1"
  (make-instance 'ident :mcar mcar))

(defun drop (mcar)
  "drop ARG1"
  (make-instance 'drop :mcar mcar))

(defun branch (mcar mcadr)
  "branch with ARG1 or ARG2"
  (make-instance 'branch :mcar mcar :mcadr mcadr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pattern Matching
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Ι don't do multi way pattern matching yet :(
(make-pattern compose     mcar mcadr)
(make-pattern fork        mcar)
(make-pattern parallel    mcar mcadr)
(make-pattern swap        mcar mcadr)
(make-pattern one         )
(make-pattern zero        )
(make-pattern ident       mcar)
(make-pattern drop        mcar)
(make-pattern branch      mcar mcadr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Domain and codomain definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod dom ((x <bitc>))
  (typecase-of bitc x
    (compose          (dom (mcadr x)))
    (fork             (dom (mcar x)))
    (parallel         (+ (dom (mcar x)) (dom (mcadr x))))
    (swap             (+ (mcar x) (mcadr x)))
    (one              0)
    (zero             0)
    (ident            (mcar x))
    (drop             (mcar x))
    (branch           (+ 1 (dom (mcar x))))
    (otherwise
      (subclass-responsibility x))))

(defmethod codom ((x <bitc>))
  (typecase-of bitc x
    (compose          (codom (mcar x)))
    (fork             (* 2 (codom (mcar x))))
    (parallel         (+ (codom (mcar x)) (codom (mcadr x))))
    (swap             (+ (mcar x) (mcadr x)))
    (one              1)
    (zero             1)
    (ident            (mcar x))
    (drop             0)
    (branch           (codom (mcar x)))
    (otherwise
      (subclass-responsibility x))))
