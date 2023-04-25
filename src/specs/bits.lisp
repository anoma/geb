(in-package #:geb.bits.spec)

(deftype bits ()
  `(or compose fork parallel negation conjunction swap true false identity drop branch))

(defclass <bits> (geb.mixins:direct-pointwise-mixin) ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructor Morphisms for Bits (Objects are just natural numbers)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass compose (<bits>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")))

(defclass fork (<bits>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")))

(defclass parallel (<bits>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")))

(defclass negation (<bits>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")))

(defclass conjunction (<bits>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")))

(defclass swap (<bits>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")))

(defclass true (<bits>)
  ())

(defclass false (<bits>)
  ())

(defclass identity (<bits>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")))

(defclass drop (<bits>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")))

(defclass branch (<bits>)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pattern Matching
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Ι don't do multi way pattern matching yet :(
(make-pattern compose     mcar mcadr)
(make-pattern fork        mcar)
(make-pattern parallel    mcar mcadr)
(make-pattern negation      mcar)
(make-pattern conjunction mcar mcadr)
(make-pattern swap        mcar mcadr)
(make-pattern true        )
(make-pattern false       )
(make-pattern identity    mcar)
(make-pattern drop        mcar)
(make-pattern branch      mcar mcadr)
