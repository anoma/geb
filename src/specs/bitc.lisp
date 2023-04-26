(in-package #:geb.bitc.spec)

(deftype bitc ()
  `(or compose fork parallel swap one zero ident drop branch))

(defclass <bitc> (geb.mixins:direct-pointwise-mixin) ())

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
