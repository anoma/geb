(in-package #:geb.poly.spec)

(deftype poly ()
  `(or compose + * / - mod integer if-zero if-lt ident))

(defclass <poly> (geb.mixins:direct-pointwise-mixin) ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructor Objects for Poly
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass compose (<poly>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")))

(defclass + (<poly>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")))

(defclass ident (<poly>)
  ()
  (:documentation "The Identity Element"))

(defclass * (<poly>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")))

(defclass - (<poly>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")))

(defclass / (<poly>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")))

(defclass mod (<poly>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")))

(defclass if-zero (<poly>)
  ((predicate :initarg :predicate
              :accessor predicate
              :documentation "")
   (then :initarg :then
         :accessor then
         :documentation "")
   (else :initarg :else
         :accessor else
         :documentation ""))
  (:documentation "compare with zero: equal takes first branch;
                   not-equal takes second branch"))
(defclass if-lt (<poly>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation "")
   (then :initarg :then
         :accessor then
         :documentation "")
   (else :initarg :else
         :accessor else
         :documentation ""))
  (:documentation
   "If the [MCAR] argument is strictly less than the [MCADR] then the
    [THEN] branch is taken, otherwise the [ELSE] branch is taken."))

(defmethod mcar ((obj if-zero))
  (predicate obj))

(defmethod mcadr ((obj if-zero))
  (then obj))

(defmethod mcaddr ((obj if-zero))
  (else obj))

(defmethod mcaddr ((obj if-lt))
  (then obj))

(defmethod mcadddr ((obj if-lt))
  (else obj))

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

(make-multi +)
(make-multi *)
(make-multi compose)
(make-multi /)
(make-multi -)

(defun mod (mcar mcadr)
  "MOD ARG1 by ARG2"
  (make-instance 'mod :mcar mcar :mcadr mcadr))

(defun if-zero (pred then else)
  "checks if [PREDICATE] is zero then take the [THEN] branch otherwise the [ELSE] branch"
  (make-instance 'if- :predicate pred :then then :else else))

(defun if-lt (mcar mcadr then else)
  "Checks if the [MCAR] is less than the [MCADR] and chooses the appropriate branch"
  (make-instance 'if-lt :mcar mcar :mcadr mcadr :then then :else else))

(serapeum:def ident (make-instance 'ident))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pattern Matching
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Ι don't do multi way pattern matching yet :(
(make-pattern +       mcar mcadr)
(make-pattern *       mcar mcadr)
(make-pattern /       mcar mcadr)
(make-pattern -       mcar mcadr)
(make-pattern compose mcar mcadr)
(make-pattern mod     mcar mcadr)
(make-pattern if-zero predicate  then else)
(make-pattern if-lt   mcar mcadr then else)
