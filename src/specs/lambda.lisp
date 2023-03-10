(in-package #:geb.lambda.spec)

(defclass <stlc> (geb.mixins:direct-pointwise-mixin geb.mixins:meta-mixin geb.mixins:cat-obj) ()
  (:documentation
   "untyped class of terms of STLC"))

(deftype stlc ()
  '(or absurd unit left right case-on pair fst snd lamb app index))

(defclass absurd (<stlc>)
  ((tcod :initarg :tcod
        :accessor tcod
        :documentation "arbitrary type")
   (term :initarg :term
         :accessor term
         :documentation "term of the empty type")
   (ttype :initarg :ttype
         :initform nil
         :accessor ttype
         :documentation ""))
  (:documentation
   "The absurd type provides an element of an arbitrary type given a term of the empty type"))

(defun absurd (tcod term &key (ttype nil))
  (make-instance 'absurd :tcod tcod :term term :ttype ttype))

(defclass unit (<stlc>)
  ((ttype :initarg :ttype
         :initform nil
         :accessor ttype
         :documentation "")))

(defun unit (&key (ttype nil))
  (make-instance 'unit :ttype ttype))

(defclass left (<stlc>)
  ((rty :initarg :rty
        :accessor rty
        :documentation "right argument of coproduct type")
   (term :initarg :term
         :accessor term
         :documentation "term of the left argument of coproduct type")
   (ttype :initarg :ttype
         :initform nil
         :accessor ttype
         :documentation "")))

(defun left (rty term &key (ttype nil))
  (make-instance 'left :rty rty :term term :ttype ttype))

(defclass right (<stlc>)
  ((lty :initarg :lty
        :accessor lty
        :documentation "left argument of coproduct type")
   (term :initarg :term
         :accessor term
         :documentation "term of the right argument of coproduct type")
   (ttype :initarg :ttype
         :initform nil
         :accessor ttype
         :documentation "")))

(defun right (lty term &key (ttype nil))
  (make-instance 'right :lty lty :term term :ttype ttype))

(defclass case-on (<stlc>)
  ((on :initarg :on
       :accessor on
       :documentation "term of coproduct type")
   (ltm :initarg :ltm
         :accessor ltm
         :documentation "term in context of left argument of coproduct type")
   (rtm :initarg :rtm
          :accessor rtm
          :documentation "term in context of right argument of coproduct type")
   (ttype :initarg :ttype
         :initform nil
         :accessor ttype
         :documentation "")))

(defun case-on (on ltm rtm &key (ttype nil))
  (make-instance 'case-on :on on :ltm ltm :rtm rtm :ttype ttype))

(defclass pair (<stlc>)
  ((ltm :initarg :ltm
         :accessor ltm
         :documentation "term of left argument of the product type")
   (rtm :initarg :rtm
          :accessor rtm
          :documentation "term of right argument of the product type")
   (ttype :initarg :ttype
         :initform nil
         :accessor ttype
         :documentation "")))

(defun pair (ltm rtm &key (ttype nil))
  (make-instance 'pair :ltm ltm :rtm rtm :ttype ttype))

(defclass fst (<stlc>)
  ((term :initarg :term
         :accessor term
         :documentation "term of product type")
   (ttype :initarg :ttype
         :initform nil
         :accessor ttype
         :documentation "")))

(defun fst (term &key (ttype nil))
  (make-instance 'fst :term term :ttype ttype))

(defclass snd (<stlc>)
  ((term :initarg :term
         :accessor term
         :documentation "term of product type")
   (ttype :initarg :ttype
         :initform nil
         :accessor ttype
         :documentation "")))

(defun snd (term &key (ttype nil))
  (make-instance 'snd :term term :ttype ttype))

(defclass lamb (<stlc>)
  ((tdom :initarg :tdom
        :accessor tdom
        :documentation "domain of the lambda term")
   (term :initarg :term
         :accessor term
         :documentation "term of the codomain mapped to given a variable of tdom")
   (ttype :initarg :ttype
         :initform nil
         :accessor ttype
         :documentation "")))

(defun lamb (tdom term &key (ttype nil))
  (make-instance 'lamb :tdom tdom :term term :ttype ttype))

(defclass app (<stlc>)
  ((fun :initarg :fun
        :accessor fun
        :documentation "term of exponential type")
   (term :initarg :term
         :accessor term
         :documentation "term of the domain")
   (ttype :initarg :ttype
         :initform nil
         :accessor ttype
         :documentation "")))

(defun app (fun term &key (ttype nil))
  (make-instance 'app :fun fun :term term :ttype ttype))

(defclass index (<stlc>)
  ((pos :initarg :pos
        :accessor pos
        :documentation "position of type")
   (ttype :initarg :ttype
         :initform nil
         :accessor ttype
         :documentation "")))

(defun index (pos &key (ttype nil))
  (make-instance 'index :pos pos :ttype ttype))


