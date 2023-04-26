(in-package :geb.extension.spec)

;; Sadly no polynomial category to extend ☹
(defclass common-sub-expression (direct-pointwise-mixin meta-mixin cat-morph)
  ((obj :initarg :obj
        :accessor obj)
   (name :initarg :name
         :accessor name))
  (:documentation
   "I represent common sub-expressions found throughout the code.

I implement a few categorical extensions. I am a valid
[CAT-MORPH][TYPE] along with fulling the interface for the
GEB.POLY.SPEC:<POLY> category.

The name should come from an algorithm that automatically fines common
sub-expressions and places the appropriate names."))

(defun make-common-sub-expression (&key obj name)
  (make-instance 'common-sub-expression :obj obj :name name))
