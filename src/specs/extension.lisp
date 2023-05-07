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
[CAT-MORPH][class] along with fulling the interface for the
[GEB.POLY.SPEC:<POLY>] category.

The name should come from an algorithm that automatically fines common
sub-expressions and places the appropriate names."))


(defclass opaque (cat-obj meta-mixin)
  ((name :initarg :name :accessor name)
   (code :initarg :code :accessor code))
  (:documentation
   "I represent an object where we want to hide the implementation
details of what kind of [GEB:SUBSTOBJ][type] I am."))

(defclass reference (cat-obj cat-morph direct-pointwise-mixin meta-mixin)
  ((name :initarg :name :accessor name))
  (:documentation
   "I represent a reference to an [OPAQUE][class] identifier."))

(defclass opaque-morph (cat-morph meta-mixin)
  ((code :initarg :code
         :accessor code
         :documentation "the code that represents the underlying morphsism")
   (dom :initarg :dom
        :accessor dom
        :documentation "The dom of the opaque morph")
   (codom :initarg :codom
          :accessor codom
          :documentation "The codom of the opaque morph"))
  (:documentation
   "This represents a morphsim where we want to deal with an
[OPAQUE][class] that we know intimate details of"))

(defun make-common-sub-expression (&key obj name)
  (make-instance 'common-sub-expression :obj obj :name name))

(defun reference (name)
  (make-instance 'reference :name name))

(defun opaque-morph (code &key (dom (dom code)) (codom (codom code)))
  (make-instance 'opaque-morph :code code :dom dom :codom codom))

(defun opaque (name code)
  (make-instance 'opaque :name name :code code))
