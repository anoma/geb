(pax:define-package :geb.mixins
  (:documentation "Package defines various useful mixins")
  (:local-nicknames (:util :geb.utils))
  (:use #:serapeum #:common-lisp))

(in-package :geb.mixins)

(pax:defsection @mixins (:title "Mixins")
  "Various [mixins](https://en.wikipedia.org/wiki/Mixin) of the
   project. Overall all these offer various services to the rest of the
   project"
  (@pointwise      pax:section)
  (@pointwise-api  pax:section)
  (@mixin-examples pax:section))

(pax:defsection @metadata (:title "Metadata Mixin")
  "Metadata is a form of meta information about a particular
   object. Having metadata about an object may be useful if the goal
   requires annotating some data with type information, identification
   information, or even various levels of compiler information. The
   possibilities are endless and are a standard technique."

  "For this task we offer the [META-MIXIN][type] which will allow
   metadata to be stored for any type that uses its service."
  (meta-mixin pax:class)

  "For working with the structure it is best to have operations to treat
   it like an ordinary hashtable"

  (meta-insert pax:function)
  (meta-lookup pax:function)

  (@mixin-performance pax:section))

(pax:defsection @mixin-performance (:title "Performance")
  "")

(pax:defsection @pointwise (:title "Pointwise Mixins")
  "Here we provide various mixins that deal with classes in a pointwise
   manner. Normally, objects can not be compared in a pointwise manner,
   instead instances are compared. This makes functional idioms like
   updating a slot in a pure manner (allocating a new object), or even
   checking if two objects are `EQUAL`-able adhoc. The pointwise API,
   however, derives the behavior and naturally allows such idioms"
  (pointwise-mixin pax:class)
  "Further we may wish to hide any values inherited from our superclass
   due to this we can instead compare only the slots defined directly
   in our class"
  (direct-pointwise-mixin pax:class))

(pax:defsection @pointwise-API (:title "Pointwise API")
  "These are the general API functions on any class that have the
   POINTWISE-MIXIN service."
  "Functions like TO-POINTWISE-LIST allow generic list traversal APIs to
   be built off the key-value pair of the raw object form, while
   OBJ-EQUALP allows the checking of functional equality between
   objects. Overall the API is focused on allowing more generic
   operations on classes that make them as useful for generic data
   traversal as `LIST`'s are"
  (to-pointwise-list pax:generic-function)
  (obj-equalp        pax:generic-function)

  (pointwise-slots   pax:generic-function))

(defun my-transcript (fn)
  (let ((pax:*transcribe-check-consistency*
          '((:readable obj-equalp))))
    (funcall fn)))

(pax:defsection @mixin-examples (:title "Mixins Examples")
  "Let's see some example uses of POINTWISE-MIXIN:

  ```cl-transcript (:check-consistency ((:readable nil))) (:dynenv my-transcript)
  (obj-equalp (geb:terminal geb:so1)
              (geb:terminal geb:so1))
  => t

  (to-pointwise-list (geb:coprod geb:so1 geb:so1))
  => ((:MCAR . s-1) (:MCADR . s-1))
  ```")
