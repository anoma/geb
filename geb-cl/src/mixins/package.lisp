(pax:define-package :geb.mixins
  (:documentation "Package defines various useful mixins")
  (:local-nicknames (:util :geb.utils))
  (:use #:serapeum #:common-lisp))

(in-package :geb.mixins)

(pax:defsection @mixins (:title "Mixins")
  "Here we provide various mixins that are useful for general
   computation."
  (pointwise-slots        pax:class)
  (direct-pointwise-mixin pax:class)
  (to-pointwise-list pax:generic-function)
  (obj-equalp        pax:generic-function)
  (to-pointwise-list pax:generic-function))
