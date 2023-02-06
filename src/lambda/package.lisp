(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.lambda
   (:documentation "A basic lambda calculus model")
   (:mix #:trivia #:serapeum #:geb.lambda.spec #:common-lisp)
   ;; we also reexport lambda.trans see the documentation below
   (:reexport #:geb.lambda.spec)))

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.lambda.trans
   (:documentation "A basic lambda translator into other parts of geb")
   (:mix #:trivia #:geb #:serapeum #:common-lisp #:geb.lambda.spec #:geb.lambda)))

(in-package #:geb.lambda.trans)

(pax:defsection @utility (:title "Utility Functionality")
  "These are utility functions relating to translating lambda terms to other types"
  (stlc-ctx-to-mu  pax:function))

(pax:defsection @stlc-conversion (:title "Transition Functions")
  "These functions deal with transforming the data structure to other
data types"
  (compile-checked-term pax:generic-function)
  (@utility             pax:section))

(in-package #:geb.lambda)

(pax:defsection @stlc (:title "The Simply Typed Lambda Calculus model")
  "This covers GEB's view on simply typed lambda calculus"
  (@lambda-specs pax:section)
  (geb.lambda.trans:@stlc-conversion pax:section))

(cl-reexport:reexport-from :geb.lambda.trans)
