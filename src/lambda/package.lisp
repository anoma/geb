(in-package :geb.utils)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; API module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.lambda.main
   (:documentation "A basic lambda calculus model")
   (:mix #:geb.lambda.spec #:geb.common #:common-lisp)
   (:reexport #:geb.lambda.spec)))

(in-package #:geb.lambda.main)

(pax:defsection @lambda-api (:title "Main functionality")
  "This covers the main API for the STLC module")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; trans module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.utils)

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.lambda.trans
   (:documentation "A basic lambda translator into other parts of geb")
   (:shadow #:to-poly #:to-circuit)
   (:local-nicknames (#:lambda #:geb.lambda.main))
   (:mix #:geb.lambda.spec #:geb.common #:common-lisp :geb.lambda.main)))

(in-package #:geb.lambda.trans)

(pax:defsection @utility (:title "Utility Functionality")
  "These are utility functions relating to translating lambda terms to other types"
  (stlc-ctx-to-mu  pax:function)
  (so-hom  pax:function))

(pax:defsection @stlc-conversion (:title "Transition Functions")
  "These functions deal with transforming the data structure to other
data types"
  (compile-checked-term pax:generic-function)
  (to-poly              pax:function)
  (to-circuit           pax:function)
  (@utility             pax:section))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lambda module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.utils)

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.lambda
   (:documentation "A basic lambda calculus model")
   (:mix #:geb.lambda.spec #:geb.lambda.trans #:geb.common #:common-lisp)
   (:use-reexport #:geb.lambda.spec #:geb.lambda.main #:geb.lambda.trans)))

(in-package #:geb.lambda)

(pax:defsection @stlc (:title "The Simply Typed Lambda Calculus model")
  "This covers GEB's view on simply typed lambda calculus"
  (@lambda-specs pax:section)
  (@lambda-api  pax:section)
  (@stlc-conversion pax:section))
