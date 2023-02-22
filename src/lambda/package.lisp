(in-package :geb.utils)

(eval-when (:compile-toplevel :load-toplevel :execute)
  ;; they all share the same mix list
  (defmacro mix (&rest symbols)
    `'(:mix #:trivia #:geb #:serapeum #:geb.lambda.spec #:common-lisp ,@symbols)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; API module
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.lambda.main
   (:documentation "A basic lambda calculus model")
   #.(mix)
   ;; we also reexport lambda.trans see the documentation below
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
   #.(mix :geb.lambda.main)))

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

(uiop:define-package #:geb.lambda
   (:documentation "A basic lambda calculus model")
   #.(mix)
   ;; we also reexport lambda.trans see the documentation below
   (:shadowing-import-from #:geb.lambda.trans :to-poly :to-circuit)
   (:shadowing-import-from #:geb.lambda.spec :pair)
   (:use-reexport #:geb.lambda.spec #:geb.lambda.main #:geb.lambda.trans))

(in-package #:geb.lambda)

(pax:defsection @stlc (:title "The Simply Typed Lambda Calculus model")
  "This covers GEB's view on simply typed lambda calculus"
  (@lambda-specs pax:section)
  (@lambda-api  pax:section)
  (@stlc-conversion pax:section))
