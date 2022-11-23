(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.lambda
   (:documentation "A basic lambda calculus model")
   (:mix #:trivia #:serapeum #:common-lisp)
   (:export
    :curry-lambda :nameless

    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    ;; Internal Data Structure Exports
    ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
    #:context #:make-context #:context-p #:context-depth :context-mapping
    #:index   #:make-index   #:index-p   #:index-depth)))

(geb.utils:muffle-package-variance
 (uiop:define-package #:geb.lambda-conversion
   (:documentation "A basic lambda calculus model")
   (:mix #:trivia #:geb #:serapeum #:common-lisp :geb.lambda.spec #:geb.lambda)
   (:export
    :compile-checked-term :stlc-ctx-to-mu)))


