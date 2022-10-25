(uiop:define-package #:geb.lambda
  (:documentation "A basic lambda calculus model")
  (:mix #:trivia #:serapeum #:common-lisp)
  (:export
   :curry-lambda :nameless

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;; Internal Data Structure Exports
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   #:context #:make-context #:context-p #:context-depth :context-mapping
   #:index   #:make-index   #:index-p   #:index-depth))
