(defpackage #:geb.lambda
  (:documentation "A basic lambda calculus model")
  (:import-from :trivia :guard :match)
  (:use #:common-lisp #:serapeum)
  (:export
   :curry-lambda :nameless

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;; Internal Data Structure Exports
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   #:context #:make-context #:context-p #:context-depth :context-mapping
   #:index   #:make-index   #:index-p   #:index-depth))
