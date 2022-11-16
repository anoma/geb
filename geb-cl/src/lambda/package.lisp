(locally (declare (sb-ext:muffle-conditions sb-int:package-at-variance))
  (handler-bind ((sb-int:package-at-variance #'muffle-warning))
    (uiop:define-package #:geb.lambda.spec
      (:documentation "Basic spec for creating lambda terms")
      (:mix #:trivia #:serapeum #:common-lisp)
      (:export
       :<stlc> :stlc
       :absurd :absurd-value
       :unit
       :pair :pair-lty :pair-rty :pair-left :pair-right
       :left :left-value
       :right :right-value
       :case-on :case-on-lty :case-on-rty :case-on-cod :case-on-on :case-on-left :case-on-right
       :fst  :fst-lty  :fst-rty  :fst-value
       :snd  :snd-lty  :snd-rty  :snd-value
       :lamb :lamb-vty :lamb-tty :lamb-value
       :app  :app-dom  :app-cod  :app-func :app-bj
       :index :index-index))

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

    (uiop:define-package #:geb.lambda-conversion
      (:documentation "A basic lambda calculus model")
      (:mix #:trivia #:geb #:serapeum #:common-lisp :geb.lambda.spec #:geb.lambda)
      (:export
       :compile-checked-term :stlc-ctx-to-mu))))


