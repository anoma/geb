;; Setup this package to extract
(defpackage #:geb.vampir.spec
  (:documentation "The Vampir model specification")
  (:use #:common-lisp)
  (:shadow :=)
  (:local-nicknames (#:ser #:serapeum))
  (:export
   ;; New Top Level Term Variants Defined
   :statement
   :constraint
   :expression
   :normal-form
   :primitive

   ;; New Term Lists Defined
   :normal-form-list
   :constraint-list
   ;; Term ADT Constructors Defined
   :alias       :name  :inputs   :outputs :body
   :pub         :wires
   :infix       :op    :lhs      :rhs
   :application :func  :arguments
   :bind        :names :value
   :equality    :lhs   :rhs
   :wire        :var
   :constant    :const
   :tuple       :wires

   ;; Constructors
   :make-alias :make-pub :make-infix :make-application :make-tuples
   :make-bind  :make-equality :make-wire :make-constant))

(defpackage #:geb.vampir
  (:documentation "Provides a vampir representation")
  (:use #:common-lisp #:serapeum #:geb.vampir.spec)
  (:shadowing-import-from #:geb.vampir.spec #:op #:tuple)
  (:shadow :=)
  (:local-nicknames (#:spc #:geb.vampir.spec))
  (:export :extract))

