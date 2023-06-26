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

(geb.utils:muffle-package-variance
 (defpackage #:geb.vampir
   (:documentation "Provides a vampir representation")
   (:use #:common-lisp #:serapeum #:geb.vampir.spec)
   (:shadowing-import-from #:geb.vampir.spec #:op #:tuple)
   (:shadowing-import-from #:common-lisp  #:=)
   (:local-nicknames (#:spc #:geb.vampir.spec))
   (:export
    :extract

    ;; vampir api functions
    :*bool*
    :bool
    :*base-range*
    :*next-range*
    :next-range
    :*range-n*
    :range-n
    :*range32*
    :range32

    :*int-range32*
    :int-range32

    :*negative32*
    :negative32

    :*non-negative32*
    :non-negative32

    :*range31*
    :range31

    :*int-range31*
    :int-range31

    :*less32*
    :less32

    :*pwless32*
    :pwless32

    :*mod32*
    :mod32

    :*pwmod32*
    :pwmod32)))

