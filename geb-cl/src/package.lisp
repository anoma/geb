(defpackage #:geb
  (:documentation "Gödel, Escher, Bach categorical model")
  (:use #:common-lisp #:serapeum)
  (:shadow :left :right :prod :case)
  (:export
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;; Types
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;; Sum Types
   :substobj
   :substmorph
   ;; Product Types
   :alias :so0 :so1 :prod :coprod :compose

   :comp :init :terminal :pair :case :distribute :functor
   :inject-left :inject-right :project-right :project-left
   :make-functor
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;; Constructors
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   :*so0*
   :*so1*
   :make-alias
   :<-left :<-right
   :left-> :right->
   :mcase
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;; accessors
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   :mcar :mcadr :mcdr :mcaddr
   :obj :name :func
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;; API
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   :pair-to-list
   :same-type-to-list
   :mlist
   :commutes
   :!->))

(uiop:define-package #:geb-bool
  (:documentation "Defines out booleans for the geb language")
  (:mix #:geb #:serapeum #:common-lisp)
  (:export
   :bool :mfasle :mtrue :snot
   :higher-and :higher-or))
