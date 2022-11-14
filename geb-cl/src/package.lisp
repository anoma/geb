(pax:define-package #:geb
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
   ;; accessors
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   :mcar :mcadr :mcdr :mcaddr
   :obj :name :func))

(uiop:define-package #:geb-bool
  (:documentation "Defines out booleans for the geb language")
  (:mix #:geb #:serapeum #:common-lisp)
  (:export
   :bool :mfasle :mtrue :snot
   :higher-and :higher-or))

(in-package :geb)

(pax:defsection @geb (:title "Geb User manual")
  "The Main GEB model. Everything here relates directly to the
   underlying machinery of GEB, or to abstractions that help extend
   it."
  (@geb-constructors pax:section)
  (@geb-api pax:section))

(pax:defsection @geb-constructors (:title "Constructors")
  "The API for creating GEB terms. All the functions and variables
   here relate to instantiating a term"
  (so0 pax:symbol-macro)
  (so1 pax:symbol-macro)
  (make-alias pax:function)
  (<-left pax:function)
  (<-right pax:function)
  (left-> pax:function)
  (right-> pax:function)
  (mcase pax:function))

(pax:defsection @geb-api (:title "api")
  "Various functions that make working with GEB easier"
  (pair-to-list pax:function)
  (same-type-to-list pax:function)
  (mlist  pax:function)
  (commutes pax:function)
  (!-> pax:function)
  (so-eval pax:function))
