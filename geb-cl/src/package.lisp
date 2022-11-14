(pax:define-package #:geb
  (:documentation "Gödel, Escher, Bach categorical model")
  (:use #:common-lisp #:serapeum)
  (:shadow :left :right :prod :case))

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
  (@geb-types pax:section)
  (@geb-constructors pax:section)
  (@geb-api pax:section)
  (@geb-examples pax:section))


(pax:defsection @geb-types (:title "Types")
  "Types Surrounding the GEB categories"
  (@geb-substmu pax:section)
  (@geb-substmorph pax:section))

(pax:defsection @geb-substmu (:title "Subst Obj")
  "This Category covers the objects of the GEB category. Every value
   that is a SUBSTOBJ is automatically lifted into a SUBSTMORPH when a
   SUBSTMORPH is expected."
  "The Type that encomposes the SUBSTOBJ category"
  (substobj pax:type)
  "The various constructors that form the SUBSTOBJ type"
  (prod pax:type)
  (coprod pax:type)
  (so0 pax:type)
  (so1 pax:type)
  (alias pax:type))

(pax:defsection @geb-substmorph (:title "Subst Morph")
  "The moprhisms of the GEB category."
  "The Type that encomposes the SUBSTMOPRH category"
  (substmorph pax:type)
  "The various constructors that form the SUBSTMORPH type"
  (comp pax:type) (init pax:type) (terminal pax:type)
  (case pax:type) (pair pax:type) (distribute pax:type)
  (inject-left  pax:type) (inject-right  pax:type)
  (project-left pax:type) (project-right pax:type)
  (functor pax:type)
  (alias pax:type))

(pax:defsection @geb-constructors (:title "Constructors")
  "The API for creating GEB terms. All the functions and variables
   here relate to instantiating a term"
  (*so0* pax:variable)
  (*so1* pax:variable)
  "More Ergonomic API variants for *SO0* and *SO1*"
  (so0 pax:symbol-macro)
  (so1 pax:symbol-macro)
  (make-alias pax:function)
  (<-left pax:function)
  (<-right pax:function)
  (left-> pax:function)
  (right-> pax:function)
  (mcase pax:function)
  (make-functor pax:function))

(pax:defsection @geb-api (:title "api")
  "Various functions that make working with GEB easier"
  (pair-to-list pax:function)
  (same-type-to-list pax:function)
  (mlist  pax:function)
  (commutes pax:function)
  (!-> pax:function)
  (so-eval pax:function))

(pax:defsection @geb-accessors (:title "Accessors")
  "These functions relate to grabbing slots out of the various GEBMOPRH and GEBOBJ types"
  (mcar pax:method) (mcadr pax:method) (mcdr pax:method) (mcaddr pax:method)
  (obj pax:method) (name pax:method) (func pax:method))

(pax:defsection @geb-examples (:title "Examples")
  "PLACEHOLDER: TO SHOW OTHERS HOW EXAMPLES WORK"
  "Let's see the transcript of a real session of someone working
  with GEB:

  ```cl-transcript
  (values (princ :hello) (list 1 2))
  .. HELLO
  => :HELLO
  => (1 2)

  (+ 1 2 3 4)
  => 10
  ```")
