(pax:define-package #:geb
  (:documentation "Gödel, Escher, Bach categorical model")
  (:use #:common-lisp #:serapeum #:geb.mixins)
  (:shadow :left :right :prod :case)
  (:export :prod :case))

(uiop:define-package #:geb-bool
  (:documentation "Defines out booleans for the geb language")
  (:mix #:geb #:serapeum #:common-lisp)
  (:export
   :bool :mfasle :mtrue :snot
   :higher-and :higher-or))

(in-package :geb)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Geb Package Documentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(pax:defsection @geb (:title "The Geb Model")
  "Everything here relates directly to the underlying machinery of
   GEB, or to abstractions that help extend it."
  (@geb-categories   pax:section)
  (@geb-accessors    pax:section)
  (@geb-constructors pax:section)
  (@geb-api          pax:section)
  (@geb-examples     pax:section))

(pax:defsection @geb-categories (:title "Core Categories")
  "The underlying category of GEB. With @GEB-SUBSTMU covering the
shapes and forms (GEB-DOCS/DOCS:@OBJECTS) of data while @GEB-SUBSTMORPH
deals with concrete GEB-DOCS/DOCS:@MORPHISMS within the category"
  (@geb-substmu    pax:section)
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
  (alias pax:type)
  "The @GEB-ACCESSORS specific to @GEB-SUBSTMU"
  (mcar (pax:method () (prod)))
  (mcadr (pax:method () (prod)))

  (mcar  (pax:method () (coprod)))
  (mcadr (pax:method () (coprod))))

(pax:defsection @geb-substmorph (:title "Subst Morph")
  "The moprhisms of the GEB category."
  "The Type that encomposes the SUBSTMOPRH category"
  (substmorph pax:type)
  "The various constructors that form the SUBSTMORPH type"
  (comp          pax:type)
  (case          pax:type)
  (init          pax:type)
  (terminal      pax:type)
  (pair          pax:type)
  (distribute    pax:type)
  (inject-left   pax:type)
  (inject-right  pax:type)
  (project-left  pax:type)
  (project-right pax:type)
  (functor       pax:type)
  (alias         pax:type)
  "The @GEB-ACCESSORS specific to @GEB-SUBSTMORPH"

  (mcar  (pax:method () (comp)))
  (mcadr (pax:method () (comp)))

  (obj (pax:method () (init)))

  (obj (pax:method () (init)))

  (mcar  (pax:method () (case)))
  (mcadr (pax:method () (case)))

  (mcar (pax:method () (pair)))
  (mcdr (pax:method () (pair)))

  (mcar   (pax:method () (distribute)))
  (mcadr  (pax:method () (distribute)))
  (mcaddr (pax:method () (distribute)))

  (mcar  (pax:method () (inject-left)))
  (mcadr (pax:method () (inject-left)))

  (mcar  (pax:method () (inject-right)))
  (mcadr (pax:method () (inject-right)))

  (mcar  (pax:method () (project-left)))
  (mcadr (pax:method () (project-left)))

  (mcar  (pax:method () (project-right)))
  (mcadr (pax:method () (project-right))))

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
  "These functions relate to grabbing slots out of the various
   @GEB-SUBSTMORPH and @GEB-SUBSTMU types. See those sections for
   specific instance documentation"
  (mcar pax:generic-function)
  (mcadr pax:generic-function)
  (mcdr pax:generic-function)
  (mcaddr pax:generic-function)
  (obj pax:generic-function)
  (name pax:generic-function)
  (func pax:generic-function))

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
