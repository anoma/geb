(in-package :geb.utils)

(muffle-package-variance
 (defpackage #:geb.specs
   (:use #:cl)))

(muffle-package-variance
 (defpackage #:geb.poly.spec
   (:shadow :+ :* :/ :- :mod)
   (:use #:geb.utils #:cl)))

;; please document this later.
(muffle-package-variance
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
    :index :index-index)))

(pax:define-package #:geb.spec
  (:documentation "Gödel, Escher, Bach categorical model")
  (:use #:common-lisp #:serapeum #:geb.mixins #:geb.utils)
  (:shadow :left :right :prod :case)
  (:export :prod :case :mcar :mcadr :mcaddr :mcdr :name :func :obj))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Geb Poly Package Documentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(in-package :geb.specs)

(pax:defsection @geb-specs (:title "Spec Files and Layouts")
  "The general layout of the codebase is one where the GEB.Package.Spec
defines the specification for the base types for any category we wish
to model. Due to loading order issues, we put all specifications and
their printers in the `specs` folder. Each Section will then in turn
properly rexport their specification."
  "For example, the GEB.POLY.SPEC defines out the types and data
structures of the Poly category, this is then rexported in GEB.POLY,
giving the module GEB.POLY a convenient interface for all functions
that operate on GEB.POLY.")

(in-package :geb.poly.spec)

(pax:defsection @poly-manual (:title "Polynomial Specification")
  "This covers a GEB view of Polynomials. In particular this type will
be used in translating GEB's view of Polynomials into Vampir"
  (@poly              pax:section)
  (@poly-constructors pax:section))

(pax:defsection @poly (:title "Polynomial Types")
  "This section covers the types of things one can find in the [POLY]
constructors"
  (poly    pax:type)
  (<poly>  pax:type)
  (ident   pax:type)
  (+       pax:type)
  (*       pax:type)
  (/       pax:type)
  (-       pax:type)
  (mod     pax:type)
  (compose pax:type)
  (if-zero pax:type)
  (if-lt   pax:type))

(pax:defsection @poly-constructors (:title "Polynomial Constructors")
  "Every accessor for each of the CLASS's found here are from @GEB-ACCESSORS"
  (ident   pax:symbol-macro)
  (+       pax:function)
  (*       pax:function)
  (/       pax:function)
  (-       pax:function)
  (mod     pax:function)
  (compose pax:function)
  (if-zero pax:function)
  (if-lt   pax:function))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Geb Package Documentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.spec)

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
  "This section covers the objects of the GEB category. Every value
   that is a SUBSTOBJ is automatically lifted into a SUBSTMORPH when a
   SUBSTMORPH is expected."
  "The Type that encomposes the SUBSTOBJ class"
  (substobj   pax:type)
  (<substobj> pax:type)
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
  "The Type that encomposes the SUBSTMOPRH class"
  (substmorph   pax:type)
  (<substmorph> pax:type)
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
  (mcar   pax:generic-function)
  (mcadr  pax:generic-function)
  (mcdr   pax:generic-function)
  (mcaddr pax:generic-function)
  (obj    pax:generic-function)
  (name   pax:generic-function)
  (func   pax:generic-function))

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
