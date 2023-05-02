(in-package :geb.utils)

(muffle-package-variance
 (defpackage #:geb.specs
   (:use #:cl)))

(muffle-package-variance
 (defpackage #:geb.poly.spec
   (:shadow :+ :* :/ :- :mod)
   (:use #:geb.utils #:cl)))

(muffle-package-variance
 (defpackage #:geb.bitc.spec
   (:export :dom :codom)
   (:shadow :drop :fork)
   (:use #:geb.utils #:cl #:geb.mixins)))

;; please document this later.
(muffle-package-variance
 (uiop:define-package #:geb.lambda.spec
   (:documentation "Basic spec for creating lambda terms")
   (:mix #:trivia #:serapeum #:common-lisp)))

(pax:define-package #:geb.spec
  (:documentation "Gödel, Escher, Bach categorical model")
  (:use #:common-lisp #:serapeum #:geb.mixins #:geb.utils)
  (:shadow :left :right :prod :case)
  (:export :prod :case :mcar :mcadr :mcaddr :mcdr :name :func :obj
   :same-type-to-list :pair-to-list))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Geb Package Documentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.specs)

(pax:defsection @geb-specs (:title "Spec Files, Main Files and Project Layout")
  "The codebase is split between many files. Each folder can be seen as
a different idea within geb itself! Thus the `poly` has packages
revolving around polynomials, the `geb` folder has packages regarding
the main types of geb GEB.SPEC:@GEB-SUBSTMU and
GEB.SPEC:@GEB-SUBSTMORPH, etc etc.

The general layout quirk of the codebase is that packages like
`geb.package.spec` defines the specification for the base types for
any category we wish to model, and these reside in the `specs` folder
not in the folder that talks about the packages of those types. This
is due to loading order issues, we thus load the `specs` packages
before each of their surrounding packages, so that each package can
built off the last. Further, packages like `geb.package.main` define
out most of the functionality of the package to be used by other
packages in `geb.package`, then all of these are reexported out in the
`geb.package` package

Further to make working with each package of an idea is easy, we have
the main package of the folder (typically named the same as the folder
name) reexport most important components so if one wants to work with
the fully fledged versions of the package they can simply without
having to import too many packages at once.

For example, the `geb.poly.spec` defines out the types and data
structures of the GEB.POLY.SPEC:@POLY, this is then rexported
in `geb.poly`, giving the module `geb.poly` a convenient interface for
all functions that operate on `geb.poly`.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Geb Poly Package Documentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.poly.spec)

(pax:defsection @poly (:title "Polynomial Types")
  "This section covers the types of things one can find in the [POLY]
constructors"
  (poly    pax:type)
  (<poly>  pax:class)
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
;; Geb Bits Package Documentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.bitc.spec)

(pax:defsection @bitc (:title "Bits Types")
  "This section covers the types of things one can find in the [BITS]
constructors"
  (bitc     pax:type)
  (<bitc>   pax:class)
  (compose  pax:class)
  (fork     pax:class)
  (parallel pax:class)
  (swap     pax:class)
  (one      pax:class)
  (zero     pax:class)
  (ident    pax:class)
  (drop     pax:class)
  (branch   pax:class))

(pax:defsection @bitc-constructors (:title "Bits (Boolean Circuit) Constructors")
  "Every accessor for each of the CLASS's found here are from @GEB-ACCESSORS"
  (compose  pax:function)
  (fork     pax:function)
  (parallel pax:function)
  (swap     pax:function)
  (one      pax:symbol-macro)
  (zero     pax:symbol-macro)
  (ident    pax:function)
  (drop     pax:function)
  (branch   pax:function))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Geb lambda Package Documentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.lambda.spec)

(pax:defsection @lambda-specs (:title "Lambda Specification")
  "This covers the various the abstract data type that is the simply
  typed lambda calculus within GEB.

The specification follows from the sum type declaration

```lisp
(defunion stlc
  (absurd (value t))
  unit
  (left (value t))
  (right (value t))
  (case-on (lty geb.spec:substmorph)
           (rty geb.spec:substmorph)
           (cod geb.spec:substmorph)
           (on t) (left t) (right t))
  (pair (lty geb.spec:substmorph) (rty geb.spec:substmorph) (left t) (right t))
  (fst  (lty geb.spec:substmorph) (rty geb.spec:substmorph) (value t))
  (snd  (lty geb.spec:substmorph) (rty geb.spec:substmorph) (value t))
  (lamb (vty geb.spec:substmorph) (tty geb.spec:substmorph) (value t))
  (app  (dom geb.spec:substmorph) (cod geb.spec:substmorph) (func t) (obj t))
  (index (index fixnum)))
```
"
  (<stlc> pax:type)
  (stlc pax:type)
  (absurd pax:type)
  (absurd-value pax:function)

  (unit pax:type)

  (pair pax:type)
  (pair-lty pax:function)
  (pair-rty pax:function)
  (pair-left pax:function)
  (pair-right pax:function)

  (left pax:type)
  (left-value pax:function)

  (right pax:type)
  (right-value pax:function)

  (case-on pax:type)
  (case-on-lty pax:function)
  (case-on-rty pax:function)
  (case-on-cod pax:function)
  (case-on-on pax:function)
  (case-on-left pax:function)
  (case-on-right pax:function)

  (fst pax:type)
  (fst-lty pax:function)
  (fst-rty pax:function)
  (fst-value pax:function)

  (snd pax:type)
  (snd-lty pax:function)
  (snd-rty pax:function)
  (snd-value pax:function)

  (lamb pax:type)
  (lamb-vty pax:function)
  (lamb-tty pax:function)
  (lamb-value pax:function)

  (app pax:type)
  (app-dom pax:function)
  (app-cod pax:function)
  (app-func pax:function)
  (app-obj pax:function)

  (index pax:type)
  (index-index pax:function)

  (typed pax:function)
  (typed-stlc-type pax:function) (typed-stlc-value pax:function))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Geb Package Documentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.spec)

(pax:defsection @geb-categories (:title "Core Category")
  "The underlying category of GEB. With @GEB-SUBSTMU covering the
shapes and forms (GEB-DOCS/DOCS:@OBJECTS) of data while @GEB-SUBSTMORPH
deals with concrete GEB-DOCS/DOCS:@MORPHISMS within the category.

From this category, most abstractions will be made, with
[SUBSTOBJ][type] serving as a concrete type layout, with
[SUBSTMORPH][type] serving as the morphisms between different
[SUBSTOBJ][type] types. This category is equivalent to
[finset](https://ncatlab.org/nlab/show/FinSet).

A good example of this category at work can be found within the
GEB-BOOL::@GEB-BOOL section."
  (@geb-substmu    pax:section)
  (@geb-substmorph pax:section)
  (@geb-realized   pax:section))

(pax:defsection @geb-substmu (:title "Subst Obj")
  "This section covers the objects of the [SUBSTMORPH][type]
category. Note that [SUBSTOBJ][type] refers to the
[GEB-DOCS/DOCS:@CLOSED-TYPE], whereas [\\<SUBSTOBJ\\>][class] refers
to the [GEB-DOCS/DOCS:@OPEN-TYPE] that allows for user extension."
  (substobj   pax:type)
  (<substobj> pax:class)
  "[SUBSTOBJ][type] type is not a constructor itself, instead it's
best viewed as the sum type, with the types below forming the
constructors for the term. In ML we would write it similarly to:

```haskell
type substobj = so0
              | so1
              | prod
              | coprod
```"
  (prod pax:type)
  (coprod pax:class)
  (so0 pax:class)
  (so1 pax:class)
  "The @GEB-ACCESSORS specific to @GEB-SUBSTMU"
  (mcar (pax:method () (prod)))
  (mcadr (pax:method () (prod)))

  (mcar  (pax:method () (coprod)))
  (mcadr (pax:method () (coprod))))

(pax:defsection @geb-realized (:title "Realized Subst Objs")
  "This section covers the [REALIZED-OBJECT][TYPE] type. This
represents a realized [SUBSTOBJ][type] term.

The [REALIZED-OBJECT][TYPE] is not a real constructor but rather a sum
type for the following type

```lisp
(deftype realized-object () `(or left right list so1 so0))
```

In ML we would have written something like

```haskell
type realized-object = so0
                     | so1
                     | list
                     | left
                     | right
```"
  (realized-object pax:type)
  (left  pax:class)
  (right pax:class)
  (left  pax:function)
  (right pax:function))

(pax:defsection @geb-substmorph (:title "Subst Morph")
  "The overarching types that categorizes the [SUBSTMORPH][type]
category. Note that [SUBSTMORPH][type] refers to the
[GEB-DOCS/DOCS:@CLOSED-TYPE], whereas [\\<SUBSTMORPH\\>][type] refers
to the [GEB-DOCS/DOCS:@OPEN-TYPE] that allows for user extension."
  (substmorph   pax:type)
  (<substmorph> pax:type)
  "[SUBSTMORPH][type] type is not a constructor itself, instead it's
best viewed as the sum type, with the types below forming the
constructors for the term. In ML we would write it similarly to:

```haskell
type substmorph = comp
                | substobj
                | case
                | init
                | terminal
                | pair
                | distribute
                | inject-left
                | inject-right
                | project-left
                | project-right
```

Note that an instance of [SUBSTOBJ][type], acts like the identity
morphism to the layout specified by the given [SUBSTOBJ][type]. Thus
we can view this as automatically lifting a [SUBSTOBJ][type] into a
[SUBSTMORPH][type]"
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
  (alias pax:macro)
  (make-alias pax:function)
  (has-aliasp pax:function)
  (<-left pax:function)
  (<-right pax:function)
  (->left pax:function)
  (->right pax:function)
  (mcase pax:function)
  (make-functor pax:function))

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
