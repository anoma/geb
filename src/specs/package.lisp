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

(muffle-package-variance
 (defpackage #:geb.seqn.spec
   (:use #:geb.utils #:cl #:geb.mixins)))

;; please document this later.
(muffle-package-variance
 (uiop:define-package #:geb.lambda.spec
   (:documentation "Basic spec for creating lambda terms")
   (:mix #:trivia #:serapeum #:common-lisp #:geb.mixins)))

(pax:define-package #:geb.spec
  (:documentation "Gödel, Escher, Bach categorical model")
  (:use #:common-lisp #:serapeum #:geb.mixins #:geb.utils)
  (:shadow :left :right :prod :case)
  (:export :prod :case :mcar :mcadr :mcaddr :mcdr :name :func :obj
   :same-type-to-list :pair-to-list))

(muffle-package-variance
 (uiop:define-package #:geb.extension.spec
   (:documentation "Extensions of the various categories")
   (:mix #:trivia #:serapeum #:common-lisp #:geb.mixins #:geb.utils)))

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
;; Geb Seqn Package Documentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.seqn.spec)

(pax:defsection @seqn (:title "Seqn Types")
  (seqn             pax:type)
  (<seqn>           pax:class)
  (composition      pax:class)
  (id               pax:class)
  (parallel-seq     pax:class)
  (fork-seq         pax:class)
  (drop-nil         pax:class)
  (remove-right     pax:class)
  (remove-left      pax:class)
  (drop-width       pax:class)
  (inj-length-left  pax:class)
  (inj-length-right pax:class)
  (inj-size         pax:class)
  (branch-seq       pax:class)
  (shift-front      pax:class)
  (zero-bit         pax:class)
  (one-bit          pax:class)
  (seqn-add         pax:class)
  (seqn-subtract    pax:class)
  (seqn-multiply    pax:class)
  (seqn-divide      pax:class)
  (seqn-nat         pax:class)
  (seqn-concat      pax:class)
  (seqn-decompose   pax:class)
  (seqn-eq          pax:class)
  (seqn-lt          pax:class))

(pax:defsection @seqn-constructors (:title "Seqn Constructors")
  "Every accessor for each of the classes making up seqn"
  (composition      pax:function)
  (id               pax:function)
  (fork-seq         pax:function)
  (parallel-seq     pax:function)
  (drop-nil         pax:function)
  (remove-right     pax:function)
  (remove-left      pax:function)
  (drop-width       pax:function)
  (inj-length-left  pax:function)
  (inj-length-right pax:function)
  (inj-size         pax:function)
  (branch-seq       pax:function)
  (shift-front      pax:function)
  (zero-bit         pax:symbol-macro)
  (one-bit          pax:symbol-macro)
  (seqn-add         pax:function)
  (seqn-subtract    pax:function)
  (seqn-multiply    pax:function)
  (seqn-divide      pax:function)
  (seqn-nat         pax:function)
  (seqn-concat      pax:function)
  (seqn-decompose   pax:function)
  (seqn-eq          pax:function)
  (seqn-lt          pax:function))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Geb lambda Package Documentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.lambda.spec)

(pax:defsection @lambda-specs (:title "Lambda Specification")
  "This covers the various the abstract data type that is the simply
  typed lambda calculus within GEB. The class presents untyped STLC terms.
"
  (stlc pax:type)
  (<stlc> pax:class)

  (absurd pax:class)
  (unit pax:class)
  (left pax:class)
  (right pax:class)
  (case-on pax:class)
  (pair pax:class)
  (fst pax:class)
  (snd pax:class)
  (lamb pax:class)
  (app pax:class)
  (index pax:class)
  (err pax:class)
  (plus pax:class)
  (times pax:class)
  (minus pax:class)
  (divide pax:class) 
  (bit-choice pax:class)
  (lamb-eq pax:class)
  (lamb-lt pax:class)

  (absurd pax:function)
  (unit pax:function)
  (left pax:function)
  (right pax:function)
  (case-on pax:function)
  (pair pax:function)
  (fst pax:function)
  (snd pax:function)
  (lamb pax:function)
  (app pax:function)
  (index pax:function)
  (err pax:function)
  (plus pax:function)
  (times pax:function)
  (minus pax:function)
  (divide pax:function)
  (bit-choice pax:function)
  (lamb-eq    pax:function)
  (lamb-lt    pax:function)
  

  "Accessors of [ABSURD][class]"

  (tcod  (pax:method () (absurd)))
  (term  (pax:method () (absurd)))
  (ttype (pax:method () (absurd)))

  "Accessors of [UNIT][class]"
  (ttype (pax:method () (unit)))

  "Accessors of [LEFT][class]"
  (rty   (pax:method () (left)))
  (term  (pax:method () (left)))
  (ttype (pax:method () (left)))

  "Accessors of [RIGHT][class]"
  (lty   (pax:method () (right)))
  (term  (pax:method () (right)))
  (ttype (pax:method () (right)))

  "Accessors of [CASE-ON][class]"
  (on    (pax:method () (case-on)))
  (ltm   (pax:method () (case-on)))
  (rtm   (pax:method () (case-on)))
  (ttype (pax:method () (case-on)))

  "Accessors of [PAIR][class]"
  (ltm   (pax:method () (pair)))
  (rtm   (pax:method () (pair)))
  (ttype (pax:method () (pair)))

  "Accessors of [FST][class]"
  (term  (pax:method () (fst)))
  (ttype (pax:method () (fst)))

  "Accessors of [SND][class]"
  (term  (pax:method () (snd)))
  (ttype (pax:method () (snd)))

  "Accessors of [LAMB][class]"
  (tdom  (pax:method () (lamb)))
  (term  (pax:method () (lamb)))
  (ttype (pax:method () (lamb)))

  "Accessors of [APP][class]"
  (fun (pax:method () (app)))
  (term (pax:method () (app)))
  (ttype (pax:method () (app)))

  "Accessors of [INDEX][class]"
  (pos (pax:method () (index)))
  (ttype (pax:method () (index)))

  "Accessor of [ERR][class]"
  (ttype (pax:method () (err)))

  "Accessors of [PLUS][class]"
  (ltm   (pax:method () (plus)))
  (rtm   (pax:method () (plus)))
  (ttype (pax:method () (plus)))

  "Accessors of [TIMES][class]"
  (ltm   (pax:method () (times)))
  (rtm   (pax:method () (times)))
  (ttype (pax:method () (times)))

  "Accessors of [MINUS][class]"
  (ltm   (pax:method () (minus)))
  (rtm   (pax:method () (minus)))
  (ttype (pax:method () (minus)))

  "Accessors of [DIVIDE][class]"
  (ltm   (pax:method () (divide)))
  (rtm   (pax:method () (divide)))
  (ttype (pax:method () (divide)))

  "Accessors of [BIT-CHOICE][class]"
  (bitv  (pax:method () (bit-choice)))
  (ttype (pax:method () (bit-choice)))

  "Accessors of [LAMB-EQ][class]"
  (ltm   (pax:method () (lamb-eq)))
  (rtm   (pax:method () (lamb-eq)))
  (ttype (pax:method () (lamb-eq)))

  "Accessors of [LAMB-LT][class]"
  (ltm   (pax:method () (lamb-lt)))
  (rtm   (pax:method () (lamb-lt)))
  (ttype (pax:method () (lamb-lt)))

  (tcod pax:generic-function)
  (tdom pax:generic-function)
  (term pax:generic-function)
  (rty pax:generic-function)
  (lty pax:generic-function)
  (ltm pax:generic-function)
  (rtm pax:generic-function)
  (on pax:generic-function)
  (fun pax:generic-function)
  (pos pax:generic-function)
  (ttype pax:generic-function)
  (bitv pax:generic-function))

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
  (prod pax:class)
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
[GEB-DOCS/DOCS:@CLOSED-TYPE], whereas [\\<SUBSTMORPH\\>][class] refers
to the [GEB-DOCS/DOCS:@OPEN-TYPE] that allows for user extension."
  (substmorph   pax:type)
  (<substmorph> pax:class)
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
  (comp          pax:class)
  (case          pax:class)
  (init          pax:class)
  (terminal      pax:class)
  (pair          pax:class)
  (distribute    pax:class)
  (inject-left   pax:class)
  (inject-right  pax:class)
  (project-left  pax:class)
  (project-right pax:class)
  (functor       pax:class)
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

(in-package :geb.extension.spec)

(pax:defsection @geb-extensions (:title "Extension Sets for Categories")
  "This package contains many extensions one may see over the codebase.

Each extension adds an unique feature to the categories they are
extending. To learn more, read about the individual extension you are
interested in."
  "Common Sub expressions represent repeat logic that can be found
throughout any piece of code"
  (common-sub-expression      pax:class)
  (make-common-sub-expression pax:function)
  "The Opaque extension lets users write categorical objects and
  morphisms where their implementation hide the specifics of what
  types they are operating over"
  (opaque       pax:class)
  (reference    pax:class)
  (opaque-morph pax:class)
  (code  (pax:method () (opaque-morph)))
  (dom   (pax:method () (opaque-morph)))
  (codom (pax:method () (opaque-morph)))
  (code  (pax:method () (opaque)))
  (name  (pax:method () (opaque)))
  (name  (pax:method () (reference)))
  (reference    pax:function)
  (opaque-morph pax:function)
  (opaque       pax:function)
  "The Natural Object/Morphism extension allows to expand the core Geb category
   with additional constructors standing in for bt-sequence representation of
   natural numbers along with basic operation relating to those."
  (natobj       pax:type)
  (<natobj>     pax:class)

  (nat-width    pax:class)

  (num   (pax:method () (nat-width)))

  (nat-width    pax:function)

  (natmorph     pax:type)
  (<natmorph>   pax:class)

  (nat-add         pax:class)
  (nat-mult        pax:class)
  (nat-sub         pax:class)
  (nat-div         pax:class)
  (nat-const       pax:class)
  (nat-inj         pax:class)
  (nat-concat      pax:class)
  (one-bit-to-bool pax:class)
  (nat-decompose   pax:class)
  (nat-eq          pax:class)
  (nat-lt          pax:class)

  (num       (pax:method () (nat-add)))
  (num       (pax:method () (nat-mult)))
  (num       (pax:method () (nat-sub)))
  (num       (pax:method () (nat-div)))
  (num       (pax:method () (nat-const)))
  (pos       (pax:method () (nat-const)))
  (num       (pax:method () (nat-inj)))
  (num-left  (pax:method () (nat-concat)))
  (num-right (pax:method () (nat-concat)))
  (num       (pax:method () (nat-decompose)))
  (num       (pax:method () (nat-eq)))
  (num       (pax:method () (nat-lt)))

  (nat-add         pax:function)
  (nat-mult        pax:function)
  (nat-sub         pax:function)
  (nat-div         pax:function)
  (nat-const       pax:function)
  (nat-inj         pax:function)
  (nat-concat      pax:function)
  (one-bit-to-bool pax:function)
  (nat-decompose   pax:function)
  (nat-eq          pax:function)
  (nat-lt          pax:function)

  (num          pax:generic-function)
  (pos          pax:generic-function)
  (num-left     pax:generic-function)
  (num-right    pax:generic-function)

  (*one-bit-to-bool* pax:variable)
  (one-bit-to-bool   pax:symbol-macro))

