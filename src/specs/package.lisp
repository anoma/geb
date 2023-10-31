(in-package :geb.utils)

(muffle-package-variance
 (defpackage #:geb.specs
   (:use #:cl)))

(muffle-package-variance
 (defpackage #:geb.poly.spec
   (:shadow :+ :* :/ :- :mod)
   (:use #:geb.utils #:cl)
   (:export #:@poly #:@poly-constructors)))

(muffle-package-variance
 (defpackage #:geb.bitc.spec
   (:export :dom :codom)
   (:shadow :drop :fork)
   (:use #:geb.utils #:cl #:geb.mixins)
   (:export #:@bitc #:@bitc-constructors)))

(muffle-package-variance
 (defpackage #:geb.seqn.spec
   (:use #:geb.utils #:cl #:geb.mixins)
   (:export #:@seqn #:@seqn-constructors)))

;; please document this later.
(muffle-package-variance
 (uiop:define-package #:geb.lambda.spec
   (:documentation "Basic spec for creating lambda terms")
   (:mix #:trivia #:serapeum #:common-lisp #:geb.mixins)
   (:export #:@lambda-specs)))

(pax:define-package #:geb.spec
  (:documentation "Gödel, Escher, Bach categorical model")
  (:use #:common-lisp #:serapeum #:geb.mixins #:geb.utils)
  (:shadow :left :right :prod :case)
  (:export :prod :case :mcar :mcadr :mcaddr :mcdr :name :func :obj
   :same-type-to-list :pair-to-list
   #:@geb-categories #:@geb-substmu #:@geb-substmorph #:@geb-constructors #:@geb-realized))

(muffle-package-variance
 (uiop:define-package #:geb.extension.spec
   (:documentation "Extensions of the various categories")
   (:mix #:trivia #:serapeum #:common-lisp #:geb.mixins #:geb.utils)
   (:export #:@geb-extensions)))

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
  (poly    type)
  (<poly>  class)
  (ident   type)
  (+       type)
  (*       type)
  (/       type)
  (-       type)
  (mod     type)
  (compose type)
  (if-zero type)
  (if-lt   type))

(pax:defsection @poly-constructors (:title "Polynomial Constructors")
  "Every accessor for each of the CLASS's found here are from @GEB-ACCESSORS"
  (ident   pax:symbol-macro)
  (+       function)
  (*       function)
  (/       function)
  (-       function)
  (mod     function)
  (compose function)
  (if-zero function)
  (if-lt   function))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Geb Bits Package Documentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.bitc.spec)

(pax:defsection @bitc (:title "Bits Types")
  "This section covers the types of things one can find in the [BITS]
constructors"
  (bitc     type)
  (<bitc>   class)
  (compose  class)
  (fork     class)
  (parallel class)
  (swap     class)
  (one      class)
  (zero     class)
  (ident    class)
  (drop     class)
  (branch   class))

(pax:defsection @bitc-constructors (:title "Bits (Boolean Circuit) Constructors")
  "Every accessor for each of the CLASS's found here are from @GEB-ACCESSORS"
  (compose  function)
  (fork     function)
  (parallel function)
  (swap     function)
  (one      pax:symbol-macro)
  (zero     pax:symbol-macro)
  (ident    function)
  (drop     function)
  (branch   function))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Geb Seqn Package Documentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.seqn.spec)

(pax:defsection @seqn (:title "Seqn Types")
  (seqn             type)
  (<seqn>           class)
  (composition      class)
  (id               class)
  (parallel-seq     class)
  (fork-seq         class)
  (drop-nil         class)
  (remove-right     class)
  (remove-left      class)
  (drop-width       class)
  (inj-length-left  class)
  (inj-length-right class)
  (inj-size         class)
  (branch-seq       class)
  (shift-front      class)
  (zero-bit         class)
  (one-bit          class)
  (seqn-add         class)
  (seqn-subtract    class)
  (seqn-multiply    class)
  (seqn-divide      class)
  (seqn-nat         class)
  (seqn-concat      class)
  (seqn-decompose   class)
  (seqn-eq          class)
  (seqn-lt          class)
  (seqn-mod         class))

(pax:defsection @seqn-constructors (:title "Seqn Constructors")
  "Every accessor for each of the classes making up seqn"
  (composition      function)
  (id               function)
  (fork-seq         function)
  (parallel-seq     function)
  (drop-nil         function)
  (remove-right     function)
  (remove-left      function)
  (drop-width       function)
  (inj-length-left  function)
  (inj-length-right function)
  (inj-size         function)
  (branch-seq       function)
  (shift-front      function)
  (zero-bit         pax:symbol-macro)
  (one-bit          pax:symbol-macro)
  (seqn-add         function)
  (seqn-subtract    function)
  (seqn-multiply    function)
  (seqn-divide      function)
  (seqn-nat         function)
  (seqn-concat      function)
  (seqn-decompose   function)
  (seqn-eq          function)
  (seqn-lt          function)
  (seqn-mod         function))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Geb lambda Package Documentation
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package :geb.lambda.spec)

(pax:defsection @lambda-specs (:title "Lambda Specification")
  "This covers the various the abstract data type that is the simply
  typed lambda calculus within GEB. The class presents untyped STLC terms.
"
  (stlc type)
  (<stlc> class)

  (absurd class)
  (unit class)
  (left class)
  (right class)
  (case-on class)
  (pair class)
  (fst class)
  (snd class)
  (lamb class)
  (app class)
  (index class)
  (err class)
  (plus class)
  (times class)
  (minus class)
  (divide class) 
  (bit-choice class)
  (lamb-eq class)
  (lamb-lt class)
  (modulo  class)

  (absurd function)
  (unit function)
  (left function)
  (right function)
  (case-on function)
  (pair function)
  (fst function)
  (snd function)
  (lamb function)
  (app function)
  (index function)
  (err function)
  (plus function)
  (times function)
  (minus function)
  (divide function)
  (bit-choice function)
  (lamb-eq    function)
  (lamb-lt    function)
  (absurd     function)
  

  "Accessors of [ABSURD][class]"

  (tcod  (method () (absurd)))
  (term  (method () (absurd)))
  (ttype (method () (absurd)))

  "Accessors of [UNIT][class]"
  (ttype (method () (unit)))

  "Accessors of [LEFT][class]"
  (rty   (method () (left)))
  (term  (method () (left)))
  (ttype (method () (left)))

  "Accessors of [RIGHT][class]"
  (lty   (method () (right)))
  (term  (method () (right)))
  (ttype (method () (right)))

  "Accessors of [CASE-ON][class]"
  (on    (method () (case-on)))
  (ltm   (method () (case-on)))
  (rtm   (method () (case-on)))
  (ttype (method () (case-on)))

  "Accessors of [PAIR][class]"
  (ltm   (method () (pair)))
  (rtm   (method () (pair)))
  (ttype (method () (pair)))

  "Accessors of [FST][class]"
  (term  (method () (fst)))
  (ttype (method () (fst)))

  "Accessors of [SND][class]"
  (term  (method () (snd)))
  (ttype (method () (snd)))

  "Accessors of [LAMB][class]"
  (tdom  (method () (lamb)))
  (term  (method () (lamb)))
  (ttype (method () (lamb)))

  "Accessors of [APP][class]"
  (fun (method () (app)))
  (term (method () (app)))
  (ttype (method () (app)))

  "Accessors of [INDEX][class]"
  (pos (method () (index)))
  (ttype (method () (index)))

  "Accessor of [ERR][class]"
  (ttype (method () (err)))

  "Accessors of [PLUS][class]"
  (ltm   (method () (plus)))
  (rtm   (method () (plus)))
  (ttype (method () (plus)))

  "Accessors of [TIMES][class]"
  (ltm   (method () (times)))
  (rtm   (method () (times)))
  (ttype (method () (times)))

  "Accessors of [MINUS][class]"
  (ltm   (method () (minus)))
  (rtm   (method () (minus)))
  (ttype (method () (minus)))

  "Accessors of [DIVIDE][class]"
  (ltm   (method () (divide)))
  (rtm   (method () (divide)))
  (ttype (method () (divide)))

  "Accessors of [BIT-CHOICE][class]"
  (bitv  (method () (bit-choice)))
  (ttype (method () (bit-choice)))

  "Accessors of [LAMB-EQ][class]"
  (ltm   (method () (lamb-eq)))
  (rtm   (method () (lamb-eq)))
  (ttype (method () (lamb-eq)))

  "Accessors of [LAMB-LT][class]"
  (ltm   (method () (lamb-lt)))
  (rtm   (method () (lamb-lt)))
  (ttype (method () (lamb-lt)))

  "Accessors of [MODULO][class]"
  (ltm   (method () (modulo)))
  (rtm   (method () (modulo)))
  (ttype (method () (modulo)))

  (tcod generic-function)
  (tdom generic-function)
  (term generic-function)
  (rty generic-function)
  (lty generic-function)
  (ltm generic-function)
  (rtm generic-function)
  (on generic-function)
  (fun generic-function)
  (pos generic-function)
  (ttype generic-function)
  (bitv generic-function))

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
  (substobj   type)
  (<substobj> class)
  "[SUBSTOBJ][type] type is not a constructor itself, instead it's
best viewed as the sum type, with the types below forming the
constructors for the term. In ML we would write it similarly to:

```haskell
type substobj = so0
              | so1
              | prod
              | coprod
```"
  (prod class)
  (coprod class)
  (so0 class)
  (so1 class)
  "The @GEB-ACCESSORS specific to @GEB-SUBSTMU"
  (mcar (method () (prod)))
  (mcadr (method () (prod)))

  (mcar  (method () (coprod)))
  (mcadr (method () (coprod))))

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
  (realized-object type)
  (left  class)
  (right class)
  (left  function)
  (right function))

(pax:defsection @geb-substmorph (:title "Subst Morph")
  "The overarching types that categorizes the [SUBSTMORPH][type]
category. Note that [SUBSTMORPH][type] refers to the
[GEB-DOCS/DOCS:@CLOSED-TYPE], whereas [\\<SUBSTMORPH\\>][class] refers
to the [GEB-DOCS/DOCS:@OPEN-TYPE] that allows for user extension."
  (substmorph   type)
  (<substmorph> class)
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
  (comp          class)
  (case          class)
  (init          class)
  (terminal      class)
  (pair          class)
  (distribute    class)
  (inject-left   class)
  (inject-right  class)
  (project-left  class)
  (project-right class)
  (functor       class)
  "The @GEB-ACCESSORS specific to @GEB-SUBSTMORPH"
  (mcar  (method () (comp)))
  (mcadr (method () (comp)))

  (obj (method () (init)))

  (obj (method () (init)))

  (mcar  (method () (case)))
  (mcadr (method () (case)))

  (mcar (method () (pair)))
  (mcdr (method () (pair)))

  (mcar   (method () (distribute)))
  (mcadr  (method () (distribute)))
  (mcaddr (method () (distribute)))

  (mcar  (method () (inject-left)))
  (mcadr (method () (inject-left)))

  (mcar  (method () (inject-right)))
  (mcadr (method () (inject-right)))

  (mcar  (method () (project-left)))
  (mcadr (method () (project-left)))

  (mcar  (method () (project-right)))
  (mcadr (method () (project-right))))

(pax:defsection @geb-constructors (:title "Constructors")
  "The API for creating GEB terms. All the functions and variables
   here relate to instantiating a term"
  (*so0* variable)
  (*so1* variable)
  "More Ergonomic API variants for *SO0* and *SO1*"
  (so0 pax:symbol-macro)
  (so1 pax:symbol-macro)
  (alias pax:macro)
  (make-alias function)
  (has-aliasp function)
  (<-left function)
  (<-right function)
  (->left function)
  (->right function)
  (mcase function)
  (make-functor function))

(in-package :geb.extension.spec)

(pax:defsection @geb-extensions (:title "Extension Sets for Categories")
  "This package contains many extensions one may see over the codebase.

Each extension adds an unique feature to the categories they are
extending. To learn more, read about the individual extension you are
interested in."
  "Common Sub expressions represent repeat logic that can be found
throughout any piece of code"
  (common-sub-expression      class)
  (make-common-sub-expression function)
  "The Opaque extension lets users write categorical objects and
  morphisms where their implementation hide the specifics of what
  types they are operating over"
  (opaque       class)
  (reference    class)
  (opaque-morph class)
  (code  (method () (opaque-morph)))
  (dom   (method () (opaque-morph)))
  (codom (method () (opaque-morph)))
  (code  (method () (opaque)))
  (name  (method () (opaque)))
  (name  (method () (reference)))
  (reference    function)
  (opaque-morph function)
  (opaque       function)
  "The Natural Object/Morphism extension allows to expand the core Geb category
   with additional constructors standing in for bt-sequence representation of
   natural numbers along with basic operation relating to those."
  (natobj       type)
  (<natobj>     class)

  (nat-width    class)

  (num   (method () (nat-width)))

  (nat-width    function)

  (natmorph     type)
  (<natmorph>   class)

  (nat-add         class)
  (nat-mult        class)
  (nat-sub         class)
  (nat-div         class)
  (nat-const       class)
  (nat-inj         class)
  (nat-concat      class)
  (one-bit-to-bool class)
  (nat-decompose   class)
  (nat-eq          class)
  (nat-lt          class)
  (nat-mod         class)

  (num       (method () (nat-add)))
  (num       (method () (nat-mult)))
  (num       (method () (nat-sub)))
  (num       (method () (nat-div)))
  (num       (method () (nat-const)))
  (pos       (method () (nat-const)))
  (num       (method () (nat-inj)))
  (num-left  (method () (nat-concat)))
  (num-right (method () (nat-concat)))
  (num       (method () (nat-decompose)))
  (num       (method () (nat-eq)))
  (num       (method () (nat-lt)))
  (num       (method () (nat-mod)))

  (nat-add         function)
  (nat-mult        function)
  (nat-sub         function)
  (nat-div         function)
  (nat-const       function)
  (nat-inj         function)
  (nat-concat      function)
  (one-bit-to-bool function)
  (nat-decompose   function)
  (nat-eq          function)
  (nat-lt          function)
  (nat-mod         function)

  (num          generic-function)
  (pos          generic-function)
  (num-left     generic-function)
  (num-right    generic-function)

  (*one-bit-to-bool* variable)
  (one-bit-to-bool   pax:symbol-macro))

