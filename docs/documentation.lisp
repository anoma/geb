(in-package geb-docs/docs)

(pythonic-string-reader:enable-pythonic-string-syntax)

(pax:defsection @index (:title "The GEB Manual")
  "Welcome to the GEB project."
  (@links            pax:section)
  (@getting-started  pax:section)
  (@glossary         pax:section)
  (@original-efforts pax:section)
  (@model            pax:section)
  (@idioms           pax:section)
  (@geb              pax:section)
  (@geb-extensions   pax:section)
  (@geb-gui-manual   pax:section)
  (@seqn-manual      pax:section)
  (@bitc-manual      pax:section)
  (@poly-manual      pax:section)
  (@stlc             pax:section)
  (@mixins           pax:section)
  (@geb-utils-manual pax:section)
  (@geb-test-manual  pax:section))

(pax:defsection @links (:title "Links")
  """
Here is the [official repository](https://github.com/anoma/geb/)

and [HTML documentation](https://anoma.github.io/geb/) for the latest version.

Maintainers: please read the [maintainers guide](https://github.com/anoma/geb/blob/main/docs/maintainers-guide.org)
"""
  (@coverage pax:section))

(pax:defsection @coverage (:title "code coverage")
  """
For test coverage it can be found at the following links:


[SBCL test coverage](./tests/cover-index.html)


[CCL test coverage: current under maintenance](./tests/report.html)

-----------------------------------------

Note that due to [#34](https://github.com/anoma/geb/issues/34)
CCL tests are not currently displaying

------------------------------------------

I recommend reading the CCL code coverage version, as it has proper tags.

Currently they are manually generated, and thus for a more accurate assessment see [GEB-TEST:CODE-COVERAGE][function]
""")

(pax:defsection @math-playground (:title "math-playground")
  """
Disabled by default, put in the @index if you want to render this

$\lbrace \text{and} \rbrace$


$\lambda \in \{ 2,3 \}.$

$\mathsf{3} = \{ 1, 2, 3 \}$

$\mathsf{3} = \{ 1, 2, 3 \}$

\curly{}

$$\mathsf{3} = \{ 1, 2, 3 \}$$

An inline $\int_0^\infty e^{-x^2} dx=\frac{\sqrt{\pi}}{2}$

a display $$\int_0^\infty e^{-x^2} dx=\frac{\sqrt{\pi}}{2}$$

hello [foo](1-foo)

[1-foo]: foo bar
""")

(pax:defsection @getting-started (:title "Getting Started")
  "Welcome to the GEB Project!"
  (@installation pax:section)
  (@loading pax:section)
  (@geb-entry pax:section))

(pax:defsection @original-efforts (:title "Original Efforts")
  "Originally GEB started off as an Idris codebase written by the
   designer and creator of GEB, Terence Rokop, However further efforts
   spawned for even further formal verification by Artem Gureev. Due
   to this, we have plenty of code not in Common Lisp that ought to be
   a good read."
  (@idris pax:section)
  (@agda  pax:section))

(pax:defsection @idris (:title "Geb's Idris Code")
  "The Idris folder can be found in the
[geb-idris](https://github.com/anoma/geb/tree/main/geb-idris) folder
provided in the codebase"
  "At the time of this document, there is over 16k lines of Idris code
written. This serves as the bulk of the POC that is GEB and is a
treasure trove of interesting information surrounding category
theory.")

(pax:defsection @agda (:title "Geb's Agda Code")
  "The Agda folder can be found in the
[geb-agda](https://github.com/anoma/geb/tree/main/geb-agda) folder
provided in the codebase"
  "The Agda codebase serves as a great place to view formally verified
properties about the GEB project. Although @IDRIS is written in a
dependently typed language, it serves as reference example of GEB,
while @AGDA serves as the mathematical formalism proving various
conjectures about GEB")

(pax:defsection @model (:title "Categorical Model")
  """Geb is organizing programming language concepts (and entities!) using
   [category theory](https://plato.stanford.edu/entries/category-theory/),
   originally developed by mathematicians,
   but very much alive in programming language theory.
   Let us look at a simple well-known example:
   the category of sets and functions.
   It is the bread and butter example:
   sets $A,B,C,…$ play the role of _objects_,
   functions are _arrows_ between objects $A—f→B$,
   and the latter _compose_ as functions do,
   such that every path of matching functions
   $$A—f→B—g→C—h→D$$
   composes to a corresponding composite function
   $$A—f;g;h→D$$ (or $h∘g∘f$ if you prefer)
   and we enjoy the luxury of not having to worry about
   the order in which we compose;
   for the sake of completeness,
   there are identify functions $A —\\mathrm{id}_A→ A$ on each set $A$,
   serving as identities
   (which correspond to the composite of the empty path on an object).
   Sets and functions _together_ form **a** category—based on
   function composition;
   thus, let's call this category _sets-'n'-functions_.
   This example,
   even “restricted” to  _finite sets-'n'-functions_,
   will permeate through Geb.
   <!--
   although the “weird” habit of avoiding
   talk about elements of sets as much as possible.
   -->

   One of the first lessons (in any introduction to category theory)
   about _sets-'n'-functions_ is the characterization of
   [product](https://en.wikipedia.org/wiki/Product_(category_theory)#Product_of_two_objects)s
   and [disjoint sum](https://en.wikipedia.org/wiki/Coproduct#Definition)s of sets
   in terms of functions alone,
   i.e.,
   **without _ever_ talking about elements of sets**.
   Products and co-products are the simplest examples of
   _universal constructions_.
   One of the first surprises follows suit
   when we generalize functions to partial functions,
   relations, or even multi-relations:
   _we obtain **very** different categories!_
   For example,
   in the category [_sets-'n'-relations_](https://en.wikipedia.org/wiki/Category_of_relations),
   the disjoint union of sets features as both a product and a co-product,
   as a categorical construction.

   _Do not fear!_
   The usual definition of products in terms of elements of sets are
   absolutely compatible with the
   universal construction in _sets-'n'-functions_.
   However we gain the possibility
   to compare the “result” of the  _universal constructions_
   in _sets-'n'-functions_ with the one in _sets-'n'-relations_
   (as both actually do have products).

   for the purposes of Geb,
   many things can be expressed in analogy to
   the category of _sets-'n'-functions_;
   thus a solid understanding of the latter
   will be quite useful.
   In particular,
   we shall rely on the following
   universal constructions:

   1. The construction of binary products $A × B$ of sets $A,B$, and the empty product $\mathsf{1}$.

   2. The construction of “function spaces” $B^A$ of sets $A,B$, called _exponentials_,
      i.e., collections of functions between pairs of sets.

   3. The so-called [_currying_](https://en.wikipedia.org/wiki/Currying)
       of functions,
      $C^{(B^A)} \cong C^{(A × B)}$,
      such that providing several arguments to a function can done
      either simultaneously, or in sequence.

   4. The construction of sums (a.k.a.  co-products) $A + B$ of sets $A,B$,
      corresponding to forming disjoint unions of sets;
      the empty sum is $\varnothing$.

   Product, sums and exponentials
   are the (almost) complete tool chest for writing
   polynomial expressions, e.g.,
   $$Ax^{\sf 2} +x^{\sf 1} - Dx^{\sf 0}.$$
   (We need these later to define [“algebraic data types”](https://en.wikipedia.org/wiki/Polynomial_functor_(type_theory)).)
   In the above expression,
   we have sets instead of numbers/constants
   where $ \mathsf{2} = \lbrace 1, 2 \rbrace$,
   $ \mathsf{1} = \lbrace 1 \rbrace$,
   $ \mathsf{0} = \lbrace  \rbrace = \varnothing$,
   and $A$ and $B$ are arbitrary (finite) sets.
   We are only missing a counterpart for the _variable_!
   Raising an arbitrary set to “the power” of a constant set
   happens to have a very natural counterpart:
   the central actor of
   [the most-well known fundamental result about categories](https://en.wikipedia.org/wiki/Yoneda_lemma),
   which generalizes Cayley's Theorem, i.e., the [Yoneda embedding](https://en.wikipedia.org/wiki/Yoneda_lemma#The_Yoneda_embedding).

   If you are familiar with the latter,
   buckle up and jump to @POLY-SETS.
   Have a look at our streamlined account of @YONEDA-LEMMA
   if you are familiar with Cartesian closed categories,
   or take it slow and read up on the background in
   one of the classic or popular
   [textbooks](https://www.goodreads.com/shelf/show/category-theory).
   Tastes tend to vary.
   However,
   Benjamin Pierce's
   [_Basic Category Theory for Computer Scientists_](https://mitpress.mit.edu/9780262660716/) deserves being pointed out
   as it is very amenable _and_
   covers the background we need in 60 short pages.
   """
  (@morphisms pax:section)
  (@objects pax:section)
  (@yoneda-lemma pax:section)
  (@poly-sets pax:section))

;; please insert more text here about category theory
(pax:defsection @morphisms (:title "Morphisms"))

(pax:defsection @objects (:title "Objects"))

(pax:defsection @yoneda-lemma (:title "The Yoneda Lemma"))

(pax:defsection @poly-sets (:title "Poly in Sets"))

(pax:defsection @installation (:title "installation")
  "This project uses [common lisp](https://common-lisp.net/), so a few
   dependencies are needed to get around the code-base and start hacking. Namely:

1. [lisp with quicklisp](https://lisp-lang.org/learn/getting-started/).

2. a) [Emacs](https://en.wikipedia.org/wiki/Emacs) along with one of the following:

    - [sly](https://github.com/joaotavora/sly)

        + [sly user manual](http://joaotavora.github.io/sly/)

    - [slime](https://github.com/slime/slime)

         + [slime user manual](http://www.chiark.greenend.org.uk/doc/slime/slime.pdf)

2. b) [Spacemacs](https://github.com/syl20bnr/spacemacs) along with:

    - [slime](https://github.com/slime/slime) via 
      [the common-lisplayer](https://www.spacemacs.org/layers/+lang/common-lisp/README.html)
      based on [sblc](https://www.sbcl.org/)")

(pax:defsection @loading (:title "loading")
  "Now that we have an environment setup, we can load the project, this
   can be done in a few steps.

1. Open the `REPL` (sbcl (terminal), `M-x` sly, `M-x` swank)

     - For the terminal, this is just calling the [common
       lisp](https://common-lisp.net/) implementation from the
       terminal.

          `user@system:geb-directory % sbcl`.

     - For Emacs, this is simply calling either `M-x sly` or `M-x slime`
       if you are using either [sly](https://github.com/joaotavora/sly) or [slime](https://github.com/slime/slime)

     - For Spacemacs, this is (also) `M-x slime` besides alternative key bindings

2. From Emacs: open `geb.asd` and press `C-ck` (`sly-compile-and-load-file`, or
   `swank-compile-and-load-file` if you are using swank).

3. From Spacemacs: open `geb.asd` and press `C-c C-k` (invoking
   `slime-compile-and-load-file`).

Now that we have the file open, we can now load the system by
writing:

```lisp
;; only necessary for the first time!
(ql:quickload :geb/documentation)

;; if you want to load it in the future
(asdf:load-system :geb/documentation)

;; if you want to load the codbase and run tests at the same time
(asdf:test-system :geb/documentation)

;; if you want to run the tests once the system is loaded!
(geb-test:run-tests)
```")

(pax:defsection @idioms (:title "Project Idioms and Conventions")
  "The Geb Project is written in [Common
Lisp](https://common-lisp.net/), which means the authors have a great
choice in freedom in how the project is laid out and operates. In
particular the style of [Common Lisp](https://common-lisp.net/) here
is a
[functional](https://en.wikipedia.org/wiki/Functional_programming)
style with some
[OO](https://en.wikipedia.org/wiki/Object-oriented_programming) idioms
in the style of [Smalltalk](https://en.wikipedia.org/wiki/Smalltalk).

The subsections will outline many idioms that can be found throughout
the codebase."
  (@geb-specs   pax:section)
  (@open-closed pax:section)
  (@<types>     pax:section))

(pax:defsection @open-closed (:title "Open Types versus Closed Types")
  "@CLOSED-TYPE's and @OPEN-TYPE's both have their perspective
tradeoff of openness versus exhaustiveness (see the linked articles
for more on that). Due to this, they both have their own favorable
applications. I would argue that a closed
[ADT](https://en.wikipedia.org/wiki/Algebraic_data_type) type is great
tool for looking at a function mathematically and treating the object
as a whole rather than piecemeal. Whereas a more open extension is
great for thinking about how a particular object/case behaves. They
are different mindsets for different styles of code.

In the geb project, we have chosen to accept both styles, and allow
both to coexist in the same setting. We have done this with a two part
idiom.

```lisp
(deftype substobj ()
  `(or alias prod coprod so0 so1))

(defclass <substobj> (direct-pointwise-mixin) ())

(defclass so0 (<substobj>) ...)

(defclass prod (<substobj>) ...)
```

The @CLOSED-TYPE is GEB:SUBSTOBJ, filling and defining every structure
it knows about. This is a fixed idea that a programmer may statically
update and get exhaustive warnings about. Whereas GEB:\\<SUBSTOBJ\\> is
the open interface for the type. Thus we can view [GEB:\\<SUBSTOBJ\\>] as
the general idea of a [GEB:SUBSTOBJ]. Before delving into how we combine
these methods, let us look at two other benefits given by [GEB:\\<SUBSTOBJ\\>]

1. We can put all the @MIXINS into the superclass to enforce that any
   type that extends it has the extended behaviors we wish. This is a
   great way to generically enhance the capabilities of the type
   without operating on it directly.

2. We can dispatch on GEB:\\<SUBSTOBJ\\> since DEFMETHOD only works on
   @CLOS types and not generic types in CL.

#### Methods for closed and open types

With these pieces in play let us explore how we write a method in a
way that is conducive to open and closed code.

```lisp
(in-package :geb)

(defgeneric to-poly (morphism))

(defmethod to-poly ((obj <substmorph>))
  (typecase-of substmorph obj
    (alias        ...)
    (substobj     (error \"Impossible\")
    (init          0)
    (terminal      0)
    (inject-left   poly:ident)
    (inject-right  ...)
    (comp          ...)
    (case          ...)
    (pair          ...)
    (project-right ...)
    (project-left  ...)
    (distribute    ...)
    (otherwise (subclass-responsibility obj))))

(defmethod to-poly ((obj <substobj>))
  (declare (ignore obj))
  poly:ident)
```

In this piece of code we can notice a few things:

1. We case on [GEB:SUBSTMORPH] exhaustively

2. We cannot hit the [GEB:\\<SUBSTOBJ\\>] case due to method dispatch

3. We have this [GEB.UTILS:SUBCLASS-RESPONSIBILITY] function getting called.

4. We can write further methods extending the function to other subtypes.

Thus the [GEB.COMMON:TO-POLY] function is written in such a way that it
supports a closed definition and open extensions, with
[GEB.UTILS:SUBCLASS-RESPONSIBILITY] serving to be called if an
extension a user wrote has no handling of this method.

Code can also be naturally written in a more open way as well, by
simply running methods on each class instead.

#### Potential Drawback and Fixes

One nasty drawback is that we can't guarantee the method exists. In
java this can easily be done with interfaces and then enforcing they
are fulfilled. Sadly CL has no such equivalent. However, this is all
easily implementable. If this ever becomes a major problem, it is
trivial to implement this by registering the subclasses, and the
perspective methods, and scouring the image for instance methods, and
computing if any parent class that isn't the one calling
responsibility fulfills it. Thus, in practice, you should be able to
ask the system if any particular extension fulfills what extension
sets that the base object has and give CI errors if they are not
fulfilled, thus enforcing closed behavior when warranted.")

(pax:defsection @<types> (:title "≺Types≻")
  "These refer to the @OPEN-TYPE variant to a @CLOSED-TYPE. Thus when
one sees a type like GEB:<SUBSTOBJ> it is the open version of
GEB:SUBSTOBJ. Read @OPEN-CLOSED for information on how to use them.")

(pax:defsection @motivation (:title "motivation"))

(defun geb-sections ()
  (list @index))

(defun geb-pages ()
  `((:objects
     (, @index)
     :source-uri-fn
     ,(pax:make-github-source-uri-fn :geb "https://github.com/anoma/geb"))))

(defun build-docs ()
  (mgl-pax:update-asdf-system-readmes
   @index :geb
   :formats '(:markdown :plain))
  (mgl-pax:update-asdf-system-html-docs
   @index :geb
   :target-dir (asdf/system:system-relative-pathname :geb "docs/")
   :pages (geb-pages)))

(pax:register-doc-in-pax-world :geb (geb-sections) (geb-pages))
