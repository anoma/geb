(pax:define-package #:geb-docs/docs
  (:use #:cl)
  (:import-from #:geb        #:@geb)
  (:import-from #:geb.mixins #:@mixins)
  (:import-from #:geb.utils  #:@geb-utils-manual)
  (:import-from #:geb-test   #:@geb-test-manual)
  (:import-from #:geb.poly   #:@poly-manual)
  (:import-from #:geb.specs  #:@geb-specs)
  (:export build-docs))

(in-package geb-docs/docs)

(pax:defsection @index (:title "The GEB Manual")
  "Welcome to the GEB project."
  (@links            pax:section)
  (@getting-started  pax:section)
  (@original-efforts pax:section)
  (@model            pax:section)
  (@geb-specs        pax:section)
  (@geb              pax:section)
  (@poly-manual      pax:section)
  (@mixins           pax:section)
  (@geb-utils-manual pax:section)
  (@geb-test-manual  pax:section))

(pax:defsection @links (:title "Links")
  "
Here is the [official repository](https://github.com/anoma/geb/)
and the [HTML documentation](https://anoma.github.io/geb/) for the latest version")

(pax:defsection @getting-started (:title "Getting Started")
  "Welcome to the GEB Project!"
  (@installation pax:section)
  (@loading pax:section))

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
theorey.")

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
  "GEB is organizing programming language concepts (and entities!) using
   [category theory](https://plato.stanford.edu/entries/category-theory/),
   originally developped by mathematicians,
   but very much alive in (theoretical) computer science.
   Let us look at a simple well-known example:
   the category of sets and functions. 
   The lattter _together_ form **a** category—based on 
   function composition;
   lets call it _sets-'n'-functions_. 
   It is the bread and butter example:
   sets $A,B,C,…$ play the role of _objects_, 
   functions are _arrows_ between objects $A—f→B$, 
   and the latter _compose_ as functions do,
   such that every path of fitting functions
   $$A—f→B—g→C—h→D$$
   composes to a correponding composite function 
   $$A—f;g;h→D$$ (or $h∘g∘f$ if you prefer)
   and we enjoy the luxury of not having to worry about 
   the order in which we compose. 
   This example,
   even if you want to restrict to finite sets, 
   will permeate through GEB.
   <!--
   although the “weird” habit of avoiding
   talk about elements of sets as much as possible.
   -->
   
   One of the first lessons (in any introduction to category theory)
   about _sets-'n'-functions_ is in fact the characterization of
   [product](https://en.wikipedia.org/wiki/Product_(category_theory)#Product_of_two_objects)s 
   and [disjoint sum](https://en.wikipedia.org/wiki/Coproduct#Definition)s of sets
   in terms of functions alone,
   i.e., **without _ever_ talking about elements of sets**, 
   known as _universal properties_ of products and co-products. 
   One of the first surprises follows suit 
   when we replace functions by partial functions, 
   relations, or even multi-relations. 
   _We obtain **very** different categories!_
   For example, 
   in the category [_sets-'n'-relations_](https://en.wikipedia.org/wiki/Category_of_relations), 
   the disjoint union of sets features as both a product and a co-product,
   in terms of their universal properties. 

   _Do not fear!_
   The usual definition of products in terms of elements of sets are
   absolutely compatible with the
   universal properties in  _sets-'n'-functions_. 
   However we gain the possibililty 
   to compare the “effect” of the  _universal properties of products_ in 
   _sets-'n'-functions_ with its “effect” in _sets-'n'-relations_,
   because the _universal properties_ apply to **every** category.
   
   For the hasty reader, 
   for the purposes of GEB, 
   a solid understanding of _sets-'n'-functions_ will already be quite useful:
   many phenomena can be understood  
   in analogy to what happens in _sets-'n'-functions_. 
   In particular,
   we shall rely on the following structure of _sets-'n'-functions_: 

   1. The formation of binary products $A × B$ of sets $A,B$, and the empty product $1$.  

   2. The formation of “function spaces” $B^A$ of sets $A,B$, called _exponentials_, 
      i.e., collections of functions between pairs of sets. 
       
   3. The so-called [_currying_](https://en.wikipedia.org/wiki/Currying)
       of functions, 
      $C^{(B^A)} ≃ C^{(A × B)}$, 
      such that providing several arguments to a function can done
      either simultaneously, or in sequence. 

   4. The formation of sums (a.k.a.  co-products) $A + B$ of sets $A,B$, 
      corresponding to forming disjoint unions of sets; 
      the empty sum is $0$. 

   Seing product sums and exponentials, 
   note that we have all the operations to build polynomial 
   expressions like $4x^3 +x^2 - 3x^0$,
   except for _variables_! 
   Somewhat surprisingly,
   this last building block can be taken from 
   one of the most-well known fundamental results about category theory:
   the [Yoneda-Lemma](https://en.wikipedia.org/wiki/Yoneda_lemma), 
   which can be understood as a generalization of Cayley's Theorem. 
   
   If you are ready,
   buckle up and jump to @POLY-SETS, 
   have a look at our stream lined account of @yoneda-lemma, 
   or take it slow and review the background in one of 
   the classic or popular
   [textbooks](https://www.goodreads.com/shelf/show/category-theory). 
   "
  (@morphisms pax:section)
  (@objects pax:section)
  (@yoneda-lemma pax:section)
  (@poly-sets pax:section)
)

;; please insert more text here about category theory
(pax:defsection @morphisms (:title "Morphisms"))

(pax:defsection @objects (:title "Objects"))

(pax:defsection @yoneda-lemma (:title "The Yoneda Lemma"))

(pax:defsection @poly-sets (:title "Poly in Sets"))

(pax:defsection @installation (:title "installation")
  "This project uses [common lisp](https://common-lisp.net/), so a few
   dependencies are needed to get around the code-base and start hacking. Namely:

1. [lisp with quicklisp](https://lisp-lang.org/learn/getting-started/).

2. [Emacs](https://en.wikipedia.org/wiki/Emacs) along with one of the following:

    - [sly](https://github.com/joaotavora/sly)

        + [sly user manual](http://joaotavora.github.io/sly/)

    - [slime](https://github.com/slime/slime)

         + [slime user manual](http://www.chiark.greenend.org.uk/doc/slime/slime.pdf)")

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


2. From Emacs: open `geb.asd` and press `C-ck` (`sly-compile-and-load-file`, or
   `swank-compile-and-load-file` if you are using swank).

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
   @index :geb)
  (mgl-pax:update-asdf-system-html-docs
   @index :geb
   :target-dir (asdf/system:system-relative-pathname :geb "docs/")
   :pages (geb-pages)))

(pax:register-doc-in-pax-world :geb (geb-sections) (geb-pages))
