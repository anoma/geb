<a id="x-28GEB-DOCS-2FDOCS-3A-40INDEX-20MGL-PAX-3ASECTION-29"></a>
# The GEB Manual

## Table of Contents

- [1 Links][9bc5]
    - [1.1 code coverage][4044]
- [2 Getting Started][3d47]
    - [2.1 installation][8fa5]
    - [2.2 loading][a7d5]
    - [2.3 Geb as a binary][8eb0]
- [3 Glossary][25f0]
- [4 Original Efforts][3686]
    - [4.1 Geb's Idris Code][8311]
    - [4.2 Geb's Agda Code][29b7]
- [5 Categorical Model][c2e9]
    - [5.1 Morphisms][ada9]
    - [5.2 Objects][dbe7]
    - [5.3 The Yoneda Lemma][0e00]
    - [5.4 Poly in Sets][925b]
- [6 Project Idioms and Conventions][b9f3]
    - [6.1 Spec Files, Main Files and Project Layout][9f9c]
    - [6.2 Open Types versus Closed Types][a920]
    - [6.3 ≺Types≻][a300]
- [7 The Geb Model][c1fb]
    - [7.1 The Categorical Interface][e91b]
    - [7.2 Core Category][cb9e]
        - [7.2.1 Subst Obj][c1b3]
        - [7.2.2 Subst Morph][d2d1]
    - [7.3 Accessors][cc51]
    - [7.4 Constructors][2ad4]
    - [7.5 API][6228]
        - [7.5.1 Booleans][399c]
        - [7.5.2 Translation Functions][b79a]
        - [7.5.3 Utility][49d4]
    - [7.6 Examples][a17b]
- [8 The GEB GUI][6f67]
    - [8.1 Visualizer][c6cf]
        - [8.1.1 Aiding the Visualizer][603e]
    - [8.2 The GEB Graphizer][1b98]
        - [8.2.1 The GEB Graphizer Core][71e9]
        - [8.2.2 The GEB Graphizer Passes][e429]
- [9 Polynomial Specification][94a8]
    - [9.1 Polynomial Types][bd81]
    - [9.2 Polynomial Constructors][b76d]
    - [9.3 Polynomial Transformations][0f3e]
- [10 The Simply Typed Lambda Calculus model][db8f]
    - [10.1 Lambda Specification][34d0]
    - [10.2 Main functionality][d2d5]
    - [10.3 Transition Functions][e3e4]
        - [10.3.1 Utility Functionality][0609]
- [11 Mixins][723a]
    - [11.1 Pointwise Mixins][d5d3]
    - [11.2 Pointwise API][2fcf]
    - [11.3 Mixins Examples][4938]
    - [11.4 Metadata Mixin][9300]
        - [11.4.1 Performance][455b]
- [12 Geb Utilities][4ffa]
    - [12.1 Accessors][cc51]
- [13 Testing][9bcb]

###### \[in package GEB-DOCS/DOCS\]
Welcome to the GEB project.

<a id="x-28GEB-DOCS-2FDOCS-3A-40LINKS-20MGL-PAX-3ASECTION-29"></a>
## 1 Links

Here is the [official repository](https://github.com/anoma/geb/)

and [HTML documentation](https://anoma.github.io/geb/) for the latest version.

<a id="x-28GEB-DOCS-2FDOCS-3A-40COVERAGE-20MGL-PAX-3ASECTION-29"></a>
### 1.1 code coverage

For test coverage it can be found at the following links:

[SBCL test coverage](./tests/cover-index.html)

[CCL test coverage: current under maintenance](./tests/report.html)

---

Note that due to [#34](https://github.com/anoma/geb/issues/34)
CCL tests are not currently displaying

---

I recommend reading the CCL code coverage version, as it has proper tags.

Currently they are manually generated, and thus for a more accurate assessment see [`GEB-TEST:CODE-COVERAGE`][417f]

<a id="x-28GEB-DOCS-2FDOCS-3A-40GETTING-STARTED-20MGL-PAX-3ASECTION-29"></a>
## 2 Getting Started

Welcome to the GEB Project!

<a id="x-28GEB-DOCS-2FDOCS-3A-40INSTALLATION-20MGL-PAX-3ASECTION-29"></a>
### 2.1 installation

This project uses [common lisp](https://common-lisp.net/), so a few
   dependencies are needed to get around the code-base and start hacking. Namely:

1. [lisp with quicklisp](https://lisp-lang.org/learn/getting-started/).

2. [Emacs](https://en.wikipedia.org/wiki/Emacs) along with one of the following:

    - [sly](https://github.com/joaotavora/sly)

        - [sly user manual](http://joaotavora.github.io/sly/)

    - [slime](https://github.com/slime/slime)

        - [slime user manual](http://www.chiark.greenend.org.uk/doc/slime/slime.pdf)


<a id="x-28GEB-DOCS-2FDOCS-3A-40LOADING-20MGL-PAX-3ASECTION-29"></a>
### 2.2 loading

Now that we have an environment setup, we can load the project, this
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
```


<a id="x-28GEB-2EENTRY-3A-40GEB-ENTRY-20MGL-PAX-3ASECTION-29"></a>
### 2.3 Geb as a binary

###### \[in package GEB.ENTRY\]
The standard way to use geb currently is by loading the code into
one's lisp environment

```lisp
(ql:quickload :geb)
```

However, one may be interested in running geb in some sort of
compilation process, that is why we also give out a binary for people
to use

An example use of this binary is as follows

```bash
mariari@Gensokyo % ./geb.image -i "foo.lisp" -e "geb.lambda.spec::*entry*" -l -v -o "foo.pir"

mariari@Gensokyo % cat foo.pir
def *entry* x {
  0
}%
mariari@Gensokyo % ./geb.image -i "foo.lisp" -e "geb.lambda.spec::*entry*" -l -v
def *entry* x {
  0
}

./geb.image -h
  -i --input                      string   Input geb file location
  -e --entry-point                string   The function to run, should be fully qualified I.E.
                                           geb::my-main
  -l --stlc                       boolean  Use the simply typed lambda calculus frontend
  -o --output                     string   Save the output to a file rather than printing
  -v --vampir                     string   Return a vamp-ir expression
  -h -? --help                    boolean  The current help message

```

starting from a file *foo.lisp* that has

```lisp
(in-package :geb.lambda.spec)

(defparameter *entry*
  (typed unit geb:so1))
```

inside of it.

The command needs an entry-point (-e or --entry-point), as we are
simply call [`LOAD`][f766] on the given file, and need to know what to
translate.

from `STLC`, we expect the form to be wrapped in the
GEB.LAMBDA.SPEC.TYPED which takes both the type and the value to
properly have enough context to evaluate.

It is advised to bind this to a parameter like in our example as -e
expects a symbol.

the -l flag means that we are not expecting a geb term, but rather a
lambda frontend term, this is to simply notify us to compile it as a
lambda term rather than a geb term. In time this will go away

<a id="x-28GEB-2EENTRY-3ACOMPILE-DOWN-20FUNCTION-29"></a>
- [function] **COMPILE-DOWN** *&KEY VAMPIR STLC ENTRY (STREAM \*STANDARD-OUTPUT\*)*

<a id="x-28GEB-DOCS-2FDOCS-3A-40GLOSSARY-20MGL-PAX-3ASECTION-29"></a>
## 3 Glossary

<a id="x-28GEB-DOCS-2FDOCS-3A-40CLOSED-TYPE-20MGL-PAX-3AGLOSSARY-TERM-29"></a>
- [glossary-term] **closed type**

    A closed type is a type that can not be extended dynamically.
    A good example of this kind of term is an ML
    [ADT](https://en.wikipedia.org/wiki/Algebraic_data_type).
    
    ```haskell
    data Tree = Empty
              | Leaf Int
              | Node Tree Tree
    ```
    
    In our lisp code we have a very similar convention:
    
    ```lisp
    (in-package :geb.spec)
    
    (deftype substmorph ()
      `(or substobj
           alias
           comp init terminal case pair distribute
           inject-left inject-right
           project-left project-right))
    ```
    
    This type is closed, as only one of [`GEB:SUBSTOBJ`][3173], [`GEB:INJECT-LEFT`][cab9],
    [`GEB:INJECT-RIGHT`][fae9] etc can form the [`GEB:SUBSTMORPH`][57dc] type.
    
    The main benefit of this form is that we can be exhaustive over what
    can be found in `GEB:SUBSTMORPH`.
    
    ```lisp
    (defun so-hom-obj (x z)
      (match-of substobj x
        (so0          so1)
        (so1          z)
        (alias        (so-hom-obj (obj x) z))
        ((coprod x y) (prod (so-hom-obj x z)
                            (so-hom-obj y z)))
        ((prod x y)   (so-hom-obj x (so-hom-obj y z)))))
    ```
    
    If we forget a case, like [`GEB:COPROD`][fb12] it wanrs us with an non exhaustion warning.
    
    Meaning that if we update definitions this works well.
    
    ---
    
    The main downside is that we can not extend the type after the fact,
    meaning that all interfaces on SO-HOM-OBJ must take the unaltered
    type. This is in stark contrast to [open type][4a87]s. To find out more about
    the trade offs and usage in the code-base read the section [Open Types versus Closed Types][a920].

<a id="x-28GEB-DOCS-2FDOCS-3A-40OPEN-TYPE-20MGL-PAX-3AGLOSSARY-TERM-29"></a>
- [glossary-term] **open type**

    An open type is a type that can be extended by user code down the
    line. A good example of this in ML is the [type class
    system](https://en.wikipedia.org/wiki/Type_class) found in Haskell.
    
    In our code base, it is simple as creating a [Common Lisp Object System (CLOS)][ecc6] term
    
    ```lisp
    (defclass <substobj> (direct-pointwise-mixin) ())
    ```
    
    and to create a child of it all we need to do is.
    
    ```lisp
    (defclass so0 (<substobj>) ())
    ```
    
    Now any methods on [`GEB:<SUBSTOBJ>`][8214] will cover `GEB:SO0`([`0`][7088] [`1`][1f3a]).
    
    ---
    
    The main disadvantage of these is that exhaustion can not be checked,
    and thus the user has to know what methods to fill out. In a system
    with a bit more checks this is not a problem in practice. To find out
    more about the trade offs and usage in the code-base read the section
    [Open Types versus Closed Types][a920].

<a id="x-28GEB-DOCS-2FDOCS-3A-40CLOS-20MGL-PAX-3AGLOSSARY-TERM-29"></a>
- [glossary-term] **Common Lisp Object System (CLOS)**

    The object system found in CL. Has great features like a [Meta Object
    Protocol](http://community.schemewiki.org/?meta-object-protocol) that
    helps it facilitate extensions.

<a id="x-28GEB-DOCS-2FDOCS-3A-40ORIGINAL-EFFORTS-20MGL-PAX-3ASECTION-29"></a>
## 4 Original Efforts

Originally GEB started off as an Idris codebase written by the
designer and creator of GEB, Terence Rokop, However further efforts
spawned for even further formal verification by Artem Gureev. Due
to this, we have plenty of code not in Common Lisp that ought to be
a good read.

<a id="x-28GEB-DOCS-2FDOCS-3A-40IDRIS-20MGL-PAX-3ASECTION-29"></a>
### 4.1 Geb's Idris Code

The Idris folder can be found in the
[geb-idris](https://github.com/anoma/geb/tree/main/geb-idris) folder
provided in the codebase

At the time of this document, there is over 16k lines of Idris code
written. This serves as the bulk of the POC that is GEB and is a
treasure trove of interesting information surrounding category
theory.

<a id="x-28GEB-DOCS-2FDOCS-3A-40AGDA-20MGL-PAX-3ASECTION-29"></a>
### 4.2 Geb's Agda Code

The Agda folder can be found in the
[geb-agda](https://github.com/anoma/geb/tree/main/geb-agda) folder
provided in the codebase

The Agda codebase serves as a great place to view formally verified
properties about the GEB project. Although [Geb's Idris Code][8311] is written in a
dependently typed language, it serves as reference example of GEB,
while [Geb's Agda Code][29b7] serves as the mathematical formalism proving various
conjectures about GEB

<a id="x-28GEB-DOCS-2FDOCS-3A-40MODEL-20MGL-PAX-3ASECTION-29"></a>
## 5 Categorical Model

Geb is organizing programming language concepts (and entities!) using
[category theory](https://plato.stanford.edu/entries/category-theory/),
originally developed by mathematicians,
but very much alive in programming language theory.
Let us look at a simple well-known example:
the category of sets and functions.
It is the bread and butter example:
sets $A,B,C,…$ play the role of *objects*,
functions are *arrows* between objects $A—f→B$,
and the latter *compose* as functions do,
such that every path of matching functions
$$A—f→B—g→C—h→D$$
composes to a corresponding composite function
$$A—f;g;h→D$$ (or $h∘g∘f$ if you prefer)
and we enjoy the luxury of not having to worry about
the order in which we compose;
for the sake of completeness,
there are identify functions $A —\mathrm{id}\_A→ A$ on each set $A$,
serving as identities
(which correspond to the composite of the empty path on an object).
Sets and functions *together* form **a** category—based on
function composition;
thus, let's call this category *sets-'n'-functions*.
This example,
even “restricted” to  *finite sets-'n'-functions*,
will permeate through Geb.
<!--
although the “weird” habit of avoiding
talk about elements of sets as much as possible.
-->

One of the first lessons (in any introduction to category theory)
about *sets-'n'-functions* is the characterization of
[product](https://en.wikipedia.org/wiki/Product_(category_theory)#Product_of_two_objects)s
and [disjoint sum](https://en.wikipedia.org/wiki/Coproduct#Definition)s of sets
in terms of functions alone,
i.e.,
**without *ever* talking about elements of sets**.
Products and co-products are the simplest examples of
*universal constructions*.
One of the first surprises follows suit
when we generalize functions to partial functions,
relations, or even multi-relations:
*we obtain **very** different categories!*
For example,
in the category [*sets-'n'-relations*](https://en.wikipedia.org/wiki/Category_of_relations),
the disjoint union of sets features as both a product and a co-product,
as a categorical construction.

*Do not fear!*
The usual definition of products in terms of elements of sets are
absolutely compatible with the
universal construction in *sets-'n'-functions*.
However we gain the possibility
to compare the “result” of the  *universal constructions*
in *sets-'n'-functions* with the one in *sets-'n'-relations*
(as both actually do have products).

for the purposes of Geb,
many things can be expressed in analogy to
the category of *sets-'n'-functions*;
thus a solid understanding of the latter
will be quite useful.
In particular,
we shall rely on the following
universal constructions:

1. The construction of binary products $A × B$ of sets $A,B$, and the empty product $\mathsf{1}$.

2. The construction of “function spaces” $B^A$ of sets $A,B$, called *exponentials*,
   i.e., collections of functions between pairs of sets.

3. The so-called [*currying*](https://en.wikipedia.org/wiki/Currying)
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
We are only missing a counterpart for the *variable*!
Raising an arbitrary set to “the power” of a constant set
happens to have a very natural counterpart:
the central actor of
[the most-well known fundamental result about categories](https://en.wikipedia.org/wiki/Yoneda_lemma),
which generalizes Cayley's Theorem, i.e., the [Yoneda embedding](https://en.wikipedia.org/wiki/Yoneda_lemma#The_Yoneda_embedding).

If you are familiar with the latter,
buckle up and jump to [Poly in Sets][925b].
Have a look at our streamlined account of [The Yoneda Lemma][0e00]
if you are familiar with Cartesian closed categories,
or take it slow and read up on the background in
one of the classic or popular
[textbooks](https://www.goodreads.com/shelf/show/category-theory).
Tastes tend to vary.
However,
Benjamin Pierce's
[*Basic Category Theory for Computer Scientists*](https://mitpress.mit.edu/9780262660716/) deserves being pointed out
as it is very amenable *and*
covers the background we need in 60 short pages.

<a id="x-28GEB-DOCS-2FDOCS-3A-40MORPHISMS-20MGL-PAX-3ASECTION-29"></a>
### 5.1 Morphisms


<a id="x-28GEB-DOCS-2FDOCS-3A-40OBJECTS-20MGL-PAX-3ASECTION-29"></a>
### 5.2 Objects


<a id="x-28GEB-DOCS-2FDOCS-3A-40YONEDA-LEMMA-20MGL-PAX-3ASECTION-29"></a>
### 5.3 The Yoneda Lemma


<a id="x-28GEB-DOCS-2FDOCS-3A-40POLY-SETS-20MGL-PAX-3ASECTION-29"></a>
### 5.4 Poly in Sets


<a id="x-28GEB-DOCS-2FDOCS-3A-40IDIOMS-20MGL-PAX-3ASECTION-29"></a>
## 6 Project Idioms and Conventions

The Geb Project is written in [Common
Lisp](https://common-lisp.net/), which means the authors have a great
choice in freedom in how the project is laid out and operates. In
particular the style of [Common Lisp](https://common-lisp.net/) here
is a
[functional](https://en.wikipedia.org/wiki/Functional_programming)
style with some
[OO](https://en.wikipedia.org/wiki/Object-oriented_programming) idioms
in the style of [Smalltalk](https://en.wikipedia.org/wiki/Smalltalk).

The subsections will outline many idioms that can be found throughout
the codebase.

<a id="x-28GEB-2ESPECS-3A-40GEB-SPECS-20MGL-PAX-3ASECTION-29"></a>
### 6.1 Spec Files, Main Files and Project Layout

###### \[in package GEB.SPECS\]
The codebase is split between many files. Each folder can be seen as
a different idea within geb itself! Thus the `poly` has packages
revolving around polynomials, the `geb` folder has packages regarding
the main types of geb [Subst Obj][c1b3] and
[Subst Morph][d2d1], etc etc.

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
structures of the [Polynomial Types][bd81], this is then rexported
in `geb.poly`, giving the module `geb.poly` a convenient interface for
all functions that operate on `geb.poly`.

<a id="x-28GEB-DOCS-2FDOCS-3A-40OPEN-CLOSED-20MGL-PAX-3ASECTION-29"></a>
### 6.2 Open Types versus Closed Types

[closed type][8932]'s and [open type][4a87]'s both have their perspective
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

The [closed type][8932] is [`GEB:SUBSTOBJ`][3173], filling and defining every structure
it knows about. This is a fixed idea that a programmer may statically
update and get exhaustive warnings about. Whereas [`GEB:<SUBSTOBJ>`][8214] is
the open interface for the type. Thus we can view [`GEB:<SUBSTOBJ>`][8214] as
the general idea of a [`GEB:SUBSTOBJ`][3173]. Before delving into how we combine
these methods, let us look at two other benefits given by [`GEB:<SUBSTOBJ>`][8214]

1. We can put all the [Mixins][723a] into the superclass to enforce that any
   type that extends it has the extended behaviors we wish. This is a
   great way to generically enhance the capabilities of the type
   without operating on it directly.

2. We can dispatch on `GEB:<SUBSTOBJ>` since [`DEFMETHOD`][a981] only works on
   [Common Lisp Object System (CLOS)][ecc6] types and not generic types in CL.

#### Methods for closed and open types

With these pieces in play let us explore how we write a method in a
way that is conducive to open and closed code.

```lisp
(in-package :geb)

(defgeneric to-poly (morphism))

(defmethod to-poly ((obj <substmorph>))
  (typecase-of substmorph obj
    (alias        ...)
    (substobj     (error "Impossible")
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

1. We case on [`GEB:SUBSTMORPH`][57dc] exhaustively

2. We cannot hit the [`GEB:<SUBSTOBJ>`][8214] case due to method dispatch

3. We have this [`GEB.UTILS:SUBCLASS-RESPONSIBILITY`][2276] function getting called.

4. We can write further methods extending the function to other subtypes.

Thus the [`GEB:TO-POLY`][642a] function is written in such a way that it
supports a closed definition and open extensions, with
[`GEB.UTILS:SUBCLASS-RESPONSIBILITY`][2276] serving to be called if an
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
fulfilled, thus enforcing closed behavior when warranted.

<a id="x-28GEB-DOCS-2FDOCS-3A-40-3CTYPES-3E-20MGL-PAX-3ASECTION-29"></a>
### 6.3 ≺Types≻

These refer to the [open type][4a87] variant to a [closed type][8932]. Thus when
one sees a type like GEB:<SUBSTOBJ> it is the open version of
[`GEB:SUBSTOBJ`][3173]. Read [Open Types versus Closed Types][a920] for information on how to use them.

<a id="x-28GEB-3A-40GEB-20MGL-PAX-3ASECTION-29"></a>
## 7 The Geb Model

###### \[in package GEB\]
Everything here relates directly to the underlying machinery of
GEB, or to abstractions that help extend it.

<a id="x-28GEB-2EMIXINS-3A-40MIXINS-CAT-20MGL-PAX-3ASECTION-29"></a>
### 7.1 The Categorical Interface

###### \[in package GEB.MIXINS\]
This covers the main Categorical interface required to be used and
contained in various data structures

<a id="x-28GEB-2EMIXINS-3ACAT-OBJ-20CLASS-29"></a>
- [class] **CAT-OBJ**

    I offer the service of being a base category objects with no
    extesnions

<a id="x-28GEB-2EMIXINS-3ACAT-MORPH-20CLASS-29"></a>
- [class] **CAT-MORPH**

    I offer the service of being a base categorical morphism with no
    extesnions

<a id="x-28GEB-2EMIXINS-3ADOM-20GENERIC-FUNCTION-29"></a>
- [generic-function] **DOM** *CAT-MORPH*

    Grabs the domain of the morphism. Returns a [`CAT-OBJ`][74bd]

<a id="x-28GEB-2EMIXINS-3ACODOM-20GENERIC-FUNCTION-29"></a>
- [generic-function] **CODOM** *CAT-MORPH*

    Grabs the codomain of the morphism. Returns a [`CAT-OBJ`][74bd]

<a id="x-28GEB-2EMIXINS-3ACURRY-PROD-20GENERIC-FUNCTION-29"></a>
- [generic-function] **CURRY-PROD** *CAT-MORPH CAT-LEFT CAT-RIGHT*

    Curries the given product type given the
    product. This returns a [`CAT-MORPH`][a7af].
    
    This interface version takes the left and right product type to
    properly dispatch on. Instances should specalize on the `CAT-RIGHT` argument
    
    Use [`GEB.MAIN:CURRY`][2cbc] instead.

<a id="x-28GEB-2ESPEC-3A-40GEB-CATEGORIES-20MGL-PAX-3ASECTION-29"></a>
### 7.2 Core Category

###### \[in package GEB.SPEC\]
The underlying category of GEB. With [Subst Obj][c1b3] covering the
shapes and forms ([Objects][dbe7]) of data while [Subst Morph][d2d1]
deals with concrete [Morphisms][ada9] within the category.

From this category, most abstractions will be made, with
[`SUBSTOBJ`][3173] serving as a concrete type layout, with
[`SUBSTMORPH`][57dc] serving as the morphisms between different
[`SUBSTOBJ`][3173] types. This category is equivalent to
[finset](https://ncatlab.org/nlab/show/FinSet).

A good example of this category at work can be found within the
[Booleans][399c] section.

<a id="x-28GEB-2ESPEC-3A-40GEB-SUBSTMU-20MGL-PAX-3ASECTION-29"></a>
#### 7.2.1 Subst Obj

This section covers the objects of the [`SUBSTMORPH`][57dc]
category. Note that [`SUBSTOBJ`][3173] refers to the
[closed type][8932], whereas [`<SUBSTOBJ>`][8214] refers
to the [open type][4a87] that allows for user extension.

<a id="x-28GEB-2ESPEC-3ASUBSTOBJ-20TYPE-29"></a>
- [type] **SUBSTOBJ**

<a id="x-28GEB-2ESPEC-3A-3CSUBSTOBJ-3E-20TYPE-29"></a>
- [type] **\<SUBSTOBJ\>**

    the class corresponding to [`SUBSTOBJ`][3173]. See [Open Types versus Closed Types][a920]

[`SUBSTOBJ`][3173] type is not a constructor itself, instead it's
best viewed as the sum type, with the types below forming the
constructors for the term. In ML we would write it similarly to:

```haskell
type substobj = so0
              | so1
              | prod
              | coprod
```


<a id="x-28GEB-2ESPEC-3APROD-20TYPE-29"></a>
- [type] **PROD**

    The [PRODUCT][77c2] object. Takes two [`CAT-OBJ`][74bd] values that
    get put into a pair.
    
    The formal grammar of [PRODUCT][77c2] is
    
    ```lisp
    (prod mcar mcadr)
    ```
    
    where [`PROD`][77c2] is the constructor, [`MCAR`][f1ce] is the left value of the
    product, and [`MCADR`][cc87] is the right value of the product.
    
    Example:
    
    ```lisp
    (geb-gui::visualize (prod geb-bool:bool geb-bool:bool))
    ```
    
    Here we create a product of two [`GEB-BOOL:BOOL`][0ad4] types.

<a id="x-28GEB-2ESPEC-3ACOPROD-20TYPE-29"></a>
- [type] **COPROD**

    the [CO-PRODUCT][fb12] object. Takes [`CAT-OBJ`][74bd] values that
    get put into a choice of either value.
    
    The formal grammar of [PRODUCT][77c2] is
    
    ```lisp
    (coprod mcar mcadr)
    ```
    
    Where [CORPOD][e755] is the constructor, [`MCAR`][f1ce] is the left choice of
    the sum, and [`MCADR`][cc87] is the right choice of the sum.
    
    Example:
    
    ```lisp
    (geb-gui::visualize (coprod so1 so1))
    ```
    
    Here we create the boolean type, having a choice between two unit
    values.

<a id="x-28GEB-2ESPEC-3ASO0-20TYPE-29"></a>
- [type] **SO0**

    The Initial Object. This is sometimes known as the
    [VOID](https://en.wikipedia.org/wiki/Void_type) type.
    
    the formal grammar of [`SO0`][1f3a] is
    
    ```lisp
    so0
    ```
    
    where [`SO0`][1f3a] is [`THE`][c767] initial object.
    
    Example
    
    `lisp
    `

<a id="x-28GEB-2ESPEC-3ASO1-20TYPE-29"></a>
- [type] **SO1**

    The Terminal Object. This is sometimes referred to as the
    [Unit](https://en.wikipedia.org/wiki/Unit_type) type.
    
    the formal grammar or [`SO1`][ebf5] is
    
    ```lisp
    so1
    ```
    
    where [`SO1`][ebf5] is [`THE`][c767] terminal object
    
    Example
    
    ```lisp
    (coprod so1 so1)
    ```
    
    Here we construct [`GEB-BOOL:BOOL`][0ad4] by simply stating that we have the
    terminal object on either side, giving us two possible ways to fill
    the type.
    
    ```lisp
    (->left so1 so1)
    
    (->right so1 so1)
    ```
    
    where applying [`->LEFT`][e2af] gives us the left unit, while [`->RIGHT`][ba44] gives
    us the right unit.

The [Accessors][cc51] specific to [Subst Obj][c1b3]

<a id="x-28GEB-2EUTILS-3AMCAR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3APROD-29-29-29"></a>
- [method] **MCAR** *(PROD PROD)*

<a id="x-28GEB-2EUTILS-3AMCADR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3APROD-29-29-29"></a>
- [method] **MCADR** *(PROD PROD)*

<a id="x-28GEB-2EUTILS-3AMCAR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3ACOPROD-29-29-29"></a>
- [method] **MCAR** *(COPROD COPROD)*

<a id="x-28GEB-2EUTILS-3AMCADR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3ACOPROD-29-29-29"></a>
- [method] **MCADR** *(COPROD COPROD)*

<a id="x-28GEB-2ESPEC-3A-40GEB-SUBSTMORPH-20MGL-PAX-3ASECTION-29"></a>
#### 7.2.2 Subst Morph

The overarching types that categorizes the [`SUBSTMORPH`][57dc]
category. Note that [`SUBSTMORPH`][57dc] refers to the
[closed type][8932], whereas [`<SUBSTMORPH>`][97fb] refers
to the [open type][4a87] that allows for user extension.

<a id="x-28GEB-2ESPEC-3ASUBSTMORPH-20TYPE-29"></a>
- [type] **SUBSTMORPH**

    The morphisms of the [`SUBSTMORPH`][57dc] category

<a id="x-28GEB-2ESPEC-3A-3CSUBSTMORPH-3E-20TYPE-29"></a>
- [type] **\<SUBSTMORPH\>**

    the class type corresponding to [`SUBSTMORPH`][57dc]. See [Open Types versus Closed Types][a920]

[`SUBSTMORPH`][57dc] type is not a constructor itself, instead it's
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

Note that an instance of [`SUBSTOBJ`][3173], acts like the identity
morphism to the layout specified by the given [`SUBSTOBJ`][3173]. Thus
we can view this as automatically lifting a [`SUBSTOBJ`][3173] into a
[`SUBSTMORPH`][57dc]

<a id="x-28GEB-2ESPEC-3ACOMP-20TYPE-29"></a>
- [type] **COMP**

    The composition morphism. Takes two [`CAT-MORPH`][a7af] values that get
    applied in standard composition order.
    
    The formal grammar of [`COMP`][f914] is
    
    ```lisp
    (comp mcar mcadr)
    ```
    
    which may be more familiar as
    
    ```haskell
    g 。f
    ```
    
    Where [`COMP`][f914]( 。) is the constructor, [`MCAR`][f1ce](g) is the second morphism
    that gets applied, and [`MCADR`][cc87](f) is the first morphism that gets
    applied.
    
    Example:
    
    ```lisp
    (geb-gui::visualize
     (comp
      (<-right so1 geb-bool:bool)
      (pair (<-left so1 geb-bool:bool)
            (<-right so1 geb-bool:bool))))
    ```
    
    In this example we are composing two morphisms. the first morphism
    that gets applied ([`PAIR`][3bc6] ...) is the identity function on the
    type ([`PROD`][77c2] [`SO1`][ebf5] [`GEB-BOOL:BOOL`][0ad4]), where we pair the
    [left projection](PROJECT-LEFT) and the [right
    projection](PROJECT-RIGHT), followed by taking the [right
    projection](PROJECT-RIGHT) of the type.
    
    Since we know ([`COMP`][f914] f id) is just f per the laws of category
    theory, this expression just reduces to
    
    ```lisp
    (<-right so1 geb-bool:bool)
    ```


<a id="x-28GEB-2ESPEC-3ACASE-20TYPE-29"></a>
- [type] **CASE**

    Eliminates coproducts. Namely Takes two [`CAT-MORPH`][a7af] values, one
    gets applied on the left coproduct while the other gets applied on the
    right coproduct. The result of each `CAT-MORPH` values must be
    the same.
    
    The formal grammar of [`CASE`][59dd] is:
    
    ```lisp
    (mcase mcar mcadr)
    ```
    
    Where [`MCASE`][cd11] is the constructor, [`MCAR`][f1ce] is the morphism that gets
    applied to the left coproduct, and [`MCADR`][cc87] is the morphism that gets
    applied to the right coproduct.
    
    Example:
    
    ```lisp
    (comp
     (mcase geb-bool:true
            geb-bool:not)
     (->right so1 geb-bool:bool))
    ```
    
    In the second example, we inject a term with the shape [`GEB-BOOL:BOOL`][0ad4]
    into a pair with the shape ([`SO1`][ebf5] × [`GEB-BOOL:BOOL`][0ad4]), then we use
    [`MCASE`][cd11] to denote a morphism saying. [`IF`][684b] the input is of the shape `SO1`([`0`][f4ba] [`1`][ebf5]),
    then give us True, otherwise flip the value of the boolean coming in.

<a id="x-28GEB-2ESPEC-3AINIT-20TYPE-29"></a>
- [type] **INIT**

    The [INITIAL][f899] Morphism, takes any [`CAT-OBJ`][74bd] and
    creates a moprhism from [`SO0`][1f3a] (also known as void) to the object given.
    
    The formal grammar of [INITIAL][f899] is
    
    ```lisp
    (init obj)
    ```
    
    where [`INIT`][f899] is the constructor. [`OBJ`][f1e6] is the type of object
    that will be conjured up from [`SO0`][1f3a], when the morphism is
    applied onto an object.
    
    Example:
    
    ```lisp
    (init so1)
    ```
    
    In this example we are creating a unit value out of void.

<a id="x-28GEB-2ESPEC-3ATERMINAL-20TYPE-29"></a>
- [type] **TERMINAL**

    The [`TERMINAL`][ae41] morphism, Takes any [`CAT-OBJ`][74bd] and creates a
    morphism from that object to [`SO1`][ebf5] (also known as unit).
    
    The formal grammar of [`TERMINAL`][ae41] is
    
    ```lisp
    (terminal obj)
    ```
    
    where [`TERMINAL`][ae41] is the constructor. [`OBJ`][f1e6] is the type of object that
    will be mapped to [`SO1`][ebf5], when the morphism is applied onto an
    object.
    
    Example:
    
    ```lisp
    (terminal (coprod so1 so1))
    
    (geb-gui::visualize (terminal (coprod so1 so1)))
    
    (comp value (terminal (codomain value)))
    
    (comp true (terminal bool))
    ```
    
    In the first example, we make a morphism from the corpoduct of
    [`SO1`][ebf5] and [`SO1`][ebf5] (essentially [`GEB-BOOL:BOOL`][0ad4]) to
    [`SO1`][ebf5].
    
    In the third example we can proclaim a constant function by ignoring
    the input value and returning a morphism from unit to the desired type.
    
    The fourth example is taking a [`GEB-BOOL:BOOL`][0ad4] and returning [`GEB-BOOL:TRUE`][f022].

<a id="x-28GEB-2ESPEC-3APAIR-20TYPE-29"></a>
- [type] **PAIR**

    Introduces products. Namely Takes two [`CAT-MORPH`][a7af] values. When
    the `PAIR` morphism is applied on data, these two [`CAT-MORPH`][a7af]'s are
    applied to the object, returning a pair of the results
    
    The formal grammar of constructing an instance of pair is:
    
    ```
    (pair mcar mcdr)
    ```
    
    where `PAIR` is the constructor, [`MCAR`][f1ce] is the left morphism, and [`MCDR`][af14] is
    the right morphism
    
    Example:
    
    ```lisp
    (pair (<-left so1 geb-bool:bool)
          (<-right so1 geb-bool:bool))
    
    (geb-gui::visualize (pair (<-left so1 geb-bool:bool)
                              (<-right so1 geb-bool:bool)))
    ```
    
    Here this pair morphism takes the pair `SO1`([`0`][f4ba] [`1`][ebf5]) × [`GEB-BOOL:BOOL`][0ad4], and
    projects back the left field `SO1` as the first value of the pair and
    projects back the `GEB-BOOL:BOOL` field as the second values.

<a id="x-28GEB-2ESPEC-3ADISTRIBUTE-20TYPE-29"></a>
- [type] **DISTRIBUTE**

    The distributive law

<a id="x-28GEB-2ESPEC-3AINJECT-LEFT-20TYPE-29"></a>
- [type] **INJECT-LEFT**

    The left injection morphism. Takes two [`CAT-OBJ`][74bd] values. It is
    the dual of [`INJECT-RIGHT`][fae9]
    
    The formal grammar is
    
    ```lisp
    (->left mcar mcadr)
    ```
    
    Where [`->LEFT`][e2af] is the constructor, [`MCAR`][f1ce] is the value being injected into
    the coproduct of [`MCAR`][f1ce] + [`MCADR`][cc87], and the [`MCADR`][cc87] is just the type for
    the unused right constructor.
    
    Example:
    
    ```lisp
    (geb-gui::visualize (->left so1 geb-bool:bool))
    
    (comp
     (mcase geb-bool:true
            geb-bool:not)
     (->left so1 geb-bool:bool))
    
    ```
    
    In the second example, we inject a term with the shape `SO1`([`0`][f4ba] [`1`][ebf5]) into a pair
    with the shape ([`SO1`][ebf5] × [`GEB-BOOL:BOOL`][0ad4]), then we use [`MCASE`][cd11] to denote a
    morphism saying. [`IF`][684b] the input is of the shape `SO1`([`0`][f4ba] [`1`][ebf5]), then give us True,
    otherwise flip the value of the boolean coming in.

<a id="x-28GEB-2ESPEC-3AINJECT-RIGHT-20TYPE-29"></a>
- [type] **INJECT-RIGHT**

    The right injection morphism. Takes two [`CAT-OBJ`][74bd] values. It is
    the dual of [`INJECT-LEFT`][cab9]
    
    The formal grammar is
    
    ```lisp
    (->right mcar mcadr)
    ```
    
    Where [`->RIGHT`][ba44] is the constructor, [`MCADR`][cc87] is the value being injected into
    the coproduct of [`MCAR`][f1ce] + [`MCADR`][cc87], and the [`MCAR`][f1ce] is just the type for
    the unused left constructor.
    
    Example:
    
    ```lisp
    (geb-gui::visualize (->right so1 geb-bool:bool))
    
    (comp
     (mcase geb-bool:true
            geb-bool:not)
     (->right so1 geb-bool:bool))
    
    ```
    
    In the second example, we inject a term with the shape [`GEB-BOOL:BOOL`][0ad4]
    into a pair with the shape ([`SO1`][ebf5] × [`GEB-BOOL:BOOL`][0ad4]), then we use
    [`MCASE`][cd11] to denote a morphism saying. [`IF`][684b] the input is of the shape `SO1`([`0`][f4ba] [`1`][ebf5]),
    then give us True, otherwise flip the value of the boolean coming in.

<a id="x-28GEB-2ESPEC-3APROJECT-LEFT-20TYPE-29"></a>
- [type] **PROJECT-LEFT**

    The [`LEFT` PROJECTION][0dcc]. Takes two
    [`CAT-MORPH`][a7af] values. When the [`LEFT` PROJECTION][0dcc] morphism is then applied, it grabs the left value of a product,
    with the type of the product being determined by the two
    [`CAT-MORPH`][a7af] values given.
    
    the formal grammar of a [`PROJECT-LEFT`][0dcc] is:
    
    ```lisp
    (<-left mcar mcadr)
    ```
    
    Where [`<-LEFT`][2882] is the constructor, [`MCAR`][f1ce] is the left type of the
    [PRODUCT][e755] and [`MCADR`][cc87] is the right type of the [PRODUCT][e755].
    
    Example:
    
    ```lisp
    (geb-gui::visualize
      (<-left geb-bool:bool (prod so1 geb-bool:bool)))
    ```
    
    In this example, we are getting the left [`GEB-BOOL:BOOL`][0ad4] from a
    product with the shape
    
    ([`GEB-BOOL:BOOL`][0ad4] [×][77c2] [`SO1`][ebf5] [×][77c2] [`GEB-BOOL:BOOL`][0ad4])

<a id="x-28GEB-2ESPEC-3APROJECT-RIGHT-20TYPE-29"></a>
- [type] **PROJECT-RIGHT**

    The [`RIGHT` PROJECTION][e65d]. Takes two
    [`CAT-MORPH`][a7af] values. When the [`RIGHT` PROJECTION][e65d] morphism is then applied, it grabs the right value of a product,
    with the type of the product being determined by the two
    [`CAT-MORPH`][a7af] values given.
    
    the formal grammar of a [`PROJECT-RIGHT`][e65d] is:
    
    ```lisp
    (<-right mcar mcadr)
    ```
    
    Where [`<-RIGHT`][0dfe] is the constructor, [`MCAR`][f1ce] is the right type of the
    [PRODUCT][e755] and [`MCADR`][cc87] is the right type of the [PRODUCT][e755].
    
    Example:
    
    ```lisp
    (geb-gui::visualize
     (comp (<-right so1 geb-bool:bool)
           (<-right geb-bool:bool (prod so1 geb-bool:bool))))
    ```
    
    In this example, we are getting the right [`GEB-BOOL:BOOL`][0ad4] from a
    product with the shape
    
    ([`GEB-BOOL:BOOL`][0ad4] [×][77c2] [`SO1`][ebf5] [×][77c2] [`GEB-BOOL:BOOL`][0ad4])

<a id="x-28GEB-2ESPEC-3AFUNCTOR-20TYPE-29"></a>
- [type] **FUNCTOR**

The [Accessors][cc51] specific to [Subst Morph][d2d1]

<a id="x-28GEB-2EUTILS-3AMCAR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3ACOMP-29-29-29"></a>
- [method] **MCAR** *(COMP COMP)*

    The first composed morphism

<a id="x-28GEB-2EUTILS-3AMCADR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3ACOMP-29-29-29"></a>
- [method] **MCADR** *(COMP COMP)*

    the second morphism

<a id="x-28GEB-2EUTILS-3AOBJ-20-28METHOD-20NIL-20-28GEB-2ESPEC-3AINIT-29-29-29"></a>
- [method] **OBJ** *(INIT INIT)*

<a id="x-28GEB-2EUTILS-3AOBJ-20-28METHOD-20NIL-20-28GEB-2ESPEC-3AINIT-29-29-29"></a>
- [method] **OBJ** *(INIT INIT)*

<a id="x-28GEB-2EUTILS-3AMCAR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3ACASE-29-29-29"></a>
- [method] **MCAR** *(CASE CASE)*

    The morphism that gets applied on the left coproduct

<a id="x-28GEB-2EUTILS-3AMCADR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3ACASE-29-29-29"></a>
- [method] **MCADR** *(CASE CASE)*

    The morphism that gets applied on the right coproduct

<a id="x-28GEB-2EUTILS-3AMCAR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3APAIR-29-29-29"></a>
- [method] **MCAR** *(PAIR PAIR)*

    The left morphism

<a id="x-28GEB-2EUTILS-3AMCDR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3APAIR-29-29-29"></a>
- [method] **MCDR** *(PAIR PAIR)*

    The right morphism

<a id="x-28GEB-2EUTILS-3AMCAR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3ADISTRIBUTE-29-29-29"></a>
- [method] **MCAR** *(DISTRIBUTE DISTRIBUTE)*

<a id="x-28GEB-2EUTILS-3AMCADR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3ADISTRIBUTE-29-29-29"></a>
- [method] **MCADR** *(DISTRIBUTE DISTRIBUTE)*

<a id="x-28GEB-2EUTILS-3AMCADDR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3ADISTRIBUTE-29-29-29"></a>
- [method] **MCADDR** *(DISTRIBUTE DISTRIBUTE)*

<a id="x-28GEB-2EUTILS-3AMCAR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3AINJECT-LEFT-29-29-29"></a>
- [method] **MCAR** *(INJECT-LEFT INJECT-LEFT)*

<a id="x-28GEB-2EUTILS-3AMCADR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3AINJECT-LEFT-29-29-29"></a>
- [method] **MCADR** *(INJECT-LEFT INJECT-LEFT)*

<a id="x-28GEB-2EUTILS-3AMCAR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3AINJECT-RIGHT-29-29-29"></a>
- [method] **MCAR** *(INJECT-RIGHT INJECT-RIGHT)*

<a id="x-28GEB-2EUTILS-3AMCADR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3AINJECT-RIGHT-29-29-29"></a>
- [method] **MCADR** *(INJECT-RIGHT INJECT-RIGHT)*

<a id="x-28GEB-2EUTILS-3AMCAR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3APROJECT-LEFT-29-29-29"></a>
- [method] **MCAR** *(PROJECT-LEFT PROJECT-LEFT)*

<a id="x-28GEB-2EUTILS-3AMCADR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3APROJECT-LEFT-29-29-29"></a>
- [method] **MCADR** *(PROJECT-LEFT PROJECT-LEFT)*

<a id="x-28GEB-2EUTILS-3AMCAR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3APROJECT-RIGHT-29-29-29"></a>
- [method] **MCAR** *(PROJECT-RIGHT PROJECT-RIGHT)*

<a id="x-28GEB-2EUTILS-3AMCADR-20-28METHOD-20NIL-20-28GEB-2ESPEC-3APROJECT-RIGHT-29-29-29"></a>
- [method] **MCADR** *(PROJECT-RIGHT PROJECT-RIGHT)*

    Right projection (product elimination)

<a id="x-28GEB-2EUTILS-3A-40GEB-ACCESSORS-20MGL-PAX-3ASECTION-29"></a>
### 7.3 Accessors

###### \[in package GEB.UTILS\]
These functions are generic lenses of the GEB codebase. If a class is
defined, where the names are not known, then these accessors are
likely to be used. They may even augment existing classes.

<a id="x-28GEB-2EUTILS-3AMCAR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCAR** *OBJ*

    Can be seen as calling [`CAR`][8c99] on a generic CLOS
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-2EUTILS-3AMCADR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCADR** *OBJ*

    like [`MCAR`][f1ce] but for the [`CADR`][74ab]

<a id="x-28GEB-2EUTILS-3AMCADDR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCADDR** *OBJ*

    like [`MCAR`][f1ce] but for the [`CADDR`][8bb8]

<a id="x-28GEB-2EUTILS-3AMCADDDR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCADDDR** *OBJ*

    like [`MCAR`][f1ce] but for the [`CADDDR`][1791]

<a id="x-28GEB-2EUTILS-3AMCDR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCDR** *OBJ*

    Similar to [`MCAR`][f1ce], however acts like a [`CDR`][2570] for
    [classes][7e58] that we wish to view as a [`SEQUENCE`][b9c1]

<a id="x-28GEB-2EUTILS-3AOBJ-20GENERIC-FUNCTION-29"></a>
- [generic-function] **OBJ** *OBJ*

    Grabs the underlying
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-2EUTILS-3ANAME-20GENERIC-FUNCTION-29"></a>
- [generic-function] **NAME** *OBJ*

    the name of the given
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-2EUTILS-3AFUNC-20GENERIC-FUNCTION-29"></a>
- [generic-function] **FUNC** *OBJ*

    the function of the
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-2EUTILS-3APREDICATE-20GENERIC-FUNCTION-29"></a>
- [generic-function] **PREDICATE** *OBJ*

    the `PREDICATE` of the
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-2EUTILS-3ATHEN-20GENERIC-FUNCTION-29"></a>
- [generic-function] **THEN** *OBJ*

    the then branch of the
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-2EUTILS-3AELSE-20GENERIC-FUNCTION-29"></a>
- [generic-function] **ELSE** *OBJ*

    the then branch of the
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-2ESPEC-3A-40GEB-CONSTRUCTORS-20MGL-PAX-3ASECTION-29"></a>
### 7.4 Constructors

###### \[in package GEB.SPEC\]
The API for creating GEB terms. All the functions and variables
here relate to instantiating a term

<a id="x-28GEB-2ESPEC-3A-2ASO0-2A-20VARIABLE-29"></a>
- [variable] **\*SO0\*** *s-0*

    The Initial Object

<a id="x-28GEB-2ESPEC-3A-2ASO1-2A-20VARIABLE-29"></a>
- [variable] **\*SO1\*** *s-1*

    The Terminal Object

More Ergonomic API variants for [`*SO0*`][e982] and [`*SO1*`][b960]

<a id="x-28GEB-2ESPEC-3ASO0-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **SO0**

<a id="x-28GEB-2ESPEC-3ASO1-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **SO1**

<a id="x-28GEB-2ESPEC-3AALIAS-20MGL-PAX-3AMACRO-29"></a>
- [macro] **ALIAS** *NAME OBJ*

<a id="x-28GEB-2ESPEC-3AMAKE-ALIAS-20FUNCTION-29"></a>
- [function] **MAKE-ALIAS** *&KEY NAME OBJ*

<a id="x-28GEB-2ESPEC-3AHAS-ALIASP-20FUNCTION-29"></a>
- [function] **HAS-ALIASP** *OBJ*

<a id="x-28GEB-2ESPEC-3A-3C-LEFT-20FUNCTION-29"></a>
- [function] **\<-LEFT** *MCAR MCADR*

    projects left constructor

<a id="x-28GEB-2ESPEC-3A-3C-RIGHT-20FUNCTION-29"></a>
- [function] **\<-RIGHT** *MCAR MCADR*

    projects right constructor

<a id="x-28GEB-2ESPEC-3A--3ELEFT-20FUNCTION-29"></a>
- [function] **-\>LEFT** *MCAR MCADR*

    injects left constructor

<a id="x-28GEB-2ESPEC-3A--3ERIGHT-20FUNCTION-29"></a>
- [function] **-\>RIGHT** *MCAR MCADR*

    injects right constructor

<a id="x-28GEB-2ESPEC-3AMCASE-20FUNCTION-29"></a>
- [function] **MCASE** *MCAR MCADR*

<a id="x-28GEB-2ESPEC-3AMAKE-FUNCTOR-20FUNCTION-29"></a>
- [function] **MAKE-FUNCTOR** *&KEY OBJ FUNC*

<a id="x-28GEB-3A-40GEB-API-20MGL-PAX-3ASECTION-29"></a>
### 7.5 API

Various forms and structures built on-top of [Core Category][cb9e]

<a id="x-28GEB-BOOL-3A-40GEB-BOOL-20MGL-PAX-3ASECTION-29"></a>
#### 7.5.1 Booleans

###### \[in package GEB-BOOL\]
Here we define out the idea of a boolean. It comes naturally from the
concept of coproducts. In ML they often define a boolean like

```haskell
data Bool = False | True
```

We likewise define it with coproducts

```lisp
(def bool (coprod so1 so1))

(def true  (->right so1 so1))
(def false (->left  so1 so1))
```

The functions given work on this.

<a id="x-28GEB-BOOL-3ATRUE-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **TRUE**

    The true value of a boolean type. In this case we've defined true as
    the right unit

<a id="x-28GEB-BOOL-3AFALSE-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **FALSE**

    The false value of a boolean type. In this case we've defined true as
    the left unit

<a id="x-28GEB-BOOL-3AFALSE-OBJ-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **FALSE-OBJ**

<a id="x-28GEB-BOOL-3ATRUE-OBJ-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **TRUE-OBJ**

<a id="x-28GEB-BOOL-3ABOOL-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **BOOL**

    The Boolean Type, composed of a coproduct of two unit objects
    
    ```lisp
    (coprod so1 so1)
    ```


<a id="x-28GEB-BOOL-3ANOT-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **NOT**

    Turns a [`TRUE`][f022] into a [`FALSE`][31c5] and vice versa

<a id="x-28GEB-BOOL-3AAND-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **AND**

<a id="x-28GEB-BOOL-3AOR-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **OR**

<a id="x-28GEB-2ETRANS-3A-40GEB-TRANSLATION-20MGL-PAX-3ASECTION-29"></a>
#### 7.5.2 Translation Functions

###### \[in package GEB.TRANS\]
These cover various conversions from [Subst Morph][d2d1] and [Subst Obj][c1b3]
into other categorical data structures.

<a id="x-28GEB-2ETRANS-3ATO-POLY-20GENERIC-FUNCTION-29"></a>
- [generic-function] **TO-POLY** *MORPHISM*

    Turns a [Subst Morph][d2d1] into a [`POLY:POLY`][8bf3]

<a id="x-28GEB-2ETRANS-3ATO-CIRCUIT-20FUNCTION-29"></a>
- [function] **TO-CIRCUIT** *OBJ NAME*

    Turns a [Subst Morph][d2d1] to a Vamp-IR Term

<a id="x-28GEB-2EMAIN-3A-40GEB-UTILITY-20MGL-PAX-3ASECTION-29"></a>
#### 7.5.3 Utility

###### \[in package GEB.MAIN\]
Various utility functions ontop of [Core Category][cb9e]

<a id="x-28GEB-2ESPEC-3APAIR-TO-LIST-20FUNCTION-29"></a>
- [function] **PAIR-TO-LIST** *PAIR &OPTIONAL ACC*

    converts excess pairs to a list format

<a id="x-28GEB-2ESPEC-3ASAME-TYPE-TO-LIST-20FUNCTION-29"></a>
- [function] **SAME-TYPE-TO-LIST** *PAIR TYPE &OPTIONAL ACC*

    converts the given type to a list format

<a id="x-28GEB-2EMAIN-3ACLEAVE-20FUNCTION-29"></a>
- [function] **CLEAVE** *V1 &REST VALUES*

    Applies each morphism to the object in turn.

<a id="x-28GEB-2EMAIN-3ACONST-20FUNCTION-29"></a>
- [function] **CONST** *F X*

    The constant morphism.
    
    Takes a morphism from [`SO1`][ebf5] to a desired value of type $B$,
    along with a [`<SUBSTOBJ>`][8214] that represents the input type say of
    type $A$, giving us a morphism from $A$ to $B$.
    
    Thus if:
    `F` : [`SO1`][ebf5] → a,
    `X` : b
    
    then: (const f x) : a → b
    
    ```
    Γ, f : so1 → b, x : a
    ----------------------
    (const f x) : a → b
    ```
    
    Further, If the input `F` is an `ALIAS`, then we wrap the output
    in a new alias to denote it's a constant version of that value.
    
    Example:
    
    ```lisp
    (const true bool) ; bool -> bool
    ```


<a id="x-28GEB-2EMAIN-3ACOMMUTES-20FUNCTION-29"></a>
- [function] **COMMUTES** *X Y*

<a id="x-28GEB-2EMAIN-3ACOMMUTES-LEFT-20FUNCTION-29"></a>
- [function] **COMMUTES-LEFT** *MORPH*

    swap the input [domain][9728] of the given [cat-morph][a7af]
    
    In order to swap the [domain][9728] we expect the [cat-morph][a7af] to
    be a [`PROD`][77c2]
    
    Thus if: `(dom morph) ≡ (prod x y)`, for any `x`, `y` [`CAT-OBJ`][74bd]
    
    then: `(commutes-left (dom morph)) ≡ (prod y x)`
    u
    `
    Γ, f : x × y → a
    ------------------------------
    (commutes-left f) : y × x → a
    `

<a id="x-28GEB-2EMAIN-3A-21--3E-20FUNCTION-29"></a>
- [function] **!-\>** *A B*

<a id="x-28GEB-2EMAIN-3ASO-EVAL-20FUNCTION-29"></a>
- [function] **SO-EVAL** *X Y*

<a id="x-28GEB-2EMAIN-3ASO-HOM-OBJ-20FUNCTION-29"></a>
- [function] **SO-HOM-OBJ** *X Z*

<a id="x-28GEB-2EMAIN-3ASO-CARD-ALG-20GENERIC-FUNCTION-29"></a>
- [generic-function] **SO-CARD-ALG** *OBJ*

    Gets the cardinality of the given object, returns a [`FIXNUM`][ceb9]

<a id="x-28GEB-2EMAIN-3ASO-CARD-ALG-20-28METHOD-20NIL-20-28GEB-2ESPEC-3A-3CSUBSTOBJ-3E-29-29-29"></a>
- [method] **SO-CARD-ALG** *(OBJ \<SUBSTOBJ\>)*

<a id="x-28GEB-2EMAIN-3ACURRY-20FUNCTION-29"></a>
- [function] **CURRY** *F*

    Curries the given object, returns a [cat-morph][a7af]
    
    The [cat-morph][a7af] given must have its [`DOM`][9728] be of a [`PROD`][77c2] type, as `CURRY`
    invokes the idea of
    
    if f : ([`PROD`][77c2] a b) → c
    
    for all `a`, `b`, and `c` being an element of [cat-morph][a7af]
    
    then: (curry f): a → c^b
    
    where c^b means c to the exponent of b ([`EXPT`][9bcb2] c b)
    
    ```
    Γ, f : a × b → c,
    --------------------
    (curry f) : a → c^b
    ```
    
    In category terms, `a → c^b` is isomorphic to `a → b → c`


<a id="x-28GEB-2EMAIN-3ATEXT-NAME-20GENERIC-FUNCTION-29"></a>
- [generic-function] **TEXT-NAME** *MORPH*

    Gets the name of the moprhism

<a id="x-28GEB-3A-40GEB-EXAMPLES-20MGL-PAX-3ASECTION-29"></a>
### 7.6 Examples

PLACEHOLDER: TO SHOW OTHERS HOW `EXAMPLE`s WORK

Let's see the transcript of a real session of someone working
with GEB:

```common-lisp
(values (princ :hello) (list 1 2))
.. HELLO
=> :HELLO
=> (1 2)

(+ 1 2 3 4)
=> 10
```


<a id="x-28GEB-GUI-3A-40GEB-GUI-MANUAL-20MGL-PAX-3ASECTION-29"></a>
## 8 The GEB GUI

###### \[in package GEB-GUI\]
This section covers the suite of tools that help visualize geb
objects and make the system nice to work with

<a id="x-28GEB-GUI-3A-40GEB-VISUALIZER-20MGL-PAX-3ASECTION-29"></a>
### 8.1 Visualizer

The GEB visualizer deals with visualizing any objects found in the [Core Category][cb9e]

if the visualizer gets a [Subst Morph][d2d1], then it will show how
the [`GEB:SUBSTMORPH`][57dc] changes any incoming term.

if the visualizer gets a [Subst Obj][c1b3], then it shows the data
layout of the term, showing what kind of data 

<a id="x-28GEB-GUI-3AVISUALIZE-20FUNCTION-29"></a>
- [function] **VISUALIZE** *OBJECT &OPTIONAL (ASYNC T)*

    Visualizes both [Subst Obj][c1b3] and [Subst Morph][d2d1] objects

<a id="x-28GEB-GUI-3AKILL-RUNNING-20FUNCTION-29"></a>
- [function] **KILL-RUNNING**

    Kills all threads and open gui objects created by [`VISUALIZE`][ada5]

<a id="x-28GEB-GUI-3A-40VISAULIZER-AID-20MGL-PAX-3ASECTION-29"></a>
#### 8.1.1 Aiding the Visualizer

One can aid the visualization process a bit, this can be done by
simply playing `GEB:ALIAS` around the object, this will place it
in a box with a name to better identify it in the graphing procedure.

<a id="x-28GEB-GUI-2EGRAPHING-3A-40GRAPHING-MANUAL-20MGL-PAX-3ASECTION-29"></a>
### 8.2 The GEB Graphizer

###### \[in package GEB-GUI.GRAPHING\]
This section covers the GEB Graph representation

<a id="x-28GEB-GUI-2ECORE-3A-40GRAPHING-CORE-20MGL-PAX-3ASECTION-29"></a>
#### 8.2.1 The GEB Graphizer Core

###### \[in package GEB-GUI.CORE\]
This section covers the graphing procedure in order to turn a GEB
object into a format for a graphing backend.

The core types that facilittate the functionality

<a id="x-28GEB-GUI-2ECORE-3ANOTE-20TYPE-29"></a>
- [type] **NOTE**

    A note is a note about a new node in the graph or a note about a
    [`NODE`][ff98] which should be merged into an upcoming `NODE`.
    
    An example of a `NODE-NOTE` would be in the case of pair
    
    ```lisp
    (pair g f)
    ```
    
    ```
                   Π₁
         --f--> Y------
    X----|            |-----> [Y × Z]
         --g--> Z-----
                   Π₂
    ```
    
    An example of a [MERGE-NOTE][7e58]
    
    ```lisp
    (Case f g)
    (COMP g f)
    ```
    
    ```
               χ₁
             -------> X --f---
    [X + Y]--|                ---> A
             -------> Y --g---/
               χ₂
    
    X -f-> Y --> Y -g-> Z
    ```
    
    Notice that in the pair case, we have a note and a shared node to
    place down, where as in both of the [MERGE-NOTE][7e58] examples, the
    Note at the end is not pre-pended by any special information

<a id="x-28GEB-GUI-2ECORE-3ANODE-20CLASS-29"></a>
- [class] **NODE** *[META-MIXIN][4529]*

    I represent a graphical node structure. I contain my children and a
    value to display, along with the representation for which the node really stands for.
    
    Further, we derive the meta-mixin, as it's important for arrow drawing
    to know if we are the left or the right or the nth child of a
    particular node. This information is tracked, by storing the object
    that goes to it in the meta table and recovering the note.

<a id="x-28GEB-GUI-2ECORE-3AMAKE-NOTE-20FUNCTION-29"></a>
- [function] **MAKE-NOTE** *&REST INITARGS &KEY FROM NOTE VALUE &ALLOW-OTHER-KEYS*

<a id="x-28GEB-GUI-2ECORE-3AMAKE-SQUASH-20FUNCTION-29"></a>
- [function] **MAKE-SQUASH** *&REST INITARGS &KEY VALUE &ALLOW-OTHER-KEYS*

<a id="x-28GEB-GUI-2ECORE-3AGRAPHIZE-20GENERIC-FUNCTION-29"></a>
- [generic-function] **GRAPHIZE** *MORPH NOTES*

    Turns a morphism into a node graph.
    
    The `NOTES` serve as a way of sharing and continuing computation.
    
    If the [`NOTE`][ef6e] is a `:SHARED` `NOTE` then it represents a [`NODE`][ff98]
    without children, along with saying where it came from. This is to be
    stored in parent of the `NOTE`
    
    If the `NOTE` is a `:CONTINUE` `NOTE`, then the computation is continued at
    the spot.
    
    The parent field is to set the note on the parent if the `NOTE` is going
    to be merged

<a id="x-28GEB-GUI-2ECORE-3AVALUE-20GENERIC-FUNCTION-29"></a>
- [generic-function] **VALUE** *OBJECT*

<a id="x-28GEB-GUI-2ECORE-3ACONS-NOTE-20FUNCTION-29"></a>
- [function] **CONS-NOTE** *NOTE NOTES*

    Adds a note to the notes list.

<a id="x-28GEB-GUI-2ECORE-3AAPPLY-NOTE-20FUNCTION-29"></a>
- [function] **APPLY-NOTE** *NOTE-TO-BE-ON NOTE*

    Here we apply the `NOTE` to the [`NODE`][ff98].
    
    In the case of a new node, we record down the information in the note,
    and set the note as the child of the current `NODE`. The `NODE` is
    returned.
    
    In the case of a squash-note, we instead just return the squash-note
    as that is the proper `NODE` to continue from

<a id="x-28GEB-GUI-2ECORE-3AREPRESENTATION-20GENERIC-FUNCTION-29"></a>
- [generic-function] **REPRESENTATION** *OBJECT*

<a id="x-28GEB-GUI-2ECORE-3ACHILDREN-20GENERIC-FUNCTION-29"></a>
- [generic-function] **CHILDREN** *OBJECT*

<a id="x-28GEB-GUI-2ECORE-3ADETERMINE-TEXT-AND-OBJECT-FROM-NODE-20FUNCTION-29"></a>
- [function] **DETERMINE-TEXT-AND-OBJECT-FROM-NODE** *FROM TO*

    Helps lookup the text from the node

<a id="x-28GEB-GUI-2ECORE-3ANOTERIZE-CHILDREN-20FUNCTION-29"></a>
- [function] **NOTERIZE-CHILDREN** *NODE FUNC*

    Applies a specified note to the [`CHILDREN`][1fbc] of the `NODE`.
    
    It does this by applying `FUNC` on all the `CHILDREN` and the index of the
    child in the list

<a id="x-28GEB-GUI-2ECORE-3ANOTORIZE-CHILDREN-WITH-INDEX-SCHEMA-20FUNCTION-29"></a>
- [function] **NOTORIZE-CHILDREN-WITH-INDEX-SCHEMA** *PREFIX NODE*

    Notorizes the node with a prefix appended with the subscripted number

<a id="x-28GEB-GUI-2EGRAPHING-2EPASSES-3A-40PASS-MANUAL-20MGL-PAX-3ASECTION-29"></a>
#### 8.2.2 The GEB Graphizer Passes

###### \[in package GEB-GUI.GRAPHING.PASSES\]
This changes how the graph is visualized, simplifying the graph in
ways that are intuitive to the user

<a id="x-28GEB-GUI-2EGRAPHING-2EPASSES-3APASSES-20FUNCTION-29"></a>
- [function] **PASSES** *NODE*

    Runs all the passes that simplify viewing the graph.
    These simplifications should not change the semantics of the graph,
    only display it in a more bearable way

<a id="x-28GEB-2EPOLY-3A-40POLY-MANUAL-20MGL-PAX-3ASECTION-29"></a>
## 9 Polynomial Specification

###### \[in package GEB.POLY\]
This covers a GEB view of Polynomials. In particular this type will
be used in translating GEB's view of Polynomials into Vampir

<a id="x-28GEB-2EPOLY-2ESPEC-3A-40POLY-20MGL-PAX-3ASECTION-29"></a>
### 9.1 Polynomial Types

###### \[in package GEB.POLY.SPEC\]
This section covers the types of things one can find in the [`POLY`][8bf3]
constructors

<a id="x-28GEB-2EPOLY-2ESPEC-3APOLY-20TYPE-29"></a>
- [type] **POLY**

<a id="x-28GEB-2EPOLY-2ESPEC-3A-3CPOLY-3E-20TYPE-29"></a>
- [type] **\<POLY\>**

<a id="x-28GEB-2EPOLY-2ESPEC-3AIDENT-20TYPE-29"></a>
- [type] **IDENT**

    The Identity Element

<a id="x-28GEB-2EPOLY-2ESPEC-3A-2B-20TYPE-29"></a>
- [type] **+**

<a id="x-28GEB-2EPOLY-2ESPEC-3A-2A-20TYPE-29"></a>
- [type] **\***

<a id="x-28GEB-2EPOLY-2ESPEC-3A-2F-20TYPE-29"></a>
- [type] **/**

<a id="x-28GEB-2EPOLY-2ESPEC-3A--20TYPE-29"></a>
- [type] **-**

<a id="x-28GEB-2EPOLY-2ESPEC-3AMOD-20TYPE-29"></a>
- [type] **MOD**

<a id="x-28GEB-2EPOLY-2ESPEC-3ACOMPOSE-20TYPE-29"></a>
- [type] **COMPOSE**

<a id="x-28GEB-2EPOLY-2ESPEC-3AIF-ZERO-20TYPE-29"></a>
- [type] **IF-ZERO**

    compare with zero: equal takes first branch;
    not-equal takes second branch

<a id="x-28GEB-2EPOLY-2ESPEC-3AIF-LT-20TYPE-29"></a>
- [type] **IF-LT**

    If the [`MCAR`][f1ce] argument is strictly less than the [`MCADR`][cc87] then the
    [`THEN`][bfa9] branch is taken, otherwise the [`ELSE`][365a] branch is taken.

<a id="x-28GEB-2EPOLY-2ESPEC-3A-40POLY-CONSTRUCTORS-20MGL-PAX-3ASECTION-29"></a>
### 9.2 Polynomial Constructors

###### \[in package GEB.POLY.SPEC\]
Every accessor for each of the [`CLASS`][7e58]'s found here are from [Accessors][cc51]

<a id="x-28GEB-2EPOLY-2ESPEC-3AIDENT-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **IDENT**

<a id="x-28GEB-2EPOLY-2ESPEC-3A-2B-20FUNCTION-29"></a>
- [function] **+** *MCAR MCADR &REST ARGS*

    Creates a multiway constructor for [+][c144]

<a id="x-28GEB-2EPOLY-2ESPEC-3A-2A-20FUNCTION-29"></a>
- [function] **\*** *MCAR MCADR &REST ARGS*

    Creates a multiway constructor for [\*][0ae3]

<a id="x-28GEB-2EPOLY-2ESPEC-3A-2F-20FUNCTION-29"></a>
- [function] **/** *MCAR MCADR &REST ARGS*

    Creates a multiway constructor for [/][c2f9]

<a id="x-28GEB-2EPOLY-2ESPEC-3A--20FUNCTION-29"></a>
- [function] **-** *MCAR MCADR &REST ARGS*

    Creates a multiway constructor for [-][2c5e]

<a id="x-28GEB-2EPOLY-2ESPEC-3AMOD-20FUNCTION-29"></a>
- [function] **MOD** *MCAR MCADR*

    `MOD` ARG1 by ARG2

<a id="x-28GEB-2EPOLY-2ESPEC-3ACOMPOSE-20FUNCTION-29"></a>
- [function] **COMPOSE** *MCAR MCADR &REST ARGS*

    Creates a multiway constructor for [`COMPOSE`][9162]

<a id="x-28GEB-2EPOLY-2ESPEC-3AIF-ZERO-20FUNCTION-29"></a>
- [function] **IF-ZERO** *PRED THEN ELSE*

    checks if [`PREDICATE`][8da6] is zero then take the [`THEN`][bfa9] branch otherwise the [`ELSE`][365a] branch

<a id="x-28GEB-2EPOLY-2ESPEC-3AIF-LT-20FUNCTION-29"></a>
- [function] **IF-LT** *MCAR MCADR THEN ELSE*

    Checks if the [`MCAR`][f1ce] is less than the [`MCADR`][cc87] and chooses the appropriate branch

<a id="x-28GEB-2EPOLY-2ETRANS-3A-40POLY-TRANS-20MGL-PAX-3ASECTION-29"></a>
### 9.3 Polynomial Transformations

###### \[in package GEB.POLY.TRANS\]
This covers transformation functions from

<a id="x-28GEB-2EPOLY-2ETRANS-3ATO-VAMPIR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **TO-VAMPIR** *MORPHISM VALUE*

    Turns a [`POLY`][8bf3] term into a Vamp-IR term with a given value

<a id="x-28GEB-2EPOLY-2ETRANS-3ATO-CIRCUIT-20FUNCTION-29"></a>
- [function] **TO-CIRCUIT** *MORPHISM NAME*

    Turns a [`POLY`][8bf3] term into a Vamp-IR Gate with the given name

<a id="x-28GEB-2ELAMBDA-3A-40STLC-20MGL-PAX-3ASECTION-29"></a>
## 10 The Simply Typed Lambda Calculus model

###### \[in package GEB.LAMBDA\]
This covers GEB's view on simply typed lambda calculus

<a id="x-28GEB-2ELAMBDA-2ESPEC-3A-40LAMBDA-SPECS-20MGL-PAX-3ASECTION-29"></a>
### 10.1 Lambda Specification

###### \[in package GEB.LAMBDA.SPEC\]
This covers the various the abstract data type that is the simply
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


<a id="x-28GEB-2ELAMBDA-2ESPEC-3A-3CSTLC-3E-20TYPE-29"></a>
- [type] **\<STLC\>**

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ASTLC-20TYPE-29"></a>
- [type] **STLC**

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AABSURD-20TYPE-29"></a>
- [type] **ABSURD**

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AABSURD-VALUE-20FUNCTION-29"></a>
- [function] **ABSURD-VALUE** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AUNIT-20TYPE-29"></a>
- [type] **UNIT**

<a id="x-28GEB-2ELAMBDA-2ESPEC-3APAIR-20TYPE-29"></a>
- [type] **PAIR**

<a id="x-28GEB-2ELAMBDA-2ESPEC-3APAIR-LTY-20FUNCTION-29"></a>
- [function] **PAIR-LTY** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3APAIR-RTY-20FUNCTION-29"></a>
- [function] **PAIR-RTY** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3APAIR-LEFT-20FUNCTION-29"></a>
- [function] **PAIR-LEFT** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3APAIR-RIGHT-20FUNCTION-29"></a>
- [function] **PAIR-RIGHT** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ALEFT-20TYPE-29"></a>
- [type] **LEFT**

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ALEFT-VALUE-20FUNCTION-29"></a>
- [function] **LEFT-VALUE** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ARIGHT-20TYPE-29"></a>
- [type] **RIGHT**

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ARIGHT-VALUE-20FUNCTION-29"></a>
- [function] **RIGHT-VALUE** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ACASE-ON-20TYPE-29"></a>
- [type] **CASE-ON**

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ACASE-ON-LTY-20FUNCTION-29"></a>
- [function] **CASE-ON-LTY** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ACASE-ON-RTY-20FUNCTION-29"></a>
- [function] **CASE-ON-RTY** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ACASE-ON-COD-20FUNCTION-29"></a>
- [function] **CASE-ON-COD** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ACASE-ON-ON-20FUNCTION-29"></a>
- [function] **CASE-ON-ON** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ACASE-ON-LEFT-20FUNCTION-29"></a>
- [function] **CASE-ON-LEFT** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ACASE-ON-RIGHT-20FUNCTION-29"></a>
- [function] **CASE-ON-RIGHT** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AFST-20TYPE-29"></a>
- [type] **FST**

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AFST-LTY-20FUNCTION-29"></a>
- [function] **FST-LTY** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AFST-RTY-20FUNCTION-29"></a>
- [function] **FST-RTY** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AFST-VALUE-20FUNCTION-29"></a>
- [function] **FST-VALUE** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ASND-20TYPE-29"></a>
- [type] **SND**

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ASND-LTY-20FUNCTION-29"></a>
- [function] **SND-LTY** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ASND-RTY-20FUNCTION-29"></a>
- [function] **SND-RTY** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ASND-VALUE-20FUNCTION-29"></a>
- [function] **SND-VALUE** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ALAMB-20TYPE-29"></a>
- [type] **LAMB**

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ALAMB-VTY-20FUNCTION-29"></a>
- [function] **LAMB-VTY** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ALAMB-TTY-20FUNCTION-29"></a>
- [function] **LAMB-TTY** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ALAMB-VALUE-20FUNCTION-29"></a>
- [function] **LAMB-VALUE** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AAPP-20TYPE-29"></a>
- [type] **APP**

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AAPP-DOM-20FUNCTION-29"></a>
- [function] **APP-DOM** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AAPP-COD-20FUNCTION-29"></a>
- [function] **APP-COD** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AAPP-FUNC-20FUNCTION-29"></a>
- [function] **APP-FUNC** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AAPP-OBJ-20FUNCTION-29"></a>
- [function] **APP-OBJ** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AINDEX-20TYPE-29"></a>
- [type] **INDEX**

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AINDEX-INDEX-20FUNCTION-29"></a>
- [function] **INDEX-INDEX** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATYPED-20FUNCTION-29"></a>
- [function] **TYPED** *V TYP*

    Puts together the type declaration with the value itself for lambda terms

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATYPED-STLC-TYPE-20FUNCTION-29"></a>
- [function] **TYPED-STLC-TYPE** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATYPED-STLC-VALUE-20FUNCTION-29"></a>
- [function] **TYPED-STLC-VALUE** *INSTANCE*

<a id="x-28GEB-2ELAMBDA-2EMAIN-3A-40LAMBDA-API-20MGL-PAX-3ASECTION-29"></a>
### 10.2 Main functionality

###### \[in package GEB.LAMBDA.MAIN\]
This covers the main API for the [`STLC`][e373] module

<a id="x-28GEB-2ELAMBDA-2ETRANS-3A-40STLC-CONVERSION-20MGL-PAX-3ASECTION-29"></a>
### 10.3 Transition Functions

###### \[in package GEB.LAMBDA.TRANS\]
These functions deal with transforming the data structure to other
data types

<a id="x-28GEB-2ELAMBDA-2ETRANS-3ACOMPILE-CHECKED-TERM-20GENERIC-FUNCTION-29"></a>
- [generic-function] **COMPILE-CHECKED-TERM** *CONTEXT TYPE TERM*

    Compiles a checked term into SubstMorph category

<a id="x-28GEB-2ELAMBDA-2ETRANS-3ATO-POLY-20FUNCTION-29"></a>
- [function] **TO-POLY** *CONTEXT TYPE OBJ*

<a id="x-28GEB-2ELAMBDA-2ETRANS-3ATO-CIRCUIT-20FUNCTION-29"></a>
- [function] **TO-CIRCUIT** *CONTEXT TYPE OBJ NAME*

<a id="x-28GEB-2ELAMBDA-2ETRANS-3A-40UTILITY-20MGL-PAX-3ASECTION-29"></a>
#### 10.3.1 Utility Functionality

These are utility functions relating to translating lambda terms to other types

<a id="x-28GEB-2ELAMBDA-2ETRANS-3ASTLC-CTX-TO-MU-20FUNCTION-29"></a>
- [function] **STLC-CTX-TO-MU** *CONTEXT*

    Converts a generic [(CODE <STLC>)][78ef] context into a [`SUBSTMORPH`][57dc]

<a id="x-28GEB-2ELAMBDA-2ETRANS-3ASO-HOM-20FUNCTION-29"></a>
- [function] **SO-HOM** *DOM COD*

    Computes the hom-object of two [`SUBSTMORPH`][57dc]s

<a id="x-28GEB-2EMIXINS-3A-40MIXINS-20MGL-PAX-3ASECTION-29"></a>
## 11 Mixins

###### \[in package GEB.MIXINS\]
Various [mixins](https://en.wikipedia.org/wiki/Mixin) of the
project. Overall all these offer various services to the rest of the
project

<a id="x-28GEB-2EMIXINS-3A-40POINTWISE-20MGL-PAX-3ASECTION-29"></a>
### 11.1 Pointwise Mixins

Here we provide various mixins that deal with classes in a pointwise
manner. Normally, objects can not be compared in a pointwise manner,
instead instances are compared. This makes functional idioms like
updating a slot in a pure manner (allocating a new object), or even
checking if two objects are [`EQUAL`][96d0]-able adhoc. The pointwise API,
however, derives the behavior and naturally allows such idioms

<a id="x-28GEB-2EMIXINS-3APOINTWISE-MIXIN-20CLASS-29"></a>
- [class] **POINTWISE-MIXIN**

    Provides the service of giving point wise
    operations to classes

Further we may wish to hide any values inherited from our superclass
due to this we can instead compare only the slots defined directly
in our class

<a id="x-28GEB-2EMIXINS-3ADIRECT-POINTWISE-MIXIN-20CLASS-29"></a>
- [class] **DIRECT-POINTWISE-MIXIN** *[POINTWISE-MIXIN][445d]*

    Works like [`POINTWISE-MIXIN`][445d], however functions on
    [`POINTWISE-MIXIN`][445d] will only operate on direct-slots
    instead of all slots the class may contain.
    
    Further all `DIRECT-POINTWISE-MIXIN`'s are [`POINTWISE-MIXIN`][445d]'s

<a id="x-28GEB-2EMIXINS-3A-40POINTWISE-API-20MGL-PAX-3ASECTION-29"></a>
### 11.2 Pointwise API

These are the general API functions on any class that have the
[`POINTWISE-MIXIN`][445d] service.

Functions like [`TO-POINTWISE-LIST`][58a9] allow generic list traversal APIs to
be built off the key-value pair of the raw object form, while
[`OBJ-EQUALP`][c111] allows the checking of functional equality between
objects. Overall the API is focused on allowing more generic
operations on classes that make them as useful for generic data
traversal as `LIST`([`0`][592c] [`1`][98f9])'s are

<a id="x-28GEB-2EMIXINS-3ATO-POINTWISE-LIST-20GENERIC-FUNCTION-29"></a>
- [generic-function] **TO-POINTWISE-LIST** *OBJ*

    Turns a given object into a pointwise `LIST`([`0`][592c] [`1`][98f9]). listing
    the [`KEYWORD`][4850] slot-name next to their value.

<a id="x-28GEB-2EMIXINS-3AOBJ-EQUALP-20GENERIC-FUNCTION-29"></a>
- [generic-function] **OBJ-EQUALP** *OBJECT1 OBJECT2*

    Compares objects with pointwise equality. This is a
    much weaker form of equality comparison than
    [`STANDARD-OBJECT`][a802] [`EQUALP`][c721], which does the much
    stronger pointer quality

<a id="x-28GEB-2EMIXINS-3APOINTWISE-SLOTS-20GENERIC-FUNCTION-29"></a>
- [generic-function] **POINTWISE-SLOTS** *OBJ*

    Works like `C2MOP:COMPUTE-SLOTS` however on the object
    rather than the class

<a id="x-28GEB-2EMIXINS-3A-40MIXIN-EXAMPLES-20MGL-PAX-3ASECTION-29"></a>
### 11.3 Mixins Examples

Let's see some example uses of [`POINTWISE-MIXIN`][445d]:

```common-lisp
(obj-equalp (geb:terminal geb:so1)
            (geb:terminal geb:so1))
=> t

(to-pointwise-list (geb:coprod geb:so1 geb:so1))
=> ((:MCAR . s-1) (:MCADR . s-1))
```


<a id="x-28GEB-2EMIXINS-3A-40METADATA-20MGL-PAX-3ASECTION-29"></a>
### 11.4 Metadata Mixin

Metadata is a form of meta information about a particular
object. Having metadata about an object may be useful if the goal
requires annotating some data with type information, identification
information, or even various levels of compiler information. The
possibilities are endless and are a standard technique.

For this task we offer the [`META-MIXIN`][4529] which will allow
metadata to be stored for any type that uses its service.

<a id="x-28GEB-2EMIXINS-3AMETA-MIXIN-20CLASS-29"></a>
- [class] **META-MIXIN**

    Use my service if you want to have metadata capabilities associated
    with the given object. [Performance][455b] covers my performance
    characteristics

For working with the structure it is best to have operations to treat
it like an ordinary hashtable

<a id="x-28GEB-2EMIXINS-3AMETA-INSERT-20FUNCTION-29"></a>
- [function] **META-INSERT** *OBJECT KEY VALUE &KEY WEAK*

    Inserts a value into storage. If the key is a one time object, then
    the insertion is considered to be volatile, which can be reclaimed
    when no more references to the data exists.
    
    If the data is however a constant like a string, then the insertion is
    considered to be long lived and will always be accessible
    
    The :weak keyword specifies if the pointer stored in the value is weak

<a id="x-28GEB-2EMIXINS-3AMETA-LOOKUP-20FUNCTION-29"></a>
- [function] **META-LOOKUP** *OBJECT KEY*

    Lookups the requested key in the metadata table of the object. We
    look past weak pointers if they exist

<a id="x-28GEB-2EMIXINS-3A-40MIXIN-PERFORMANCE-20MGL-PAX-3ASECTION-29"></a>
#### 11.4.1 Performance

The data stored is at the [`CLASS`][7e58] level. So having your type take the
[`META-MIXIN`][4529] does interfere with the cache.

Due to concerns about meta information being populated over time, the
table which it is stored with is in a
[weak](http://www.lispworks.com/documentation/lcl50/aug/aug-141.html)
hashtable, so if the object that the metadata is about gets
deallocated, so does the metadata table.

The full layout can be observed from this interaction

```lisp
;; any class that uses the service
(defparameter *x* (make-instance 'meta-mixin))

(meta-insert *x* :a 3)

(defparameter *y* (make-instance 'meta-mixin))

(meta-insert *y* :b 3)

(defparameter *z* (make-instance 'meta-mixin))

;; where {} is a hashtable
{*x* {:a 3}
 *y* {:b 3}}
```

Since `*z*` does not interact with storage no overhead of storage is
had. Further if \`*x* goes out of scope, gc would reclaim the table leaving

```lisp
{*y* {:b 3}}
```

for the hashtable.

Even the tables inside each object's map are weak, thus we can make
storage inside metadata be separated into volatile and stable
storage.

<a id="x-28GEB-2EUTILS-3A-40GEB-UTILS-MANUAL-20MGL-PAX-3ASECTION-29"></a>
## 12 Geb Utilities

###### \[in package GEB.UTILS\]
The Utilities package provides general utility functionality that is
used throughout the GEB codebase

<a id="x-28GEB-2EUTILS-3ALIST-OF-20TYPE-29"></a>
- [type] **LIST-OF** *TY*

    Allows us to state a list contains a given type.
    
    ---
    
    *NOTE*
    
    This does not type check the whole list, but only the first
    element. This is an issue with how lists are defined in the
    language. Thus this should be be used for intent purposes.
    
    ---
    
    For a more proper version that checks all elements please look at writing code like
    
    ```cl
    (deftype normal-form-list ()
      `(satisfies normal-form-list))
    
    (defun normal-form-list (list)
      (and (listp list)
           (every (lambda (x) (typep x 'normal-form)) list)))
    
    (deftype normal-form ()
      `(or wire constant))
    ```
    
    Example usage of this can be used with [`typep`][d908]
    
    ```common-lisp
    (typep '(1 . 23) '(list-of fixnum))
    => NIL
    
    (typep '(1 23) '(list-of fixnum))
    => T
    
    (typep '(1 3 4 "hi" 23) '(list-of fixnum))
    => T
    
    (typep '(1 23 . 5) '(list-of fixnum))
    => T
    ```
    
    Further this can be used in type signatures
    
    ```cl
    (-> foo (fixnum) (list-of fixnum))
    (defun foo (x)
      (list x))
    ```


<a id="x-28GEB-2EUTILS-3ASYMBOL-TO-KEYWORD-20FUNCTION-29"></a>
- [function] **SYMBOL-TO-KEYWORD** *SYMBOL*

    Turns a [symbol][7f9f] into a [keyword][4850]

<a id="x-28GEB-2EUTILS-3AMUFFLE-PACKAGE-VARIANCE-20MGL-PAX-3AMACRO-29"></a>
- [macro] **MUFFLE-PACKAGE-VARIANCE** *&REST PACKAGE-DECLARATIONS*

    Muffle any errors about package variance and stating exports out of order.
    This is particularly an issue for SBCL as it will error when using MGL-PAX
    to do the [export][bf07] instead of [`DEFPACKAGE`][42d7].
    
    This is more modular thank
    [MGL-PAX:DEFINE-PACKAGE](https://melisgl.Githubc.io/mgl-pax-world/mgl-pax-manual.html#MGL-PAX:DEFINE-PACKAGE%20MGL-PAX:MACRO)
    in that this can be used with any package creation function like
    [UIOP:DEFINE-PACKAGE](https://privet-kitty.github.io/etc/uiop.html#UIOP_002fPACKAGE).
    
    Here is an example usage:
    
    ```lisp
         (geb.utils:muffle-package-variance
           (uiop:define-package #:geb.lambda.trans
             (:mix #:trivia #:geb #:serapeum #:common-lisp)
             (:export
              :compile-checked-term :stlc-ctx-to-mu)))
    ```


<a id="x-28GEB-2EUTILS-3ASUBCLASS-RESPONSIBILITY-20FUNCTION-29"></a>
- [function] **SUBCLASS-RESPONSIBILITY** *OBJ*

    Denotes that the given method is the subclasses
    responsibility. Inspired from Smalltalk

<a id="x-28GEB-2EUTILS-3ASHALLOW-COPY-OBJECT-20FUNCTION-29"></a>
- [function] **SHALLOW-COPY-OBJECT** *ORIGINAL*

<a id="x-28GEB-2EUTILS-3AMAKE-PATTERN-20MGL-PAX-3AMACRO-29"></a>
- [macro] **MAKE-PATTERN** *OBJECT-NAME &REST CONSTRUCTOR-NAMES*

    make pattern matching position style instead of record style. This
    removes the record constructor style, however it can be brought back
    if wanted
    
    ```lisp
    (defclass alias (<substmorph> <substobj>)
      ((name :initarg :name
             :accessor name
             :type     symbol
             :documentation "The name of the GEB object")
       (obj :initarg :obj
            :accessor obj
            :documentation "The underlying geb object"))
      (:documentation "an alias for a geb object"))
    
    (make-pattern alias name obj)
    ```


<a id="x-28GEB-2EUTILS-3ANUMBER-TO-DIGITS-20FUNCTION-29"></a>
- [function] **NUMBER-TO-DIGITS** *NUMBER &OPTIONAL REM*

    turns an [`INTEGER`][ac8a] into a list of its digits

<a id="x-28GEB-2EUTILS-3ADIGIT-TO-UNDER-20FUNCTION-29"></a>
- [function] **DIGIT-TO-UNDER** *DIGIT*

    Turns a digit into a subscript string version of the number

<a id="x-28GEB-2EUTILS-3ANUMBER-TO-UNDER-20FUNCTION-29"></a>
- [function] **NUMBER-TO-UNDER** *INDEX*

    Turns an [`INTEGER`][ac8a] into a subscripted [`STRING`][4267]

<a id="x-28GEB-2EUTILS-3A-40GEB-ACCESSORS-20MGL-PAX-3ASECTION-29"></a>
### 12.1 Accessors

These functions are generic lenses of the GEB codebase. If a class is
defined, where the names are not known, then these accessors are
likely to be used. They may even augment existing classes.

<a id="x-28GEB-2EUTILS-3AMCAR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCAR** *OBJ*

    Can be seen as calling [`CAR`][8c99] on a generic CLOS
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-2EUTILS-3AMCADR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCADR** *OBJ*

    like [`MCAR`][f1ce] but for the [`CADR`][74ab]

<a id="x-28GEB-2EUTILS-3AMCADDR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCADDR** *OBJ*

    like [`MCAR`][f1ce] but for the [`CADDR`][8bb8]

<a id="x-28GEB-2EUTILS-3AMCADDDR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCADDDR** *OBJ*

    like [`MCAR`][f1ce] but for the [`CADDDR`][1791]

<a id="x-28GEB-2EUTILS-3AMCDR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCDR** *OBJ*

    Similar to [`MCAR`][f1ce], however acts like a [`CDR`][2570] for
    [classes][7e58] that we wish to view as a [`SEQUENCE`][b9c1]

<a id="x-28GEB-2EUTILS-3AOBJ-20GENERIC-FUNCTION-29"></a>
- [generic-function] **OBJ** *OBJ*

    Grabs the underlying
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-2EUTILS-3ANAME-20GENERIC-FUNCTION-29"></a>
- [generic-function] **NAME** *OBJ*

    the name of the given
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-2EUTILS-3AFUNC-20GENERIC-FUNCTION-29"></a>
- [generic-function] **FUNC** *OBJ*

    the function of the
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-2EUTILS-3APREDICATE-20GENERIC-FUNCTION-29"></a>
- [generic-function] **PREDICATE** *OBJ*

    the `PREDICATE` of the
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-2EUTILS-3ATHEN-20GENERIC-FUNCTION-29"></a>
- [generic-function] **THEN** *OBJ*

    the then branch of the
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-2EUTILS-3AELSE-20GENERIC-FUNCTION-29"></a>
- [generic-function] **ELSE** *OBJ*

    the then branch of the
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-TEST-3A-40GEB-TEST-MANUAL-20MGL-PAX-3ASECTION-29"></a>
## 13 Testing

###### \[in package GEB-TEST\]
We use [parachute](https://quickref.common-lisp.net/parachute.html)
as our testing framework.

Please read the
[manual](https://quickref.common-lisp.net/parachute.html) for extra
features and how to better lay out future tests

<a id="x-28GEB-TEST-3ARUN-TESTS-20FUNCTION-29"></a>
- [function] **RUN-TESTS** *&KEY (INTERACTIVE? NIL) (SUMMARY? NIL) (PLAIN? T) (DESIGNATORS '(GEB-TEST-SUITE))*

    Here we run all the tests. We have many flags to determine how the
    tests ought to work
    
    ```lisp
    (run-tests :plain? nil :interactive? t) ==> 'interactive
    (run-tests :summary? t :interactive? t) ==> 'noisy-summary
    (run-tests :interactive? t)             ==> 'noisy-interactive
    (run-tests :summary? t)                 ==> 'summary
    (run-tests)                             ==> 'plain
    
    (run-tests :designators '(geb geb.lambda)) ==> run only those packages
    ```


<a id="x-28GEB-TEST-3ARUN-TESTS-ERROR-20FUNCTION-29"></a>
- [function] **RUN-TESTS-ERROR**

<a id="x-28GEB-TEST-3ACODE-COVERAGE-20FUNCTION-29"></a>
- [function] **CODE-COVERAGE** *&OPTIONAL (PATH NIL)*

    generates code coverage, for CCL the coverage can be found at
    
    [CCL test coverage](../docs/tests/report.html)
    
    [SBCL test coverage](../docs/tests/cover-index.html)
    
    simply run this function to generate a fresh one

  [0609]: #x-28GEB-2ELAMBDA-2ETRANS-3A-40UTILITY-20MGL-PAX-3ASECTION-29 "Utility Functionality"
  [0ad4]: #x-28GEB-BOOL-3ABOOL-20MGL-PAX-3ASYMBOL-MACRO-29 "GEB-BOOL:BOOL MGL-PAX:SYMBOL-MACRO"
  [0ae3]: #x-28GEB-2EPOLY-2ESPEC-3A-2A-20TYPE-29 "GEB.POLY.SPEC:* TYPE"
  [0dcc]: #x-28GEB-2ESPEC-3APROJECT-LEFT-20TYPE-29 "GEB.SPEC:PROJECT-LEFT TYPE"
  [0dfe]: #x-28GEB-2ESPEC-3A-3C-RIGHT-20FUNCTION-29 "GEB.SPEC:<-RIGHT FUNCTION"
  [0e00]: #x-28GEB-DOCS-2FDOCS-3A-40YONEDA-LEMMA-20MGL-PAX-3ASECTION-29 "The Yoneda Lemma"
  [0f3e]: #x-28GEB-2EPOLY-2ETRANS-3A-40POLY-TRANS-20MGL-PAX-3ASECTION-29 "Polynomial Transformations"
  [1791]: http://www.lispworks.com/documentation/HyperSpec/Body/f_car_c.htm "CADDDR FUNCTION"
  [1b98]: #x-28GEB-GUI-2EGRAPHING-3A-40GRAPHING-MANUAL-20MGL-PAX-3ASECTION-29 "The GEB Graphizer"
  [1f3a]: #x-28GEB-2ESPEC-3ASO0-20TYPE-29 "GEB.SPEC:SO0 TYPE"
  [1fbc]: #x-28GEB-GUI-2ECORE-3ACHILDREN-20GENERIC-FUNCTION-29 "GEB-GUI.CORE:CHILDREN GENERIC-FUNCTION"
  [2276]: #x-28GEB-2EUTILS-3ASUBCLASS-RESPONSIBILITY-20FUNCTION-29 "GEB.UTILS:SUBCLASS-RESPONSIBILITY FUNCTION"
  [2570]: http://www.lispworks.com/documentation/HyperSpec/Body/f_car_c.htm "CDR FUNCTION"
  [25f0]: #x-28GEB-DOCS-2FDOCS-3A-40GLOSSARY-20MGL-PAX-3ASECTION-29 "Glossary"
  [2882]: #x-28GEB-2ESPEC-3A-3C-LEFT-20FUNCTION-29 "GEB.SPEC:<-LEFT FUNCTION"
  [29b7]: #x-28GEB-DOCS-2FDOCS-3A-40AGDA-20MGL-PAX-3ASECTION-29 "Geb's Agda Code"
  [2ad4]: #x-28GEB-2ESPEC-3A-40GEB-CONSTRUCTORS-20MGL-PAX-3ASECTION-29 "Constructors"
  [2c5e]: #x-28GEB-2EPOLY-2ESPEC-3A--20TYPE-29 "GEB.POLY.SPEC:- TYPE"
  [2cbc]: #x-28GEB-2EMAIN-3ACURRY-20FUNCTION-29 "GEB.MAIN:CURRY FUNCTION"
  [2fcf]: #x-28GEB-2EMIXINS-3A-40POINTWISE-API-20MGL-PAX-3ASECTION-29 "Pointwise API"
  [3173]: #x-28GEB-2ESPEC-3ASUBSTOBJ-20TYPE-29 "GEB.SPEC:SUBSTOBJ TYPE"
  [31c5]: #x-28GEB-BOOL-3AFALSE-20MGL-PAX-3ASYMBOL-MACRO-29 "GEB-BOOL:FALSE MGL-PAX:SYMBOL-MACRO"
  [34d0]: #x-28GEB-2ELAMBDA-2ESPEC-3A-40LAMBDA-SPECS-20MGL-PAX-3ASECTION-29 "Lambda Specification"
  [365a]: #x-28GEB-2EUTILS-3AELSE-20GENERIC-FUNCTION-29 "GEB.UTILS:ELSE GENERIC-FUNCTION"
  [3686]: #x-28GEB-DOCS-2FDOCS-3A-40ORIGINAL-EFFORTS-20MGL-PAX-3ASECTION-29 "Original Efforts"
  [399c]: #x-28GEB-BOOL-3A-40GEB-BOOL-20MGL-PAX-3ASECTION-29 "Booleans"
  [3bc6]: #x-28GEB-2ESPEC-3APAIR-20TYPE-29 "GEB.SPEC:PAIR TYPE"
  [3d47]: #x-28GEB-DOCS-2FDOCS-3A-40GETTING-STARTED-20MGL-PAX-3ASECTION-29 "Getting Started"
  [4044]: #x-28GEB-DOCS-2FDOCS-3A-40COVERAGE-20MGL-PAX-3ASECTION-29 "code coverage"
  [417f]: #x-28GEB-TEST-3ACODE-COVERAGE-20FUNCTION-29 "GEB-TEST:CODE-COVERAGE FUNCTION"
  [4267]: http://www.lispworks.com/documentation/HyperSpec/Body/t_string.htm "STRING TYPE"
  [42d7]: http://www.lispworks.com/documentation/HyperSpec/Body/m_defpkg.htm "DEFPACKAGE MGL-PAX:MACRO"
  [445d]: #x-28GEB-2EMIXINS-3APOINTWISE-MIXIN-20CLASS-29 "GEB.MIXINS:POINTWISE-MIXIN CLASS"
  [4529]: #x-28GEB-2EMIXINS-3AMETA-MIXIN-20CLASS-29 "GEB.MIXINS:META-MIXIN CLASS"
  [455b]: #x-28GEB-2EMIXINS-3A-40MIXIN-PERFORMANCE-20MGL-PAX-3ASECTION-29 "Performance"
  [4850]: http://www.lispworks.com/documentation/HyperSpec/Body/t_kwd.htm "KEYWORD TYPE"
  [4938]: #x-28GEB-2EMIXINS-3A-40MIXIN-EXAMPLES-20MGL-PAX-3ASECTION-29 "Mixins Examples"
  [49d4]: #x-28GEB-2EMAIN-3A-40GEB-UTILITY-20MGL-PAX-3ASECTION-29 "Utility"
  [4a87]: #x-28GEB-DOCS-2FDOCS-3A-40OPEN-TYPE-20MGL-PAX-3AGLOSSARY-TERM-29 "GEB-DOCS/DOCS:@OPEN-TYPE MGL-PAX:GLOSSARY-TERM"
  [4ffa]: #x-28GEB-2EUTILS-3A-40GEB-UTILS-MANUAL-20MGL-PAX-3ASECTION-29 "Geb Utilities"
  [57dc]: #x-28GEB-2ESPEC-3ASUBSTMORPH-20TYPE-29 "GEB.SPEC:SUBSTMORPH TYPE"
  [58a9]: #x-28GEB-2EMIXINS-3ATO-POINTWISE-LIST-20GENERIC-FUNCTION-29 "GEB.MIXINS:TO-POINTWISE-LIST GENERIC-FUNCTION"
  [592c]: http://www.lispworks.com/documentation/HyperSpec/Body/f_list_.htm "LIST FUNCTION"
  [59dd]: #x-28GEB-2ESPEC-3ACASE-20TYPE-29 "GEB.SPEC:CASE TYPE"
  [603e]: #x-28GEB-GUI-3A-40VISAULIZER-AID-20MGL-PAX-3ASECTION-29 "Aiding the Visualizer"
  [6228]: #x-28GEB-3A-40GEB-API-20MGL-PAX-3ASECTION-29 "API"
  [642a]: #x-28GEB-2ETRANS-3ATO-POLY-20GENERIC-FUNCTION-29 "GEB.TRANS:TO-POLY GENERIC-FUNCTION"
  [684b]: http://www.lispworks.com/documentation/HyperSpec/Body/s_if.htm "IF MGL-PAX:MACRO"
  [6f67]: #x-28GEB-GUI-3A-40GEB-GUI-MANUAL-20MGL-PAX-3ASECTION-29 "The GEB GUI"
  [7088]: #x-28GEB-2ESPEC-3ASO0-20MGL-PAX-3ASYMBOL-MACRO-29 "GEB.SPEC:SO0 MGL-PAX:SYMBOL-MACRO"
  [71e9]: #x-28GEB-GUI-2ECORE-3A-40GRAPHING-CORE-20MGL-PAX-3ASECTION-29 "The GEB Graphizer Core"
  [723a]: #x-28GEB-2EMIXINS-3A-40MIXINS-20MGL-PAX-3ASECTION-29 "Mixins"
  [74ab]: http://www.lispworks.com/documentation/HyperSpec/Body/f_car_c.htm "CADR FUNCTION"
  [74bd]: #x-28GEB-2EMIXINS-3ACAT-OBJ-20CLASS-29 "GEB.MIXINS:CAT-OBJ CLASS"
  [77c2]: #x-28GEB-2ESPEC-3APROD-20TYPE-29 "GEB.SPEC:PROD TYPE"
  [78ef]: http://www.lispworks.com/documentation/HyperSpec/Body/t_nil.htm "NIL TYPE"
  [7e58]: http://www.lispworks.com/documentation/HyperSpec/Body/t_class.htm "CLASS CLASS"
  [7f9f]: http://www.lispworks.com/documentation/HyperSpec/Body/t_symbol.htm "SYMBOL TYPE"
  [8214]: #x-28GEB-2ESPEC-3A-3CSUBSTOBJ-3E-20TYPE-29 "GEB.SPEC:<SUBSTOBJ> TYPE"
  [8311]: #x-28GEB-DOCS-2FDOCS-3A-40IDRIS-20MGL-PAX-3ASECTION-29 "Geb's Idris Code"
  [8932]: #x-28GEB-DOCS-2FDOCS-3A-40CLOSED-TYPE-20MGL-PAX-3AGLOSSARY-TERM-29 "GEB-DOCS/DOCS:@CLOSED-TYPE MGL-PAX:GLOSSARY-TERM"
  [8bb8]: http://www.lispworks.com/documentation/HyperSpec/Body/f_car_c.htm "CADDR FUNCTION"
  [8bf3]: #x-28GEB-2EPOLY-2ESPEC-3APOLY-20TYPE-29 "GEB.POLY.SPEC:POLY TYPE"
  [8c99]: http://www.lispworks.com/documentation/HyperSpec/Body/f_car_c.htm "CAR FUNCTION"
  [8da6]: #x-28GEB-2EUTILS-3APREDICATE-20GENERIC-FUNCTION-29 "GEB.UTILS:PREDICATE GENERIC-FUNCTION"
  [8eb0]: #x-28GEB-2EENTRY-3A-40GEB-ENTRY-20MGL-PAX-3ASECTION-29 "Geb as a binary"
  [8fa5]: #x-28GEB-DOCS-2FDOCS-3A-40INSTALLATION-20MGL-PAX-3ASECTION-29 "installation"
  [9162]: #x-28GEB-2EPOLY-2ESPEC-3ACOMPOSE-20TYPE-29 "GEB.POLY.SPEC:COMPOSE TYPE"
  [925b]: #x-28GEB-DOCS-2FDOCS-3A-40POLY-SETS-20MGL-PAX-3ASECTION-29 "Poly in Sets"
  [9300]: #x-28GEB-2EMIXINS-3A-40METADATA-20MGL-PAX-3ASECTION-29 "Metadata Mixin"
  [94a8]: #x-28GEB-2EPOLY-3A-40POLY-MANUAL-20MGL-PAX-3ASECTION-29 "Polynomial Specification"
  [96d0]: http://www.lispworks.com/documentation/HyperSpec/Body/f_equal.htm "EQUAL FUNCTION"
  [9728]: #x-28GEB-2EMIXINS-3ADOM-20GENERIC-FUNCTION-29 "GEB.MIXINS:DOM GENERIC-FUNCTION"
  [97fb]: #x-28GEB-2ESPEC-3A-3CSUBSTMORPH-3E-20TYPE-29 "GEB.SPEC:<SUBSTMORPH> TYPE"
  [98f9]: http://www.lispworks.com/documentation/HyperSpec/Body/t_list.htm "LIST TYPE"
  [9bc5]: #x-28GEB-DOCS-2FDOCS-3A-40LINKS-20MGL-PAX-3ASECTION-29 "Links"
  [9bcb]: #x-28GEB-TEST-3A-40GEB-TEST-MANUAL-20MGL-PAX-3ASECTION-29 "Testing"
  [9bcb2]: http://www.lispworks.com/documentation/HyperSpec/Body/f_exp_e.htm "EXPT FUNCTION"
  [9f9c]: #x-28GEB-2ESPECS-3A-40GEB-SPECS-20MGL-PAX-3ASECTION-29 "Spec Files, Main Files and Project Layout"
  [a17b]: #x-28GEB-3A-40GEB-EXAMPLES-20MGL-PAX-3ASECTION-29 "Examples"
  [a300]: #x-28GEB-DOCS-2FDOCS-3A-40-3CTYPES-3E-20MGL-PAX-3ASECTION-29 "≺Types≻"
  [a7af]: #x-28GEB-2EMIXINS-3ACAT-MORPH-20CLASS-29 "GEB.MIXINS:CAT-MORPH CLASS"
  [a7d5]: #x-28GEB-DOCS-2FDOCS-3A-40LOADING-20MGL-PAX-3ASECTION-29 "loading"
  [a802]: http://www.lispworks.com/documentation/HyperSpec/Body/t_std_ob.htm "STANDARD-OBJECT TYPE"
  [a920]: #x-28GEB-DOCS-2FDOCS-3A-40OPEN-CLOSED-20MGL-PAX-3ASECTION-29 "Open Types versus Closed Types"
  [a981]: http://www.lispworks.com/documentation/HyperSpec/Body/m_defmet.htm "DEFMETHOD MGL-PAX:MACRO"
  [ac8a]: http://www.lispworks.com/documentation/HyperSpec/Body/t_intege.htm "INTEGER TYPE"
  [ada5]: #x-28GEB-GUI-3AVISUALIZE-20FUNCTION-29 "GEB-GUI:VISUALIZE FUNCTION"
  [ada9]: #x-28GEB-DOCS-2FDOCS-3A-40MORPHISMS-20MGL-PAX-3ASECTION-29 "Morphisms"
  [ae41]: #x-28GEB-2ESPEC-3ATERMINAL-20TYPE-29 "GEB.SPEC:TERMINAL TYPE"
  [af14]: #x-28GEB-2EUTILS-3AMCDR-20GENERIC-FUNCTION-29 "GEB.UTILS:MCDR GENERIC-FUNCTION"
  [b76d]: #x-28GEB-2EPOLY-2ESPEC-3A-40POLY-CONSTRUCTORS-20MGL-PAX-3ASECTION-29 "Polynomial Constructors"
  [b79a]: #x-28GEB-2ETRANS-3A-40GEB-TRANSLATION-20MGL-PAX-3ASECTION-29 "Translation Functions"
  [b960]: #x-28GEB-2ESPEC-3A-2ASO1-2A-20VARIABLE-29 "GEB.SPEC:*SO1* VARIABLE"
  [b9c1]: http://www.lispworks.com/documentation/HyperSpec/Body/t_seq.htm "SEQUENCE TYPE"
  [b9f3]: #x-28GEB-DOCS-2FDOCS-3A-40IDIOMS-20MGL-PAX-3ASECTION-29 "Project Idioms and Conventions"
  [ba44]: #x-28GEB-2ESPEC-3A--3ERIGHT-20FUNCTION-29 "GEB.SPEC:->RIGHT FUNCTION"
  [bd81]: #x-28GEB-2EPOLY-2ESPEC-3A-40POLY-20MGL-PAX-3ASECTION-29 "Polynomial Types"
  [bf07]: http://www.lispworks.com/documentation/HyperSpec/Body/f_export.htm "EXPORT FUNCTION"
  [bfa9]: #x-28GEB-2EUTILS-3ATHEN-20GENERIC-FUNCTION-29 "GEB.UTILS:THEN GENERIC-FUNCTION"
  [c111]: #x-28GEB-2EMIXINS-3AOBJ-EQUALP-20GENERIC-FUNCTION-29 "GEB.MIXINS:OBJ-EQUALP GENERIC-FUNCTION"
  [c144]: #x-28GEB-2EPOLY-2ESPEC-3A-2B-20TYPE-29 "GEB.POLY.SPEC:+ TYPE"
  [c1b3]: #x-28GEB-2ESPEC-3A-40GEB-SUBSTMU-20MGL-PAX-3ASECTION-29 "Subst Obj"
  [c1fb]: #x-28GEB-3A-40GEB-20MGL-PAX-3ASECTION-29 "The Geb Model"
  [c2e9]: #x-28GEB-DOCS-2FDOCS-3A-40MODEL-20MGL-PAX-3ASECTION-29 "Categorical Model"
  [c2f9]: #x-28GEB-2EPOLY-2ESPEC-3A-2F-20TYPE-29 "GEB.POLY.SPEC:/ TYPE"
  [c6cf]: #x-28GEB-GUI-3A-40GEB-VISUALIZER-20MGL-PAX-3ASECTION-29 "Visualizer"
  [c721]: http://www.lispworks.com/documentation/HyperSpec/Body/f_equalp.htm "EQUALP FUNCTION"
  [c767]: http://www.lispworks.com/documentation/HyperSpec/Body/s_the.htm "THE MGL-PAX:MACRO"
  [cab9]: #x-28GEB-2ESPEC-3AINJECT-LEFT-20TYPE-29 "GEB.SPEC:INJECT-LEFT TYPE"
  [cb9e]: #x-28GEB-2ESPEC-3A-40GEB-CATEGORIES-20MGL-PAX-3ASECTION-29 "Core Category"
  [cc51]: #x-28GEB-2EUTILS-3A-40GEB-ACCESSORS-20MGL-PAX-3ASECTION-29 "Accessors"
  [cc87]: #x-28GEB-2EUTILS-3AMCADR-20GENERIC-FUNCTION-29 "GEB.UTILS:MCADR GENERIC-FUNCTION"
  [cd11]: #x-28GEB-2ESPEC-3AMCASE-20FUNCTION-29 "GEB.SPEC:MCASE FUNCTION"
  [ceb9]: http://www.lispworks.com/documentation/HyperSpec/Body/t_fixnum.htm "FIXNUM TYPE"
  [d2d1]: #x-28GEB-2ESPEC-3A-40GEB-SUBSTMORPH-20MGL-PAX-3ASECTION-29 "Subst Morph"
  [d2d5]: #x-28GEB-2ELAMBDA-2EMAIN-3A-40LAMBDA-API-20MGL-PAX-3ASECTION-29 "Main functionality"
  [d5d3]: #x-28GEB-2EMIXINS-3A-40POINTWISE-20MGL-PAX-3ASECTION-29 "Pointwise Mixins"
  [d908]: http://www.lispworks.com/documentation/HyperSpec/Body/f_typep.htm "TYPEP FUNCTION"
  [db8f]: #x-28GEB-2ELAMBDA-3A-40STLC-20MGL-PAX-3ASECTION-29 "The Simply Typed Lambda Calculus model"
  [dbe7]: #x-28GEB-DOCS-2FDOCS-3A-40OBJECTS-20MGL-PAX-3ASECTION-29 "Objects"
  [e2af]: #x-28GEB-2ESPEC-3A--3ELEFT-20FUNCTION-29 "GEB.SPEC:->LEFT FUNCTION"
  [e373]: #x-28GEB-2ELAMBDA-2ESPEC-3ASTLC-20TYPE-29 "GEB.LAMBDA.SPEC:STLC TYPE"
  [e3e4]: #x-28GEB-2ELAMBDA-2ETRANS-3A-40STLC-CONVERSION-20MGL-PAX-3ASECTION-29 "Transition Functions"
  [e429]: #x-28GEB-GUI-2EGRAPHING-2EPASSES-3A-40PASS-MANUAL-20MGL-PAX-3ASECTION-29 "The GEB Graphizer Passes"
  [e65d]: #x-28GEB-2ESPEC-3APROJECT-RIGHT-20TYPE-29 "GEB.SPEC:PROJECT-RIGHT TYPE"
  [e755]: http://www.lispworks.com/documentation/HyperSpec/Body/d_type.htm "TYPE DECLARATION"
  [e91b]: #x-28GEB-2EMIXINS-3A-40MIXINS-CAT-20MGL-PAX-3ASECTION-29 "The Categorical Interface"
  [e982]: #x-28GEB-2ESPEC-3A-2ASO0-2A-20VARIABLE-29 "GEB.SPEC:*SO0* VARIABLE"
  [ebf5]: #x-28GEB-2ESPEC-3ASO1-20TYPE-29 "GEB.SPEC:SO1 TYPE"
  [ecc6]: #x-28GEB-DOCS-2FDOCS-3A-40CLOS-20MGL-PAX-3AGLOSSARY-TERM-29 "GEB-DOCS/DOCS:@CLOS MGL-PAX:GLOSSARY-TERM"
  [ef6e]: #x-28GEB-GUI-2ECORE-3ANOTE-20TYPE-29 "GEB-GUI.CORE:NOTE TYPE"
  [f022]: #x-28GEB-BOOL-3ATRUE-20MGL-PAX-3ASYMBOL-MACRO-29 "GEB-BOOL:TRUE MGL-PAX:SYMBOL-MACRO"
  [f1ce]: #x-28GEB-2EUTILS-3AMCAR-20GENERIC-FUNCTION-29 "GEB.UTILS:MCAR GENERIC-FUNCTION"
  [f1e6]: #x-28GEB-2EUTILS-3AOBJ-20GENERIC-FUNCTION-29 "GEB.UTILS:OBJ GENERIC-FUNCTION"
  [f4ba]: #x-28GEB-2ESPEC-3ASO1-20MGL-PAX-3ASYMBOL-MACRO-29 "GEB.SPEC:SO1 MGL-PAX:SYMBOL-MACRO"
  [f766]: http://www.lispworks.com/documentation/HyperSpec/Body/f_load.htm "LOAD FUNCTION"
  [f899]: #x-28GEB-2ESPEC-3AINIT-20TYPE-29 "GEB.SPEC:INIT TYPE"
  [f914]: #x-28GEB-2ESPEC-3ACOMP-20TYPE-29 "GEB.SPEC:COMP TYPE"
  [fae9]: #x-28GEB-2ESPEC-3AINJECT-RIGHT-20TYPE-29 "GEB.SPEC:INJECT-RIGHT TYPE"
  [fb12]: #x-28GEB-2ESPEC-3ACOPROD-20TYPE-29 "GEB.SPEC:COPROD TYPE"
  [ff98]: #x-28GEB-GUI-2ECORE-3ANODE-20CLASS-29 "GEB-GUI.CORE:NODE CLASS"

* * *
###### \[generated by [MGL-PAX](https://github.com/melisgl/mgl-pax)\]
