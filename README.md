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
    - [7.2 Geneircs][a84b]
    - [7.3 Core Category][cb9e]
        - [7.3.1 Subst Obj][c1b3]
        - [7.3.2 Subst Morph][d2d1]
        - [7.3.3 Realized Subst Objs][dca9]
    - [7.4 Accessors][cc51]
    - [7.5 Constructors][2ad4]
    - [7.6 API][6228]
        - [7.6.1 Booleans][399c]
        - [7.6.2 Lists][1c91]
        - [7.6.3 Translation Functions][b79a]
        - [7.6.4 Utility][49d4]
    - [7.7 Examples][a17b]
- [8 Extension Sets for Categories][0efa]
- [9 The GEB GUI][6f67]
    - [9.1 Visualizer][c6cf]
        - [9.1.1 Aiding the Visualizer][603e]
    - [9.2 The GEB Graphizer][1b98]
        - [9.2.1 The GEB Graphizer Core][71e9]
        - [9.2.2 The GEB Graphizer Passes][e429]
- [10 Bits (Boolean Circuit) Specification][6b63]
    - [10.1 Bits Types][2172]
    - [10.2 Bits (Boolean Circuit) Constructors][fc10]
    - [10.3 Bits (Boolean Circuit) API][4659]
    - [10.4 Bits (Boolean Circuit) Transformations][2ebc]
- [11 Polynomial Specification][94a8]
    - [11.1 Polynomial Types][bd81]
    - [11.2 Polynomial API][0251]
    - [11.3 Polynomial Constructors][b76d]
    - [11.4 Polynomial Transformations][0f3e]
- [12 The Simply Typed Lambda Calculus model][db8f]
    - [12.1 Lambda Specification][34d0]
    - [12.2 Main functionality][d2d5]
    - [12.3 Transition Functions][e3e4]
        - [12.3.1 Utility Functionality][0609]
- [13 Mixins][723a]
    - [13.1 Pointwise Mixins][d5d3]
    - [13.2 Pointwise API][2fcf]
    - [13.3 Mixins Examples][4938]
    - [13.4 Metadata Mixin][9300]
        - [13.4.1 Performance][455b]
- [14 Geb Utilities][4ffa]
    - [14.1 Accessors][cc51]
- [15 Testing][9bcb]

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
mariari@Gensokyo % ./geb.image -i "foo.lisp" -e "geb.lambda.main::*entry*" -l -v -o "foo.pir"

mariari@Gensokyo % cat foo.pir
def entry x1 = {
  (x1)
};%
mariari@Gensokyo % ./geb.image -i "foo.lisp" -e "geb.lambda.main::*entry*" -l -v
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

any valid lambda form. Good examples can be found at the following section:

[The Simply Typed Lambda Calculus model][db8f]

with the term bound to some global variable

```lisp
(in-package :geb.lambda.main)

(defparameter *entry*
  (lamb (list (coprod so1 so1))
        (index 0)))
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
    
    This type is closed, as only one of [`GEB:SUBSTOBJ`][3173], [`GEB:INJECT-LEFT`][8387],
    [`GEB:INJECT-RIGHT`][e947] etc can form the [`GEB:SUBSTMORPH`][57dc] type.
    
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
    
    If we forget a case, like [`GEB:COPROD`][8be5] it wanrs us with an non exhaustion warning.
    
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
    
    Now any methods on [`GEB:<SUBSTOBJ>`][fb79] will cover `GEB:SO0`([`0`][5c7c] [`1`][7088]).
    
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
update and get exhaustive warnings about. Whereas [`GEB:<SUBSTOBJ>`][fb79] is
the open interface for the type. Thus we can view [`GEB:<SUBSTOBJ>`][fb79] as
the general idea of a [`GEB:SUBSTOBJ`][3173]. Before delving into how we combine
these methods, let us look at two other benefits given by [`GEB:<SUBSTOBJ>`][fb79]

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

2. We cannot hit the [`GEB:<SUBSTOBJ>`][fb79] case due to method dispatch

3. We have this [`GEB.UTILS:SUBCLASS-RESPONSIBILITY`][2276] function getting called.

4. We can write further methods extending the function to other subtypes.

Thus the [`GEB.COMMON:TO-POLY`][2eb9] function is written in such a way that it
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

<a id="x-28GEB-2EGENERICS-3A-40GENERICS-20MGL-PAX-3ASECTION-29"></a>
### 7.2 Geneircs

###### \[in package GEB.GENERICS\]
These functions represent the generic functions that can be run on
many parts of the compiler, they are typically rexported on any
package that implements the given generic function.

You can view their documentation in their respective API sections.

The main documentation for the functionality is given here, with
examples often given in the specific methods

<a id="x-28GEB-2EGENERICS-3AGAPPLY-20GENERIC-FUNCTION-29"></a>
- [generic-function] **GAPPLY** *MORPHISM OBJECT*

    Applies a given Moprhism to a given object.
    
    This is practically a naive interpreter for any category found
    throughout the codebase.
    
    Some example usages of `GAPPLY` are.
    
    ```lisp
    GEB> (gapply (comp
                  (mcase geb-bool:true
                         geb-bool:not)
                  (->right so1 geb-bool:bool))
                 (left so1))
    (right s-1)
    GEB> (gapply (comp
                  (mcase geb-bool:true
                         geb-bool:not)
                  (->right so1 geb-bool:bool))
                 (right so1))
    (left s-1)
    ```


<a id="x-28GEB-2EGENERICS-3AMAYBE-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MAYBE** *OBJECT*

    Wraps the given `OBJECT` into a Maybe monad The Maybe monad in this
    case is simply wrapping the term in a [coprod][8be5]
    of so1([`0`][5cfe] [`1`][f4ba])
    
    ```lisp
    ;; Before
    x
    
    ;; After
    (COPROD SO1 X)
    ```


<a id="x-28GEB-2EGENERICS-3ATO-CIRCUIT-20GENERIC-FUNCTION-29"></a>
- [generic-function] **TO-CIRCUIT** *MORPHISM NAME*

    Turns a `MORPHISM` into a Vampir circuit. the `NAME` is the given name of
    the output circuit.

<a id="x-28GEB-2EGENERICS-3ATO-BITC-20GENERIC-FUNCTION-29"></a>
- [generic-function] **TO-BITC** *MORPHISM*

    Turns a given `MORPHISM` into a [`GEB.BITC.SPEC:BITC`][e017]

<a id="x-28GEB-2EGENERICS-3ATO-POLY-20GENERIC-FUNCTION-29"></a>
- [generic-function] **TO-POLY** *MORPHISM*

    Turns a given `MORPHISM` into a [`GEB.POLY.SPEC:POLY`][8bf3]

<a id="x-28GEB-2EGENERICS-3ATO-CAT-20GENERIC-FUNCTION-29"></a>
- [generic-function] **TO-CAT** *CONTEXT TERM*

    Turns a `MORPHISM` with a context into Geb's Core category

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **TO-VAMPIR** *MORPHISM VALUES CONSTRAINTS*

    Turns a `MORPHISM` into a Vampir circuit, with concrete values.
    
    The more natural interface is [`TO-CIRCUIT`][b0d9], however this is a more low
    level interface into what the polynomial categories actually
    implement, and thus can be extended or changed.
    
    The `VALUES` are likely vampir values in a list.
    
    The `CONSTRAINTS` represent constraints that get creating

<a id="x-28GEB-2ESPEC-3A-40GEB-CATEGORIES-20MGL-PAX-3ASECTION-29"></a>
### 7.3 Core Category

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
#### 7.3.1 Subst Obj

This section covers the objects of the [`SUBSTMORPH`][57dc]
category. Note that [`SUBSTOBJ`][3173] refers to the
[closed type][8932], whereas [`<SUBSTOBJ>`][fb79] refers
to the [open type][4a87] that allows for user extension.

<a id="x-28GEB-2ESPEC-3ASUBSTOBJ-20TYPE-29"></a>
- [type] **SUBSTOBJ**

<a id="x-28GEB-2ESPEC-3A-3CSUBSTOBJ-3E-20CLASS-29"></a>
- [class] **\<SUBSTOBJ\>** *[\<SUBSTMORPH\>][db35] [DIRECT-POINTWISE-MIXIN][e2b0] [META-MIXIN][4529] [CAT-OBJ][74bd]*

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


<a id="x-28GEB-2ESPEC-3APROD-20CLASS-29"></a>
- [class] **PROD** *[\<SUBSTOBJ\>][fb79]*

    The [PRODUCT][06c6] object. Takes two [`CAT-OBJ`][74bd] values that
    get put into a pair.
    
    The formal grammar of [PRODUCT][06c6] is
    
    ```lisp
    (prod mcar mcadr)
    ```
    
    where [`PROD`][06c6] is the constructor, [`MCAR`][f1ce] is the left value of the
    product, and [`MCADR`][cc87] is the right value of the product.
    
    Example:
    
    ```lisp
    (geb-gui::visualize (prod geb-bool:bool geb-bool:bool))
    ```
    
    Here we create a product of two [`GEB-BOOL:BOOL`][0ad4] types.

<a id="x-28GEB-2ESPEC-3ACOPROD-20CLASS-29"></a>
- [class] **COPROD** *[\<SUBSTOBJ\>][fb79]*

    the [CO-PRODUCT][8be5] object. Takes [`CAT-OBJ`][74bd] values that
    get put into a choice of either value.
    
    The formal grammar of [PRODUCT][06c6] is
    
    ```lisp
    (coprod mcar mcadr)
    ```
    
    Where [CORPOD][7e58] is the constructor, [`MCAR`][f1ce] is the left choice of
    the sum, and [`MCADR`][cc87] is the right choice of the sum.
    
    Example:
    
    ```lisp
    (geb-gui::visualize (coprod so1 so1))
    ```
    
    Here we create the boolean type, having a choice between two unit
    values.

<a id="x-28GEB-2ESPEC-3ASO0-20CLASS-29"></a>
- [class] **SO0** *[\<SUBSTOBJ\>][fb79]*

    The Initial Object. This is sometimes known as the
    [VOID](https://en.wikipedia.org/wiki/Void_type) type.
    
    the formal grammar of [`SO0`][5c7c] is
    
    ```lisp
    so0
    ```
    
    where [`SO0`][5c7c] is [`THE`][c767] initial object.
    
    Example
    
    `lisp
    `

<a id="x-28GEB-2ESPEC-3ASO1-20CLASS-29"></a>
- [class] **SO1** *[\<SUBSTOBJ\>][fb79]*

    The Terminal Object. This is sometimes referred to as the
    [Unit](https://en.wikipedia.org/wiki/Unit_type) type.
    
    the formal grammar or [`SO1`][5cfe] is
    
    ```lisp
    so1
    ```
    
    where [`SO1`][5cfe] is [`THE`][c767] terminal object
    
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
#### 7.3.2 Subst Morph

The overarching types that categorizes the [`SUBSTMORPH`][57dc]
category. Note that [`SUBSTMORPH`][57dc] refers to the
[closed type][8932], whereas [`<SUBSTMORPH>`][db35] refers
to the [open type][4a87] that allows for user extension.

<a id="x-28GEB-2ESPEC-3ASUBSTMORPH-20TYPE-29"></a>
- [type] **SUBSTMORPH**

    The morphisms of the [`SUBSTMORPH`][57dc] category

<a id="x-28GEB-2ESPEC-3A-3CSUBSTMORPH-3E-20CLASS-29"></a>
- [class] **\<SUBSTMORPH\>** *[DIRECT-POINTWISE-MIXIN][e2b0] [META-MIXIN][4529] [CAT-MORPH][a7af]*

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

<a id="x-28GEB-2ESPEC-3ACOMP-20CLASS-29"></a>
- [class] **COMP** *[\<SUBSTMORPH\>][db35]*

    The composition morphism. Takes two [`CAT-MORPH`][a7af] values that get
    applied in standard composition order.
    
    The formal grammar of [`COMP`][ce5b] is
    
    ```lisp
    (comp mcar mcadr)
    ```
    
    which may be more familiar as
    
    ```haskell
    g 。f
    ```
    
    Where [`COMP`][ce5b]( 。) is the constructor, [`MCAR`][f1ce](g) is the second morphism
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
    that gets applied ([`PAIR`][dfa2] ...) is the identity function on the
    type ([`PROD`][06c6] [`SO1`][5cfe] [`GEB-BOOL:BOOL`][0ad4]), where we pair the
    [left projection](PROJECT-LEFT) and the [right
    projection](PROJECT-RIGHT), followed by taking the [right
    projection](PROJECT-RIGHT) of the type.
    
    Since we know ([`COMP`][ce5b] f id) is just f per the laws of category
    theory, this expression just reduces to
    
    ```lisp
    (<-right so1 geb-bool:bool)
    ```


<a id="x-28GEB-2ESPEC-3ACASE-20CLASS-29"></a>
- [class] **CASE** *[\<SUBSTMORPH\>][db35]*

    Eliminates coproducts. Namely Takes two [`CAT-MORPH`][a7af] values, one
    gets applied on the left coproduct while the other gets applied on the
    right coproduct. The result of each `CAT-MORPH` values must be
    the same.
    
    The formal grammar of [`CASE`][5d7c] is:
    
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
    into a pair with the shape ([`SO1`][5cfe] × [`GEB-BOOL:BOOL`][0ad4]), then we use
    [`MCASE`][cd11] to denote a morphism saying. [`IF`][684b] the input is of the shape `SO1`([`0`][5cfe] [`1`][f4ba]),
    then give us True, otherwise flip the value of the boolean coming in.

<a id="x-28GEB-2ESPEC-3AINIT-20CLASS-29"></a>
- [class] **INIT** *[\<SUBSTMORPH\>][db35]*

    The [INITIAL][8e11] Morphism, takes any [`CAT-OBJ`][74bd] and
    creates a moprhism from [`SO0`][5c7c] (also known as void) to the object given.
    
    The formal grammar of [INITIAL][8e11] is
    
    ```lisp
    (init obj)
    ```
    
    where [`INIT`][8e11] is the constructor. [`OBJ`][f1e6] is the type of object
    that will be conjured up from [`SO0`][5c7c], when the morphism is
    applied onto an object.
    
    Example:
    
    ```lisp
    (init so1)
    ```
    
    In this example we are creating a unit value out of void.

<a id="x-28GEB-2ESPEC-3ATERMINAL-20CLASS-29"></a>
- [class] **TERMINAL** *[\<SUBSTMORPH\>][db35]*

    The [`TERMINAL`][874b] morphism, Takes any [`CAT-OBJ`][74bd] and creates a
    morphism from that object to [`SO1`][5cfe] (also known as unit).
    
    The formal grammar of [`TERMINAL`][874b] is
    
    ```lisp
    (terminal obj)
    ```
    
    where [`TERMINAL`][874b] is the constructor. [`OBJ`][f1e6] is the type of object that
    will be mapped to [`SO1`][5cfe], when the morphism is applied onto an
    object.
    
    Example:
    
    ```lisp
    (terminal (coprod so1 so1))
    
    (geb-gui::visualize (terminal (coprod so1 so1)))
    
    (comp value (terminal (codomain value)))
    
    (comp true (terminal bool))
    ```
    
    In the first example, we make a morphism from the corpoduct of
    [`SO1`][5cfe] and [`SO1`][5cfe] (essentially [`GEB-BOOL:BOOL`][0ad4]) to
    [`SO1`][5cfe].
    
    In the third example we can proclaim a constant function by ignoring
    the input value and returning a morphism from unit to the desired type.
    
    The fourth example is taking a [`GEB-BOOL:BOOL`][0ad4] and returning [`GEB-BOOL:TRUE`][f022].

<a id="x-28GEB-2ESPEC-3APAIR-20CLASS-29"></a>
- [class] **PAIR** *[\<SUBSTMORPH\>][db35]*

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
    
    Here this pair morphism takes the pair `SO1`([`0`][5cfe] [`1`][f4ba]) × [`GEB-BOOL:BOOL`][0ad4], and
    projects back the left field [`SO1`][5cfe] as the first value of the pair and
    projects back the `GEB-BOOL:BOOL` field as the second values.

<a id="x-28GEB-2ESPEC-3ADISTRIBUTE-20CLASS-29"></a>
- [class] **DISTRIBUTE** *[\<SUBSTMORPH\>][db35]*

    The distributive law

<a id="x-28GEB-2ESPEC-3AINJECT-LEFT-20CLASS-29"></a>
- [class] **INJECT-LEFT** *[\<SUBSTMORPH\>][db35]*

    The left injection morphism. Takes two [`CAT-OBJ`][74bd] values. It is
    the dual of [`INJECT-RIGHT`][e947]
    
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
    
    In the second example, we inject a term with the shape `SO1`([`0`][5cfe] [`1`][f4ba]) into a pair
    with the shape ([`SO1`][5cfe] × [`GEB-BOOL:BOOL`][0ad4]), then we use [`MCASE`][cd11] to denote a
    morphism saying. [`IF`][684b] the input is of the shape `SO1`([`0`][5cfe] [`1`][f4ba]), then give us True,
    otherwise flip the value of the boolean coming in.

<a id="x-28GEB-2ESPEC-3AINJECT-RIGHT-20CLASS-29"></a>
- [class] **INJECT-RIGHT** *[\<SUBSTMORPH\>][db35]*

    The right injection morphism. Takes two [`CAT-OBJ`][74bd] values. It is
    the dual of [`INJECT-LEFT`][8387]
    
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
    into a pair with the shape ([`SO1`][5cfe] × [`GEB-BOOL:BOOL`][0ad4]), then we use
    [`MCASE`][cd11] to denote a morphism saying. [`IF`][684b] the input is of the shape `SO1`([`0`][5cfe] [`1`][f4ba]),
    then give us True, otherwise flip the value of the boolean coming in.

<a id="x-28GEB-2ESPEC-3APROJECT-LEFT-20CLASS-29"></a>
- [class] **PROJECT-LEFT** *[\<SUBSTMORPH\>][db35]*

    The [`LEFT` PROJECTION][5ae3]. Takes two
    [`CAT-MORPH`][a7af] values. When the [`LEFT` PROJECTION][5ae3] morphism is then applied, it grabs the left value of a product,
    with the type of the product being determined by the two
    [`CAT-MORPH`][a7af] values given.
    
    the formal grammar of a [`PROJECT-LEFT`][5ae3] is:
    
    ```lisp
    (<-left mcar mcadr)
    ```
    
    Where [`<-LEFT`][2882] is the constructor, [`MCAR`][f1ce] is the left type of the
    [PRODUCT][7e58] and [`MCADR`][cc87] is the right type of the [PRODUCT][7e58].
    
    Example:
    
    ```lisp
    (geb-gui::visualize
      (<-left geb-bool:bool (prod so1 geb-bool:bool)))
    ```
    
    In this example, we are getting the left [`GEB-BOOL:BOOL`][0ad4] from a
    product with the shape
    
    ([`GEB-BOOL:BOOL`][0ad4] [×][06c6] [`SO1`][5cfe] [×][06c6] [`GEB-BOOL:BOOL`][0ad4])

<a id="x-28GEB-2ESPEC-3APROJECT-RIGHT-20CLASS-29"></a>
- [class] **PROJECT-RIGHT** *[\<SUBSTMORPH\>][db35]*

    The [`RIGHT` PROJECTION][06e0]. Takes two
    [`CAT-MORPH`][a7af] values. When the [`RIGHT` PROJECTION][06e0] morphism is then applied, it grabs the right value of a product,
    with the type of the product being determined by the two
    [`CAT-MORPH`][a7af] values given.
    
    the formal grammar of a [`PROJECT-RIGHT`][06e0] is:
    
    ```lisp
    (<-right mcar mcadr)
    ```
    
    Where [`<-RIGHT`][0dfe] is the constructor, [`MCAR`][f1ce] is the right type of the
    [PRODUCT][7e58] and [`MCADR`][cc87] is the right type of the [PRODUCT][7e58].
    
    Example:
    
    ```lisp
    (geb-gui::visualize
     (comp (<-right so1 geb-bool:bool)
           (<-right geb-bool:bool (prod so1 geb-bool:bool))))
    ```
    
    In this example, we are getting the right [`GEB-BOOL:BOOL`][0ad4] from a
    product with the shape
    
    ([`GEB-BOOL:BOOL`][0ad4] [×][06c6] [`SO1`][5cfe] [×][06c6] [`GEB-BOOL:BOOL`][0ad4])

<a id="x-28GEB-2ESPEC-3AFUNCTOR-20CLASS-29"></a>
- [class] **FUNCTOR** *[\<SUBSTMORPH\>][db35]*

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

<a id="x-28GEB-2ESPEC-3A-40GEB-REALIZED-20MGL-PAX-3ASECTION-29"></a>
#### 7.3.3 Realized Subst Objs

This section covers the [`REALIZED-OBJECT`][73be] type. This
represents a realized [`SUBSTOBJ`][3173] term.

The [`REALIZED-OBJECT`][73be] is not a real constructor but rather a sum
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
```


<a id="x-28GEB-2ESPEC-3AREALIZED-OBJECT-20TYPE-29"></a>
- [type] **REALIZED-OBJECT**

    A realized object that can be sent into.
    
    Lists represent [`PROD`][06c6] in the [`<SUBSTOBJ>`][fb79] category
    
    [`LEFT`][6444] and [`RIGHT`][c275] represents realized values for [`COPROD`][8be5]
    
    Lastly [`SO1`][5cfe] and [`SO0`][5c7c] represent the proper class

<a id="x-28GEB-2ESPEC-3ALEFT-20CLASS-29"></a>
- [class] **LEFT** *[DIRECT-POINTWISE-MIXIN][e2b0]*

<a id="x-28GEB-2ESPEC-3ARIGHT-20CLASS-29"></a>
- [class] **RIGHT** *[DIRECT-POINTWISE-MIXIN][e2b0]*

<a id="x-28GEB-2ESPEC-3ALEFT-20FUNCTION-29"></a>
- [function] **LEFT** *OBJ*

<a id="x-28GEB-2ESPEC-3ARIGHT-20FUNCTION-29"></a>
- [function] **RIGHT** *OBJ*

<a id="x-28GEB-2EUTILS-3A-40GEB-ACCESSORS-20MGL-PAX-3ASECTION-29"></a>
### 7.4 Accessors

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

<a id="x-28GEB-2EUTILS-3ACODE-20GENERIC-FUNCTION-29"></a>
- [generic-function] **CODE** *OBJ*

    the code of the
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-2ESPEC-3A-40GEB-CONSTRUCTORS-20MGL-PAX-3ASECTION-29"></a>
### 7.5 Constructors

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
### 7.6 API

Various forms and structures built on-top of [Core Category][cb9e]

<a id="x-28GEB-2EGENERICS-3AGAPPLY-20-28METHOD-20NIL-20-28GEB-2ESPEC-3A-3CSUBSTMORPH-3E-20T-29-29-29"></a>
- [method] **GAPPLY** *(MORPH \<SUBSTMORPH\>) OBJECT*

    My main documentation can be found on [`GAPPLY`][bb34]
    
    I am the [`GAPPLY`][bb34] for [<SBUSTMORPH>][7e58], the
    OBJECT that I expect is of type [`REALIZED-OBJECT`][73be]. See the
    documentation for [`REALIZED-OBJECT`][73be] for the forms it can take.
    
    Some examples of me are
    
    ```lisp
    GEB> (gapply (comp
                  (mcase geb-bool:true
                         geb-bool:not)
                  (->right so1 geb-bool:bool))
                 (left so1))
    (right s-1)
    GEB> (gapply (comp
                  (mcase geb-bool:true
                         geb-bool:not)
                  (->right so1 geb-bool:bool))
                 (right so1))
    (left s-1)
    GEB> (gapply geb-bool:and
                 (list (right so1)
                       (right so1)))
    (right s-1)
    GEB> (gapply geb-bool:and
                 (list (left so1)
                       (right so1)))
    (left s-1)
    GEB> (gapply geb-bool:and
                 (list (right so1)
                       (left so1)))
    (left s-1)
    GEB> (gapply geb-bool:and
                 (list (left so1)
                       (left so1)))
    (left s-1)
    ```


<a id="x-28GEB-2EGENERICS-3AGAPPLY-20-28METHOD-20NIL-20-28GEB-2EEXTENSION-2ESPEC-3AOPAQUE-MORPH-20T-29-29-29"></a>
- [method] **GAPPLY** *(MORPH OPAQUE-MORPH) OBJECT*

    My main documentation can be found on [`GAPPLY`][bb34]
    
    I am the [`GAPPLY`][bb34] for a generic [OPAQUE-MOPRH][7e58]
    I simply dispatch [`GAPPLY`][bb34] on my interior code
    `lisp
    GEB> (gapply (comp geb-list:*car* geb-list:*cons*)
                 (list (right geb-bool:true-obj) (left geb-list:*nil*)))
    (right GEB-BOOL:TRUE)
    `

<a id="x-28GEB-2EGENERICS-3AGAPPLY-20-28METHOD-20NIL-20-28GEB-2EEXTENSION-2ESPEC-3AOPAQUE-20T-29-29-29"></a>
- [method] **GAPPLY** *(MORPH OPAQUE) OBJECT*

    My main documentation can be found on [`GAPPLY`][bb34]
    
    I am the [`GAPPLY`][bb34] for a generic [`OPAQUE`][2fc2] I
    simply dispatch [`GAPPLY`][bb34] on my interior code, which
    is likely just an object

<a id="x-28GEB-BOOL-3A-40GEB-BOOL-20MGL-PAX-3ASECTION-29"></a>
#### 7.6.1 Booleans

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

<a id="x-28GEB-LIST-3A-40GEB-LIST-20MGL-PAX-3ASECTION-29"></a>
#### 7.6.2 Lists

###### \[in package GEB-LIST\]
Here we define out the idea of a List. It comes naturally from the
concept of coproducts. Since we lack polymorphism this list is
concrete over [`GEB-BOOL:@GEB-BOOL`][section] In ML syntax it looks like

```haskell
data List = Nil | Cons Bool List
```

We likewise define it with coproducts, with the recursive type being opaque

```lisp
(defparameter *nil* (so1))

(defparameter *cons-type* (reference 'cons))

(defparameter *canonical-cons-type*
  (opaque 'cons
          (prod geb-bool:bool *cons-type*)))

(defparameter *list*
  (coprod *nil* *cons-type*))
```

The functions given work on this.

<a id="x-28GEB-LIST-3A-2ANIL-2A-20VARIABLE-29"></a>
- [variable] **\*NIL\*** *NIL*

<a id="x-28GEB-LIST-3A-2ACONS-TYPE-2A-20VARIABLE-29"></a>
- [variable] **\*CONS-TYPE\*** *CONS*

<a id="x-28GEB-LIST-3A-2ALIST-2A-20VARIABLE-29"></a>
- [variable] **\*LIST\*** *LIST*

<a id="x-28GEB-LIST-3A-2ACAR-2A-20VARIABLE-29"></a>
- [variable] **\*CAR\*** *CAR*

<a id="x-28GEB-LIST-3A-2ACONS-2A-20VARIABLE-29"></a>
- [variable] **\*CONS\*** *CONS-Μ*

<a id="x-28GEB-LIST-3A-2ACDR-2A-20VARIABLE-29"></a>
- [variable] **\*CDR\*** *CDR*

<a id="x-28GEB-LIST-3ACONS--3ELIST-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **CONS-\>LIST**

<a id="x-28GEB-LIST-3ANIL--3ELIST-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **NIL-\>LIST**

<a id="x-28GEB-LIST-3A-2ACANONICAL-CONS-TYPE-2A-20VARIABLE-29"></a>
- [variable] **\*CANONICAL-CONS-TYPE\*** *CONS*

<a id="x-28GEB-2ETRANS-3A-40GEB-TRANSLATION-20MGL-PAX-3ASECTION-29"></a>
#### 7.6.3 Translation Functions

###### \[in package GEB.TRANS\]
These cover various conversions from [Subst Morph][d2d1] and [Subst Obj][c1b3]
into other categorical data structures.

<a id="x-28GEB-2EGENERICS-3ATO-POLY-20-28METHOD-20NIL-20-28GEB-2ESPEC-3A-3CSUBSTOBJ-3E-29-29-29"></a>
- [method] **TO-POLY** *(OBJ \<SUBSTOBJ\>)*

<a id="x-28GEB-2EGENERICS-3ATO-POLY-20-28METHOD-20NIL-20-28GEB-2ESPEC-3A-3CSUBSTMORPH-3E-29-29-29"></a>
- [method] **TO-POLY** *(OBJ \<SUBSTMORPH\>)*

<a id="x-28GEB-2EGENERICS-3ATO-CIRCUIT-20-28METHOD-20NIL-20-28GEB-2ESPEC-3A-3CSUBSTMORPH-3E-20T-29-29-29"></a>
- [method] **TO-CIRCUIT** *(OBJ \<SUBSTMORPH\>) NAME*

    Turns a [Subst Morph][d2d1] to a Vamp-IR Term

<a id="x-28GEB-2EGENERICS-3ATO-BITC-20-28METHOD-20NIL-20-28GEB-2ESPEC-3A-3CSUBSTMORPH-3E-29-29-29"></a>
- [method] **TO-BITC** *(OBJ \<SUBSTMORPH\>)*

<a id="x-28GEB-2EMAIN-3A-40GEB-UTILITY-20MGL-PAX-3ASECTION-29"></a>
#### 7.6.4 Utility

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
    
    Takes a morphism from [`SO1`][5cfe] to a desired value of type $B$,
    along with a [`<SUBSTOBJ>`][fb79] that represents the input type say of
    type $A$, giving us a morphism from $A$ to $B$.
    
    Thus if:
    `F` : [`SO1`][5cfe] → a,
    `X` : b
    
    then: (const f x) : a → b
    
    ```
    Γ, f : so1 → b, x : a
    ----------------------
    (const f x) : a → b
    ```
    
    Further, If the input `F` has an [`ALIAS`][315f], then we wrap the output
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
    be a [`PROD`][06c6]
    
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
    
    The [cat-morph][a7af] given must have its [`DOM`][9728] be of a [`PROD`][06c6] type, as [`CURRY`][2cbc]
    invokes the idea of
    
    if f : ([`PROD`][06c6] a b) → c
    
    for all `a`, `b`, and `c` being an element of [cat-morph][a7af]
    
    then: (curry f): a → c^b
    
    where c^b means c to the exponent of b ([`EXPT`][9bcb2] c b)
    
    ```
    Γ, f : a × b → c,
    --------------------
    (curry f) : a → c^b
    ```
    
    In category terms, `a → c^b` is isomorphic to `a → b → c`


<a id="x-28GEB-2EMAIN-3ACOPROD-MOR-20FUNCTION-29"></a>
- [function] **COPROD-MOR** *F G*

    Given f : A  → B and g : C  → D gives appropriate morphism between
    [`COPROD`][8be5] objects f x g : A + B  → C + D via the unversal property.
    That is, the morphism part of the coproduct functor Geb x Geb → Geb

<a id="x-28GEB-2EMAIN-3APROD-MOR-20FUNCTION-29"></a>
- [function] **PROD-MOR** *F G*

    Given f : A  → B and g : C  → D gives appropriate morphism between
    [`PROD`][06c6] objects f x g : A x B  → C x D via the unversal property.
    This is the morphism part of the product functor Geb x Geb → Geb

<a id="x-28GEB-2EMAIN-3AUNCURRY-20FUNCTION-29"></a>
- [function] **UNCURRY** *Y Z F*

    Given a morphism f : x → z^y and explicitly given y and z variables
    produces an uncurried version f' : x × y → z of said morphism

<a id="x-28GEB-2EMAIN-3ATEXT-NAME-20GENERIC-FUNCTION-29"></a>
- [generic-function] **TEXT-NAME** *MORPH*

    Gets the name of the moprhism

These utilities are ontop of [`CAT-OBJ`][74bd]

<a id="x-28GEB-2EGENERICS-3AMAYBE-20-28METHOD-20NIL-20-28GEB-2ESPEC-3A-3CSUBSTOBJ-3E-29-29-29"></a>
- [method] **MAYBE** *(OBJ \<SUBSTOBJ\>)*

    I recursively add maybe terms to all [<SBUSTOBJ>][7e58] terms,
    for what maybe means checkout [my generic function documentation][65a4].
    
    turning [products][06c6] of A x B into Maybe (Maybe A x Maybe B),
    
    turning [coproducts][8be5] of A | B into Maybe (Maybe A | Maybe B),
    
    turning `SO1`([`0`][5cfe] [`1`][f4ba]) into Maybe `SO1`([`0`][5cfe] [`1`][f4ba])
    
    and `SO0`([`0`][5c7c] [`1`][7088]) into Maybe `SO0`([`0`][5c7c] [`1`][7088])

<a id="x-28GEB-3A-40GEB-EXAMPLES-20MGL-PAX-3ASECTION-29"></a>
### 7.7 Examples

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


<a id="x-28GEB-2EEXTENSION-2ESPEC-3A-40GEB-EXTENSIONS-20MGL-PAX-3ASECTION-29"></a>
## 8 Extension Sets for Categories

###### \[in package GEB.EXTENSION.SPEC\]
This package contains many extensions one may see over the codebase.

Each extension adds an unique feature to the categories they are
extending. To learn more, read about the individual extension you are
interested in.

Common Sub expressions represent repeat logic that can be found
throughout any piece of code

<a id="x-28GEB-2EEXTENSION-2ESPEC-3ACOMMON-SUB-EXPRESSION-20CLASS-29"></a>
- [class] **COMMON-SUB-EXPRESSION** *[DIRECT-POINTWISE-MIXIN][e2b0] [META-MIXIN][4529] [CAT-MORPH][a7af]*

    I represent common sub-expressions found throughout the code.
    
    I implement a few categorical extensions. I am a valid
    [`CAT-MORPH`][a7af] along with fulling the interface for the
    GEB.POLY.SPEC:<POLY>([`0`][7058] [`1`][78ef]) category.
    
    The name should come from an algorithm that automatically fines common
    sub-expressions and places the appropriate names.

<a id="x-28GEB-2EEXTENSION-2ESPEC-3AMAKE-COMMON-SUB-EXPRESSION-20FUNCTION-29"></a>
- [function] **MAKE-COMMON-SUB-EXPRESSION** *&KEY OBJ NAME*

The Opaque extension lets users write categorical objects and
morphisms where their implementation hide the specifics of what
types they are operating over

<a id="x-28GEB-2EEXTENSION-2ESPEC-3AOPAQUE-20CLASS-29"></a>
- [class] **OPAQUE** *[CAT-OBJ][74bd] [META-MIXIN][4529]*

    I represent an object where we want to hide the implementation
    details of what kind of [`GEB:SUBSTOBJ`][3173] I am.

<a id="x-28GEB-2EEXTENSION-2ESPEC-3AREFERENCE-20CLASS-29"></a>
- [class] **REFERENCE** *[CAT-OBJ][74bd] [CAT-MORPH][a7af] [DIRECT-POINTWISE-MIXIN][e2b0] [META-MIXIN][4529]*

    I represent a reference to an [`OPAQUE`][2fc2] identifier.

<a id="x-28GEB-2EEXTENSION-2ESPEC-3AOPAQUE-MORPH-20CLASS-29"></a>
- [class] **OPAQUE-MORPH** *[CAT-MORPH][a7af] [META-MIXIN][4529]*

    This represents a morphsim where we want to deal with an
    [`OPAQUE`][2fc2] that we know intimate details of

<a id="x-28GEB-2EUTILS-3ACODE-20-28METHOD-20NIL-20-28GEB-2EEXTENSION-2ESPEC-3AOPAQUE-MORPH-29-29-29"></a>
- [method] **CODE** *(OPAQUE-MORPH OPAQUE-MORPH)*

    the code that represents the underlying morphsism

<a id="x-28GEB-2EMIXINS-3ADOM-20-28METHOD-20NIL-20-28GEB-2EEXTENSION-2ESPEC-3AOPAQUE-MORPH-29-29-29"></a>
- [method] **DOM** *(OPAQUE-MORPH OPAQUE-MORPH)*

    The dom of the opaque morph

<a id="x-28GEB-2EMIXINS-3ACODOM-20-28METHOD-20NIL-20-28GEB-2EEXTENSION-2ESPEC-3AOPAQUE-MORPH-29-29-29"></a>
- [method] **CODOM** *(OPAQUE-MORPH OPAQUE-MORPH)*

    The codom of the opaque morph

<a id="x-28GEB-2EUTILS-3ACODE-20-28METHOD-20NIL-20-28GEB-2EEXTENSION-2ESPEC-3AOPAQUE-29-29-29"></a>
- [method] **CODE** *(OPAQUE OPAQUE)*

<a id="x-28GEB-2EUTILS-3ANAME-20-28METHOD-20NIL-20-28GEB-2EEXTENSION-2ESPEC-3AOPAQUE-29-29-29"></a>
- [method] **NAME** *(OPAQUE OPAQUE)*

<a id="x-28GEB-2EUTILS-3ANAME-20-28METHOD-20NIL-20-28GEB-2EEXTENSION-2ESPEC-3AREFERENCE-29-29-29"></a>
- [method] **NAME** *(REFERENCE REFERENCE)*

<a id="x-28GEB-2EEXTENSION-2ESPEC-3AREFERENCE-20FUNCTION-29"></a>
- [function] **REFERENCE** *NAME*

<a id="x-28GEB-2EEXTENSION-2ESPEC-3AOPAQUE-MORPH-20FUNCTION-29"></a>
- [function] **OPAQUE-MORPH** *CODE &KEY (DOM (DOM CODE)) (CODOM (CODOM CODE))*

<a id="x-28GEB-2EEXTENSION-2ESPEC-3AOPAQUE-20FUNCTION-29"></a>
- [function] **OPAQUE** *NAME CODE*

<a id="x-28GEB-GUI-3A-40GEB-GUI-MANUAL-20MGL-PAX-3ASECTION-29"></a>
## 9 The GEB GUI

###### \[in package GEB-GUI\]
This section covers the suite of tools that help visualize geb
objects and make the system nice to work with

<a id="x-28GEB-GUI-3A-40GEB-VISUALIZER-20MGL-PAX-3ASECTION-29"></a>
### 9.1 Visualizer

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
#### 9.1.1 Aiding the Visualizer

One can aid the visualization process a bit, this can be done by
simply placing ALIAS around the object, this will place it
in a box with a name to better identify it in the graphing procedure.

<a id="x-28GEB-GUI-2EGRAPHING-3A-40GRAPHING-MANUAL-20MGL-PAX-3ASECTION-29"></a>
### 9.2 The GEB Graphizer

###### \[in package GEB-GUI.GRAPHING\]
This section covers the GEB Graph representation

<a id="x-28GEB-GUI-2ECORE-3A-40GRAPHING-CORE-20MGL-PAX-3ASECTION-29"></a>
#### 9.2.1 The GEB Graphizer Core

###### \[in package GEB-GUI.CORE\]
This section covers the graphing procedure in order to turn a GEB
object into a format for a graphing backend.

The core types that facilittate the functionality

<a id="x-28GEB-GUI-2ECORE-3ANOTE-20TYPE-29"></a>
- [type] **NOTE**

    A note is a note about a new node in the graph or a note about a
    [`NODE`][ff98] which should be merged into an upcoming `NODE`.
    
    An example of a [`NODE-NOTE`][c3e8] would be in the case of pair
    
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

<a id="x-28GEB-GUI-2ECORE-3ANODE-NOTE-20CLASS-29"></a>
- [class] **NODE-NOTE**

<a id="x-28GEB-GUI-2ECORE-3ASQUASH-NOTE-20CLASS-29"></a>
- [class] **SQUASH-NOTE**

    This note should be squashed into another note and or node.

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
#### 9.2.2 The GEB Graphizer Passes

###### \[in package GEB-GUI.GRAPHING.PASSES\]
This changes how the graph is visualized, simplifying the graph in
ways that are intuitive to the user

<a id="x-28GEB-GUI-2EGRAPHING-2EPASSES-3APASSES-20FUNCTION-29"></a>
- [function] **PASSES** *NODE*

    Runs all the passes that simplify viewing the graph.
    These simplifications should not change the semantics of the graph,
    only display it in a more bearable way

<a id="x-28GEB-2EBITC-3A-40BITC-MANUAL-20MGL-PAX-3ASECTION-29"></a>
## 10 Bits (Boolean Circuit) Specification

###### \[in package GEB.BITC\]
This covers a GEB view of Boolean Circuits. In particular this type will
be used in translating GEB's view of Boolean Circuits into Vampir

<a id="x-28GEB-2EBITC-2ESPEC-3A-40BITC-20MGL-PAX-3ASECTION-29"></a>
### 10.1 Bits Types

###### \[in package GEB.BITC.SPEC\]
This section covers the types of things one can find in the `BIT`s([`0`][6a3c] [`1`][2410])
constructors

<a id="x-28GEB-2EBITC-2ESPEC-3ABITC-20TYPE-29"></a>
- [type] **BITC**

<a id="x-28GEB-2EBITC-2ESPEC-3A-3CBITC-3E-20CLASS-29"></a>
- [class] **\<BITC\>** *[DIRECT-POINTWISE-MIXIN][e2b0] [CAT-MORPH][a7af]*

<a id="x-28GEB-2EBITC-2ESPEC-3ACOMPOSE-20CLASS-29"></a>
- [class] **COMPOSE** *[\<BITC\>][26d4]*

    composes the [`MCAR`][f1ce] and the [`MCADR`][cc87]

<a id="x-28GEB-2EBITC-2ESPEC-3AFORK-20CLASS-29"></a>
- [class] **FORK** *[\<BITC\>][26d4]*

    Copies the [`MCAR`][f1ce] of length n onto length 2\*n by copying its
    inputs (`MCAR`).

<a id="x-28GEB-2EBITC-2ESPEC-3APARALLEL-20CLASS-29"></a>
- [class] **PARALLEL** *[\<BITC\>][26d4]*

    ```lisp
    (parallel x y)
    ```
    
    constructs a [`PARALLEL`][46bc] term where the [`MCAR`][f1ce] is `x` and the
    [`MCADR`][cc87] is `y`,
    
    where if
    
    ```
    x : a → b,          y : c → d
    -------------------------------
    (parallel x y) : a + c → b + d
    ```
    
    then the [`PARALLEL`][46bc] will return a function from a and c to b
    and d where the [`MCAR`][f1ce] and [`MCADR`][cc87] run on subvectors of the input.

<a id="x-28GEB-2EBITC-2ESPEC-3ASWAP-20CLASS-29"></a>
- [class] **SWAP** *[\<BITC\>][26d4]*

    ```lisp
    (swap n m)
    ```
    
    binds the [`MCAR`][f1ce] to n and [`MCADR`][cc87] to m, where if the input
    vector is of length `n + m`, then it swaps the bits, algebraically we
    view it as
    
    ```lisp
    (swap n m) : #*b₁...bₙbₙ₊₁...bₙ₊ₘ → #*bₙ₊₁...bₘ₊ₙb₁...bₙ
    ```


<a id="x-28GEB-2EBITC-2ESPEC-3AONE-20CLASS-29"></a>
- [class] **ONE** *[\<BITC\>][26d4]*

    [`ONE`][cf10] represents the map from 0 onto 1 producing a vector
    with only 1 in it.

<a id="x-28GEB-2EBITC-2ESPEC-3AZERO-20CLASS-29"></a>
- [class] **ZERO** *[\<BITC\>][26d4]*

    [`ZERO`][fa6c] map from 0 onto 1 producing a vector with only 0 in
    it.

<a id="x-28GEB-2EBITC-2ESPEC-3AIDENT-20CLASS-29"></a>
- [class] **IDENT** *[\<BITC\>][26d4]*

    [`IDENT`][c417] represents the identity

<a id="x-28GEB-2EBITC-2ESPEC-3ADROP-20CLASS-29"></a>
- [class] **DROP** *[\<BITC\>][26d4]*

    [`DROP`][f130] represents the unique morphism from n to 0.

<a id="x-28GEB-2EBITC-2ESPEC-3ABRANCH-20CLASS-29"></a>
- [class] **BRANCH** *[\<BITC\>][26d4]*

    ```lisp
    (branch x y)
    ```
    
    constructs a [`BRANCH`][414c] term where the [`MCAR`][f1ce] is `x` and the
    [`MCADR`][cc87] is `y`,
    
    where if
    
    ```
    x : a → b,          y : a → b
    -------------------------------
    (branch x y) : 1+a → b
    ```
    
    then the [`BRANCH`][1774] will return a function on the type `1 + a`, where the
    1 represents a bit to branch on. If the first bit is `0`, then the
    [`MCAR`][f1ce] is ran, however if the bit is `1`, then the [`MCADR`][cc87] is ran.

<a id="x-28GEB-2EBITC-2ESPEC-3A-40BITC-CONSTRUCTORS-20MGL-PAX-3ASECTION-29"></a>
### 10.2 Bits (Boolean Circuit) Constructors

###### \[in package GEB.BITC.SPEC\]
Every accessor for each of the [`CLASS`][7e58]'s found here are from [Accessors][cc51]

<a id="x-28GEB-2EBITC-2ESPEC-3ACOMPOSE-20FUNCTION-29"></a>
- [function] **COMPOSE** *MCAR MCADR &REST ARGS*

    Creates a multiway constructor for [`COMPOSE`][ecb2]

<a id="x-28GEB-2EBITC-2ESPEC-3AFORK-20FUNCTION-29"></a>
- [function] **FORK** *MCAR*

    `FORK` ARG1

<a id="x-28GEB-2EBITC-2ESPEC-3APARALLEL-20FUNCTION-29"></a>
- [function] **PARALLEL** *MCAR MCADR &REST ARGS*

    Creates a multiway constructor for [`PARALLEL`][46bc]

<a id="x-28GEB-2EBITC-2ESPEC-3ASWAP-20FUNCTION-29"></a>
- [function] **SWAP** *MCAR MCADR*

    swap ARG1 and ARG2

<a id="x-28GEB-2EBITC-2ESPEC-3AONE-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **ONE**

<a id="x-28GEB-2EBITC-2ESPEC-3AZERO-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **ZERO**

<a id="x-28GEB-2EBITC-2ESPEC-3AIDENT-20FUNCTION-29"></a>
- [function] **IDENT** *MCAR*

    ident ARG1

<a id="x-28GEB-2EBITC-2ESPEC-3ADROP-20FUNCTION-29"></a>
- [function] **DROP** *MCAR*

    drop ARG1

<a id="x-28GEB-2EBITC-2ESPEC-3ABRANCH-20FUNCTION-29"></a>
- [function] **BRANCH** *MCAR MCADR*

    branch with ARG1 or ARG2

<a id="x-28GEB-2EBITC-2EMAIN-3A-40BITC-API-20MGL-PAX-3ASECTION-29"></a>
### 10.3 Bits (Boolean Circuit) API

###### \[in package GEB.BITC.MAIN\]
This covers the Bits (Boolean Circuit) API

<a id="x-28GEB-2EGENERICS-3AGAPPLY-20-28METHOD-20NIL-20-28GEB-2EBITC-2ESPEC-3A-3CBITC-3E-20BIT-VECTOR-29-29-29"></a>
- [method] **GAPPLY** *(MORPHISM \<BITC\>) (OBJECT BIT-VECTOR)*

    My My main documentation can be found on [`GAPPLY`][bb34]
    
    I am the [`GAPPLY`][bb34] for [`<BITC>`][26d4], the
    `OBJECT` that I expect is of type [`NUMBER`][7dbb]. [`GAPPLY`][bb34]
    reduces down to ordinary common lisp expressions rather straight
    forwardly
    
    ```lisp
    ;; figure out the number of bits the function takes
    GEB-TEST> (dom (to-bitc geb-bool:and))
    2 (2 bits, #x2, #o2, #b10)
    GEB-TEST> (gapply (to-bitc geb-bool:and) #*11)
    #*1
    GEB-TEST> (gapply (to-bitc geb-bool:and) #*10)
    #*0
    GEB-TEST> (gapply (to-bitc geb-bool:and) #*01)
    #*0
    GEB-TEST> (gapply (to-bitc geb-bool:and) #*00)
    #*0
    ```


<a id="x-28GEB-2EGENERICS-3AGAPPLY-20-28METHOD-20NIL-20-28GEB-2EBITC-2ESPEC-3A-3CBITC-3E-20LIST-29-29-29"></a>
- [method] **GAPPLY** *(MORPHISM \<BITC\>) (OBJECT LIST)*

    I am a helper gapply function, where the second argument for
    [`<BITC>`][26d4] is a list. See the docs for the [`BIT-VECTOR`][46ed] version for
    the proper one. We do allow sending in a list like so
    
    ```lisp
    ;; figure out the number of bits the function takes
    GEB-TEST> (dom (to-bitc geb-bool:and))
    2 (2 bits, #x2, #o2, #b10)
    GEB-TEST> (gapply (to-bitc geb-bool:and) (list 1 1))
    #*1
    GEB-TEST> (gapply (to-bitc geb-bool:and) (list 1 0))
    #*0
    GEB-TEST> (gapply (to-bitc geb-bool:and) (list 0 1))
    #*0
    GEB-TEST> (gapply (to-bitc geb-bool:and) (list 0 0))
    #*0
    ```


<a id="x-28GEB-2EMIXINS-3ADOM-20-28METHOD-20NIL-20-28GEB-2EBITC-2ESPEC-3A-3CBITC-3E-29-29-29"></a>
- [method] **DOM** *(X \<BITC\>)*

    Gives the length of the bit vector the [`<BITC>`][26d4] moprhism takes

<a id="x-28GEB-2EMIXINS-3ACODOM-20-28METHOD-20NIL-20-28GEB-2EBITC-2ESPEC-3A-3CBITC-3E-29-29-29"></a>
- [method] **CODOM** *(X \<BITC\>)*

    Gives the length of the bit vector the [`<BITC>`][26d4] morphism returns

<a id="x-28GEB-2EBITC-2ETRANS-3A-40BITC-TRANS-20MGL-PAX-3ASECTION-29"></a>
### 10.4 Bits (Boolean Circuit) Transformations

###### \[in package GEB.BITC.TRANS\]
This covers transformation functions from

<a id="x-28GEB-2EGENERICS-3ATO-CIRCUIT-20-28METHOD-20NIL-20-28GEB-2EBITC-2ESPEC-3A-3CBITC-3E-20T-29-29-29"></a>
- [method] **TO-CIRCUIT** *(MORPHISM \<BITC\>) NAME*

    Turns a [`BITC`][e017] term into a Vamp-IR Gate with the given name

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EBITC-2ESPEC-3ACOMPOSE-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ COMPOSE) VALUES CONSTRAINTS*

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EBITC-2ESPEC-3AFORK-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ FORK) VALUES CONSTRAINTS*

    Copy input n intput bits into 2\*n output bits

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EBITC-2ESPEC-3APARALLEL-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ PARALLEL) VALUES CONSTRAINTS*

    Take n + m bits, execute car the n bits and cadr on the m bits and
    concat the results from car and cadr

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EBITC-2ESPEC-3ASWAP-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ SWAP) VALUES CONSTRAINTS*

    Turn n + m bits into m + n bits by swapping

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EBITC-2ESPEC-3AONE-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ ONE) VALUES CONSTRAINTS*

    Produce a bitvector of length 1 containing 1

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EBITC-2ESPEC-3AZERO-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ ZERO) VALUES CONSTRAINTS*

    Produce a bitvector of length 1 containing 0

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EBITC-2ESPEC-3AIDENT-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ IDENT) VALUES CONSTRAINTS*

    turn n bits into n bits by doing nothing

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EBITC-2ESPEC-3ADROP-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ DROP) VALUES CONSTRAINTS*

    turn n bits into an empty bitvector

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EBITC-2ESPEC-3ABRANCH-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ BRANCH) VALUES CONSTRAINTS*

    Look at the first bit.
    
    If its 0, run f on the remaining bits.
    
    If its 1, run g on the remaining bits.

<a id="x-28GEB-2EPOLY-3A-40POLY-MANUAL-20MGL-PAX-3ASECTION-29"></a>
## 11 Polynomial Specification

###### \[in package GEB.POLY\]
This covers a GEB view of Polynomials. In particular this type will
be used in translating GEB's view of Polynomials into Vampir

<a id="x-28GEB-2EPOLY-2ESPEC-3A-40POLY-20MGL-PAX-3ASECTION-29"></a>
### 11.1 Polynomial Types

###### \[in package GEB.POLY.SPEC\]
This section covers the types of things one can find in the [`POLY`][8bf3]
constructors

<a id="x-28GEB-2EPOLY-2ESPEC-3APOLY-20TYPE-29"></a>
- [type] **POLY**

<a id="x-28GEB-2EPOLY-2ESPEC-3A-3CPOLY-3E-20CLASS-29"></a>
- [class] **\<POLY\>** *[GEB.MIXINS:DIRECT-POINTWISE-MIXIN][e2b0]*

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

<a id="x-28GEB-2EPOLY-2EMAIN-3A-40POLY-API-20MGL-PAX-3ASECTION-29"></a>
### 11.2 Polynomial API

###### \[in package GEB.POLY.MAIN\]
This covers the polynomial API

<a id="x-28GEB-2EGENERICS-3AGAPPLY-20-28METHOD-20NIL-20-28GEB-2EPOLY-2ESPEC-3A-3CPOLY-3E-20T-29-29-29"></a>
- [method] **GAPPLY** *(MORPHISM \<POLY\>) OBJECT*

    My main documentation can be found on [`GAPPLY`][bb34]
    
    I am the [`GAPPLY`][bb34] for [`POLY:<POLY>`][b4a6], the
    `OBJECT` that I expect is of type [`NUMBER`][7dbb]. [`GAPPLY`][bb34] reduces down to
    ordinary common lisp expressions rather straight forwardly
    
    Some examples of me are
    
    ```lisp
    (in-package :geb.poly)
    
    POLY> (gapply (if-zero (- ident ident 1) 10 ident) 5)
    5 (3 bits, #x5, #o5, #b101)
    
    POLY> (gapply (if-zero (- ident ident) 10 ident) 5)
    10 (4 bits, #xA, #o12, #b1010)
    
    POLY> (gapply (- (* 2 ident ident) (* ident ident)) 5)
    25 (5 bits, #x19, #o31, #b11001)
    ```


<a id="x-28GEB-2EGENERICS-3AGAPPLY-20-28METHOD-20NIL-20-28INTEGER-20T-29-29-29"></a>
- [method] **GAPPLY** *(MORPHISM INTEGER) OBJECT*

    My main documentation can be found on [`GAPPLY`][bb34]
    
    I am the [`GAPPLY`][bb34] for [`INTEGER`][ac8a]s, the
    `OBJECT` that I expect is of type [`NUMBER`][7dbb]. I simply return myself.
    
    Some examples of me are
    
    ```lisp
    (in-package :geb.poly)
    
    POLY> (gapply 10 5)
    10 (4 bits, #xA, #o12, #b1010)
    ```


<a id="x-28GEB-2EPOLY-2ESPEC-3A-40POLY-CONSTRUCTORS-20MGL-PAX-3ASECTION-29"></a>
### 11.3 Polynomial Constructors

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

    checks if [`PREDICATE`][8da6] is zero then take the [`THEN`][bfa9] branch otherwise
    the [`ELSE`][365a] branch

<a id="x-28GEB-2EPOLY-2ESPEC-3AIF-LT-20FUNCTION-29"></a>
- [function] **IF-LT** *MCAR MCADR THEN ELSE*

    Checks if the [`MCAR`][f1ce] is less than the [`MCADR`][cc87] and chooses the appropriate branch

<a id="x-28GEB-2EPOLY-2ETRANS-3A-40POLY-TRANS-20MGL-PAX-3ASECTION-29"></a>
### 11.4 Polynomial Transformations

###### \[in package GEB.POLY.TRANS\]
This covers transformation functions from

<a id="x-28GEB-2EGENERICS-3ATO-CIRCUIT-20-28METHOD-20NIL-20-28GEB-2EPOLY-2ESPEC-3A-3CPOLY-3E-20T-29-29-29"></a>
- [method] **TO-CIRCUIT** *(MORPHISM \<POLY\>) NAME*

    Turns a [`POLY`][8bf3] term into a Vamp-IR Gate with the given name

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28INTEGER-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ INTEGER) VALUE LET-VARS*

    Numbers act like a constant function, ignoring input

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EPOLY-2ESPEC-3AIDENT-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ IDENT) VALUE LET-VARS*

    Identity acts as the identity function

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EPOLY-2ESPEC-3A-2B-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ +) VALUE LET-VARS*

    Propagates the value and adds them

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EPOLY-2ESPEC-3A-2A-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ \*) VALUE LET-VARS*

    Propagates the value and times them

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EPOLY-2ESPEC-3A--20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ -) VALUE LET-VARS*

    Propagates the value and subtracts them

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EPOLY-2ESPEC-3A-2F-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ /) VALUE LET-VARS*

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EPOLY-2ESPEC-3ACOMPOSE-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ COMPOSE) VALUE LET-VARS*

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EPOLY-2ESPEC-3AIF-ZERO-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ IF-ZERO) VALUE LET-VARS*

    The [`PREDICATE`][8da6] that comes in must be 1 or 0 for the formula to work out.

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EPOLY-2ESPEC-3AIF-LT-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ IF-LT) VALUE LET-VARS*

<a id="x-28GEB-2EGENERICS-3ATO-VAMPIR-20-28METHOD-20NIL-20-28GEB-2EPOLY-2ESPEC-3AMOD-20T-20T-29-29-29"></a>
- [method] **TO-VAMPIR** *(OBJ MOD) VALUE LET-VARS*

<a id="x-28GEB-2ELAMBDA-3A-40STLC-20MGL-PAX-3ASECTION-29"></a>
## 12 The Simply Typed Lambda Calculus model

###### \[in package GEB.LAMBDA\]
This covers GEB's view on simply typed lambda calculus

This serves as a useful frontend for those wishing to write a compiler
to GEB and do not wish to target the categorical model.

If one is targeting their compiler to the frontend, then the following
code should be useful for you.

```lisp
(in-package :geb.lambda.main)

MAIN>
(to-circuit
 (lamb (list (coprod so1 so1))
              (index 0))
 :id)
(def id x1 = {
   (x1)
 };)

MAIN>
(to-circuit
 (lamb (list (coprod so1 so1))
              (case-on (index 0)
                              (lamb (list so1)
                                           (right so1 (unit)))
                              (lamb (list so1)
                                           (left so1 (unit)))))
 :not)
(def not x1 = {
   (((1 - x1) * 1) + (x1 * 0), ((1 - x1) * 1) + (x1 * 0))
 };)

MAIN> (to-circuit (lamb (list geb-bool:bool)
                        (left so1 (right so1 (index 0)))) :foo)
(def foo x1 = {
   (0, 1, x1)
 };)
```

For testing purposes, it may be useful to go to the `BITC` backend and
run our interpreter

```lisp
MAIN>
(gapply (to-bitc
         (lamb (list (coprod so1 so1))
               (case-on (index 0)
                        (lamb (list so1)
                              (right so1 (unit)))
                        (lamb (list so1)
                              (left so1 (unit))))))
        #*1)
#*00
MAIN>
(gapply (to-bitc
         (lamb (list (coprod so1 so1))
               (case-on (index 0)
                        (lamb (list so1)
                              (right so1 (unit)))
                        (lamb (list so1)
                              (left so1 (unit))))))
        #*0)
#*11
```


<a id="x-28GEB-2ELAMBDA-2ESPEC-3A-40LAMBDA-SPECS-20MGL-PAX-3ASECTION-29"></a>
### 12.1 Lambda Specification

###### \[in package GEB.LAMBDA.SPEC\]
This covers the various the abstract data type that is the simply
typed lambda calculus within GEB. The class presents untyped [`STLC`][e373] terms.

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ASTLC-20TYPE-29"></a>
- [type] **STLC**

    Type of untyped terms of [`STLC`][e373]. Each class of a term has a slot for a type,
    which can be filled by auxillary functions or by user. Types are
    represented as [SUBSTOBJ][3173].

<a id="x-28GEB-2ELAMBDA-2ESPEC-3A-3CSTLC-3E-20CLASS-29"></a>
- [class] **\<STLC\>** *[DIRECT-POINTWISE-MIXIN][e2b0] [META-MIXIN][4529] [CAT-OBJ][74bd]*

    Class of untyped terms of simply typed lambda claculus. Given our
    presentation, we look at the latter as a type theory spanned by empty,
    unit types as well as coproduct, product, and function types.

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AABSURD-20CLASS-29"></a>
- [class] **ABSURD** *[\<STLC\>][b36a]*

    The [`ABSURD`][4710] term provides an element of an arbitrary type
    given a term of the empty type, denoted by [SO0][5c7c].
    The formal grammar of [`ABSURD`][4710] is
    
    ```lisp
    (absurd tcod term)
    ```
    
    where we possibly can include type information by
    
    ```lisp
    (absurd tcod term :ttype ttype)
    ```
    
    The intended semantics are: [`TCOD`][70c0] is a type whose term we want to
    get (and hence a [SUBSTOBJ][3173]) and [`TERM`][0171] is a term
    of the empty type (and hence an [`STLC`][e373].
    
    This corresponds to the elimination rule of the empty type. Namely,
    given
    $$\Gamma \vdash \text{tcod : Type}$$ and
    $$\Gamma \vdash \text{term : so0}$$ one deduces
    $$\Gamma \vdash \text{(absurd tcod term) : tcod}$$

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AUNIT-20CLASS-29"></a>
- [class] **UNIT** *[\<STLC\>][b36a]*

    The unique term of the unit type, the latter represented by
    [SO1][5cfe]. The formal grammar of [`UNIT`][0433] is
    
    ```lisp
    (unit)
    ```
    
    where we can optionally include type information by
    
    ```lisp
    (unit :ttype ttype)
    ```
    
    Clearly the type of [`UNIT`][0433] is [SO1][5cfe] but here
    we provide all terms untyped.
    
    This grammar corresponds to the introduction rule of the unit type. Namely
    $$\Gamma \dashv \text{(unit) : so1}$$

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ALEFT-20CLASS-29"></a>
- [class] **LEFT** *[\<STLC\>][b36a]*

    Term of a coproduct type gotten by injecting into the left type of the coproduct. The formal grammar of
    [`LEFT`][56b3] is
    
    ```lisp
    (left rty term)
    ```
    
    where we can include optional type information by
    
    ```lisp
    (left rty term :ttype ttype)
    ```
    
    The indended semantics are as follows: [`RTY`][abea] should
    be a type (and hence a [SUBSTOBJ][3173]) and specify the
    right part of the coproduct of the type [`TTYPE`][134c] of
    the entire term. The term (and hence an [`STLC`][e373]) we are injecting
    is [`TERM`][0171].
    
    This corresponds to the introduction rule of the coproduct type. Namely, given
    $$\Gamma \dashv \text{(ttype term) : Type}$$ and
    $$\Gamma \dashv \text{rty : Type}$$
    with
    $$\Gamma \dashv \text{term : (ttype term)}$$ we deduce
    $$\Gamma \dashv \text{(left rty term) : (coprod (ttype term) rty)}$$

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ARIGHT-20CLASS-29"></a>
- [class] **RIGHT** *[\<STLC\>][b36a]*

    Term of a coproduct type gotten by injecting into the right type of
    the coproduct. The formal grammar of [`RIGHT`][48fc] is
    
    ```lisp
    (right lty term)
    ```
    
    where we can include optional type information by
    
    ```lisp
    (right lty term :ttype ttype)
    ```
    
    The indended semantics are as follows: [`LTY`][15a3] should be a type (and
    hence a [SUBSTOBJ][3173]) and specify the left part of
    the coproduct of the type [`TTYPE`][134c] of the entire term. The term (and
    hence an [`STLC`][e373]) we are injecting is [`TERM`][0171].
    
    This corresponds to the introduction rule of the coproduct type. Namely, given
    $$\Gamma \dashv \text{(ttype term) : Type}$$ and
    $$\Gamma \dashv \text{lty : Type}$$
    with
    $$\Gamma \dashv \text{term : (ttype term)}$$ we deduce
    $$\Gamma \dashv \text{(right lty term) : (coprod lty (ttype term))}$$

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ACASE-ON-20CLASS-29"></a>
- [class] **CASE-ON** *[\<STLC\>][b36a]*

    A term of an arbutrary type provided by casing on a coproduct term. The
    formal grammar of [`CASE-ON`][3f9d] is
    
    ```lisp
    (case-on on ltm rtm)
    ```
    
    where we can possibly include type information by
    
    ```lisp
    (case-on on ltm rtm :ttype ttype)
    ```
    
    The intended semantics are as follows: [`ON`][7c57] is a term (and hence an
    [`STLC`][e373]) of a coproduct type, and [`LTM`][fcda] and [`RTM`][d762] terms (hence
    also [`STLC`][e373]) of the same type in the context of - appropriately
    - (mcar (ttype on)) and (mcadr (ttype on)).
    
    This corresponds to the elimination rule of the coprodut type. Namely, given
    $$\Gamma \vdash \text{on : (coprod (mcar (ttype on)) (mcadr (ttype on)))}$$
    and
    $$\text{(mcar (ttype on))} , \Gamma \vdash \text{ltm : (ttype ltm)}$$
    , $$\text{(mcadr (ttype on))} , \Gamma \vdash \text{rtm : (ttype ltm)}$$
    we get
    $$\Gamma \vdash \text{(case-on on ltm rtm) : (ttype ltm)}$$
    Note that in practice we append contexts on the left as computation of
    [`INDEX`][5b8b] is done from the left. Otherwise, the rules are the same as in
    usual type theory if context was read from right to left.

<a id="x-28GEB-2ELAMBDA-2ESPEC-3APAIR-20CLASS-29"></a>
- [class] **PAIR** *[\<STLC\>][b36a]*

    A term of the product type gotten by pairing a terms of a left and right
    parts of the product. The formal grammar of [`PAIR`][5dae] is
    
    ```lisp
    (pair ltm rtm)
    ```
    
    where we can possibly include type information by
    
    ```lisp
    (pair ltm rtm :ttype ttype)
    ```
    
    The intended semantics are as follows: [`LTM`][fcda] is a term (and hence an
    [`STLC`][e373]) of a left part of the product type whose terms we are
    producing. [`RTM`][d762] is a term (hence also [`STLC`][e373])of the right part
    of the product.
    
    The grammar corresponds to the introdcution rule of the pair type. Given
    $$\Gamma \vdash \text{ltm : (mcar (ttype (pair ltm rtm)))}$$ and
    $$\Gamma \vdash \text{rtm : (mcadr (ttype (pair ltm rtm)))}$$ we have
    $$\Gamma \vdash \text{(pair ltm rtm) : (ttype (pair ltm rtm))}$$

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AFST-20CLASS-29"></a>
- [class] **FST** *[\<STLC\>][b36a]*

    The first projection of a term of a product type.
    The formal grammar of [`FST`][b4a5] is:
    
    ```lisp
    (fst term)
    ```
    
    where we can possibly include type information by
    
    ```lisp
    (fst term :ttype ttype)
    ```
    
    The indended semantics are as follows: [`TERM`][0171] is a
    term (and hence an [`STLC`][e373]) of a product type, to whose left part
    we are projecting to.
    
    This corresponds to the first projection function gotten by induction
    on a term of a product type.

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ASND-20CLASS-29"></a>
- [class] **SND** *[\<STLC\>][b36a]*

    The second projection of a term of a product type.
    The formal grammar of [`SND`][0424] is:
    
    ```lisp
    (snd term)
    ```
    
    where we can possibly include type information by
    
    ```lisp
    (snd term :ttype ttype)
    ```
    
    The indended semantics are as follows: [`TERM`][0171] is a
    term (and hence an [`STLC`][e373]) of a product type, to whose right
    part we are projecting to.
    
    This corresponds to the second projection function gotten by induction
    on a term of a product type.

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ALAMB-20CLASS-29"></a>
- [class] **LAMB** *[\<STLC\>][b36a]*

    A term of a function type gotten by providing a term in the codomain
    of the function type by assuming one is given variables in the
    specified list of types. [`LAMB`][8cde] takes in the [`TDOM`][2c8c]
    accessor a list of types - and hence of [SUBSTOBJ][7e58] - and in the
    [`TERM`][0171] a term - and hence an [`STLC`][e373]. The formal grammar
    of [`LAMB`][8cde] is:
    
    ```lisp
    (lamb tdom term)
    ```
    
    where we can possibly include type information by
    
    ```lisp
    (lamb tdom term :ttype ttype)
    ```
    
    The intended semnatics are: [`TDOM`][2c8c] is a list of types (and
    hence a list of [SUBSTOBJ][3173]) whose iterative product of
    components form the domain of the function type. [`TERM`][0171]
    is a term (and hence an [`STLC`][e373]) of the codomain of the function type
    gotten in the context to whom we append the list of the domains.
    
    For a list of length 1, corresponds to the introduction rule of the function
    type. Namely, given
    $$\Gamma \vdash \text{tdom : Type}$$ and
    $$\Gamma, \text{tdom} \vdash \text{term : (ttype term)}$$ we have
    $$\Gamma \vdash \text{(lamb tdom term) : (so-hom-obj tdom (ttype term))}$$
    
    For a list of length n, this coreesponds to the iterated lambda type, e.g.
    
    ```lisp
    (lamb (list so1 so0) (index 0))
    ```
    
    is a term of
    
    ```lisp
    (so-hom-obj (prod so1 so0) so0)
    ```
    
    or equivalently
    
    ```lisp
    (so-hom-obj so1 (so-hom-obj so0 so0))
    ```
    
    due to Geb's computational definition of the function type.
    
    Note that [`INDEX`][5b8b] 0 in the above code is of type [SO1][7e58].
    So that after annotating the term, one gets
    
    ```lisp
    LAMBDA> (ttype (term (lamb (list so1 so0)) (index 0)))
    s-1
    ```
    
    So the counting of indeces starts with the leftmost argument for
    computational reasons. In practice, typing of [`LAMB`][8cde] corresponds with
    taking a list of arguments provided to a lambda term, making it a context
    in that order and then counting the index of the varibale. Type-theoretically,
    
    $$\Gamma \vdash \lambda \Delta (index i)$$
    $$\Delta, \Gamma \vdash (index i)$$
    
    So that by the operational semantics of [`INDEX`][5b8b], the type of (index i)
    in the above context will be the i'th element of the Delta context counted from
    the left. Note that in practice we append contexts on the left as computation of
    [`INDEX`][5b8b] is done from the left. Otherwise, the rules are the same as in
    usual type theory if context was read from right to left.

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AAPP-20CLASS-29"></a>
- [class] **APP** *[\<STLC\>][b36a]*

    A term of an arbitrary type gotten by applying a function of an iterated
    function type with a corresponding codomain iteratively to terms in the
    domains. [`APP`][04f2] takes as argument for the [`FUN`][cccf] accessor
    a function - and hence an [`STLC`][e373] - whose function type has domain an
    iterated [`GEB:PROD`][06c6] of [SUBSTOBJ][clas] and for the [`TERM`][0171]
    a list of terms - and hence of [`STLC`][e373] - matching the types of the
    product. The formal grammar of [`APP`][04f2] is
    
    ```lisp
    (app fun term)
    ```
    
    where we can possibly include type information by
    
    ```lisp
    (app fun term :ttype ttype)
    ```
    
    The intended semantics are as follows:
    [`FUN`][cccf] is a term (and hence an [`STLC`][e373]) of a coproduct
     type - say of (so-hom-obj (ttype term) y) - and [`TERM`][0171] is a
    list of terms (hence also of [`STLC`][e373]) with nth term in the list having the
    n-th part of the function type.
    
    For a one-argument term list, this corresponds to the elimination rule of the
    function type. Given
    $$\Gamma \vdash \text{fun : (so-hom-obj (ttype term) y)}$$ and
    $$\Gamma \vdash \text{term : (ttype term)}$$ we get
    $$\Gamma \vdash \text{(app fun term) : y}$$
    
    For several arguments, this corresponds to successive function application.
    Using currying, this corresponds to, given
    
    ```
    G ⊢ (so-hom-obj (A₁ × ··· × Aₙ₋₁) Aₙ)
    G ⊢ f : (so-hom-obj (A₁ × ··· × Aₙ₋₁)
    G ⊢ tᵢ : Aᵢ
    ```
    
    then for each `i` less than `n` gets us
    
    ```lisp
    G ⊢ (app f t₁ ··· tₙ₋₁) : Aₙ
    ```
    
    Note again that i'th term should correspond to the ith element of the product
    in the codomain counted from the left.

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AINDEX-20CLASS-29"></a>
- [class] **INDEX** *[\<STLC\>][b36a]*

    The variable term of an arbitrary type in a context. The formal
    grammar of [`INDEX`][5b8b] is
    
    ```lisp
    (index pos)
    ```
    
    where we can possibly include type information by
    
    ```lisp
    (index pos :ttype ttype)
    ```
    
    The intended semantics are as follows: [`POS`][3f85] is a
    natural number indicating the position of a type in a context.
    
    This corresponds to the variable rule. Namely given a context
    $$\Gamma\_1 , \ldots , \Gamma\_{pos} , \ldots , \Gamma\_k $$ we have
    
    $$\Gamma\_1 , \ldots , \Gamma\_k \vdash \text{(index pos) :} \Gamma\_{pos}$$
    
    Note that we add contexts on the left rather than on the right contra classical
    type-theoretic notation.

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AERR-20CLASS-29"></a>
- [class] **ERR** *[\<STLC\>][b36a]*

    An error term of a type supplied by the user. The formal grammar of
    [`ERR`][3a9f] is
    `lisp
    (err ttype)
    `
    The intended semantics are as follows: [`ERR`][3a9f] represents an error node
    currently having no particular feedback but with functionality to be of an
    arbitrary type. Note that this is the only [`STLC`][e373] term class which does not
    have [`TTYPE`][134c] a possibly empty accessor.

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AABSURD-20FUNCTION-29"></a>
- [function] **ABSURD** *TCOD TERM &KEY (TTYPE NIL)*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AUNIT-20FUNCTION-29"></a>
- [function] **UNIT** *&KEY (TTYPE NIL)*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ALEFT-20FUNCTION-29"></a>
- [function] **LEFT** *RTY TERM &KEY (TTYPE NIL)*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ARIGHT-20FUNCTION-29"></a>
- [function] **RIGHT** *LTY TERM &KEY (TTYPE NIL)*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ACASE-ON-20FUNCTION-29"></a>
- [function] **CASE-ON** *ON LTM RTM &KEY (TTYPE NIL)*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3APAIR-20FUNCTION-29"></a>
- [function] **PAIR** *LTM RTM &KEY (TTYPE NIL)*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AFST-20FUNCTION-29"></a>
- [function] **FST** *TERM &KEY (TTYPE NIL)*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ASND-20FUNCTION-29"></a>
- [function] **SND** *TERM &KEY (TTYPE NIL)*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ALAMB-20FUNCTION-29"></a>
- [function] **LAMB** *TDOM TERM &KEY (TTYPE NIL)*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AAPP-20FUNCTION-29"></a>
- [function] **APP** *FUN TERM &KEY (TTYPE NIL)*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AINDEX-20FUNCTION-29"></a>
- [function] **INDEX** *POS &KEY (TTYPE NIL)*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AERR-20FUNCTION-29"></a>
- [function] **ERR** *TTYPE*

Accessors of [`ABSURD`][4710]

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATCOD-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3AABSURD-29-29-29"></a>
- [method] **TCOD** *(ABSURD ABSURD)*

    An arbitrary type

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATERM-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3AABSURD-29-29-29"></a>
- [method] **TERM** *(ABSURD ABSURD)*

    A term of the empty type

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATTYPE-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3AABSURD-29-29-29"></a>
- [method] **TTYPE** *(ABSURD ABSURD)*

Accessors of [`UNIT`][0433]

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATTYPE-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3AUNIT-29-29-29"></a>
- [method] **TTYPE** *(UNIT UNIT)*

Accessors of [`LEFT`][56b3]

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ARTY-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3ALEFT-29-29-29"></a>
- [method] **RTY** *(LEFT LEFT)*

    Right argument of coproduct type

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATERM-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3ALEFT-29-29-29"></a>
- [method] **TERM** *(LEFT LEFT)*

    Term of the left argument of coproduct type

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATTYPE-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3ALEFT-29-29-29"></a>
- [method] **TTYPE** *(LEFT LEFT)*

Accessors of [`RIGHT`][48fc]

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ALTY-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3ARIGHT-29-29-29"></a>
- [method] **LTY** *(RIGHT RIGHT)*

    Left argument of coproduct type

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATERM-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3ARIGHT-29-29-29"></a>
- [method] **TERM** *(RIGHT RIGHT)*

    Term of the right argument of coproduct type

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATTYPE-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3ARIGHT-29-29-29"></a>
- [method] **TTYPE** *(RIGHT RIGHT)*

Accessors of [`CASE-ON`][3f9d]

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AON-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3ACASE-ON-29-29-29"></a>
- [method] **ON** *(CASE-ON CASE-ON)*

    Term of coproduct type

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ALTM-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3ACASE-ON-29-29-29"></a>
- [method] **LTM** *(CASE-ON CASE-ON)*

    Term in context of left argument of coproduct type

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ARTM-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3ACASE-ON-29-29-29"></a>
- [method] **RTM** *(CASE-ON CASE-ON)*

    Term in context of right argument of coproduct type

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATTYPE-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3ACASE-ON-29-29-29"></a>
- [method] **TTYPE** *(CASE-ON CASE-ON)*

Accessors of [`PAIR`][5dae]

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ALTM-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3APAIR-29-29-29"></a>
- [method] **LTM** *(PAIR PAIR)*

    Term of left argument of the product type

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ARTM-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3APAIR-29-29-29"></a>
- [method] **RTM** *(PAIR PAIR)*

    Term of right argument of the product type

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATTYPE-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3APAIR-29-29-29"></a>
- [method] **TTYPE** *(PAIR PAIR)*

Accessors of [`FST`][b4a5]

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATERM-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3AFST-29-29-29"></a>
- [method] **TERM** *(FST FST)*

    Term of product type

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATTYPE-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3AFST-29-29-29"></a>
- [method] **TTYPE** *(FST FST)*

Accessors of [`SND`][0424]

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATERM-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3ASND-29-29-29"></a>
- [method] **TERM** *(SND SND)*

    Term of product type

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATTYPE-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3ASND-29-29-29"></a>
- [method] **TTYPE** *(SND SND)*

Accessors of [`LAMB`][8cde]

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATDOM-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3ALAMB-29-29-29"></a>
- [method] **TDOM** *(LAMB LAMB)*

    Domain of the lambda term

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATERM-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3ALAMB-29-29-29"></a>
- [method] **TERM** *(LAMB LAMB)*

    Term of the codomain mapped to given a variable of tdom

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATTYPE-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3ALAMB-29-29-29"></a>
- [method] **TTYPE** *(LAMB LAMB)*

Accessors of [`APP`][04f2]

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AFUN-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3AAPP-29-29-29"></a>
- [method] **FUN** *(APP APP)*

    Term of exponential type

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATERM-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3AAPP-29-29-29"></a>
- [method] **TERM** *(APP APP)*

    List of Terms of the domain

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATTYPE-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3AAPP-29-29-29"></a>
- [method] **TTYPE** *(APP APP)*

Accessors of [`INDEX`][5b8b]

<a id="x-28GEB-2ELAMBDA-2ESPEC-3APOS-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3AINDEX-29-29-29"></a>
- [method] **POS** *(INDEX INDEX)*

    Position of type

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATTYPE-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3AINDEX-29-29-29"></a>
- [method] **TTYPE** *(INDEX INDEX)*

Accessors of [`ERR`][3a9f]

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATTYPE-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3AERR-29-29-29"></a>
- [method] **TTYPE** *(ERR ERR)*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATCOD-20GENERIC-FUNCTION-29"></a>
- [generic-function] **TCOD** *OBJ*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATDOM-20GENERIC-FUNCTION-29"></a>
- [generic-function] **TDOM** *OBJ*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATERM-20GENERIC-FUNCTION-29"></a>
- [generic-function] **TERM** *OBJ*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ARTY-20GENERIC-FUNCTION-29"></a>
- [generic-function] **RTY** *OBJ*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ALTY-20GENERIC-FUNCTION-29"></a>
- [generic-function] **LTY** *OBJ*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ALTM-20GENERIC-FUNCTION-29"></a>
- [generic-function] **LTM** *OBJ*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ARTM-20GENERIC-FUNCTION-29"></a>
- [generic-function] **RTM** *OBJ*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AON-20GENERIC-FUNCTION-29"></a>
- [generic-function] **ON** *OBJ*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3AFUN-20GENERIC-FUNCTION-29"></a>
- [generic-function] **FUN** *OBJ*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3APOS-20GENERIC-FUNCTION-29"></a>
- [generic-function] **POS** *OBJ*

<a id="x-28GEB-2ELAMBDA-2ESPEC-3ATTYPE-20GENERIC-FUNCTION-29"></a>
- [generic-function] **TTYPE** *OBJ*

<a id="x-28GEB-2ELAMBDA-2EMAIN-3A-40LAMBDA-API-20MGL-PAX-3ASECTION-29"></a>
### 12.2 Main functionality

###### \[in package GEB.LAMBDA.MAIN\]
This covers the main API for the [`STLC`][e373] module

<a id="x-28GEB-2ELAMBDA-2EMAIN-3AANN-TERM1-20GENERIC-FUNCTION-29"></a>
- [generic-function] **ANN-TERM1** *CTX TTERM*

    Given a list of [`SUBSTOBJ`][3173] objects with
    [`SO-HOM-OBJ`][07dd] occurences replaced by [`FUN-TYPE`][8dcc]
    and an [`STLC`][e373] similarly replacing type occurences of the hom object
    to [`FUN-TYPE`][8dcc], provides the [`TTYPE`][134c] accessor to all
    subterms as well as the term itself, using [`FUN-TYPE`][8dcc]. Once again,
    note  that it is important for the context and term to be giving as
    per above description. While not always, not doing so result in an error upon
    evaluation. As an example of a valid entry we have
    
    ```lisp
     (ann-term1 (list so1 (fun-type so1 so1)) (app (index 1) (list (index 0))))
    ```
    
    while
    
    ```lisp
    (ann-term1 (list so1 (so-hom-obj so1 so1)) (app (index 1) (list (index 0))))
    ```
    
    produces an error trying to use [`HOM-COD`][b324]. This warning applies to other
    functions taking in context and terms below as well.
    
    Moreover, note that for terms whose typing needs addition of new context
    we append contexts on the left rather than on the right contra usual type
    theoretic notation for the convenience of computation. That means, e.g. that
    asking for a type of a lambda term as below produces:
    
    ```lisp
    LAMBDA> (ttype (term (ann-term1 (lambda (list so1 so0) (index 0)))))
    s-1
    ```
    
    as we count indeces from the left of the context while appending new types to
    the context on the left as well. For more info check [`LAMB`][8cde]

<a id="x-28GEB-2ELAMBDA-2EMAIN-3AHOM-COD-20FUNCTION-29"></a>
- [function] **HOM-COD** *CTX F*

    Given a context of [`SUBSTOBJ`][3173] with occurences of
    [`SO-HOM-OBJ`][07dd] replaced by [`FUN-TYPE`][8dcc], and similarly
    an [`STLC`][e373] term of the stand-in for the hom object, produces the stand-in
    to the codomain.

<a id="x-28GEB-2ELAMBDA-2EMAIN-3AINDEX-CHECK-20FUNCTION-29"></a>
- [function] **INDEX-CHECK** *I CTX*

    Given an natural number `I` and a context, checks that the context is of
    length at least `I` and then produces the Ith entry of the context counted
    from the left starting with 0.

<a id="x-28GEB-2ELAMBDA-2EMAIN-3AFUN-TO-HOM-20FUNCTION-29"></a>
- [function] **FUN-TO-HOM** *T1*

    Given a [`SUBSTOBJ`][3173] whose subobjects might have a
    [`FUN-TYPE`][8dcc] occurence replaces all occurences of [`FUN-TYPE`][8dcc] with a
    suitable [`SO-HOM-OBJ`][07dd], hence giving a pure
    [`SUBSTOBJ`][3173]
    
    ```lisp
    LAMBDA> (fun-to-hom (fun-type geb-bool:bool geb-bool:bool))
    (× (+ GEB-BOOL:FALSE GEB-BOOL:TRUE) (+ GEB-BOOL:FALSE GEB-BOOL:TRUE))
    ```


<a id="x-28GEB-2ELAMBDA-2EMAIN-3AANN-TERM2-20FUNCTION-29"></a>
- [function] **ANN-TERM2** *TTERM*

    Given an [`STLC`][e373] term with a [`TTYPE`][134c] accessor from
    [`ANN-TERM1`][ac2d] - i.e. including possible [`FUN-TYPE`][8dcc]
    occurences - re-annotates the term and its subterms with actual
    [`SUBSTOBJ`][3173] objects.

<a id="x-28GEB-2ELAMBDA-2EMAIN-3AANNOTATED-TERM-20FUNCTION-29"></a>
- [function] **ANNOTATED-TERM** *CTX TERM*

    Given a context consisting of a list of [`SUBSTOBJ`][3173]
    with occurences of [`SO-HOM-OBJ`][07dd] replaced by
    [`FUN-TYPE`][8dcc] and an [`STLC`][e373] term with similarly replaced occurences
    of [`SO-HOM-OBJ`][07dd], provides an [`STLC`][e373] with all
    subterms typed, i.e. providing the [`TTYPE`][134c] accessor,
    which is a pure [`SUBSTOBJ`][3173]

<a id="x-28GEB-2ELAMBDA-2EMAIN-3ATYPE-OF-TERM-W-FUN-20FUNCTION-29"></a>
- [function] **TYPE-OF-TERM-W-FUN** *CTX TTERM*

    Given a context consisting of a list of [`SUBSTOBJ`][3173] with
    occurences of [`SO-HOM-OBJ`][07dd] replaced by [`FUN-TYPE`][8dcc]
    and an [`STLC`][e373] term with similarly replaced occurences of
    [`SO-HOM-OBJ`][07dd], gives out a type of the whole term with
    occurences of [`SO-HOM-OBJ`][07dd] replaced by [`FUN-TYPE`][8dcc].

<a id="x-28GEB-2ELAMBDA-2EMAIN-3ATYPE-OF-TERM-20FUNCTION-29"></a>
- [function] **TYPE-OF-TERM** *CTX TTERM*

    Given a context consisting of a list of [`SUBSTOBJ`][3173] with
    occurences of [`SO-HOM-OBJ`][07dd] replaced by [`FUN-TYPE`][8dcc]
    and an [`STLC`][e373] term with similarly replaced occurences of
    [`SO-HOM-OBJ`][07dd], provides the type of the whole term,
    which is a pure [`SUBSTOBJ`][3173].

<a id="x-28GEB-2ELAMBDA-2EMAIN-3AWELL-DEFP-20GENERIC-FUNCTION-29"></a>
- [generic-function] **WELL-DEFP** *CTX TTERM*

    Given a context consisting of a list of [`SUBSTOBJ`][3173]
    with occurences of [`SO-HOM-OBJ`][07dd] replaced by
    [`FUN-TYPE`][8dcc] and an [`STLC`][e373] term with similarly replaced
    occurences of [`SO-HOM-OBJ`][07dd], checks that the term
    is well-defined in the context based on structural rules of simply
    typed lambda calculus. returns the t if it is, otherwise returning
    nil

<a id="x-28GEB-2ELAMBDA-2EMAIN-3AFUN-TYPE-20CLASS-29"></a>
- [class] **FUN-TYPE** *[DIRECT-POINTWISE-MIXIN][e2b0] [CAT-OBJ][74bd]*

    Stand-in for the [`SO-HOM-OBJ`][07dd] object. It does not have
    any computational properties and can be seen as just a function of two arguments
    with accessors [`MCAR`][f1ce] to the first argument and
    [`MCADR`][cc87] to the second argument. There is an evident canonical
    way to associate [`FUN-TYPE`][8dcc] and [`SO-HOM-OBJ`][07dd]
    pointwise.

<a id="x-28GEB-2ELAMBDA-2EMAIN-3AFUN-TYPE-20FUNCTION-29"></a>
- [function] **FUN-TYPE** *MCAR MCADR*

<a id="x-28GEB-2ELAMBDA-2EMAIN-3AERRORP-20FUNCTION-29"></a>
- [function] **ERRORP** *TTERM*

    Evaluates to true iff the term has an error subterm.

<a id="x-28GEB-2EUTILS-3AMCAR-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2EMAIN-3AFUN-TYPE-29-29-29"></a>
- [method] **MCAR** *(FUN-TYPE FUN-TYPE)*

<a id="x-28GEB-2EUTILS-3AMCADR-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2EMAIN-3AFUN-TYPE-29-29-29"></a>
- [method] **MCADR** *(FUN-TYPE FUN-TYPE)*

<a id="x-28GEB-2EGENERICS-3AMAYBE-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2EMAIN-3AFUN-TYPE-29-29-29"></a>
- [method] **MAYBE** *(OBJECT FUN-TYPE)*

    I recursively add maybe terms to my domain and codomain, and even
    return a maybe function. Thus if the original function was
    
    ```
    f : a -> b
    ```
    
    we would now be
    
    ```
    f : maybe (maybe a -> maybe b)
    ```
    
    for what maybe means checkout [my generic function documentation][65a4].

<a id="x-28GEB-2ELAMBDA-2ETRANS-3A-40STLC-CONVERSION-20MGL-PAX-3ASECTION-29"></a>
### 12.3 Transition Functions

###### \[in package GEB.LAMBDA.TRANS\]
These functions deal with transforming the data structure to other
data types

One important note about the lambda conversions is that all
transition functions except [`TO-CAT`][d243] do not take a context.

Thus if the [`<STLC>`][b36a] term contains free variables, then call
[`TO-CAT`][d243] and give it the desired context before calling
any other transition functions

<a id="x-28GEB-2EGENERICS-3ATO-CAT-20-28METHOD-20NIL-20-28T-20GEB-2ELAMBDA-2ESPEC-3A-3CSTLC-3E-29-29-29"></a>
- [method] **TO-CAT** *CONTEXT (TTERM \<STLC\>)*

    Compiles a checked term in said context to a Geb morphism. If the term has
    an instance of an erorr term, wraps it in a Maybe monad, otherwise, compiles
    according to the term model interpretation of [`STLC`][e373]

<a id="x-28GEB-2EGENERICS-3ATO-POLY-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3A-3CSTLC-3E-29-29-29"></a>
- [method] **TO-POLY** *(OBJ \<STLC\>)*

    I convert a lambda term into a [`GEB.POLY.SPEC:POLY`][8bf3] term
    
    Note that [`<STLC>`][b36a] terms with free variables require a context,
    and we do not supply them here to conform to the standard interface
    
    If you want to give a context, please call [to-cat][d243] before
    calling me

<a id="x-28GEB-2EGENERICS-3ATO-BITC-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3A-3CSTLC-3E-29-29-29"></a>
- [method] **TO-BITC** *(OBJ \<STLC\>)*

    I convert a lambda term into a [`GEB.BITC.SPEC:BITC`][e017] term
    
    Note that [`<STLC>`][b36a] terms with free variables require a context,
    and we do not supply them here to conform to the standard interface
    
    If you want to give a context, please call [to-cat][d243] before
    calling me

<a id="x-28GEB-2EGENERICS-3ATO-CIRCUIT-20-28METHOD-20NIL-20-28GEB-2ELAMBDA-2ESPEC-3A-3CSTLC-3E-20T-29-29-29"></a>
- [method] **TO-CIRCUIT** *(OBJ \<STLC\>) NAME*

    I convert a lambda term into a vampir term
    
    Note that [`<STLC>`][b36a] terms with free variables require a context,
    and we do not supply them here to conform to the standard interface
    
    If you want to give a context, please call [to-cat][d243] before
    calling me

<a id="x-28GEB-2ELAMBDA-2ETRANS-3A-40UTILITY-20MGL-PAX-3ASECTION-29"></a>
#### 12.3.1 Utility Functionality

These are utility functions relating to translating lambda terms to other types

<a id="x-28GEB-2ELAMBDA-2ETRANS-3ASTLC-CTX-TO-MU-20FUNCTION-29"></a>
- [function] **STLC-CTX-TO-MU** *CONTEXT*

    Converts a generic [(CODE <STLC>)][78ef] context into a
    [`SUBSTMORPH`][57dc]. Note that usually contexts can be interpreted
    in a category as a $Sigma$-type$, which in a non-dependent setting gives us a
    usual [`PROD`][06c6]
    
    ```lisp
    LAMBDA> (stlc-ctx-to-mu (list so1 (fun-to-hom (fun-type geb-bool:bool geb-bool:bool))))
    (× s-1
       (× (+ GEB-BOOL:FALSE GEB-BOOL:TRUE) (+ GEB-BOOL:FALSE GEB-BOOL:TRUE))
       s-1)
    ```


<a id="x-28GEB-2ELAMBDA-2ETRANS-3ASO-HOM-20FUNCTION-29"></a>
- [function] **SO-HOM** *DOM COD*

    Computes the hom-object of two [`SUBSTMORPH`][57dc]s

<a id="x-28GEB-2EMIXINS-3A-40MIXINS-20MGL-PAX-3ASECTION-29"></a>
## 13 Mixins

###### \[in package GEB.MIXINS\]
Various [mixins](https://en.wikipedia.org/wiki/Mixin) of the
project. Overall all these offer various services to the rest of the
project

<a id="x-28GEB-2EMIXINS-3A-40POINTWISE-20MGL-PAX-3ASECTION-29"></a>
### 13.1 Pointwise Mixins

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
### 13.2 Pointwise API

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

<a id="x-28GEB-2EMIXINS-3AMAP-POINTWISE-20FUNCTION-29"></a>
- [function] **MAP-POINTWISE** *FUNCTION OBJ*

<a id="x-28GEB-2EMIXINS-3AREDUCE-POINTWISE-20FUNCTION-29"></a>
- [function] **REDUCE-POINTWISE** *FUNCTION OBJ INITIAL*

<a id="x-28GEB-2EMIXINS-3A-40MIXIN-EXAMPLES-20MGL-PAX-3ASECTION-29"></a>
### 13.3 Mixins Examples

Let's see some example uses of [`POINTWISE-MIXIN`][445d]:

```common-lisp
(obj-equalp (geb:terminal geb:so1)
            (geb:terminal geb:so1))
=> t

(to-pointwise-list (geb:coprod geb:so1 geb:so1))
=> ((:MCAR . s-1) (:MCADR . s-1))
```


<a id="x-28GEB-2EMIXINS-3A-40METADATA-20MGL-PAX-3ASECTION-29"></a>
### 13.4 Metadata Mixin

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
#### 13.4.1 Performance

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
## 14 Geb Utilities

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

<a id="x-28GEB-2EUTILS-3ACOPY-INSTANCE-20GENERIC-FUNCTION-29"></a>
- [generic-function] **COPY-INSTANCE** *OBJECT &REST INITARGS &KEY &ALLOW-OTHER-KEYS*

    Makes and returns a shallow copy of `OBJECT`.
    
    An uninitialized object of the same class as `OBJECT` is allocated by
    calling [`ALLOCATE-INSTANCE`][a859].  For all slots returned by
    CLASS-SLOTS, the returned object has the
    same slot values and slot-unbound status as `OBJECT`.
    
    [`REINITIALIZE-INSTANCE`][1456] is called to update the copy with `INITARGS`.

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

<a id="x-28GEB-2EUTILS-3AAPPLY-N-20FUNCTION-29"></a>
- [function] **APPLY-N** *TIMES F INITIAL*

    Applies a function, f, n `TIMES` to the `INITIAL` values
    
    ```lisp
    GEB> (apply-n 10 #'1+ 0)
    10 (4 bits, #xA, #o12, #b1010)
    ```


<a id="x-28GEB-2EUTILS-3A-40GEB-ACCESSORS-20MGL-PAX-3ASECTION-29"></a>
### 14.1 Accessors

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

<a id="x-28GEB-2EUTILS-3ACODE-20GENERIC-FUNCTION-29"></a>
- [generic-function] **CODE** *OBJ*

    the code of the
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-TEST-3A-40GEB-TEST-MANUAL-20MGL-PAX-3ASECTION-29"></a>
## 15 Testing

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

  [0171]: #x-28GEB-2ELAMBDA-2ESPEC-3ATERM-20GENERIC-FUNCTION-29 "GEB.LAMBDA.SPEC:TERM GENERIC-FUNCTION"
  [0251]: #x-28GEB-2EPOLY-2EMAIN-3A-40POLY-API-20MGL-PAX-3ASECTION-29 "Polynomial API"
  [0424]: #x-28GEB-2ELAMBDA-2ESPEC-3ASND-20CLASS-29 "GEB.LAMBDA.SPEC:SND CLASS"
  [0433]: #x-28GEB-2ELAMBDA-2ESPEC-3AUNIT-20CLASS-29 "GEB.LAMBDA.SPEC:UNIT CLASS"
  [04f2]: #x-28GEB-2ELAMBDA-2ESPEC-3AAPP-20CLASS-29 "GEB.LAMBDA.SPEC:APP CLASS"
  [0609]: #x-28GEB-2ELAMBDA-2ETRANS-3A-40UTILITY-20MGL-PAX-3ASECTION-29 "Utility Functionality"
  [06c6]: #x-28GEB-2ESPEC-3APROD-20CLASS-29 "GEB.SPEC:PROD CLASS"
  [06e0]: #x-28GEB-2ESPEC-3APROJECT-RIGHT-20CLASS-29 "GEB.SPEC:PROJECT-RIGHT CLASS"
  [07dd]: #x-28GEB-2EMAIN-3ASO-HOM-OBJ-20FUNCTION-29 "GEB.MAIN:SO-HOM-OBJ FUNCTION"
  [0ad4]: #x-28GEB-BOOL-3ABOOL-20MGL-PAX-3ASYMBOL-MACRO-29 "GEB-BOOL:BOOL MGL-PAX:SYMBOL-MACRO"
  [0ae3]: #x-28GEB-2EPOLY-2ESPEC-3A-2A-20TYPE-29 "GEB.POLY.SPEC:* TYPE"
  [0dfe]: #x-28GEB-2ESPEC-3A-3C-RIGHT-20FUNCTION-29 "GEB.SPEC:<-RIGHT FUNCTION"
  [0e00]: #x-28GEB-DOCS-2FDOCS-3A-40YONEDA-LEMMA-20MGL-PAX-3ASECTION-29 "The Yoneda Lemma"
  [0efa]: #x-28GEB-2EEXTENSION-2ESPEC-3A-40GEB-EXTENSIONS-20MGL-PAX-3ASECTION-29 "Extension Sets for Categories"
  [0f3e]: #x-28GEB-2EPOLY-2ETRANS-3A-40POLY-TRANS-20MGL-PAX-3ASECTION-29 "Polynomial Transformations"
  [134c]: #x-28GEB-2ELAMBDA-2ESPEC-3ATTYPE-20GENERIC-FUNCTION-29 "GEB.LAMBDA.SPEC:TTYPE GENERIC-FUNCTION"
  [1456]: http://www.lispworks.com/documentation/HyperSpec/Body/f_reinit.htm "REINITIALIZE-INSTANCE FUNCTION"
  [15a3]: #x-28GEB-2ELAMBDA-2ESPEC-3ALTY-20GENERIC-FUNCTION-29 "GEB.LAMBDA.SPEC:LTY GENERIC-FUNCTION"
  [1774]: #x-28GEB-2EBITC-2ESPEC-3ABRANCH-20FUNCTION-29 "GEB.BITC.SPEC:BRANCH FUNCTION"
  [1791]: http://www.lispworks.com/documentation/HyperSpec/Body/f_car_c.htm "CADDDR FUNCTION"
  [1b98]: #x-28GEB-GUI-2EGRAPHING-3A-40GRAPHING-MANUAL-20MGL-PAX-3ASECTION-29 "The GEB Graphizer"
  [1c91]: #x-28GEB-LIST-3A-40GEB-LIST-20MGL-PAX-3ASECTION-29 "Lists"
  [1fbc]: #x-28GEB-GUI-2ECORE-3ACHILDREN-20GENERIC-FUNCTION-29 "GEB-GUI.CORE:CHILDREN GENERIC-FUNCTION"
  [2172]: #x-28GEB-2EBITC-2ESPEC-3A-40BITC-20MGL-PAX-3ASECTION-29 "Bits Types"
  [2276]: #x-28GEB-2EUTILS-3ASUBCLASS-RESPONSIBILITY-20FUNCTION-29 "GEB.UTILS:SUBCLASS-RESPONSIBILITY FUNCTION"
  [2410]: http://www.lispworks.com/documentation/HyperSpec/Body/t_bit.htm "BIT TYPE"
  [2570]: http://www.lispworks.com/documentation/HyperSpec/Body/f_car_c.htm "CDR FUNCTION"
  [25f0]: #x-28GEB-DOCS-2FDOCS-3A-40GLOSSARY-20MGL-PAX-3ASECTION-29 "Glossary"
  [26d4]: #x-28GEB-2EBITC-2ESPEC-3A-3CBITC-3E-20CLASS-29 "GEB.BITC.SPEC:<BITC> CLASS"
  [2882]: #x-28GEB-2ESPEC-3A-3C-LEFT-20FUNCTION-29 "GEB.SPEC:<-LEFT FUNCTION"
  [29b7]: #x-28GEB-DOCS-2FDOCS-3A-40AGDA-20MGL-PAX-3ASECTION-29 "Geb's Agda Code"
  [2ad4]: #x-28GEB-2ESPEC-3A-40GEB-CONSTRUCTORS-20MGL-PAX-3ASECTION-29 "Constructors"
  [2c5e]: #x-28GEB-2EPOLY-2ESPEC-3A--20TYPE-29 "GEB.POLY.SPEC:- TYPE"
  [2c8c]: #x-28GEB-2ELAMBDA-2ESPEC-3ATDOM-20GENERIC-FUNCTION-29 "GEB.LAMBDA.SPEC:TDOM GENERIC-FUNCTION"
  [2cbc]: #x-28GEB-2EMAIN-3ACURRY-20FUNCTION-29 "GEB.MAIN:CURRY FUNCTION"
  [2eb9]: #x-28GEB-2EGENERICS-3ATO-POLY-20GENERIC-FUNCTION-29 "GEB.GENERICS:TO-POLY GENERIC-FUNCTION"
  [2ebc]: #x-28GEB-2EBITC-2ETRANS-3A-40BITC-TRANS-20MGL-PAX-3ASECTION-29 "Bits (Boolean Circuit) Transformations"
  [2fc2]: #x-28GEB-2EEXTENSION-2ESPEC-3AOPAQUE-20CLASS-29 "GEB.EXTENSION.SPEC:OPAQUE CLASS"
  [2fcf]: #x-28GEB-2EMIXINS-3A-40POINTWISE-API-20MGL-PAX-3ASECTION-29 "Pointwise API"
  [315f]: #x-28GEB-2ESPEC-3AALIAS-20MGL-PAX-3AMACRO-29 "GEB.SPEC:ALIAS MGL-PAX:MACRO"
  [3173]: #x-28GEB-2ESPEC-3ASUBSTOBJ-20TYPE-29 "GEB.SPEC:SUBSTOBJ TYPE"
  [31c5]: #x-28GEB-BOOL-3AFALSE-20MGL-PAX-3ASYMBOL-MACRO-29 "GEB-BOOL:FALSE MGL-PAX:SYMBOL-MACRO"
  [34d0]: #x-28GEB-2ELAMBDA-2ESPEC-3A-40LAMBDA-SPECS-20MGL-PAX-3ASECTION-29 "Lambda Specification"
  [365a]: #x-28GEB-2EUTILS-3AELSE-20GENERIC-FUNCTION-29 "GEB.UTILS:ELSE GENERIC-FUNCTION"
  [3686]: #x-28GEB-DOCS-2FDOCS-3A-40ORIGINAL-EFFORTS-20MGL-PAX-3ASECTION-29 "Original Efforts"
  [399c]: #x-28GEB-BOOL-3A-40GEB-BOOL-20MGL-PAX-3ASECTION-29 "Booleans"
  [3a9f]: #x-28GEB-2ELAMBDA-2ESPEC-3AERR-20CLASS-29 "GEB.LAMBDA.SPEC:ERR CLASS"
  [3d47]: #x-28GEB-DOCS-2FDOCS-3A-40GETTING-STARTED-20MGL-PAX-3ASECTION-29 "Getting Started"
  [3f85]: #x-28GEB-2ELAMBDA-2ESPEC-3APOS-20GENERIC-FUNCTION-29 "GEB.LAMBDA.SPEC:POS GENERIC-FUNCTION"
  [3f9d]: #x-28GEB-2ELAMBDA-2ESPEC-3ACASE-ON-20CLASS-29 "GEB.LAMBDA.SPEC:CASE-ON CLASS"
  [4044]: #x-28GEB-DOCS-2FDOCS-3A-40COVERAGE-20MGL-PAX-3ASECTION-29 "code coverage"
  [414c]: #x-28GEB-2EBITC-2ESPEC-3ABRANCH-20CLASS-29 "GEB.BITC.SPEC:BRANCH CLASS"
  [417f]: #x-28GEB-TEST-3ACODE-COVERAGE-20FUNCTION-29 "GEB-TEST:CODE-COVERAGE FUNCTION"
  [4267]: http://www.lispworks.com/documentation/HyperSpec/Body/t_string.htm "STRING TYPE"
  [42d7]: http://www.lispworks.com/documentation/HyperSpec/Body/m_defpkg.htm "DEFPACKAGE MGL-PAX:MACRO"
  [445d]: #x-28GEB-2EMIXINS-3APOINTWISE-MIXIN-20CLASS-29 "GEB.MIXINS:POINTWISE-MIXIN CLASS"
  [4529]: #x-28GEB-2EMIXINS-3AMETA-MIXIN-20CLASS-29 "GEB.MIXINS:META-MIXIN CLASS"
  [455b]: #x-28GEB-2EMIXINS-3A-40MIXIN-PERFORMANCE-20MGL-PAX-3ASECTION-29 "Performance"
  [4659]: #x-28GEB-2EBITC-2EMAIN-3A-40BITC-API-20MGL-PAX-3ASECTION-29 "Bits (Boolean Circuit) API"
  [46bc]: #x-28GEB-2EBITC-2ESPEC-3APARALLEL-20CLASS-29 "GEB.BITC.SPEC:PARALLEL CLASS"
  [46ed]: http://www.lispworks.com/documentation/HyperSpec/Body/t_bt_vec.htm "BIT-VECTOR TYPE"
  [4710]: #x-28GEB-2ELAMBDA-2ESPEC-3AABSURD-20CLASS-29 "GEB.LAMBDA.SPEC:ABSURD CLASS"
  [4850]: http://www.lispworks.com/documentation/HyperSpec/Body/t_kwd.htm "KEYWORD TYPE"
  [48fc]: #x-28GEB-2ELAMBDA-2ESPEC-3ARIGHT-20CLASS-29 "GEB.LAMBDA.SPEC:RIGHT CLASS"
  [4938]: #x-28GEB-2EMIXINS-3A-40MIXIN-EXAMPLES-20MGL-PAX-3ASECTION-29 "Mixins Examples"
  [49d4]: #x-28GEB-2EMAIN-3A-40GEB-UTILITY-20MGL-PAX-3ASECTION-29 "Utility"
  [4a87]: #x-28GEB-DOCS-2FDOCS-3A-40OPEN-TYPE-20MGL-PAX-3AGLOSSARY-TERM-29 "GEB-DOCS/DOCS:@OPEN-TYPE MGL-PAX:GLOSSARY-TERM"
  [4ffa]: #x-28GEB-2EUTILS-3A-40GEB-UTILS-MANUAL-20MGL-PAX-3ASECTION-29 "Geb Utilities"
  [56b3]: #x-28GEB-2ELAMBDA-2ESPEC-3ALEFT-20CLASS-29 "GEB.LAMBDA.SPEC:LEFT CLASS"
  [57dc]: #x-28GEB-2ESPEC-3ASUBSTMORPH-20TYPE-29 "GEB.SPEC:SUBSTMORPH TYPE"
  [58a9]: #x-28GEB-2EMIXINS-3ATO-POINTWISE-LIST-20GENERIC-FUNCTION-29 "GEB.MIXINS:TO-POINTWISE-LIST GENERIC-FUNCTION"
  [592c]: http://www.lispworks.com/documentation/HyperSpec/Body/f_list_.htm "LIST FUNCTION"
  [5ae3]: #x-28GEB-2ESPEC-3APROJECT-LEFT-20CLASS-29 "GEB.SPEC:PROJECT-LEFT CLASS"
  [5b8b]: #x-28GEB-2ELAMBDA-2ESPEC-3AINDEX-20CLASS-29 "GEB.LAMBDA.SPEC:INDEX CLASS"
  [5c7c]: #x-28GEB-2ESPEC-3ASO0-20CLASS-29 "GEB.SPEC:SO0 CLASS"
  [5cfe]: #x-28GEB-2ESPEC-3ASO1-20CLASS-29 "GEB.SPEC:SO1 CLASS"
  [5d7c]: #x-28GEB-2ESPEC-3ACASE-20CLASS-29 "GEB.SPEC:CASE CLASS"
  [5dae]: #x-28GEB-2ELAMBDA-2ESPEC-3APAIR-20CLASS-29 "GEB.LAMBDA.SPEC:PAIR CLASS"
  [603e]: #x-28GEB-GUI-3A-40VISAULIZER-AID-20MGL-PAX-3ASECTION-29 "Aiding the Visualizer"
  [6228]: #x-28GEB-3A-40GEB-API-20MGL-PAX-3ASECTION-29 "API"
  [6444]: #x-28GEB-2ESPEC-3ALEFT-20CLASS-29 "GEB.SPEC:LEFT CLASS"
  [65a4]: #x-28GEB-2EGENERICS-3AMAYBE-20GENERIC-FUNCTION-29 "GEB.GENERICS:MAYBE GENERIC-FUNCTION"
  [684b]: http://www.lispworks.com/documentation/HyperSpec/Body/s_if.htm "IF MGL-PAX:MACRO"
  [6a3c]: http://www.lispworks.com/documentation/HyperSpec/Body/f_bt_sb.htm "BIT FUNCTION"
  [6b63]: #x-28GEB-2EBITC-3A-40BITC-MANUAL-20MGL-PAX-3ASECTION-29 "Bits (Boolean Circuit) Specification"
  [6f67]: #x-28GEB-GUI-3A-40GEB-GUI-MANUAL-20MGL-PAX-3ASECTION-29 "The GEB GUI"
  [7058]: http://www.lispworks.com/documentation/HyperSpec/Body/v_nil.htm "NIL MGL-PAX:CONSTANT"
  [7088]: #x-28GEB-2ESPEC-3ASO0-20MGL-PAX-3ASYMBOL-MACRO-29 "GEB.SPEC:SO0 MGL-PAX:SYMBOL-MACRO"
  [70c0]: #x-28GEB-2ELAMBDA-2ESPEC-3ATCOD-20GENERIC-FUNCTION-29 "GEB.LAMBDA.SPEC:TCOD GENERIC-FUNCTION"
  [71e9]: #x-28GEB-GUI-2ECORE-3A-40GRAPHING-CORE-20MGL-PAX-3ASECTION-29 "The GEB Graphizer Core"
  [723a]: #x-28GEB-2EMIXINS-3A-40MIXINS-20MGL-PAX-3ASECTION-29 "Mixins"
  [73be]: #x-28GEB-2ESPEC-3AREALIZED-OBJECT-20TYPE-29 "GEB.SPEC:REALIZED-OBJECT TYPE"
  [74ab]: http://www.lispworks.com/documentation/HyperSpec/Body/f_car_c.htm "CADR FUNCTION"
  [74bd]: #x-28GEB-2EMIXINS-3ACAT-OBJ-20CLASS-29 "GEB.MIXINS:CAT-OBJ CLASS"
  [78ef]: http://www.lispworks.com/documentation/HyperSpec/Body/t_nil.htm "NIL TYPE"
  [7c57]: #x-28GEB-2ELAMBDA-2ESPEC-3AON-20GENERIC-FUNCTION-29 "GEB.LAMBDA.SPEC:ON GENERIC-FUNCTION"
  [7dbb]: http://www.lispworks.com/documentation/HyperSpec/Body/t_number.htm "NUMBER TYPE"
  [7e58]: http://www.lispworks.com/documentation/HyperSpec/Body/t_class.htm "CLASS CLASS"
  [7f9f]: http://www.lispworks.com/documentation/HyperSpec/Body/t_symbol.htm "SYMBOL TYPE"
  [8311]: #x-28GEB-DOCS-2FDOCS-3A-40IDRIS-20MGL-PAX-3ASECTION-29 "Geb's Idris Code"
  [8387]: #x-28GEB-2ESPEC-3AINJECT-LEFT-20CLASS-29 "GEB.SPEC:INJECT-LEFT CLASS"
  [874b]: #x-28GEB-2ESPEC-3ATERMINAL-20CLASS-29 "GEB.SPEC:TERMINAL CLASS"
  [8932]: #x-28GEB-DOCS-2FDOCS-3A-40CLOSED-TYPE-20MGL-PAX-3AGLOSSARY-TERM-29 "GEB-DOCS/DOCS:@CLOSED-TYPE MGL-PAX:GLOSSARY-TERM"
  [8bb8]: http://www.lispworks.com/documentation/HyperSpec/Body/f_car_c.htm "CADDR FUNCTION"
  [8be5]: #x-28GEB-2ESPEC-3ACOPROD-20CLASS-29 "GEB.SPEC:COPROD CLASS"
  [8bf3]: #x-28GEB-2EPOLY-2ESPEC-3APOLY-20TYPE-29 "GEB.POLY.SPEC:POLY TYPE"
  [8c99]: http://www.lispworks.com/documentation/HyperSpec/Body/f_car_c.htm "CAR FUNCTION"
  [8cde]: #x-28GEB-2ELAMBDA-2ESPEC-3ALAMB-20CLASS-29 "GEB.LAMBDA.SPEC:LAMB CLASS"
  [8da6]: #x-28GEB-2EUTILS-3APREDICATE-20GENERIC-FUNCTION-29 "GEB.UTILS:PREDICATE GENERIC-FUNCTION"
  [8dcc]: #x-28GEB-2ELAMBDA-2EMAIN-3AFUN-TYPE-20CLASS-29 "GEB.LAMBDA.MAIN:FUN-TYPE CLASS"
  [8e11]: #x-28GEB-2ESPEC-3AINIT-20CLASS-29 "GEB.SPEC:INIT CLASS"
  [8eb0]: #x-28GEB-2EENTRY-3A-40GEB-ENTRY-20MGL-PAX-3ASECTION-29 "Geb as a binary"
  [8fa5]: #x-28GEB-DOCS-2FDOCS-3A-40INSTALLATION-20MGL-PAX-3ASECTION-29 "installation"
  [9162]: #x-28GEB-2EPOLY-2ESPEC-3ACOMPOSE-20TYPE-29 "GEB.POLY.SPEC:COMPOSE TYPE"
  [925b]: #x-28GEB-DOCS-2FDOCS-3A-40POLY-SETS-20MGL-PAX-3ASECTION-29 "Poly in Sets"
  [9300]: #x-28GEB-2EMIXINS-3A-40METADATA-20MGL-PAX-3ASECTION-29 "Metadata Mixin"
  [94a8]: #x-28GEB-2EPOLY-3A-40POLY-MANUAL-20MGL-PAX-3ASECTION-29 "Polynomial Specification"
  [96d0]: http://www.lispworks.com/documentation/HyperSpec/Body/f_equal.htm "EQUAL FUNCTION"
  [9728]: #x-28GEB-2EMIXINS-3ADOM-20GENERIC-FUNCTION-29 "GEB.MIXINS:DOM GENERIC-FUNCTION"
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
  [a84b]: #x-28GEB-2EGENERICS-3A-40GENERICS-20MGL-PAX-3ASECTION-29 "Geneircs"
  [a859]: http://www.lispworks.com/documentation/HyperSpec/Body/f_alloca.htm "ALLOCATE-INSTANCE FUNCTION"
  [a920]: #x-28GEB-DOCS-2FDOCS-3A-40OPEN-CLOSED-20MGL-PAX-3ASECTION-29 "Open Types versus Closed Types"
  [a981]: http://www.lispworks.com/documentation/HyperSpec/Body/m_defmet.htm "DEFMETHOD MGL-PAX:MACRO"
  [abea]: #x-28GEB-2ELAMBDA-2ESPEC-3ARTY-20GENERIC-FUNCTION-29 "GEB.LAMBDA.SPEC:RTY GENERIC-FUNCTION"
  [ac2d]: #x-28GEB-2ELAMBDA-2EMAIN-3AANN-TERM1-20GENERIC-FUNCTION-29 "GEB.LAMBDA.MAIN:ANN-TERM1 GENERIC-FUNCTION"
  [ac8a]: http://www.lispworks.com/documentation/HyperSpec/Body/t_intege.htm "INTEGER TYPE"
  [ada5]: #x-28GEB-GUI-3AVISUALIZE-20FUNCTION-29 "GEB-GUI:VISUALIZE FUNCTION"
  [ada9]: #x-28GEB-DOCS-2FDOCS-3A-40MORPHISMS-20MGL-PAX-3ASECTION-29 "Morphisms"
  [af14]: #x-28GEB-2EUTILS-3AMCDR-20GENERIC-FUNCTION-29 "GEB.UTILS:MCDR GENERIC-FUNCTION"
  [b0d9]: #x-28GEB-2EGENERICS-3ATO-CIRCUIT-20GENERIC-FUNCTION-29 "GEB.GENERICS:TO-CIRCUIT GENERIC-FUNCTION"
  [b324]: #x-28GEB-2ELAMBDA-2EMAIN-3AHOM-COD-20FUNCTION-29 "GEB.LAMBDA.MAIN:HOM-COD FUNCTION"
  [b36a]: #x-28GEB-2ELAMBDA-2ESPEC-3A-3CSTLC-3E-20CLASS-29 "GEB.LAMBDA.SPEC:<STLC> CLASS"
  [b4a5]: #x-28GEB-2ELAMBDA-2ESPEC-3AFST-20CLASS-29 "GEB.LAMBDA.SPEC:FST CLASS"
  [b4a6]: #x-28GEB-2EPOLY-2ESPEC-3A-3CPOLY-3E-20CLASS-29 "GEB.POLY.SPEC:<POLY> CLASS"
  [b76d]: #x-28GEB-2EPOLY-2ESPEC-3A-40POLY-CONSTRUCTORS-20MGL-PAX-3ASECTION-29 "Polynomial Constructors"
  [b79a]: #x-28GEB-2ETRANS-3A-40GEB-TRANSLATION-20MGL-PAX-3ASECTION-29 "Translation Functions"
  [b960]: #x-28GEB-2ESPEC-3A-2ASO1-2A-20VARIABLE-29 "GEB.SPEC:*SO1* VARIABLE"
  [b9c1]: http://www.lispworks.com/documentation/HyperSpec/Body/t_seq.htm "SEQUENCE TYPE"
  [b9f3]: #x-28GEB-DOCS-2FDOCS-3A-40IDIOMS-20MGL-PAX-3ASECTION-29 "Project Idioms and Conventions"
  [ba44]: #x-28GEB-2ESPEC-3A--3ERIGHT-20FUNCTION-29 "GEB.SPEC:->RIGHT FUNCTION"
  [bb34]: #x-28GEB-2EGENERICS-3AGAPPLY-20GENERIC-FUNCTION-29 "GEB.GENERICS:GAPPLY GENERIC-FUNCTION"
  [bd81]: #x-28GEB-2EPOLY-2ESPEC-3A-40POLY-20MGL-PAX-3ASECTION-29 "Polynomial Types"
  [bf07]: http://www.lispworks.com/documentation/HyperSpec/Body/f_export.htm "EXPORT FUNCTION"
  [bfa9]: #x-28GEB-2EUTILS-3ATHEN-20GENERIC-FUNCTION-29 "GEB.UTILS:THEN GENERIC-FUNCTION"
  [c111]: #x-28GEB-2EMIXINS-3AOBJ-EQUALP-20GENERIC-FUNCTION-29 "GEB.MIXINS:OBJ-EQUALP GENERIC-FUNCTION"
  [c144]: #x-28GEB-2EPOLY-2ESPEC-3A-2B-20TYPE-29 "GEB.POLY.SPEC:+ TYPE"
  [c1b3]: #x-28GEB-2ESPEC-3A-40GEB-SUBSTMU-20MGL-PAX-3ASECTION-29 "Subst Obj"
  [c1fb]: #x-28GEB-3A-40GEB-20MGL-PAX-3ASECTION-29 "The Geb Model"
  [c275]: #x-28GEB-2ESPEC-3ARIGHT-20CLASS-29 "GEB.SPEC:RIGHT CLASS"
  [c2e9]: #x-28GEB-DOCS-2FDOCS-3A-40MODEL-20MGL-PAX-3ASECTION-29 "Categorical Model"
  [c2f9]: #x-28GEB-2EPOLY-2ESPEC-3A-2F-20TYPE-29 "GEB.POLY.SPEC:/ TYPE"
  [c3e8]: #x-28GEB-GUI-2ECORE-3ANODE-NOTE-20CLASS-29 "GEB-GUI.CORE:NODE-NOTE CLASS"
  [c417]: #x-28GEB-2EBITC-2ESPEC-3AIDENT-20FUNCTION-29 "GEB.BITC.SPEC:IDENT FUNCTION"
  [c6cf]: #x-28GEB-GUI-3A-40GEB-VISUALIZER-20MGL-PAX-3ASECTION-29 "Visualizer"
  [c721]: http://www.lispworks.com/documentation/HyperSpec/Body/f_equalp.htm "EQUALP FUNCTION"
  [c767]: http://www.lispworks.com/documentation/HyperSpec/Body/s_the.htm "THE MGL-PAX:MACRO"
  [cb9e]: #x-28GEB-2ESPEC-3A-40GEB-CATEGORIES-20MGL-PAX-3ASECTION-29 "Core Category"
  [cc51]: #x-28GEB-2EUTILS-3A-40GEB-ACCESSORS-20MGL-PAX-3ASECTION-29 "Accessors"
  [cc87]: #x-28GEB-2EUTILS-3AMCADR-20GENERIC-FUNCTION-29 "GEB.UTILS:MCADR GENERIC-FUNCTION"
  [cccf]: #x-28GEB-2ELAMBDA-2ESPEC-3AFUN-20GENERIC-FUNCTION-29 "GEB.LAMBDA.SPEC:FUN GENERIC-FUNCTION"
  [cd11]: #x-28GEB-2ESPEC-3AMCASE-20FUNCTION-29 "GEB.SPEC:MCASE FUNCTION"
  [ce5b]: #x-28GEB-2ESPEC-3ACOMP-20CLASS-29 "GEB.SPEC:COMP CLASS"
  [ceb9]: http://www.lispworks.com/documentation/HyperSpec/Body/t_fixnum.htm "FIXNUM TYPE"
  [cf10]: #x-28GEB-2EBITC-2ESPEC-3AONE-20CLASS-29 "GEB.BITC.SPEC:ONE CLASS"
  [d243]: #x-28GEB-2EGENERICS-3ATO-CAT-20GENERIC-FUNCTION-29 "GEB.GENERICS:TO-CAT GENERIC-FUNCTION"
  [d2d1]: #x-28GEB-2ESPEC-3A-40GEB-SUBSTMORPH-20MGL-PAX-3ASECTION-29 "Subst Morph"
  [d2d5]: #x-28GEB-2ELAMBDA-2EMAIN-3A-40LAMBDA-API-20MGL-PAX-3ASECTION-29 "Main functionality"
  [d5d3]: #x-28GEB-2EMIXINS-3A-40POINTWISE-20MGL-PAX-3ASECTION-29 "Pointwise Mixins"
  [d762]: #x-28GEB-2ELAMBDA-2ESPEC-3ARTM-20GENERIC-FUNCTION-29 "GEB.LAMBDA.SPEC:RTM GENERIC-FUNCTION"
  [d908]: http://www.lispworks.com/documentation/HyperSpec/Body/f_typep.htm "TYPEP FUNCTION"
  [db35]: #x-28GEB-2ESPEC-3A-3CSUBSTMORPH-3E-20CLASS-29 "GEB.SPEC:<SUBSTMORPH> CLASS"
  [db8f]: #x-28GEB-2ELAMBDA-3A-40STLC-20MGL-PAX-3ASECTION-29 "The Simply Typed Lambda Calculus model"
  [dbe7]: #x-28GEB-DOCS-2FDOCS-3A-40OBJECTS-20MGL-PAX-3ASECTION-29 "Objects"
  [dca9]: #x-28GEB-2ESPEC-3A-40GEB-REALIZED-20MGL-PAX-3ASECTION-29 "Realized Subst Objs"
  [dfa2]: #x-28GEB-2ESPEC-3APAIR-20CLASS-29 "GEB.SPEC:PAIR CLASS"
  [e017]: #x-28GEB-2EBITC-2ESPEC-3ABITC-20TYPE-29 "GEB.BITC.SPEC:BITC TYPE"
  [e2af]: #x-28GEB-2ESPEC-3A--3ELEFT-20FUNCTION-29 "GEB.SPEC:->LEFT FUNCTION"
  [e2b0]: #x-28GEB-2EMIXINS-3ADIRECT-POINTWISE-MIXIN-20CLASS-29 "GEB.MIXINS:DIRECT-POINTWISE-MIXIN CLASS"
  [e373]: #x-28GEB-2ELAMBDA-2ESPEC-3ASTLC-20TYPE-29 "GEB.LAMBDA.SPEC:STLC TYPE"
  [e3e4]: #x-28GEB-2ELAMBDA-2ETRANS-3A-40STLC-CONVERSION-20MGL-PAX-3ASECTION-29 "Transition Functions"
  [e429]: #x-28GEB-GUI-2EGRAPHING-2EPASSES-3A-40PASS-MANUAL-20MGL-PAX-3ASECTION-29 "The GEB Graphizer Passes"
  [e91b]: #x-28GEB-2EMIXINS-3A-40MIXINS-CAT-20MGL-PAX-3ASECTION-29 "The Categorical Interface"
  [e947]: #x-28GEB-2ESPEC-3AINJECT-RIGHT-20CLASS-29 "GEB.SPEC:INJECT-RIGHT CLASS"
  [e982]: #x-28GEB-2ESPEC-3A-2ASO0-2A-20VARIABLE-29 "GEB.SPEC:*SO0* VARIABLE"
  [ecb2]: #x-28GEB-2EBITC-2ESPEC-3ACOMPOSE-20CLASS-29 "GEB.BITC.SPEC:COMPOSE CLASS"
  [ecc6]: #x-28GEB-DOCS-2FDOCS-3A-40CLOS-20MGL-PAX-3AGLOSSARY-TERM-29 "GEB-DOCS/DOCS:@CLOS MGL-PAX:GLOSSARY-TERM"
  [ef6e]: #x-28GEB-GUI-2ECORE-3ANOTE-20TYPE-29 "GEB-GUI.CORE:NOTE TYPE"
  [f022]: #x-28GEB-BOOL-3ATRUE-20MGL-PAX-3ASYMBOL-MACRO-29 "GEB-BOOL:TRUE MGL-PAX:SYMBOL-MACRO"
  [f130]: #x-28GEB-2EBITC-2ESPEC-3ADROP-20FUNCTION-29 "GEB.BITC.SPEC:DROP FUNCTION"
  [f1ce]: #x-28GEB-2EUTILS-3AMCAR-20GENERIC-FUNCTION-29 "GEB.UTILS:MCAR GENERIC-FUNCTION"
  [f1e6]: #x-28GEB-2EUTILS-3AOBJ-20GENERIC-FUNCTION-29 "GEB.UTILS:OBJ GENERIC-FUNCTION"
  [f4ba]: #x-28GEB-2ESPEC-3ASO1-20MGL-PAX-3ASYMBOL-MACRO-29 "GEB.SPEC:SO1 MGL-PAX:SYMBOL-MACRO"
  [f766]: http://www.lispworks.com/documentation/HyperSpec/Body/f_load.htm "LOAD FUNCTION"
  [fa6c]: #x-28GEB-2EBITC-2ESPEC-3AZERO-20MGL-PAX-3ASYMBOL-MACRO-29 "GEB.BITC.SPEC:ZERO MGL-PAX:SYMBOL-MACRO"
  [fb79]: #x-28GEB-2ESPEC-3A-3CSUBSTOBJ-3E-20CLASS-29 "GEB.SPEC:<SUBSTOBJ> CLASS"
  [fc10]: #x-28GEB-2EBITC-2ESPEC-3A-40BITC-CONSTRUCTORS-20MGL-PAX-3ASECTION-29 "Bits (Boolean Circuit) Constructors"
  [fcda]: #x-28GEB-2ELAMBDA-2ESPEC-3ALTM-20GENERIC-FUNCTION-29 "GEB.LAMBDA.SPEC:LTM GENERIC-FUNCTION"
  [ff98]: #x-28GEB-GUI-2ECORE-3ANODE-20CLASS-29 "GEB-GUI.CORE:NODE CLASS"

* * *
###### \[generated by [MGL-PAX](https://github.com/melisgl/mgl-pax)\]
