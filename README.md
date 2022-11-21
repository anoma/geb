<a id="x-28GEB-DOCS-2FDOCS-3A-40INDEX-20MGL-PAX-3ASECTION-29"></a>
# The GEB Manual

## Table of Contents

- [1 Links][9bc5]
- [2 Getting Started][3d47]
    - [2.1 installation][8fa5]
    - [2.2 loading][a7d5]
- [3 Original Efforts][3686]
    - [3.1 Geb's Idris Code][8311]
    - [3.2 Geb's Agda Code][29b7]
- [4 Categorical Model][c2e9]
    - [4.1 Morphisms][ada9]
    - [4.2 Objects][dbe7]
- [5 The Geb Model][c1fb]
    - [5.1 Core Categories][5d9d]
        - [5.1.1 Subst Obj][ca6e]
        - [5.1.2 Subst Morph][ffb7]
    - [5.2 Accessors][b26a]
    - [5.3 Constructors][0c5c]
    - [5.4 api][6228]
    - [5.5 Examples][a17b]
- [6 Mixins][723a]
    - [6.1 Pointwise Mixins][d5d3]
    - [6.2 Pointwise API][2fcf]
    - [6.3 Mixins Examples][4938]
- [7 Geb Utilities][4ffa]
- [8 Testing][9bcb]

###### \[in package GEB-DOCS/DOCS\]
Welcome to the GEB project.

<a id="x-28GEB-DOCS-2FDOCS-3A-40LINKS-20MGL-PAX-3ASECTION-29"></a>
## 1 Links

Here is the [official repository](https://github.com/anoma/geb/)
and the [HTML documentation](https://anoma.github.io/geb/) for the latest version

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


<a id="x-28GEB-DOCS-2FDOCS-3A-40ORIGINAL-EFFORTS-20MGL-PAX-3ASECTION-29"></a>
## 3 Original Efforts

Originally GEB started off as an Idris codebase written by the
designer and creator of GEB, Terence Rokop, However further efforts
spawned for even further formal verification by Artem Gureev. Due
to this, we have plenty of code not in Common Lisp that ought to be
a good read.

<a id="x-28GEB-DOCS-2FDOCS-3A-40IDRIS-20MGL-PAX-3ASECTION-29"></a>
### 3.1 Geb's Idris Code

The Idris folder can be found in the
[geb-idris](https://github.com/anoma/geb/tree/main/geb-idris) folder
provided in the codebase

At the time of this document, there is over 16k lines of Idris code
written. This serves as the bulk of the POC that is GEB and is a
treasure trove of interesting information surrounding category
theorey.

<a id="x-28GEB-DOCS-2FDOCS-3A-40AGDA-20MGL-PAX-3ASECTION-29"></a>
### 3.2 Geb's Agda Code

The Agda folder can be found in the
[geb-agda](https://github.com/anoma/geb/tree/main/geb-agda) folder
provided in the codebase

The Agda codebase serves as a great place to view formally verified
properties about the GEB project. Although [Geb's Idris Code][8311] is written in a
dependently typed language, it serves as reference example of GEB,
while [Geb's Agda Code][29b7] serves as the mathematical formalism proving various
conjectures about GEB

<a id="x-28GEB-DOCS-2FDOCS-3A-40MODEL-20MGL-PAX-3ASECTION-29"></a>
## 4 Categorical Model

GEB is organizing programming language concepts
using [category theory](https://plato.stanford.edu/entries/category-theory/),
originally developped by mathematicians,
but very much alive in (theoretical) computer science.

<a id="x-28GEB-DOCS-2FDOCS-3A-40MORPHISMS-20MGL-PAX-3ASECTION-29"></a>
### 4.1 Morphisms


<a id="x-28GEB-DOCS-2FDOCS-3A-40OBJECTS-20MGL-PAX-3ASECTION-29"></a>
### 4.2 Objects


<a id="x-28GEB-3A-40GEB-20MGL-PAX-3ASECTION-29"></a>
## 5 The Geb Model

###### \[in package GEB\]
Everything here relates directly to the underlying machinery of
GEB, or to abstractions that help extend it.

<a id="x-28GEB-3A-40GEB-CATEGORIES-20MGL-PAX-3ASECTION-29"></a>
### 5.1 Core Categories

The underlying category of GEB. With [Subst Obj][ca6e] covering the
shapes and forms ([Objects][dbe7]) of data while [Subst Morph][ffb7]
deals with concrete [Morphisms][ada9] within the category

<a id="x-28GEB-3A-40GEB-SUBSTMU-20MGL-PAX-3ASECTION-29"></a>
#### 5.1.1 Subst Obj

This section covers the objects of the GEB category. Every value
that is a [`SUBSTOBJ`][718e] is automatically lifted into a [`SUBSTMORPH`][e5d9] when a
`SUBSTMORPH` is expected.

The Type that encomposes the [`SUBSTOBJ`][718e] class

<a id="x-28GEB-3ASUBSTOBJ-20TYPE-29"></a>
- [type] **SUBSTOBJ**

<a id="x-28GEB-3A-3CSUBSTOBJ-3E-20TYPE-29"></a>
- [type] **\<SUBSTOBJ\>**

    the class corresponding to [`SUBSTOBJ`][718e]

The various constructors that form the [`SUBSTOBJ`][718e] type

<a id="x-28GEB-3APROD-20TYPE-29"></a>
- [type] **PROD**

    the product

<a id="x-28GEB-3ACOPROD-20TYPE-29"></a>
- [type] **COPROD**

    the coproduct

<a id="x-28GEB-3ASO0-20TYPE-29"></a>
- [type] **SO0**

    The Initial/Void Object

<a id="x-28GEB-3ASO1-20TYPE-29"></a>
- [type] **SO1**

    The Terminal/Unit Object

<a id="x-28GEB-3AALIAS-20TYPE-29"></a>
- [type] **ALIAS**

    an alias for a geb object

The [Accessors][b26a] specific to [Subst Obj][ca6e]

<a id="x-28GEB-3AMCAR-20-28METHOD-20NIL-20-28GEB-3APROD-29-29-29"></a>
- [method] **MCAR** *(PROD PROD)*

<a id="x-28GEB-3AMCADR-20-28METHOD-20NIL-20-28GEB-3APROD-29-29-29"></a>
- [method] **MCADR** *(PROD PROD)*

<a id="x-28GEB-3AMCAR-20-28METHOD-20NIL-20-28GEB-3ACOPROD-29-29-29"></a>
- [method] **MCAR** *(COPROD COPROD)*

<a id="x-28GEB-3AMCADR-20-28METHOD-20NIL-20-28GEB-3ACOPROD-29-29-29"></a>
- [method] **MCADR** *(COPROD COPROD)*

<a id="x-28GEB-3A-40GEB-SUBSTMORPH-20MGL-PAX-3ASECTION-29"></a>
#### 5.1.2 Subst Morph

The moprhisms of the GEB category.

The Type that encomposes the SUBSTMOPRH class

<a id="x-28GEB-3ASUBSTMORPH-20TYPE-29"></a>
- [type] **SUBSTMORPH**

<a id="x-28GEB-3A-3CSUBSTMORPH-3E-20TYPE-29"></a>
- [type] **\<SUBSTMORPH\>**

    the class type corresponding to [`SUBSTMORPH`][e5d9]

The various constructors that form the [`SUBSTMORPH`][e5d9] type

<a id="x-28GEB-3ACOMP-20TYPE-29"></a>
- [type] **COMP**

    Composition of morphism

<a id="x-28GEB-3ACASE-20TYPE-29"></a>
- [type] **CASE**

    Coproduct elimination (case statement)

<a id="x-28GEB-3AINIT-20TYPE-29"></a>
- [type] **INIT**

    The initial Morphism

<a id="x-28GEB-3ATERMINAL-20TYPE-29"></a>
- [type] **TERMINAL**

    The terminal Morhpism

<a id="x-28GEB-3APAIR-20TYPE-29"></a>
- [type] **PAIR**

    Product introduction (morphism pairing)

<a id="x-28GEB-3ADISTRIBUTE-20TYPE-29"></a>
- [type] **DISTRIBUTE**

    The distributive law

<a id="x-28GEB-3AINJECT-LEFT-20TYPE-29"></a>
- [type] **INJECT-LEFT**

    Left injection (coproduct introduction)

<a id="x-28GEB-3AINJECT-RIGHT-20TYPE-29"></a>
- [type] **INJECT-RIGHT**

    Right injection (coproduct introduction)

<a id="x-28GEB-3APROJECT-LEFT-20TYPE-29"></a>
- [type] **PROJECT-LEFT**

    Left projection (product elimination)

<a id="x-28GEB-3APROJECT-RIGHT-20TYPE-29"></a>
- [type] **PROJECT-RIGHT**

<a id="x-28GEB-3AFUNCTOR-20TYPE-29"></a>
- [type] **FUNCTOR**

<a id="x-28GEB-3AALIAS-20TYPE-29"></a>
- [type] **ALIAS**

    an alias for a geb object

The [Accessors][b26a] specific to [Subst Morph][ffb7]

<a id="x-28GEB-3AMCAR-20-28METHOD-20NIL-20-28GEB-3ACOMP-29-29-29"></a>
- [method] **MCAR** *(COMP COMP)*

    The first composed morphism

<a id="x-28GEB-3AMCADR-20-28METHOD-20NIL-20-28GEB-3ACOMP-29-29-29"></a>
- [method] **MCADR** *(COMP COMP)*

    the second morphism

<a id="x-28GEB-3AOBJ-20-28METHOD-20NIL-20-28GEB-3AINIT-29-29-29"></a>
- [method] **OBJ** *(INIT INIT)*

<a id="x-28GEB-3AOBJ-20-28METHOD-20NIL-20-28GEB-3AINIT-29-29-29"></a>
- [method] **OBJ** *(INIT INIT)*

<a id="x-28GEB-3AMCAR-20-28METHOD-20NIL-20-28GEB-3ACASE-29-29-29"></a>
- [method] **MCAR** *(CASE CASE)*

<a id="x-28GEB-3AMCADR-20-28METHOD-20NIL-20-28GEB-3ACASE-29-29-29"></a>
- [method] **MCADR** *(CASE CASE)*

<a id="x-28GEB-3AMCAR-20-28METHOD-20NIL-20-28GEB-3APAIR-29-29-29"></a>
- [method] **MCAR** *(PAIR PAIR)*

    Head of the pair cell

<a id="x-28GEB-3AMCDR-20-28METHOD-20NIL-20-28GEB-3APAIR-29-29-29"></a>
- [method] **MCDR** *(PAIR PAIR)*

    Tail of the pair cell

<a id="x-28GEB-3AMCAR-20-28METHOD-20NIL-20-28GEB-3ADISTRIBUTE-29-29-29"></a>
- [method] **MCAR** *(DISTRIBUTE DISTRIBUTE)*

<a id="x-28GEB-3AMCADR-20-28METHOD-20NIL-20-28GEB-3ADISTRIBUTE-29-29-29"></a>
- [method] **MCADR** *(DISTRIBUTE DISTRIBUTE)*

<a id="x-28GEB-3AMCADDR-20-28METHOD-20NIL-20-28GEB-3ADISTRIBUTE-29-29-29"></a>
- [method] **MCADDR** *(DISTRIBUTE DISTRIBUTE)*

<a id="x-28GEB-3AMCAR-20-28METHOD-20NIL-20-28GEB-3AINJECT-LEFT-29-29-29"></a>
- [method] **MCAR** *(INJECT-LEFT INJECT-LEFT)*

<a id="x-28GEB-3AMCADR-20-28METHOD-20NIL-20-28GEB-3AINJECT-LEFT-29-29-29"></a>
- [method] **MCADR** *(INJECT-LEFT INJECT-LEFT)*

<a id="x-28GEB-3AMCAR-20-28METHOD-20NIL-20-28GEB-3AINJECT-RIGHT-29-29-29"></a>
- [method] **MCAR** *(INJECT-RIGHT INJECT-RIGHT)*

<a id="x-28GEB-3AMCADR-20-28METHOD-20NIL-20-28GEB-3AINJECT-RIGHT-29-29-29"></a>
- [method] **MCADR** *(INJECT-RIGHT INJECT-RIGHT)*

<a id="x-28GEB-3AMCAR-20-28METHOD-20NIL-20-28GEB-3APROJECT-LEFT-29-29-29"></a>
- [method] **MCAR** *(PROJECT-LEFT PROJECT-LEFT)*

<a id="x-28GEB-3AMCADR-20-28METHOD-20NIL-20-28GEB-3APROJECT-LEFT-29-29-29"></a>
- [method] **MCADR** *(PROJECT-LEFT PROJECT-LEFT)*

<a id="x-28GEB-3AMCAR-20-28METHOD-20NIL-20-28GEB-3APROJECT-RIGHT-29-29-29"></a>
- [method] **MCAR** *(PROJECT-RIGHT PROJECT-RIGHT)*

<a id="x-28GEB-3AMCADR-20-28METHOD-20NIL-20-28GEB-3APROJECT-RIGHT-29-29-29"></a>
- [method] **MCADR** *(PROJECT-RIGHT PROJECT-RIGHT)*

    Right projection (product elimination)

<a id="x-28GEB-3A-40GEB-ACCESSORS-20MGL-PAX-3ASECTION-29"></a>
### 5.2 Accessors

These functions relate to grabbing slots out of the various
[Subst Morph][ffb7] and [Subst Obj][ca6e] types. See those sections for
specific instance documentation

<a id="x-28GEB-3AMCAR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCAR** *OBJ*

    Can be seen as calling [`CAR`][8c99] on a generic CLOS
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-3AMCADR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCADR** *OBJ*

    like [`MCAR`][493b] but for the [`CADR`][74ab]

<a id="x-28GEB-3AMCDR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCDR** *OBJ*

    Similar to [`MCAR`][493b], however acts like a [`CDR`][2570] for
    [classes][7e58] that we wish to view as a [`SEQUENCE`][b9c1]

<a id="x-28GEB-3AMCADDR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCADDR** *OBJ*

    like [`MCAR`][493b] but for the [`CADDR`][8bb8]

<a id="x-28GEB-3AOBJ-20GENERIC-FUNCTION-29"></a>
- [generic-function] **OBJ** *OBJ*

    Grabs the underlying
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-3ANAME-20GENERIC-FUNCTION-29"></a>
- [generic-function] **NAME** *OBJ*

    the name of the given
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-3AFUNC-20GENERIC-FUNCTION-29"></a>
- [generic-function] **FUNC** *OBJ*

    the function of the
    [object](http://www.lispworks.com/documentation/HyperSpec/Body/26_glo_o.htm#object)

<a id="x-28GEB-3A-40GEB-CONSTRUCTORS-20MGL-PAX-3ASECTION-29"></a>
### 5.3 Constructors

The API for creating GEB terms. All the functions and variables
here relate to instantiating a term

<a id="x-28GEB-3A-2ASO0-2A-20VARIABLE-29"></a>
- [variable] **\*SO0\*** *s-0*

    The Initial Object

<a id="x-28GEB-3A-2ASO1-2A-20VARIABLE-29"></a>
- [variable] **\*SO1\*** *s-1*

    The Terminal Object

More Ergonomic API variants for [`*SO0*`][9f7a] and [`*SO1*`][6380]

<a id="x-28GEB-3ASO0-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **SO0**

<a id="x-28GEB-3ASO1-20MGL-PAX-3ASYMBOL-MACRO-29"></a>
- [symbol-macro] **SO1**

<a id="x-28GEB-3AMAKE-ALIAS-20FUNCTION-29"></a>
- [function] **MAKE-ALIAS** *&KEY NAME OBJ*

<a id="x-28GEB-3A-3C-LEFT-20FUNCTION-29"></a>
- [function] **\<-LEFT** *MCAR MCADR*

    projects left constructor

<a id="x-28GEB-3A-3C-RIGHT-20FUNCTION-29"></a>
- [function] **\<-RIGHT** *MCAR MCADR*

    projects right constructor

<a id="x-28GEB-3ALEFT--3E-20FUNCTION-29"></a>
- [function] **LEFT-\>** *MCAR MCADR*

    injects left constructor

<a id="x-28GEB-3ARIGHT--3E-20FUNCTION-29"></a>
- [function] **RIGHT-\>** *MCAR MCADR*

    injects right constructor

<a id="x-28GEB-3AMCASE-20FUNCTION-29"></a>
- [function] **MCASE** *MCAR MCADR*

<a id="x-28GEB-3AMAKE-FUNCTOR-20FUNCTION-29"></a>
- [function] **MAKE-FUNCTOR** *&KEY OBJ FUNC*

<a id="x-28GEB-3A-40GEB-API-20MGL-PAX-3ASECTION-29"></a>
### 5.4 api

Various functions that make working with GEB easier

<a id="x-28GEB-3APAIR-TO-LIST-20FUNCTION-29"></a>
- [function] **PAIR-TO-LIST** *PAIR &OPTIONAL ACC*

    converts excess pairs to a list format

<a id="x-28GEB-3ASAME-TYPE-TO-LIST-20FUNCTION-29"></a>
- [function] **SAME-TYPE-TO-LIST** *PAIR TYPE &OPTIONAL ACC*

    converts the given type to a list format

<a id="x-28GEB-3AMLIST-20FUNCTION-29"></a>
- [function] **MLIST** *V1 &REST VALUES*

<a id="x-28GEB-3ACOMMUTES-20FUNCTION-29"></a>
- [function] **COMMUTES** *X Y*

<a id="x-28GEB-3A-21--3E-20FUNCTION-29"></a>
- [function] **!-\>** *A B*

<a id="x-28GEB-3ASO-EVAL-20FUNCTION-29"></a>
- [function] **SO-EVAL** *X Y*

<a id="x-28GEB-3A-40GEB-EXAMPLES-20MGL-PAX-3ASECTION-29"></a>
### 5.5 Examples

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


<a id="x-28GEB-2EMIXINS-3A-40MIXINS-20MGL-PAX-3ASECTION-29"></a>
## 6 Mixins

###### \[in package GEB.MIXINS\]
Various [mixins](https://en.wikipedia.org/wiki/Mixin) of the
project. Overall all these offer various services to the rest of the
project

<a id="x-28GEB-2EMIXINS-3A-40POINTWISE-20MGL-PAX-3ASECTION-29"></a>
### 6.1 Pointwise Mixins

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
### 6.2 Pointwise API

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
### 6.3 Mixins Examples

Let's see some example uses of [`POINTWISE-MIXIN`][445d]:

```common-lisp
(obj-equalp (geb:terminal geb:so1)
            (geb:terminal geb:so1))
=> t

(to-pointwise-list (geb:coprod geb:so1 geb:so1))
=> ((:MCAR . s-1) (:MCADR . s-1))
```


<a id="x-28GEB-2EUTILS-3A-40GEB-UTILS-MANUAL-20MGL-PAX-3ASECTION-29"></a>
## 7 Geb Utilities

###### \[in package GEB.UTILS\]
The Utilities package provide general utility functionality that is
used throughout the GEB codebase

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
           (uiop:define-package #:geb.lambda-conversion
             (:mix #:trivia #:geb #:serapeum #:common-lisp)
             (:export
              :compile-checked-term :stlc-ctx-to-mu)))
    ```


<a id="x-28GEB-TEST-3A-40GEB-TEST-MANUAL-20MGL-PAX-3ASECTION-29"></a>
## 8 Testing

###### \[in package GEB-TEST\]
We use [parachtue](https://quickref.common-lisp.net/parachute.html)
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


  [0c5c]: #x-28GEB-3A-40GEB-CONSTRUCTORS-20MGL-PAX-3ASECTION-29 "Constructors"
  [2570]: http://www.lispworks.com/documentation/HyperSpec/Body/f_car_c.htm "CDR FUNCTION"
  [29b7]: #x-28GEB-DOCS-2FDOCS-3A-40AGDA-20MGL-PAX-3ASECTION-29 "Geb's Agda Code"
  [2fcf]: #x-28GEB-2EMIXINS-3A-40POINTWISE-API-20MGL-PAX-3ASECTION-29 "Pointwise API"
  [3686]: #x-28GEB-DOCS-2FDOCS-3A-40ORIGINAL-EFFORTS-20MGL-PAX-3ASECTION-29 "Original Efforts"
  [3d47]: #x-28GEB-DOCS-2FDOCS-3A-40GETTING-STARTED-20MGL-PAX-3ASECTION-29 "Getting Started"
  [42d7]: http://www.lispworks.com/documentation/HyperSpec/Body/m_defpkg.htm "DEFPACKAGE MGL-PAX:MACRO"
  [445d]: #x-28GEB-2EMIXINS-3APOINTWISE-MIXIN-20CLASS-29 "GEB.MIXINS:POINTWISE-MIXIN CLASS"
  [4850]: http://www.lispworks.com/documentation/HyperSpec/Body/t_kwd.htm "KEYWORD TYPE"
  [4938]: #x-28GEB-2EMIXINS-3A-40MIXIN-EXAMPLES-20MGL-PAX-3ASECTION-29 "Mixins Examples"
  [493b]: #x-28GEB-3AMCAR-20GENERIC-FUNCTION-29 "GEB:MCAR GENERIC-FUNCTION"
  [4ffa]: #x-28GEB-2EUTILS-3A-40GEB-UTILS-MANUAL-20MGL-PAX-3ASECTION-29 "Geb Utilities"
  [58a9]: #x-28GEB-2EMIXINS-3ATO-POINTWISE-LIST-20GENERIC-FUNCTION-29 "GEB.MIXINS:TO-POINTWISE-LIST GENERIC-FUNCTION"
  [592c]: http://www.lispworks.com/documentation/HyperSpec/Body/f_list_.htm "LIST FUNCTION"
  [5d9d]: #x-28GEB-3A-40GEB-CATEGORIES-20MGL-PAX-3ASECTION-29 "Core Categories"
  [6228]: #x-28GEB-3A-40GEB-API-20MGL-PAX-3ASECTION-29 "api"
  [6380]: #x-28GEB-3A-2ASO1-2A-20VARIABLE-29 "GEB:*SO1* VARIABLE"
  [718e]: #x-28GEB-3ASUBSTOBJ-20TYPE-29 "GEB:SUBSTOBJ TYPE"
  [723a]: #x-28GEB-2EMIXINS-3A-40MIXINS-20MGL-PAX-3ASECTION-29 "Mixins"
  [74ab]: http://www.lispworks.com/documentation/HyperSpec/Body/f_car_c.htm "CADR FUNCTION"
  [7e58]: http://www.lispworks.com/documentation/HyperSpec/Body/t_class.htm "CLASS CLASS"
  [7f9f]: http://www.lispworks.com/documentation/HyperSpec/Body/t_symbol.htm "SYMBOL TYPE"
  [8311]: #x-28GEB-DOCS-2FDOCS-3A-40IDRIS-20MGL-PAX-3ASECTION-29 "Geb's Idris Code"
  [8bb8]: http://www.lispworks.com/documentation/HyperSpec/Body/f_car_c.htm "CADDR FUNCTION"
  [8c99]: http://www.lispworks.com/documentation/HyperSpec/Body/f_car_c.htm "CAR FUNCTION"
  [8fa5]: #x-28GEB-DOCS-2FDOCS-3A-40INSTALLATION-20MGL-PAX-3ASECTION-29 "installation"
  [96d0]: http://www.lispworks.com/documentation/HyperSpec/Body/f_equal.htm "EQUAL FUNCTION"
  [98f9]: http://www.lispworks.com/documentation/HyperSpec/Body/t_list.htm "LIST TYPE"
  [9bc5]: #x-28GEB-DOCS-2FDOCS-3A-40LINKS-20MGL-PAX-3ASECTION-29 "Links"
  [9bcb]: #x-28GEB-TEST-3A-40GEB-TEST-MANUAL-20MGL-PAX-3ASECTION-29 "Testing"
  [9f7a]: #x-28GEB-3A-2ASO0-2A-20VARIABLE-29 "GEB:*SO0* VARIABLE"
  [a17b]: #x-28GEB-3A-40GEB-EXAMPLES-20MGL-PAX-3ASECTION-29 "Examples"
  [a7d5]: #x-28GEB-DOCS-2FDOCS-3A-40LOADING-20MGL-PAX-3ASECTION-29 "loading"
  [a802]: http://www.lispworks.com/documentation/HyperSpec/Body/t_std_ob.htm "STANDARD-OBJECT TYPE"
  [ada9]: #x-28GEB-DOCS-2FDOCS-3A-40MORPHISMS-20MGL-PAX-3ASECTION-29 "Morphisms"
  [b26a]: #x-28GEB-3A-40GEB-ACCESSORS-20MGL-PAX-3ASECTION-29 "Accessors"
  [b9c1]: http://www.lispworks.com/documentation/HyperSpec/Body/t_seq.htm "SEQUENCE TYPE"
  [bf07]: http://www.lispworks.com/documentation/HyperSpec/Body/f_export.htm "EXPORT FUNCTION"
  [c111]: #x-28GEB-2EMIXINS-3AOBJ-EQUALP-20GENERIC-FUNCTION-29 "GEB.MIXINS:OBJ-EQUALP GENERIC-FUNCTION"
  [c1fb]: #x-28GEB-3A-40GEB-20MGL-PAX-3ASECTION-29 "The Geb Model"
  [c2e9]: #x-28GEB-DOCS-2FDOCS-3A-40MODEL-20MGL-PAX-3ASECTION-29 "Categorical Model"
  [c721]: http://www.lispworks.com/documentation/HyperSpec/Body/f_equalp.htm "EQUALP FUNCTION"
  [ca6e]: #x-28GEB-3A-40GEB-SUBSTMU-20MGL-PAX-3ASECTION-29 "Subst Obj"
  [d5d3]: #x-28GEB-2EMIXINS-3A-40POINTWISE-20MGL-PAX-3ASECTION-29 "Pointwise Mixins"
  [dbe7]: #x-28GEB-DOCS-2FDOCS-3A-40OBJECTS-20MGL-PAX-3ASECTION-29 "Objects"
  [e5d9]: #x-28GEB-3ASUBSTMORPH-20TYPE-29 "GEB:SUBSTMORPH TYPE"
  [ffb7]: #x-28GEB-3A-40GEB-SUBSTMORPH-20MGL-PAX-3ASECTION-29 "Subst Morph"

* * *
###### \[generated by [MGL-PAX](https://github.com/melisgl/mgl-pax)\]
