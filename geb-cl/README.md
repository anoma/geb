<a id="x-28GEB-DOCS-2FDOCS-3A-40INDEX-20MGL-PAX-3ASECTION-29"></a>
# The GEB Manual

## Table of Contents

- [1 Geb User manual][c1fb]
    - [1.1 Accessors][b26a]
    - [1.2 Types][49e9]
        - [1.2.1 Subst Obj][ca6e]
        - [1.2.2 Subst Morph][ffb7]
    - [1.3 Constructors][0c5c]
    - [1.4 api][6228]
    - [1.5 Examples][a17b]

###### \[in package GEB-DOCS/DOCS with nicknames EXAMPLE-DOCS\]
Welcome to the GEB project

<a id="x-28GEB-3A-40GEB-20MGL-PAX-3ASECTION-29"></a>
## 1 Geb User manual

###### \[in package GEB\]
The Main GEB model. Everything here relates directly to the
underlying machinery of GEB, or to abstractions that help extend
it.

<a id="x-28GEB-3A-40GEB-ACCESSORS-20MGL-PAX-3ASECTION-29"></a>
### 1.1 Accessors

These functions relate to grabbing slots out of the various GEBMOPRH and GEBOBJ types

<a id="x-28GEB-3AMCAR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCAR** *OBJECT*

<a id="x-28GEB-3AMCADR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCADR** *OBJECT*

<a id="x-28GEB-3AMCDR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCDR** *OBJECT*

<a id="x-28GEB-3AMCADDR-20GENERIC-FUNCTION-29"></a>
- [generic-function] **MCADDR** *OBJECT*

<a id="x-28GEB-3AOBJ-20GENERIC-FUNCTION-29"></a>
- [generic-function] **OBJ** *OBJECT*

<a id="x-28GEB-3ANAME-20GENERIC-FUNCTION-29"></a>
- [generic-function] **NAME** *OBJECT*

<a id="x-28GEB-3AFUNC-20GENERIC-FUNCTION-29"></a>
- [generic-function] **FUNC** *OBJECT*

<a id="x-28GEB-3A-40GEB-TYPES-20MGL-PAX-3ASECTION-29"></a>
### 1.2 Types

Types Surrounding the GEB categories

<a id="x-28GEB-3A-40GEB-SUBSTMU-20MGL-PAX-3ASECTION-29"></a>
#### 1.2.1 Subst Obj

This Category covers the objects of the GEB category. Every value
that is a [`SUBSTOBJ`][718e] is automatically lifted into a [`SUBSTMORPH`][e5d9] when a
`SUBSTMORPH` is expected.

The Type that encomposes the [`SUBSTOBJ`][718e] category

<a id="x-28GEB-3ASUBSTOBJ-20TYPE-29"></a>
- [type] **SUBSTOBJ**

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

<a id="x-28GEB-3A-40GEB-SUBSTMORPH-20MGL-PAX-3ASECTION-29"></a>
#### 1.2.2 Subst Morph

The moprhisms of the GEB category.

The Type that encomposes the SUBSTMOPRH category

<a id="x-28GEB-3ASUBSTMORPH-20TYPE-29"></a>
- [type] **SUBSTMORPH**

The various constructors that form the [`SUBSTMORPH`][e5d9] type

<a id="x-28GEB-3ACOMP-20TYPE-29"></a>
- [type] **COMP**

    Composition of morphism

<a id="x-28GEB-3AINIT-20TYPE-29"></a>
- [type] **INIT**

    The initial Morphism

<a id="x-28GEB-3ATERMINAL-20TYPE-29"></a>
- [type] **TERMINAL**

    The terminal Morhpism

<a id="x-28GEB-3ACASE-20TYPE-29"></a>
- [type] **CASE**

    Casing on objects

<a id="x-28GEB-3APAIR-20TYPE-29"></a>
- [type] **PAIR**

    Consing Morphisms

<a id="x-28GEB-3ADISTRIBUTE-20TYPE-29"></a>
- [type] **DISTRIBUTE**

    The distribute law

<a id="x-28GEB-3AINJECT-LEFT-20TYPE-29"></a>
- [type] **INJECT-LEFT**

<a id="x-28GEB-3AINJECT-RIGHT-20TYPE-29"></a>
- [type] **INJECT-RIGHT**

<a id="x-28GEB-3APROJECT-LEFT-20TYPE-29"></a>
- [type] **PROJECT-LEFT**

<a id="x-28GEB-3APROJECT-RIGHT-20TYPE-29"></a>
- [type] **PROJECT-RIGHT**

<a id="x-28GEB-3AFUNCTOR-20TYPE-29"></a>
- [type] **FUNCTOR**

<a id="x-28GEB-3AALIAS-20TYPE-29"></a>
- [type] **ALIAS**

    an alias for a geb object

<a id="x-28GEB-3A-40GEB-CONSTRUCTORS-20MGL-PAX-3ASECTION-29"></a>
### 1.3 Constructors

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
### 1.4 api

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
### 1.5 Examples

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


  [0c5c]: #x-28GEB-3A-40GEB-CONSTRUCTORS-20MGL-PAX-3ASECTION-29 "Constructors"
  [49e9]: #x-28GEB-3A-40GEB-TYPES-20MGL-PAX-3ASECTION-29 "Types"
  [6228]: #x-28GEB-3A-40GEB-API-20MGL-PAX-3ASECTION-29 "api"
  [6380]: #x-28GEB-3A-2ASO1-2A-20VARIABLE-29 "GEB:*SO1* VARIABLE"
  [718e]: #x-28GEB-3ASUBSTOBJ-20TYPE-29 "GEB:SUBSTOBJ TYPE"
  [9f7a]: #x-28GEB-3A-2ASO0-2A-20VARIABLE-29 "GEB:*SO0* VARIABLE"
  [a17b]: #x-28GEB-3A-40GEB-EXAMPLES-20MGL-PAX-3ASECTION-29 "Examples"
  [b26a]: #x-28GEB-3A-40GEB-ACCESSORS-20MGL-PAX-3ASECTION-29 "Accessors"
  [c1fb]: #x-28GEB-3A-40GEB-20MGL-PAX-3ASECTION-29 "Geb User manual"
  [ca6e]: #x-28GEB-3A-40GEB-SUBSTMU-20MGL-PAX-3ASECTION-29 "Subst Obj"
  [e5d9]: #x-28GEB-3ASUBSTMORPH-20TYPE-29 "GEB:SUBSTMORPH TYPE"
  [ffb7]: #x-28GEB-3A-40GEB-SUBSTMORPH-20MGL-PAX-3ASECTION-29 "Subst Morph"

* * *
###### \[generated by [MGL-PAX](https://github.com/melisgl/mgl-pax)\]
