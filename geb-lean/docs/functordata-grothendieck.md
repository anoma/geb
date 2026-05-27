<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [FunctorData, Grothendieck, and Iterated Schemas](#functordata-grothendieck-and-iterated-schemas)
  - [Overview](#overview)
  - [Part 1: FunctorData and the flattening equivalence](#part-1-functordata-and-the-flattening-equivalence)
    - [J as a schema for categorical structure](#j-as-a-schema-for-categorical-structure)
    - [FunctorData-valued functors as copresheaves](#functordata-valued-functors-as-copresheaves)
    - [The reflective embedding](#the-reflective-embedding)
  - [Part 2: Generalized Grothendieck construction](#part-2-generalized-grothendieck-construction)
    - [The construction](#the-construction)
    - [Connection to PshInternalCat](#connection-to-pshinternalcat)
  - [Part 3: Iterated schemas and n-fold structure](#part-3-iterated-schemas-and-n-fold-structure)
    - [Internal categories in J-copresheaves](#internal-categories-in-j-copresheaves)
    - [The iteration](#the-iteration)
    - [Reflective tower](#reflective-tower)
    - [The fixed point: J^ω](#the-fixed-point-j%5E%CF%89)
  - [Part 4: Comparison with established approaches](#part-4-comparison-with-established-approaches)
    - [n-fold categories and multisimplicial sets](#n-fold-categories-and-multisimplicial-sets)
    - [Globular vs cubical/product approach](#globular-vs-cubicalproduct-approach)
    - [The ω-fold limit](#the-%CF%89-fold-limit)
  - [Part 5: Avenues for investigation](#part-5-avenues-for-investigation)
    - [A. Implement `toFunctorDataFunctor`](#a-implement-tofunctordatafunctor)
    - [B. Formalize the currying equivalence](#b-formalize-the-currying-equivalence)
    - [C. Formalize the double schema](#c-formalize-the-double-schema)
    - [D. Formalize the n-fold iteration](#d-formalize-the-n-fold-iteration)
    - [E. Investigate the Segal condition analogue](#e-investigate-the-segal-condition-analogue)
    - [F. Explore the fixed point `J^ω`](#f-explore-the-fixed-point-j%5E%CF%89)
    - [G. Compare with the globular approach](#g-compare-with-the-globular-approach)
    - [H. Connections (exchange laws)](#h-connections-exchange-laws)
  - [References](#references)
    - [Internal to this project](#internal-to-this-project)
    - [External: n-fold categories and multisimplicial sets](#external-n-fold-categories-and-multisimplicial-sets)
    - [External: globular approach](#external-globular-approach)
    - [External: cubical-globular comparison](#external-cubical-globular-comparison)
    - [Mathlib](#mathlib)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# FunctorData, Grothendieck, and Iterated Schemas

## Overview

This document describes three layers of structure built
on `CategoryJudgments.Obj` (abbreviated `J` throughout):

1. The equivalence between `FunctorData`-valued functors
   and copresheaves on a product category (the
   "flattening" equivalence).
2. The generalization of the internal
   presheaf--Grothendieck equivalence from `Cat`-valued
   to `FunctorData`-valued functors.
3. The iteration of "internal category in copresheaves
   on `J`" producing n-fold schemas (copresheaves on
   `Jⁿ`), with a fixed point at `J^ω`.

---

## Part 1: FunctorData and the flattening equivalence

### J as a schema for categorical structure

The category `J = CategoryJudgments.Obj` has four
objects:

```text
obj   — the type of objects
mor   — the type of morphisms
id    — identity witnesses
comp  — composition witnesses
```

and morphisms encoding structural relationships:

```text
dom : mor → obj       (source of a morphism)
cod : mor → obj       (target of a morphism)
idMor : id → mor      (identity morphism assignment)
idObj : id → obj      (underlying object of identity)
left : comp → mor     (first morphism in a composite)
right : comp → mor    (second morphism in a composite)
composite : comp → mor (the composite morphism)
```

with conditions `h_id_endo`, `h_comp_match`,
`h_comp_dom`, `h_comp_cod` ensuring structural
compatibility.

A `FunctorData(Type w)` — equivalently, a copresheaf
`J ⥤ Type w` — assigns a type to each of these four
roles and functions between them respecting the
structural relationships.  This is the data of a
"proto-category": objects, morphisms, identities, and
compositions, but without the category axioms
(associativity, identity laws).

### FunctorData-valued functors as copresheaves

A functor `F : Cᵒᵖ ⥤ FunctorData(Type w)` assigns to
each stage `c : Cᵒᵖ` a proto-category `F(c)`, with
restriction maps preserving the structure.

Via the equivalence
`FunctorData(Type w) ≅ (J ⥤ Type w)`:

```text
[Cᵒᵖ, FunctorData(Type w)]
  ≅ [Cᵒᵖ, [J, Type w]]
  ≅ [Cᵒᵖ × J, Type w]
```

The second step uses currying.  A FunctorData-valued
functor on `Cᵒᵖ` is therefore the same as a copresheaf
on the product category `Cᵒᵖ × J`.  The four components
of `J` decompose the copresheaf into families:

```text
F(c, obj)  = type of objects at stage c
F(c, mor)  = type of morphisms at stage c
F(c, id)   = identity witnesses at stage c
F(c, comp) = composition witnesses at stage c
```

### The reflective embedding

The adjunction `LFunctor ⊣ PhiFunctor` relates
`FunctorData(Type)` and `BundledOverCategoryData`
(equivalent to `Cat`):

```text
LFunctor : FunctorData(Type u) → BundledOverCategoryData
PhiFunctor : BundledOverCategoryData → FunctorData(Type u)
```

`PhiFunctor` is fully faithful
(`phiFunctor_reflective`), making `Cat` a reflective
subcategory of `FunctorData(Type)`.  The reflection
`LFunctor` sends a proto-category to the free category
on its morphism data, quotiented by the identity and
composition relations.

This adjunction lifts pointwise to functor categories
(`CatValuedFunctor.lean`):

```text
lWhiskering Cᵒᵖ  ⊣  phiWhiskering Cᵒᵖ
```

with `phiWhiskering_reflective`.

---

## Part 2: Generalized Grothendieck construction

### The construction

Given `F : Cᵒᵖ ⥤ FunctorData(Type u)`:

1. Compose with `LFunctor` (and `overToCatFunctor`) to
   obtain `reflectToCat F : Cᵒᵖ ⥤ Cat`.
2. Form `Grothendieck (reflectToCat F)`, the total
   category.
3. The equivalence `pshInternalGrothendieckEquiv`
   (applied to the corresponding internal category)
   gives internal presheaves ≌ copresheaves on the
   Grothendieck category.

### Connection to PshInternalCat

For `X : PshInternalCat C`, the externalization
`externalize X : Cᵒᵖ ⥤ Cat` factors through
`FunctorData(Type w)`.

**Extract FunctorData.** At each `c : Cᵒᵖ`, the fiber
data of `X` gives a `FunctorData(Type w)`:

```text
toFunctorDataFunctor X : Cᵒᵖ ⥤ FunctorData(Type w)
```

where `(toFunctorDataFunctor X).obj c` has:

- `objC = fiberObj X c`
- `morC = fiberMor X c`
- `dom = fiberSrc X c`, `cod = fiberTgt X c`
- `idC = fiberObj X c` (one identity per object)
- `idMor = fiberId X c`
- `compC = fiberCompPairs X c`
- `left`, `right`, `composite` from the pullback
  projections and `fiberComp`

**Image of Phi.** Since `X` is an internal category
(not merely a proto-category), each fiber satisfies the
category axioms.  The FunctorData at each stage
therefore lies in the image of `PhiFunctor` —
equivalently, the reflection `L` recovers the original
category:

```text
reflectToCat (toFunctorDataFunctor X) ≅ externalize X
```

**Grothendieck compatibility.** The Grothendieck
constructions agree:

```text
Grothendieck (reflectToCat (toFunctorDataFunctor X))
  ≅ Grothendieck (externalize X) = X.groth
```

---

## Part 3: Iterated schemas and n-fold structure

### Internal categories in J-copresheaves

An internal category in `[J, Type]` (the category of
J-copresheaves, i.e., `FunctorData(Type)`) is, by our
externalization (`PshInternalCat` with `C = Jᵒᵖ`), a
functor `J ⥤ Cat`.  A functor `J ⥤ Cat` is the same as
`FunctorData(Cat)`: a proto-category where each
component is itself a category.

By the flattening equivalence:

```text
FunctorData(Cat)
  ≅ FunctorData([J, Type])
  ≅ [J, [J, Type]]
  ≅ [J², Type]
```

An internal category in `[J, Type]` — a "double
schema" — is a copresheaf on `J² = J × J`.

This `J²` has 16 objects, indexed by pairs
`(j₁, j₂)` with `j₁, j₂ ∈ {obj, mor, id, comp}`.
The outer index represents the "double category" level
(objects vs morphisms vs identities vs compositions of
the internal category), and the inner index represents
the categorical structure within each of those.

### The iteration

Iterating "internal category in copresheaves on the
previous level" produces:

```text
Level 0:  [J⁰, Type] = [1, Type] = Type
Level 1:  [J¹, Type] = [J, Type] ≅ FunctorData(Type)
Level 2:  [J², Type] ≅ FunctorData(FunctorData(Type))
Level 3:  [J³, Type] ≅ FunctorData³(Type)
  ...
Level n:  [Jⁿ, Type]
```

| Level | Schema category | Component types |
| ----- | -------------- | --------------- |
| 0 | `1` | 1 |
| 1 | `J` | 4 |
| 2 | `J²` | 16 |
| 3 | `J³` | 64 |
| n | `Jⁿ` | 4ⁿ |

Each level adds one copy of `J` to the product.  An
element of `Jⁿ` is an n-tuple from
`{obj, mor, id, comp}`, and the copresheaf assigns a
type to each such tuple.

### Reflective tower

At each level, there is a tower of reflections stripping
away "proto" structure.  For `[Jⁿ, Type]`:

```text
[Jⁿ, Type]
  ⊃ [Jⁿ⁻¹, Cat]       (reflect level n)
  ⊃ [Jⁿ⁻², 2-Cat]     (reflect levels n, n-1)
  ...
  ⊃ n-FoldCat          (reflect all levels)
```

Each step applies the reflection `L` at one level,
turning proto-categorical data at that level into actual
categorical structure.  The innermost subcategory
(`n-FoldCat`) consists of the actual n-fold categories
in the sense of Ehresmann.

### The fixed point: J^ω

The fixed-point equation for the iteration
`S ↦ [J, S]` is `S ≅ [J, S]`.  Setting
`S = [K, Type]`:

```text
[K, Type] ≅ [J × K, Type]
```

so `K ≅ J × K`.  The solution is
`K = J^ω = ∏_{n ∈ ℕ} J`, the countable product, with
the shift isomorphism `J × J^ω ≅ J^ω`.

**Objects of `J^ω`** are infinite sequences
`(j₁, j₂, j₃, ...)` with each `jᵢ ∈ {obj, mor, id, comp}`.
There are `4^ℕ` (continuum-many) objects.  Morphisms
are componentwise.

A copresheaf on `J^ω` — an "ω-fold schema" — assigns a
type to each infinite sequence of judgment components.
The sequence encodes a path through infinitely many
levels of categorical structure:

```text
(obj, obj, obj, ...) — objects, all the way down
(mor, obj, obj, ...) — morphisms at level 1
(obj, mor, obj, ...) — objects of morphisms at level 2
(mor, mor, obj, ...) — morphisms of morphisms
(comp, mor, id, ...) — comp-witnesses of morphisms of
                       identity-witnesses of ...
```

The copresheaf category `[J^ω, Type]` is:

- a presheaf topos (all limits, colimits, exponentials)
- locally finitely presentable
- the limit `lim_n [Jⁿ, Type]` in the appropriate
  2-categorical sense

An object of `[J^ω, Type]` is a coherent family: a
copresheaf on `Jⁿ` for each `n`, compatible under the
restriction functors `[Jⁿ⁺¹, Type] → [Jⁿ, Type]`.

---

## Part 4: Comparison with established approaches

### n-fold categories and multisimplicial sets

The standard approach to n-fold categories in the
literature uses the simplex category `Δ` in place of
`J`.  An n-fold category corresponds to a presheaf on
`Δⁿ = Δ × Δ × ... × Δ` satisfying the **Segal
condition** in each variable.  The Segal condition
states that the nerve map is an isomorphism at each
level — it is what turns "proto-categorical" simplicial
data into actual categorical data.

The relationship between the two approaches:

| Aspect | Simplicial (`Δ`) | Judgment (`J`) |
| ------ | --------------- | -------------- |
| Objects | `[n]` for `n ≥ 0` | `obj, mor, id, comp` |
| Size | countably infinite | 4 objects |
| Identity/comp | encoded by degeneracy/face | explicit types |
| Axioms enforced by | Segal condition | reflection `L` |
| n-fold structure | `Δⁿ`-presheaves | `Jⁿ`-copresheaves |
| ω structure | `Δ^ω`-presheaves | `J^ω`-copresheaves |

The Segal condition on `Δⁿ`-presheaves plays the same
role as the reflective inclusion via `L` on
`Jⁿ`-copresheaves: both carve out actual n-fold
categories from within a larger category of
"proto-n-fold-categorical data."

### Globular vs cubical/product approach

There are two distinct traditions for higher categorical
structure:

**Globular.** Strict ω-categories use the globe
category `G` (objects = natural numbers, source/target
maps `σₙ, τₙ : n → n+1`).  Joyal's cell category
`Θ = Δ ≀ Δ ≀ ...` (iterated wreath product) extends
this to the weak setting.  In the globular approach,
an n-cell has a *single* source and target at level
n-1; the shape is tree-like.

**Cubical/product.** n-fold categories use `Δⁿ` (or
`J^n` in our setting).  An n-cell has *n independent*
source/target pairs, one for each direction.  The shape
is hypercube-like.

The wreath product `Θₙ = Δ ≀ Δ ≀ ... ≀ Δ` (n times)
is *not* the same as the product `Δⁿ`; there is a
functor `Δⁿ → Θₙ` but it is not an equivalence.
Bergner and Rezk proved that `Θₙ`-spaces and iterated
Segal spaces (on `(Δᵒᵖ)ⁿ`) give equivalent models of
(∞,n)-categories, despite having different domain
categories.

Al-Agl, Brown, and Steiner proved that strict globular
ω-categories are equivalent to cubical ω-categories
*with connections* (additional degeneracy operators
forcing exchange laws).  Plain n-fold categories
(without connections) do not enforce these exchange
laws and thus give a coarser structure.

Paoli's "weakly globular n-fold categories" bridge the
gap: they are n-fold categories (presheaves on `Δⁿ`)
with an additional *weak globularity condition*
(homotopy pullback conditions) that makes them
equivalent to Tamsamani-Simpson weak n-categories.

### The ω-fold limit

The iteration `Cat₀ = Set`, `Catₙ₊₁ = Cat(Catₙ)`
produces n-fold categories.  The limit in the globular
tradition gives strict ω-categories (via the enrichment
chain `0-Cat → 1-Cat → 2-Cat → ...`).

The limit in the cubical/product tradition — "ω-fold
categories" in the cubical sense — is a different,
coarser structure.  It is indexed by `Δ^ω` (or `J^ω` in
our setting) and does not enforce exchange laws between
levels.  This structure does not appear to have a
standard name or treatment in the literature.

---

## Part 5: Avenues for investigation

The following are directions that could be explored
further, in approximate order of concreteness.

### A. Implement `toFunctorDataFunctor`

Extract `FunctorData` from `PshInternalCat` and prove
the compatibility with `externalize` via the reflective
adjunction.  This is the content of Tasks 10-12 in the
implementation plan.

### B. Formalize the currying equivalence

Prove `[Cᵒᵖ, FunctorData(Type w)] ≌ [Cᵒᵖ × J, Type w]`
using `functorDataIsoCat` and mathlib's functor category
currying.  This establishes the flattening.

### C. Formalize the double schema

Define `PshInternalCat (Jᵒᵖ)` (internal categories in
J-copresheaves) and show the externalization gives
`J ⥤ Cat ≅ FunctorData(Cat)`.  Apply the flattening to
obtain the `[J², Type]` description.

### D. Formalize the n-fold iteration

Define the iteration `S(n+1) = [J, S(n)]` and prove
`S(n) ≅ [Jⁿ, Type]` by induction.  This requires
explicit universe management for the product `Jⁿ`.

### E. Investigate the Segal condition analogue

The Segal condition on `Δⁿ`-presheaves characterizes
actual n-fold categories among all presheaves.  Find the
analogous condition on `Jⁿ`-copresheaves.  This should
be related to the image of the reflective inclusion via
iterated `PhiFunctor`: a copresheaf on `Jⁿ` satisfies
the condition iff it lies in the (iterated) image of
`Φⁿ`.

### F. Explore the fixed point `J^ω`

Define `J^ω` as a category (the countable product) and
study the copresheaf topos `[J^ω, Type]`.  Prove the
fixed-point property `[J, [J^ω, Type]] ≅ [J^ω, Type]`.
Investigate whether the reflective tower stabilizes and
what "ω-fold categories" look like as a reflective
subcategory.

### G. Compare with the globular approach

Investigate the functor from `Jⁿ`-copresheaves to
globular sets (presheaves on `G`).  The source and
target morphisms in `J` correspond to the globular maps
`σₙ`, `τₙ` in `G`.  The identity and composition
components in `J` carry additional data not present in
`G`.  A precise comparison functor would clarify the
relationship between the "judgment schema" and
"globular" approaches to higher categorical structure.

### H. Connections (exchange laws)

The result of Al-Agl, Brown, and Steiner says strict
ω-categories ≅ cubical ω-categories *with connections*.
Determine what "connections" correspond to in the
`Jⁿ`-copresheaf setting.  These should be additional
morphisms or conditions in `Jⁿ` that enforce exchange
laws between levels.

---

## References

### Internal to this project

- `GebLean/CategoryJudgments.lean`: `Obj`, `FunctorData`,
  `NatTransData`, `functorDataIsoCat`
- `GebLean/CatJudgmentAdjunction.lean`: `LFunctor`,
  `PhiFunctor`, `phiFunctor_reflective`
- `GebLean/CatValuedFunctor.lean`: `phiWhiskering`,
  `lWhiskering`, `phiWhiskering_reflective`
- `GebLean/PshInternalExternalize.lean`: `externalize`,
  `fiberCategory`
- `GebLean/PshInternalPresheaf.lean`:
  `PshInternalPresheaf`, `PshInternalPresheafHom`
- `GebLean/PshInternalGrothendieck.lean`:
  `pshInternalGrothendieckEquiv`

### External: n-fold categories and multisimplicial sets

- Ehresmann, "Catégories et Structures" (Dunod, 1965).
  Original definition of multiple (n-fold) categories.
- Bastiani and Ehresmann, "Multiple functors I--IV,"
  Cahiers TGDC (1974--1979).  Limits, monoidal
  structure, and cartesian closure for n-fold
  categories.
- Fiore and Paoli, "A Thomason model structure on the
  category of small n-fold categories," Algebr. Geom.
  Topol. 10, 2010 (arXiv:0808.4108).  Quillen
  equivalence between n-fold categories and presheaves
  on `Δⁿ` with the n-fold Segal condition.
- Paoli, "Simplicial Methods for Higher Categories:
  Segal-type Models of Weak n-Categories," Springer,
  2019 (arXiv:1609.04072 for the underlying paper).
  Weakly globular n-fold categories as a model of weak
  n-categories.

### External: globular approach

- Batanin, "Monoidal globular categories as a natural
  environment for the theory of weak n-categories," Adv.
  Math. 136, 1998.  Weak ω-categories via contractible
  globular operads.
- Leinster, "Higher Operads, Higher Categories,"
  Cambridge, 2004.  Equivalent reformulation of
  Batanin's definition.
- Joyal, "Disks, duality, and Theta-categories," 1997
  (unpublished; see Berger's treatment in "A cellular
  nerve for higher categories," Adv. Math. 169, 2002).
  The cell category `Θ` and strict ω-categories as
  `Θ`-presheaves with the cellular Segal condition.

### External: cubical-globular comparison

- Al-Agl, Brown, and Steiner, "Multiple categories: the
  equivalence of a globular and a cubical approach,"
  Adv. Math. 170, 2002 (arXiv:math/0007009).  Strict
  ω-categories ≅ cubical ω-categories with connections.
- Bergner and Rezk, "Comparison of models for
  (∞,n)-categories, I," Geom. Topol. 17, 2013 and
  "Comparison of models for (∞,n)-categories, II,"
  J. Topol. 13, 2020 (arXiv:1204.2013, 1406.4182).
  Equivalence of Θₙ-spaces and n-fold Segal spaces.
- Bergner and Rezk, "Reedy categories and the
  Θ-construction," Math. Z. 274, 2013
  (arXiv:1110.1066).  Comparison of `Δⁿ` and `Θₙ`.

### Mathlib

- `Mathlib.CategoryTheory.Grothendieck`: the covariant
  Grothendieck construction used in
  `pshInternalGrothendieckEquiv`.
- `Mathlib.AlgebraicTopology.SimplicialSet.Basic`:
  simplicial sets (presheaves on `Δ`).
- `Mathlib.CategoryTheory.Products.Basic`: product
  categories.
- `Mathlib.CategoryTheory.Functor.Currying` (or
  equivalent): currying/uncurrying for functor
  categories.
