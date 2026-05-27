<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Paranatural Topos Research](#paranatural-topos-research)
  - [Question (historical)](#question-historical)
  - [Background](#background)
    - [Profunctors with natural transformations](#profunctors-with-natural-transformations)
    - [Profunctors with paranatural transformations](#profunctors-with-paranatural-transformations)
    - [Reduction to natural transformations](#reduction-to-natural-transformations)
  - [Literature Survey](#literature-survey)
    - [Paranatural transformations do not form a topos](#paranatural-transformations-do-not-form-a-topos)
    - [Neumann's di-Yoneda lemma](#neumanns-di-yoneda-lemma)
    - [Twisted arrow categories and ends](#twisted-arrow-categories-and-ends)
    - [The full subcategory I of identity arrows](#the-full-subcategory-i-of-identity-arrows)
    - [Kan extension formula](#kan-extension-formula)
    - [Alternative: inclusion into copresheaves](#alternative-inclusion-into-copresheaves)
    - [Tambara modules as presheaves](#tambara-modules-as-presheaves)
    - [Factorization categories as reflective subcategories](#factorization-categories-as-reflective-subcategories)
    - [Mathlib infrastructure](#mathlib-infrastructure)
  - [Analysis](#analysis)
    - [Limits in the paranatural category](#limits-in-the-paranatural-category)
    - [Colimits in the paranatural category](#colimits-in-the-paranatural-category)
    - [Cartesian closure](#cartesian-closure)
    - [The diagonalization monad](#the-diagonalization-monad)
    - [Connections to formalized infrastructure](#connections-to-formalized-infrastructure)
  - [Open Questions](#open-questions)
  - [Experimental Strategy](#experimental-strategy)
  - [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Paranatural Topos Research

> **Resolved.** The answer is: `PshRelEdge C` is a
> quasitopos (separated presheaves in the presheaf
> topos `[WalkingSpan, PSh(C)]`).  The ambient
> presheaf topos is the exact completion.  The former
> search for a topos of profunctors with paranatural
> morphisms was resolved by the copresheaf/edge
> category approach.  See
> `.session/workstreams/parametric-copresheaf-topos.md`.

## Question (historical)

Is there a subcategory of profunctors with paranatural
transformations as morphisms that forms a topos?

## Background

### Profunctors with natural transformations

The category `[C^op x C, Type v]` of `Type v`-valued
profunctors on `C` with natural transformations is a
presheaf topos (presheaves on `(C^op x C)^op`).

### Profunctors with paranatural transformations

Paranatural transformations between profunctors
`H, G : C^op x C -> Type v` consist of families
`phi_c : H(c, c) -> G(c, c)` satisfying an
"extraordinary naturality" condition mixing covariant
and contravariant actions.

### Reduction to natural transformations

Via the comprehensive factorization and weighted-limit
machinery:

```text
Paranat H G ≃
  (wedgeWeight H ⟶ profunctorOnTwistedArrow C G)
```

where `wedgeWeight H : Tw(C)^op -> Type v` and
`profunctorOnTwistedArrow C G : Tw(C)^op -> Type v`.

## Literature Survey

### Paranatural transformations do not form a topos

The category of difunctors `C^op x C -> Set` with
paranatural transformations as morphisms is not
Cartesian closed in general (Uustalu 2010; noted on
nLab "strong dinatural transformation"). Since every
topos is Cartesian closed, this category is not a topos.

Paranatural transformations do compose (Mulry 1992,
Pare-Roman 1998, Neumann 2023), unlike the weaker
dinatural transformations.

### Neumann's di-Yoneda lemma

Neumann's "Paranatural Category Theory"
(arXiv:2307.09289) claims a di-Yoneda lemma for the
category of difunctors with paranaturals. However,
Neumann later discovered an error in the proof; the
di-Yoneda lemma as stated is not true. This error
invalidates the hom-objects derived from it.

Since `paranatWeightedLimitEquiv` reduces paranaturals
to natural transformations in the presheaf topos
`[Tw(C)^op, Type v]`, we can apply the standard
Yoneda lemma there instead.

### Twisted arrow categories and ends

The twisted arrow category `Tw(C)` is the category
of elements of the hom-functor `Hom : C^op x C -> Set`.
The projection `pi : Tw(C) -> C^op x C` is a discrete
opfibration. Ends over `C` are limits over `Tw(C)`:

```text
int_c F(c, c) = lim_{Tw(C)} F . pi
```

(Mac Lane, CWM, exercise IX.6.3; Loregian,
(Co)end Calculus, 2021.)

### The full subcategory I of identity arrows

There is no functor `C -> Tw(C)` sending `c` to `id_c`:
a morphism `m : c -> d` in `C` would need to produce a
morphism `id_c -> id_d` in `Tw(C)`, which consists of a
pair `(alpha : d -> c, beta : c -> d)` with
`beta . alpha = id_d`. A single morphism `m` provides
only one direction, not both.

Instead, the identity arrows `{id_c | c in C}` form a
full subcategory `I` of `Tw(C)`, with inclusion functor
`iota : I -> Tw(C)`. The morphisms `Hom_I(id_c, id_d)`
are section-retraction pairs `(alpha, beta)` with
`beta . alpha = id_d`. There is a non-full, non-faithful
functor `p : I -> C` sending `(alpha, beta) |-> beta`.

The comma category `iota/f` for `f : a -> b` has objects
that are factorizations of `f` through some `c`:
`Hom_{Tw(C)}(id_c, f) = {(alpha, beta) | f = beta . alpha}`.
This is the factorization category of `f`.

### Kan extension formula

The left Kan extension along `iota` gives:

```text
Lan_iota(F)(f : a -> b)
  = colim_{(id_c, sigma : id_c -> f)} F(id_c)
  = colim_{factorizations of f through c} F(id_c)
```

This is a "diagonalized density formula": it builds
a presheaf on `Tw(C)^op` from its values on identity
arrows, weighted by factorization data.

### Alternative: inclusion into copresheaves

There is an inclusion from `C` into copresheaves on
`Tw(C)^op` via Yoneda followed by domain projection:
`c |-> Hom_{Tw(C)}(-, id_c)`. This avoids the
nonexistent functorial inclusion `C -> Tw(C)` while
still allowing diagonal data to be expressed.

### Tambara modules as presheaves

Pastro and Street (2008) show that for a monoidal
category `A`, the category of Tambara modules (profunctors
with a dinaturality condition involving monoidal actions)
is equivalent to a presheaf category `[DA, V]` where
`DA` is the "double" of `A`. This provides a template:
profunctors with a dinaturality condition can sometimes
equal presheaves on a suitable small category.

Clarke et al. (2021) establish that optics are what
Tambara modules are copresheaves over, giving another
instance of this pattern.

### Factorization categories as reflective subcategories

In our codebase (`Factorization.lean`), the
factorization category `Factorisation f` is a
reflective subcategory of `Over (twObjMk f)` in
`Tw(C)`. The reflector `overTwToFactorisation` sends
a twisted arrow over `f` to its canonical factorization.

The decorated factorization functor
`decFactFunctor F : Tw(C) -> Cat` (for
`F : Tw(C) -> Cat`) assigns to each twisted arrow
`tw` the category `DecFactObj F tw`, whose objects are
pairs (factorization of `twArr tw`, element of
`F(id_mid)`). A factorization of `f` through `mid` is
a morphism `id_mid -> f` in `Tw(C)`, so `DecFactObj F tw`
is the category of elements of the diagram
`(factorizations of f) -> Cat` sending
`(mid, iota, pi) |-> F(id_mid)`. This is exactly the
fiber of `Lan_iota(iota* F)` at `f`, where
`iota : I -> Tw(C)` is the full subcategory inclusion
of identity arrows.

The total category `TotalDecFactObj C F` (equivalently,
`TotalDecFactGrothendieck C F`) gathers all decorated
factorizations across all morphisms in `C`. It is the
total space of `Lan_iota(iota* F)` viewed as a
`Cat`-valued functor on `Tw(C)`.

### Mathlib infrastructure

Mathlib has the components for this investigation:

- `CategoryTheory.Functor.KanExtension.*`: Left/right
  Kan extensions, pointwise formulas, lan/ran functors,
  adjunctions `lan |- precomposition |- ran`.
- `CategoryTheory.Adjunction.Reflective`: Reflective
  subcategories via `Reflective` typeclass.
- `CategoryTheory.Sites.Grothendieck`: Grothendieck
  topologies.
- `CategoryTheory.Sites.Sheaf*`: Sheaf categories.
- `CategoryTheory.Topos.Classifier`: Subobject
  classifiers (`HasClassifier`).
- `CategoryTheory.Monoidal.Closed.*`: Cartesian closed
  categories via `MonoidalClosed`.

Mathlib does not have:

- A unified "ElementaryTopos" definition.
- The theorem that left-exact reflective subcategories
  of presheaf toposes are Grothendieck toposes.
- Discrete fibrations (not in mathlib; formalized in
  our `ComprehensiveFactorization.lean`).

## Analysis

### Limits in the paranatural category

Limits exist and are computed pointwise. Since
`profOnTwArr` (restriction along `pi`) preserves
limits, and `Nat(F, -)` preserves limits:

```text
Paranat(H, prod_i G_i)
  = Nat(wedgeWeight H, profOnTwArr(C, prod_i G_i))
  = Nat(wedgeWeight H, prod_i profOnTwArr(C, G_i))
  = prod_i Nat(wedgeWeight H, profOnTwArr(C, G_i))
  = prod_i Paranat(H, G_i)
```

### Colimits in the paranatural category

Colimits are less clear. The colimit of `H_i` in the
paranatural category would require a profunctor `G`
with `wedgeWeight G = colim_i wedgeWeight H_i` as
presheaves on `Tw(C)^op`. This requires the colimit
to stay in the image of `wedgeWeight`, which is the
subcategory of presheaves that factor through the
"twist" of `pi`. Restriction functors preserve limits
but not colimits in general, so the image may not be
closed under colimits.

### Cartesian closure

The internal hom in `[Tw(C)^op, Type v]` is:

```text
[F, G](f) = Nat(Y(f) x F, G)
```

For `F = profOnTwArr(C, H)` and `G = profOnTwArr(C, K)`,
the internal hom `[F, G]` is a presheaf on `Tw(C)^op`,
but it may not be in the image of `profOnTwArr`. If it
is not, then the paranatural category is not Cartesian
closed (consistent with Uustalu's result).

### The diagonalization monad

Let `iota : I -> Tw(C)` be the full subcategory
inclusion of identity arrows. The composite
`Lan_iota . iota*` on `[Tw(C)^op, Type v]` is an
idempotent monad if
`iota* . Lan_iota . iota* = iota*` (the counit of the
adjunction `Lan_iota |- iota*` is an iso on the
essential image of `Lan_iota`). The fixed points would
be "diagonally determined" presheaves.

If this monad is left-exact (preserves finite limits),
then by Giraud's theorem, the fixed-point subcategory
is a Grothendieck topos (sheaves for the corresponding
topology on `Tw(C)^op`).

The reflector "makes a presheaf diagonalizable" by
replacing `F(f)` with the colimit of `F(id_c)` over
all factorizations of `f` through `c`.

### Connections to formalized infrastructure

- The factorization category of `f` through `c` is
  `Hom_{Tw(C)}(id_c, f)`, already formalized as
  `Factorisation f`.
- The reflective inclusion of factorization categories
  into over-categories of `Tw(C)` is formalized as
  `factorisationToOverTw`.
- `decFactFunctor F` implements the fiberwise Kan
  extension: its value at `tw` is the category of
  elements of the Kan extension diagram, so
  `DecFactObj F tw` computes `Lan_iota(iota* F)(tw)` as
  a `Cat`-valued left Kan extension.
- `TotalDecFactObj C F` (equivalently
  `TotalDecFactGrothendieck C F`) is the total space
  of this Kan extension across all twisted arrows.
- Discrete (op)fibrations are formalized in
  `ComprehensiveFactorization.lean`.

## Open Questions

1. Is `Lan_iota . iota*` idempotent on
   `[Tw(C)^op, Type v]`?
2. If so, is it left-exact (preserves finite limits)?
3. Which profunctors `P` satisfy
   `profOnTwArr(C, P) =
    Lan_iota(iota* profOnTwArr(C, P))`?
4. Is the image of `profOnTwArr` closed under the
   topos operations of `[Tw(C)^op, Type v]`?
5. Can the Kan extension formula be related to the
   Tambara double construction of Pastro-Street?
6. Does the two-variable density formula
   `P(a,b) = int^c P(c,c) x Hom(a,c) x Hom(c,b)`
   hold for algebra/coalgebra profunctors?

## Experimental Strategy

Try to construct the topos operations (limits, colimits,
Cartesian closure, subobject classifier) for the
category of all profunctors with paranaturals:

1. Verify limits exist (expected to work).
2. Try colimits (may fail for non-diagonalizable
   profunctors).
3. Try internal hom (expected to fail in general,
   per Uustalu). Identify what goes wrong: the internal
   hom in `[Tw(C)^op, Type v]` likely leaves the image
   of `profOnTwArr`.
4. The failure mode of (3) may identify which profunctors
   are "closed under taking internal homs", pointing to
   the right subcategory.

## References

- Eilenberg-Kelly, "A generalization of the functorial
  calculus" (1966)
- Mulry, "Strong Monads, Algebras and Fixed Points"
  (1992)
- Pare-Roman, "Dinatural numbers" (JPAA 1998)
- Pastro-Street, "Doubles for monoidal categories"
  (arXiv:0711.1859, 2008)
- Uustalu, "Mendler-style Inductive Types,
  Categorically" (2010)
- Loregian, "(Co)end Calculus" (arXiv:1501.02503, 2021)
- McCusker-Santamaria, "Composing Dinatural
  Transformations" (arXiv:2007.07576, 2021)
- Clarke et al., "Profunctor Optics, a Categorical
  Update" (arXiv:2001.07488, 2021)
- Neumann, "Paranatural Category Theory"
  (arXiv:2307.09289, 2023; note: di-Yoneda proof has
  an error)
- Neumann-Licata, "Di- is for Directed"
  (arXiv:2409.10237, POPL 2026)
