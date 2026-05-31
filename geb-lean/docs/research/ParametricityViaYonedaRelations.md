# Parametricity via Yoneda Relations

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Overview](#overview)
- [Sources](#sources)
- [Reynolds/Wadler Parametricity](#reynoldswadler-parametricity)
  - [The relational interpretation of types](#the-relational-interpretation-of-types)
  - [Specialization to functions](#specialization-to-functions)
  - [Full relational parametricity vs. functional parametricity](#full-relational-parametricity-vs-functional-parametricity)
- [Paranaturality (our existing formalization)](#paranaturality-our-existing-formalization)
  - [Definition](#definition)
  - [Equivalence with span-based parametricity](#equivalence-with-span-based-parametricity)
  - [Relations and spans](#relations-and-spans)
  - [Where paranaturality is correct](#where-paranaturality-is-correct)
- [The Divergence](#the-divergence)
  - [Neumann's example](#neumanns-example)
  - [Formal separation](#formal-separation)
  - [What we know and don't know](#what-we-know-and-dont-know)
- [The Yoneda Relation Double Category](#the-yoneda-relation-double-category)
  - [Structure](#structure)
  - [How it relates to Reynolds](#how-it-relates-to-reynolds)
  - [Limits and colimits in the double category](#limits-and-colimits-in-the-double-category)
- [Toward a definition of parametricity](#toward-a-definition-of-parametricity)
  - [The idea](#the-idea)
  - [What must be defined](#what-must-be-defined)
  - [Test cases for correctness](#test-cases-for-correctness)
  - [Function-space relation lifting](#function-space-relation-lifting)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **Partially superseded.** The analysis of the
> Reynolds/Wadler correspondence here remains valid,
> but the framework has shifted from `PshRelSpanObj`
> copresheaves to `PshRelEdge C` (the edge category
> of presheaf relations) with its reflective embedding
> into `[WalkingSpan, PSh(C)]`.  See
> `.session/workstreams/parametric-copresheaf-topos.md`
> for the current framework and Wadler correspondence.

## Overview

This document analyzes the relationship between Reynolds/Wadler
parametric polymorphism and our Yoneda relation double category,
with the goal of defining a category-theoretic notion of
parametricity that:

1. Recovers Reynolds/Wadler parametricity for Set-based types
2. Generalizes beyond Set to an arbitrary category C
3. Differs from paranaturality where parametricity and
   paranaturality diverge
4. Agrees with paranaturality where paranaturality is correct

## Sources

- Wadler, "Theorems for free!" (1989) --
  `docs/.claude/wadler89-theorems-for-free.pdf`
- Maguire, "Review of Theorems for Free" --
  `https://reasonablypolymorphic.com/blog/theorems-for-free/`
- Neumann, "Paranatural Category Theory" and TYPES 2024 talk --
  `docs/updates-on-paranatural-category-theory-*.pdf`
- nLab, "Rel: Relations and spans" --
  `https://ncatlab.org/nlab/show/Rel#relations_and_spans`
- nLab, "Rel: In the double category of relations" --
  `https://ncatlab.org/nlab/show/Rel#in_the_double_category_of_relations`
- Codebase: `GebLean/ParamPoly.lean`,
  `GebLean/ParanaturalTopos.lean` (ParametricityDivergence
  section), `GebLean/YonedaRelDouble.lean`

## Reynolds/Wadler Parametricity

### The relational interpretation of types

Wadler's framework assigns to each type a relation between
its interpretations at two different type instantiations.
The construction is recursive on the type structure:

- **Base types** yield the identity relation.
- **Products** `A x B`: pairs are related iff each component
  is related.
- **Functions** `A -> B`: `(f, f')` are related iff for all
  `(x, x')` related in `A`, `(f x, f' x')` are related in
  `B`. This is contravariant in `A` and covariant in `B`.
- **Universal quantification** `forall X. F(X)`: `(g, g')` are
  related iff for every relation `R` between types `A` and
  `A'`, the instantiations `g_A` and `g'_{A'}` are related
  in `F(R)`.

The parametricity theorem states: every well-typed term `t : T`
satisfies `(t, t) in [[T]]`, where `[[T]]` is the relational
interpretation of `T`.

### Specialization to functions

When the relation `R` is specialized to be the graph of a
function `f : A -> A'` (i.e., `(x, x') in R` iff `x' = f x`):

- Product relations become `bimap`
- List relations become `map`
- Function relations become commuting squares:
  `f' . g = h . f` (i.e., naturality conditions)

This is the observation from the "Reasonably Polymorphic" blog
post: "relations specialized to functions become bifunctors"
and "the function relation becomes a naturality square."

### Full relational parametricity vs. functional parametricity

When specialized to functions, parametricity recovers
naturality. When using general (non-functional) relations,
parametricity gives strictly more information. For types
involving nested function spaces, the relational interpretation
correlates inputs and outputs through the relation in ways
that functional specialization cannot capture.

## Paranaturality (our existing formalization)

### Definition

A family `alpha : (I : C) -> F(I,I) -> G(I,I)` between
endoprofunctors is paranatural (`IsParanatural`) if it
preserves the diagonal compatibility condition: whenever
`d_0 in F(I_0, I_0)` and `d_1 in F(I_1, I_1)` satisfy

```text
F.rmap(f)(d_0) = F.lmap(f)(d_1)    in F(I_0, I_1)
```

for a morphism `f : I_0 -> I_1`, then their images under
`alpha` satisfy the same condition in `G`.

### Equivalence with span-based parametricity

The span-based `IsParamPoly` (from `ParamPoly.lean`), which
quantifies over all spans `(R, pi_1, pi_2)`, is equivalent
to paranaturality (`isParamPoly_iff_isParanatural`). The
reason: each span decomposes into two independent `DiagCompat`
conditions sharing a common witness, and paranaturality handles
each leg separately. There is no cross-leg interaction in the
span-based formulation.

### Relations and spans

There is a pseudofunctor `|-| : Span -> Rel` that sends a
span `X <- S -> Y` to its image relation in `X x Y`.
Concretely, a relation from `X` to `Y` is a subobject of
the terminal span `X <- X x Y -> Y`, and the pseudofunctor
extracts this subobject from any span. This pseudofunctor
preserves composition: `|R x_B S| = |R| . |S|`.

Our formalization works with both categories: spans (via
`PshProdOver`, which is a morphism into a product presheaf)
and relations (via `PshRel` = `Subfunctor`, which is a
sub-presheaf of the product). The projection
`pshProdOverToRel` from `PshProdOver` to `PshRel` is the
presheaf-level analogue of the pseudofunctor `|-|`.

The span-based `IsParamPoly` quantifies over all spans
`(R, pi_1, pi_2)`, while the relational parametricity
condition quantifies over all relations (= subfunctors of
the product). The pseudofunctor connecting these two
categories may give a route to relating the span-based and
relation-based formulations more precisely.

### Where paranaturality is correct

Paranaturality gives the right notion of morphism for:

- **Initial algebras** (`StructuralEnd` of the algebra
  profunctor)
- **Terminal coalgebras** (`StructuralCoend` of the coalgebra
  profunctor)
- **Dinatural numbers** (endo-transformations of the hom
  profunctor)

In these cases, paranaturality agrees with what Reynolds
parametricity would predict.

## The Divergence

### Neumann's example

For the type `phi : forall X. ((X -> X) -> X) -> X`:

- **Source profunctor**: `P(a, b) = (b -> a) -> b`
  (formalized as `divSource`)
- **Target profunctor**: `Q(a, b) = b`
  (formalized as `divTarget = IdProf`)

The two conditions are:

- **DivParanatural**: For all `f : I -> J`, `p`, `q`, if
  for all `r : J -> I`, `f(p(r . f)) = q(f . r)`, then
  `f(phi_I(p)) = phi_J(q)`.

- **DivParametric**: For all `f : I -> J`, `p`, `q`, if
  for all `h : I -> I`, `k : J -> J` with `f . h = k . f`,
  `f(p(h)) = q(k)`, then `f(phi_I(p)) = phi_J(q)`.

The paranaturality hypothesis tests pairs `(r . f, f . r)`,
while the parametricity hypothesis tests all pairs `(h, k)`
with `f . h = k . f`. The paranaturality hypothesis is
weaker (admits more input pairs), making paranaturality the
stronger condition on `phi`.

### Formal separation

`divApplyId` (the function `fun I p => p id`) is:

- **Parametric** (`divApplyId_parametric`): trivially, since
  `h = id, k = id` satisfies `f . id = id . f`.
- **Not paranatural** (`divApplyId_not_paranatural`): witnessed
  by `I = Bool`, `f = const true`, `p = q = (. false)`.

Thus: **paranaturality implies parametricity, but not
conversely**, for this type.

### What we know and don't know

Paranaturality is a condition on profunctors that does not
capture Reynolds parametricity: `divApplyId` is parametric
but not paranatural.

Whether there exists some other profunctor-level condition
(not paranaturality, but some other notion of transformation
between profunctors) that does capture parametricity is an
open question. It is conceivable that parametricity depends
on the syntactic structure of the type expression in a way
that no condition on profunctors alone can recover. It is
also conceivable that the profunctor carries enough
information and we have not yet found the right condition.
We do not currently have evidence for either possibility.

The profunctors in the divergence example (`divSource` with
`P(a, b) = (b -> a) -> b`) are genuinely different from
those in the cases where paranaturality is correct (e.g.,
the hom profunctor `Hom(a, b) = a -> b`). Whether this
difference is sufficient to distinguish the parametricity
conditions at the profunctor level remains to be determined.

## The Yoneda Relation Double Category

### Structure

From `YonedaRelDouble.lean`:

- **Objects**: objects of `C`
- **Horizontal morphisms**: morphisms of `C`
  (`homSetOfQuiver C`)
- **Vertical morphisms**: Yoneda relations
  `YonedaRel X Y = Skeleton(YonedaProdOver X Y)`
- **2-cells**: `relRelated f f' R S` -- a `Prop`-valued
  lifting condition

A Yoneda relation from `X` to `Y` is an isomorphism class
of morphisms `G -> yoneda(X) x yoneda(Y)` in the presheaf
category `PSh(C)`. This is a presheaf-level analogue of a
relation between sets: where a relation `R` between sets
`X` and `Y` is a subset of `X x Y`, a Yoneda relation is a
sub-presheaf (up to isomorphism) of the product presheaf.

### How it relates to Reynolds

In Reynolds' framework for Set:

- A **relation** `R` between sets `X` and `Y` is a subset
  `R` of `X x Y`, equivalently a function `R -> X x Y`.
- A morphism `f : X -> X'` and relation `R` between `X, Y`
  and `S` between `X', Y'` are **related** when there exists
  a function `phi : R -> S` making the square commute:
  `phi; S.proj = R.proj; (f x f')`.

This is exactly the structure of `YonedaProdOverRelated`:
the existence of a presheaf morphism `phi : R.left -> S.left`
such that `phi >> S.hom = R.hom >> yonedaProdMap f f'`.

The Yoneda relation double category thus provides a
categorical generalization of the "relations and commuting
squares" structure that underlies Reynolds parametricity.

### Limits and colimits in the double category

The bicategory Rel has limited (co)limit structure, but
when embedded in the double category RRel (with sets as
objects, functions as horizontal morphisms, relations as
vertical morphisms, and commuting squares as 2-cells), the
double category has all double limits and colimits. In
particular:

- The cartesian product `a x b : X x Y -> X' x Y'`
  serves as a product in the double category.
- The disjoint sum `a + b : X + Y -> X' + Y'` serves as
  a coproduct in the double category.

This is an instance of a general phenomenon: bicategories
of spans, cospans, relations, and profunctors may have
limited (co)limits, but their embeddings in double
categories (with the same objects, strict morphisms, same
loose morphisms, and suitable double cells) can have all
limits and colimits.

Our presheaf relation double category (`PshRelDouble`)
is the presheaf-level analogue of RRel. The existence
of double categorical (co)limits may be relevant for
constructing parametric functors, since the relational
interpretation of type constructors (products, coproducts,
function spaces) may correspond to (co)limit constructions
in the double category.

## Toward a definition of parametricity

### The idea

Given an endoprofunctor `F : C^op x C -> Type v` and a
type expression `T` built from `F` using type constructors
(function spaces, products, universal quantification), the
relational interpretation `[[T]]` should assign to each
pair of Yoneda relations a new Yoneda relation, in a way
that respects the type structure.

A family `alpha : (I : C) -> F(I,I) -> G(I,I)` is
**parametric** if for every Yoneda relation `R`, the
appropriate 2-cell (commuting square in the double category)
exists.

### What must be defined

1. **Relation lifting**: For each type constructor (products,
   function spaces, universal quantification), define how
   Yoneda relations are lifted. The lifting of function
   spaces is where paranaturality and parametricity diverge.

2. **Parametric family**: A family that admits 2-cells for
   all Yoneda relations, not just those arising from
   morphisms.

3. **Correspondence with Reynolds**: When `C = Set`, the
   Yoneda relations are ordinary relations, and the
   construction should recover Reynolds' relational
   interpretation.

### Test cases for correctness

Any proposed definition must satisfy:

1. **Divergence test**: For the type
   `((X -> X) -> X) -> X`, `divApplyId` (= `fun I p => p id`)
   should be parametric. Any paranatural-but-not-parametric
   families should fail the parametricity condition.

2. **Initial algebra test**: For the algebra profunctor,
   parametricity should agree with paranaturality (both give
   the initial algebra as the structural end).

3. **Terminal coalgebra test**: For the coalgebra profunctor,
   parametricity should agree with paranaturality (both give
   the terminal coalgebra as the structural coend).

4. **Dinatural number test**: For endo-transformations of the
   hom profunctor, parametricity should agree with
   paranaturality.

### Function-space relation lifting

The function-space lifting is the point where the double
category potentially resolves the divergence. In Reynolds'
framework, the relation `[[A -> B]]` at relations
`R_A, R_B` is:

```text
(f, f') in [[A -> B]](R_A, R_B)
  iff
for all (x, x') in R_A, (f x, f' x') in R_B
```

This correlates the domain relation with the codomain
relation through the function. In the Yoneda relation
setting, this should correspond to a construction on
`YonedaProdOver` objects: given relations `R_A` on `X, X'`
and `R_B` on `Y, Y'`, the function-space relation on
`(X -> Y), (X' -> Y')` is built from `R_A` and `R_B`
using the internal hom of the presheaf category.

The presheaf category is a topos, so it has an internal
hom `[R_A, R_B]` that is the presheaf-level analogue of
the function-space relation. Composing this with the
appropriate projections into the Yoneda product presheaf
gives a `YonedaProdOver` object, hence a Yoneda relation.

This is the construction that differs from the span-based
`ProfRelLift`: the function-space lifting builds a genuinely
new relation that captures the correlation between inputs
and outputs, rather than decomposing into independent legs.
