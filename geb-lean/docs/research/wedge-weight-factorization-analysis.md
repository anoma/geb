# Wedge weight factorization and TypeExpr copresheaves

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Summary](#summary)
- [1. Factorization characterization of wedgeWeight](#1-factorization-characterization-of-wedgeweight)
  - [1.1. Definition recap](#11-definition-recap)
  - [1.2. General factorization characterization](#12-general-factorization-characterization)
  - [1.3. Specialization to AlgProf F](#13-specialization-to-algprof-f)
  - [1.4. Specialization to CoalgProf F](#14-specialization-to-coalgprof-f)
- [2. Identity twisted arrows and surjectivity](#2-identity-twisted-arrows-and-surjectivity)
- [3. Natural transformations from wedgeWeight to profunctorOnTwistedArrow](#3-natural-transformations-from-wedgeweight-to-profunctorontwistedarrow)
- [4. TypeExpr as a copresheaf](#4-typeexpr-as-a-copresheaf)
  - [4.1. Motivation](#41-motivation)
  - [4.2. Proposed recursive copresheaf](#42-proposed-recursive-copresheaf)
  - [4.3. Comparison with wedgeWeight](#43-comparison-with-wedgeweight)
  - [4.4. TypeExpr weight vs. parametric families](#44-typeexpr-weight-vs-parametric-families)
- [5. Dual characterization: cowedgeWeight](#5-dual-characterization-cowedgeweight)
  - [5.1. Definition](#51-definition)
  - [5.2. Factorization characterization](#52-factorization-characterization)
  - [5.3. Relationship to cowedge equivalence](#53-relationship-to-cowedge-equivalence)
- [6. Formalization plan](#6-formalization-plan)
  - [Step 1: Factorization description at general twisted arrows](#step-1-factorization-description-at-general-twisted-arrows)
  - [Step 2: Define typeExprWeight recursively](#step-2-define-typeexprweight-recursively)
  - [Step 3: Comparison natural transformation](#step-3-comparison-natural-transformation)
- [7. Composition analysis of relInterp (RelInterpComposition.lean)](#7-composition-analysis-of-relinterp-relinterpcompositionlean)
  - [7.1. Motivation](#71-motivation)
  - [7.2. Arrow-free types and graph relations](#72-arrow-free-types-and-graph-relations)
  - [7.3. Arrow case: conditional composition](#73-arrow-case-conditional-composition)
  - [7.4. Counterexample: decomposition fails for `X -> X`](#74-counterexample-decomposition-fails-for-x---x)
  - [7.5. Structural characterization](#75-structural-characterization)
  - [7.6. Implications for ParamDiagElem](#76-implications-for-paramdiagelem)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Summary

This document analyzes the structure of the wedge weight functor
`wedgeWeight H : TwistedArrow C -> Type v` for a profunctor
`H : C^op x C -> Type v`, characterizes its values at non-identity
twisted arrows as connected components of factorizations through
`DiagElem(H)`, and explores whether the `TypeExpr` construction
gives rise to a different copresheaf on the twisted-arrow category
that captures parametricity rather than paranaturality.

## 1. Factorization characterization of wedgeWeight

### 1.1. Definition recap

The wedge weight is defined as:

```text
wedgeWeight H = comprehensiveCopresheaf (twistedArrowMap (DiagElem.forget H))
```

where `comprehensiveCopresheaf F` at `d` is
`ConnectedComponents (CostructuredArrow F d)`.

At a twisted arrow `tw = (f : A -> B)`, a costructured arrow
over `tw` in the image of `twistedArrowMap (DiagElem.forget H)`
consists of:

- A twisted arrow in `TwistedArrow (DiagElem H)`, which is a
  triple `((I_0, d_0), (I_1, d_1), h)` where
  `(I_k, d_k) : DiagElem H` (i.e., `d_k : diagApp H I_k`) and
  `h : (I_0, d_0) -> (I_1, d_1)` is a `DiagElem H` morphism
  (a morphism `h.base : I_0 -> I_1` in `C` with the DiagCompat
  condition).

- A twisted-arrow morphism from `twObjMk h.base` to `tw`,
  which consists of `alpha : A -> I_0` and `beta : I_1 -> B`
  with `alpha >> h.base >> beta = f`.

### 1.2. General factorization characterization

For any profunctor `H : C^op x C -> Type v`, an element of
`(wedgeWeight H).obj tw` at a twisted arrow `tw = (f : A -> B)` is a
connected component of factorizations of `f` through a morphism in
`DiagElem(H)`:

```text
       alpha         h.base         beta
  A ---------> I_0 ---------> I_1 ---------> B
               |               |
               d_0             d_1
               |               |
           diagApp H I_0   diagApp H I_1
```

where:

- `alpha >> h.base >> beta = f`
- `h : (I_0, d_0) -> (I_1, d_1)` is a `DiagElem(H)` morphism,
  meaning `h.base : I_0 -> I_1` satisfies
  `DiagCompat H I_0 I_1 h.base d_0 d_1`.

Two factorizations are identified when they are connected by a
zigzag of costructured arrow morphisms.

This characterization holds for arbitrary `H`, not just
`AlgProf F`. It is a direct consequence of the definitions of
`comprehensiveCopresheaf` and `twistedArrowMap`.

### 1.3. Specialization to AlgProf F

For `H = AlgProf F`, the diagonal elements are F-algebra structures
(`diagApp (AlgProf F) I = (F.obj I -> I)`), and the DiagCompat
condition for `h : I_0 -> I_1` between algebras `d_0` and `d_1`
becomes `d_0 >> h = F.map h >> d_1`, which (with `.symm`) is the
standard algebra homomorphism condition. Since
`DiagElem (AlgProf F) ~= Algebra F` (a proven equivalence in the
codebase), the factorization data is:

- A factorization of `f` through an `Algebra F` homomorphism
- Two factorizations are identified when connected by a zigzag
  of refinements

### 1.4. Specialization to CoalgProf F

By duality, `DiagElem (CoalgProf F) ~= Coalgebra F`, and the
factorization data at `(f : A -> B)` consists of factorizations
through coalgebra homomorphisms.

## 2. Identity twisted arrows and surjectivity

At the identity twisted arrow `(id_I : I -> I)`, a factorization
consists of:

- A `DiagElem(H)` morphism `h : (I_0, d_0) -> (I_1, d_1)`
- Morphisms `alpha : I -> I_0` and `beta : I_1 -> I` with
  `alpha >> h.base >> beta = id_I`

The canonical embedding `wedgeWeightIdentityMap H I` sends each
diagonal element `d : diagApp H I` to the connected component of
the trivial factorization `(id_I, d, d, id_(I,d), id_I, id_I)`.

`wedgeWeightIdentityMap_injective` (proven) shows this map is
injective.

Surjectivity requires that every connected component contains a
canonical arrow. A factorization `A -> I_0 -> I_1 -> A` with
`alpha >> h.base >> beta = id_A` does not, in general, zigzag to a
canonical factorization: the intermediate objects `I_0, I_1` may
differ from `A`, and there is no morphism in the costructured arrow
category connecting them to the canonical arrow unless there is a
`DiagElem(H)` morphism from `(A, d)` to `(I_0, d_0)` or similar.

For specific profunctors (e.g., `AlgProf F` with an initial algebra),
surjectivity may hold as a consequence of the universal property, but
it does not hold in general.

## 3. Natural transformations from wedgeWeight to profunctorOnTwistedArrow

The equivalence `paranatWeightedLimitEquiv` identifies:

```text
Paranat H G ~= (wedgeWeight H --> profunctorOnTwistedArrow C G)
```

For `G = IdProf` (the identity profunctor `Q(a,b) = b`), the
target `profunctorOnTwistedArrow C IdProf` at `(f : A -> B)` is
`(IdProf.obj (op A)).obj B = B`.

A natural transformation
`eta : wedgeWeight H --> profunctorOnTwistedArrow C IdProf` assigns
to each connected component of factorizations at `(f : A -> B)` an
element of `B`. By naturality, the value is determined by the value
at identity twisted arrows: given a twisted-arrow morphism
`m : (id_I : I -> I) -> (f : A -> B)` with components
`(alpha : A -> I, beta : I -> B)`, naturality gives:

```text
eta_(f)(m_*(x)) = beta(eta_(id_I)(x))
```

where `m_*` applies the `CostructuredArrow.map` to connected
components.

Since every connected component at `(f : A -> B)` is the image of
some component at an identity twisted arrow (by using the
factorization data), the natural transformation is determined by
its values at identity twisted arrows, i.e., by a function
`(I : C) -> (wedgeWeight H).obj (twObjMk (id_I)) -> I`.

Pre-composing with `wedgeWeightIdentityMap`, this gives a function
`(I : C) -> diagApp H I -> I`, which (by the weighted limit
equivalence) is a paranatural transformation from `H` to `IdProf`.

## 4. TypeExpr as a copresheaf

### 4.1. Motivation

`ParametricFamily T` for a type expression `T : TypeExpr` is not the
end of `T.toProfunctor` in general (this is the
parametricity/paranaturality divergence documented in
`ParametricityViaYonedaRelations.md`). However, parametric families
might still be expressible as weighted limits for a different weight
functor.

The wedge weight `wedgeWeight (T.toProfunctor)` characterizes
paranatural transformations from `T.toProfunctor`, which are the end
elements. A hypothetical `typeExprWeight T` should characterize
parametric families, which use `T.relInterp` rather than
`DiagCompat (T.toProfunctor)`.

### 4.2. Proposed recursive copresheaf

Define `typeExprWeight : TypeExpr -> (TwistedArrow Type -> Type)` by
recursion on `T`:

- **`T = var`**: At `(f : A -> B)`, the set is `A` (the domain of
  `f`). This is because `var.relInterp f` is `graphRel f`, and
  elements related by `graphRel f` are pairs `(a, f a)` indexed by
  `a : A`. Equivalently, this is the "fiber" or "graph" copresheaf.

- **`T = app F T'`**: At `(f : A -> B)`, the set is
  `{(x, y) | functorRelLift F (T'.relInterp f) x y}`, i.e., the
  set of pairs related by the lifted relation. Since `functorRelLift`
  creates pairs by mapping `F` over related pairs in the sub-relation,
  this is `F.obj (T'.relInterp_pairs f)` (the image of `F` applied
  to the type of related pairs from the sub-expression).

- **`T = arrow T_1 T_2`**: At `(f : A -> B)`, the set is
  `{(h, k) | T_1.relInterp f a_0 a_1 -> T_2.relInterp f (h a_0) (k a_1)}
  for all (a_0, a_1) satisfying T_1.relInterp f`.
  This is the function-space (exponential) applied to the sub-relations.

### 4.3. Comparison with wedgeWeight

For `wedgeWeight (T.toProfunctor)`, the test condition at
`(f : A -> B)` is DiagCompat, which (for the arrow case) restricts to
pairs arising from off-diagonal elements:
`{(T_1.profMap f id c, T_1.profMap id f c) | c : T_1.interp B A}`.

For `typeExprWeight T`, the test uses `T_1.relInterp f`, which tests
all pairs `(a_0, a_1)` satisfying the relational interpretation.

The difference:

- **DiagCompat pairs**: Arise from a single witness `c` in the
  off-diagonal `T_1.interp B A`. By `relInterp_of_offDiag`, such
  pairs always satisfy `T_1.relInterp f`, so DiagCompat pairs are a
  subset of relInterp pairs.

- **relInterp pairs**: Include DiagCompat pairs but potentially more.
  For nested arrows like `((X -> X) -> X) -> X`, there exist
  `relInterp`-related pairs that do not arise from off-diagonal
  elements. This is the parametricity/paranaturality gap.

Therefore, there should be a natural transformation
`typeExprWeight T -> wedgeWeight (T.toProfunctor)` (since the
relInterp test space includes the DiagCompat test space). For type
expressions where the two conditions agree (leaves, algebra
profunctor, hom profunctor), this should be an isomorphism. For the
divergence type `((X -> X) -> X) -> X`, it should not be.

The direction of the morphism means that `typeExprWeight T` is
"larger" (has more test pairs). A parametric family is a weighted
limit element for `typeExprWeight T`, which is therefore a smaller
set than the weighted limit for `wedgeWeight` (the end). This is
consistent with: every parametric family is a wedge element (proven),
but not conversely.

### 4.4. TypeExpr weight vs. parametric families

A parametric family `phi : ParametricFamily T` consists of
`phi.app : (I : Type) -> T.interp I I` satisfying
`T.relInterp f (phi.app I_0) (phi.app I_1)` for all `f : I_0 -> I_1`.

If `typeExprWeight T` is made into a functor
`TwistedArrow Type -> Type`, a natural transformation from
`typeExprWeight T` to `profunctorOnTwistedArrow Type IdProf` at
`(f : A -> B)` should send each related pair (or test witness) to an
element of `B`, compatibly with the twisted-arrow structure. At
identity twisted arrows `(id_I : I -> I)`, the value should be an
element of `T.interp I I` (a diagonal element). The naturality
condition at `(f : I_0 -> I_1)` should encode exactly `T.relInterp f`.

## 5. Dual characterization: cowedgeWeight

### 5.1. Definition

The cowedge weight is defined as:

```text
cowedgeWeight H = comprehensivePresheaf (coTwistedArrowMap (DiagElem.forget H))
```

where `comprehensivePresheaf F` at `d` is
`ConnectedComponents (StructuredArrow d.unop F)`.

### 5.2. Factorization characterization

By the same reasoning as Section 1.2, an element of
`(cowedgeWeight H).obj (op tw)` at a co-twisted arrow
`tw = (f : B -> A)` is a connected component of factorizations of `f`
through a morphism of `DiagElem(H)`:

```text
       beta          h.base         alpha
  B ---------> I_1 ---------> I_0 ---------> A
               |               |
               d_1             d_0
               |               |
           diagApp H I_1   diagApp H I_0
```

where:

- `beta >> h.base >> alpha = f`
- `h : (I_0, d_0) -> (I_1, d_1)` is a `DiagElem(H)` morphism

This is the dual of the wedge weight characterization: the
factorization goes through the same category `DiagElem(H)`, but the
direction of the outer maps and the role of domain/codomain are
reversed, matching the co-twisted-arrow structure.

The codebase includes `comprehensivePresheafCopresheafIso`,
which identifies `comprehensivePresheaf F` with
`comprehensiveCopresheaf F.op`. This makes the duality precise
at the level of the comprehensive factorization. The cowedge
weight at `(op tw)` is isomorphic to
`comprehensiveCopresheaf (coTwistedArrowMap
(DiagElem.forget H)).op` at `(op tw)`.

### 5.3. Relationship to cowedge equivalence

The equivalence
`strongRestrictedCowedge_weightedCocone_equivalence` identifies
cowedge elements with weighted cocones for `cowedgeWeight H`. This
is the dual of `strongRestrictedWedge_weightedCone_equivalence`.

## 6. Formalization plan

### Step 1: Factorization description at general twisted arrows

Define a type `WedgeWeightFactorization H tw` that makes the
factorization data from Section 1.2 explicit:

```text
structure WedgeWeightFactorization (H : C^op x C -> Type v)
    (tw : TwistedArrow C) where
  src : DiagElem H
  tgt : DiagElem H
  hom : src -> tgt
  domArr : twDom tw -> src.base
  codArr : tgt.base -> twCod tw
  comm : domArr >> hom.base >> codArr = twArr tw
```

Then construct an equivalence (or at least a bijection) between
`(wedgeWeight H).obj tw` and the connected components of
`WedgeWeightFactorization H tw` under the relation induced by
costructured arrow morphisms. Since `wedgeWeight H` is defined as
`ConnectedComponents (CostructuredArrow ...)`, this should be
definitional or require only straightforward unfolding.

### Step 2: Define typeExprWeight recursively

Define `typeExprWeight : TypeExpr -> (TwistedArrow Type -> Type)` as
described in Section 4.2. Making this functorial (a functor
`TwistedArrow Type -> Type`) requires defining the map action:
for a twisted-arrow morphism `m : (f : A -> B) -> (g : A' -> B')`
with components `(alpha : A' -> A, beta : B -> B')`, the map should
transform related-pair data compatibly.

### Step 3: Comparison natural transformation

Construct a natural transformation
`typeExprWeight T -> wedgeWeight (T.toProfunctor)` and show it is
an isomorphism for leaves and the algebra/coalgebra profunctor case,
but not for the divergence type `((X -> X) -> X) -> X`.

## 7. Composition analysis of relInterp (RelInterpComposition.lean)

### 7.1. Motivation

Defining a "parametric diagonal element" category `ParamDiagElem T`
(with morphisms using `T.relInterp` instead of `DiagCompat`) requires
`T.relInterp` to compose transitively. This section characterizes
when composition holds.

### 7.2. Arrow-free types and graph relations

For type expressions built from `var` and `app` only (no `arrow`
constructor), the relational interpretation reduces to a graph
relation: `T.relInterp f = graphRel (arrowFreeMap T haf f)` where
`arrowFreeMap` is the covariant map. Graph relations compose and
decompose, so arrow-free types have both properties.

### 7.3. Arrow case: conditional composition

For `arrow T_1 T_2`, composition requires:

- **Decomposition of T_1**: given `T_1.relInterp (g . f) a_0 a_2`,
  find `a_1` with `T_1.relInterp f a_0 a_1` and
  `T_1.relInterp g a_1 a_2`.
- **Composition of T_2**: given `T_2.relInterp f b_0 b_1` and
  `T_2.relInterp g b_1 b_2`, conclude
  `T_2.relInterp (g . f) b_0 b_2`.

The asymmetry: the domain only needs decomposition (which requires
being arrow-free), while the codomain only needs composition (which
is weaker, allowing nested arrows with arrow-free domains).

### 7.4. Counterexample: decomposition fails for `X -> X`

Using `I_0 = Unit`, `I_1 = Bool`, `I_2 = Fin 3`:

- `f : Unit -> Bool` maps `() |-> false`
- `g : Bool -> Fin 3` maps `false |-> 0, true |-> 1`
- `h_0 = id`, `h_2 : Fin 3 -> Fin 3` maps `0 |-> 0, else |-> 2`

The composed condition `arrowRel (graphRel (g . f)) (graphRel (g . f))`
holds for `(h_0, h_2)`, but no intermediate `h_1 : Bool -> Bool` can
satisfy both `arrowRel (graphRel f) (graphRel f)` and
`arrowRel (graphRel g) (graphRel g)`. The first forces
`h_1 false = false`; the second requires `g (h_1 true) = 2`, but
`Im(g) = {0, 1}`.

### 7.5. Structural characterization

`hasRelInterpComp T` holds iff every `arrow` node in `T` has an
arrow-free domain. Classification:

| Type expression | `hasRelInterpComp` |
| --- | --- |
| `var` (X) | true |
| `leaf F` (F(X)) | true |
| `arrow (leaf F) (leaf G)` (F(X) -> G(X)) | true |
| `arrow var var` (X -> X) | true |
| `arrow (arrow var var) (arrow var var)` | false |
| `arrow (arrow (leaf F) var) var` | false |
| `arrow (arrow (arrow var var) var) var` | false |

The algebra type `(F(X) -> X) -> X`, dinatural type
`(X -> X) -> (X -> X)`, and divergence type `((X -> X) -> X) -> X`
all fail the criterion.

### 7.6. Implications for ParamDiagElem

Defining `ParamDiagElem T` as a category using `T.relInterp` for
morphisms fails for most type expressions. For the algebra
and dinatural types where parametricity and paranaturality are known
to agree, the composability of `relInterp` relies on the specific
structure of the relational interpretation (e.g., naturality squares
compose by functoriality) rather than the generic type-expression
criterion. A "parametric weight" construction based on
`ParamDiagElem` would need to be formulated differently from the
naive approach of paralleling `wedgeWeight`.
