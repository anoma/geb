<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Polynomial Presentation Localization](#polynomial-presentation-localization)
  - [Overview](#overview)
  - [Background](#background)
    - [The Density Formula](#the-density-formula)
    - [The Presentation Category](#the-presentation-category)
    - [The Evaluation Functor Problem](#the-evaluation-functor-problem)
  - [The Localization Approach](#the-localization-approach)
    - [Morphism Equivalence Relation](#morphism-equivalence-relation)
    - [The Quotient Category](#the-quotient-category)
    - [Properties of the Quotient](#properties-of-the-quotient)
  - [The Density Presentation Functor](#the-density-presentation-functor)
    - [Construction for Objects](#construction-for-objects)
    - [Construction for Morphisms](#construction-for-morphisms)
    - [The Density Isomorphism](#the-density-isomorphism)
  - [The Equivalence](#the-equivalence)
    - [Statement](#statement)
    - [Counit: `E ∘ S ≅ Id`](#counit-e-%E2%88%98-s-%E2%89%85-id)
    - [Unit: `S ∘ E ≅ Id`](#unit-s-%E2%88%98-e-%E2%89%85-id)
  - [Implementation Notes](#implementation-notes)
    - [Using Lean's Quot](#using-leans-quot)
    - [Composition Well-Definedness](#composition-well-definedness)
    - [Category Instance](#category-instance)
  - [Relationship to Existing Literature](#relationship-to-existing-literature)
  - [Constructivity Analysis](#constructivity-analysis)
    - [Non-constructivity of quotients](#non-constructivity-of-quotients)
    - [Constructive Alternative: Setoid-Valued Copresheaves](#constructive-alternative-setoid-valued-copresheaves)
      - [Setoid-Valued Evaluation](#setoid-valued-evaluation)
      - [Setoid Density Presentation](#setoid-density-presentation)
      - [Constructive Inverse](#constructive-inverse)
      - [The Constructive Equivalence](#the-constructive-equivalence)
    - [Relationship to Type-Valued Copresheaves](#relationship-to-type-valued-copresheaves)
    - [Derived Properties](#derived-properties)
  - [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Polynomial Presentation Localization

This document describes the localization approach for establishing an
equivalence between the category of polynomial presentations and the
copresheaf category.

## Overview

The goal is to construct a categorical equivalence:

```text
PolyPresentationLoc D ≃ (D ⥤ Type)
```

where `PolyPresentationLoc D` is a localization (quotient) of the category
of polynomial presentations.

## Background

### The Density Formula

Every copresheaf `F : D ⥤ Type` is a colimit of representable functors:

```text
F ≅ colim_{(d, x) ∈ ∫F} D(d, -)
```

where `∫F` denotes the category of elements of `F`.

Since colimits can be computed as coequalizers of coproducts, every
copresheaf is isomorphic to a coequalizer of polynomial functors
(coproducts of representables).

### The Presentation Category

A polynomial presentation `(P, Q, α, β)` consists of:

- `P, Q : CoprodCovarRepCat D` (polynomial functors)
- `α, β : P ⟶ Q` (parallel morphisms)

The represented copresheaf is `coeq(eval(α), eval(β))` in `(D ⥤ Type)`.

### The Evaluation Functor Problem

The evaluation functor `E : PolyPresentation D ⥤ (D ⥤ Type)` sending each
presentation to its coequalizer is:

- **Essentially surjective**: Every copresheaf is a coequalizer of
  polynomials (density formula)
- **Not faithful**: Different morphisms can induce the same map on
  coequalizers
- **Not full**: Not every natural transformation between coequalizers lifts
  to a presentation morphism

## The Localization Approach

### Morphism Equivalence Relation

Two morphisms `f, g : X ⟶ Y` in `PolyPresentationQ D` are equivalent if
they induce the same map on coequalizers:

```text
f ≈ g  iff  f.toInducedMap = g.toInducedMap
```

where `toInducedMap : X.toCopresheaf ⟶ Y.toCopresheaf` is the unique map
determined by the universal property of coequalizers.

### The Quotient Category

Define `PolyPresentationLoc D` as:

- **Objects**: Same as `PolyPresentation D`
- **Morphisms X → Y**: Equivalence classes `[f]` of `PolyPresentationQ.Hom`
  under the relation `≈`
- **Composition**: `[f] ≫ [g] = [f ≫ g]` (well-defined because induced maps
  compose)
- **Identity**: `[id]`

### Properties of the Quotient

**Composition is well-defined**: If `f₁ ≈ f₂` and `g₁ ≈ g₂`, then:

- `f₁.toInducedMap = f₂.toInducedMap`
- `g₁.toInducedMap = g₂.toInducedMap`
- Therefore `(f₁ ≫ g₁).toInducedMap = (f₂ ≫ g₂).toInducedMap`
- So `f₁ ≫ g₁ ≈ f₂ ≫ g₂`

**The evaluation functor is faithful**: By construction, `E([f]) = E([g])`
implies `f ≈ g` implies `[f] = [g]`.

## The Density Presentation Functor

To complete the equivalence, we need a quasi-inverse `S : (D ⥤ Type) →
PolyPresentationLoc D`.

### Construction for Objects

For `F : D ⥤ Type`, define `densityPresentation(F)`:

**Target polynomial** `Q_F`:

- Index set: `F.Elements` (objects of the category of elements)
- Family: `(d, x) ↦ d` (the underlying object in D)

**Source polynomial** `P_F`:

- Index set: morphisms in `F.Elementsᵒᵖ`, i.e., `Σ (p q : F.Elements), (q ⟶ p)`
- Family: `(p, q, f) ↦ p.fst` (source object)

**Parallel morphisms**:

- `fst : P_F → Q_F`: source map, reindex `(p, q, f) ↦ p`, fiber `𝟙`
- `snd : P_F → Q_F`: target map, reindex `(p, q, f) ↦ q`, fiber `f.val`

### Construction for Morphisms

For `α : F ⟶ G` (natural transformation), the induced functor on categories
of elements `α* : ∫F → ∫G` sends `(d, x)` to `(d, α.app d x)`.

This induces:

- A morphism on target polynomials via reindexing by `α*` on objects
- A morphism on source polynomials via reindexing by `α*` on morphisms

### The Density Isomorphism

For any `F : D ⥤ Type`:

```text
E(densityPresentation(F)) ≅ F
```

This is the co-Yoneda lemma / density theorem: the canonical cocone from
representables indexed by the category of elements is a colimit cocone.

## The Equivalence

### Statement

The functors `E : PolyPresentationLoc D ⥤ (D ⥤ Type)` and
`S : (D ⥤ Type) ⥤ PolyPresentationLoc D` form an adjoint equivalence.

### Counit: `E ∘ S ≅ Id`

For `F : D ⥤ Type`:

- `E(S(F)) = densityPresentation(F).toCopresheaf`
- By the density theorem, this is isomorphic to `F`

### Unit: `S ∘ E ≅ Id`

For `X : PolyPresentation D`:

- `S(E(X)) = densityPresentation(X.toCopresheaf)`
- Both `X` and `S(E(X))` are presentations of the same copresheaf
- In `PolyPresentationLoc`, they are isomorphic via the comparison maps

The comparison maps exist because:

1. The identity `id : X.toCopresheaf → S(E(X)).toCopresheaf` factors through
   the canonical presentation
2. In the localized category, this gives an isomorphism

## Implementation Notes

### Using Lean's Quot

The quotient category uses Lean's `Quot` for equivalence classes:

```lean
def PolyPresentationLoc.Hom (X Y : PolyPresentation D) :=
  Quot (PolyPresentationQ.Hom.Setoid X Y).r
```

### Composition Well-Definedness

To define composition on the quotient, we use `Quot.lift₂` with the proof
that composition respects the equivalence relation.

### Category Instance

The category laws follow from:

- `toInducedMap_id`: identity induces identity
- `toInducedMap_comp`: composition induces composition
- These facts lift to the quotient

## Relationship to Existing Literature

This construction corresponds to the "category of presentations" described
in `docs/yoneda-coproduct-coequalizer-factorization.md`. The factorization:

```text
C → Fam(C) → PSh(C)
```

corresponds to:

```text
D → CoprodCovarRepCat D → (D ⥤ Type)
```

where the second arrow factors through `PolyPresentationLoc D`.

The localization quotients away the non-canonical choices in presentations,
leaving only the represented copresheaf.

## Constructivity Analysis

The equivalence with Type-valued copresheaves is non-constructive.

### Non-constructivity of quotients

For the inverse morphism `g : S(E(X)) → X`, we need
`tgtHom : densityTgt(E(X)) → X.tgt`.

The index type of `densityTgt(E(X))` is `E(X).Elements = Σ A, typeCoeq ...`,
which contains quotient elements.

To define `base(A, y)` where `y = [⟨i, h⟩]`, we want to extract `i`. But the
coequalizer relation can identify elements with **different indices**:

```text
[⟨ccrReindex X.fst j, ...⟩] ~ [⟨ccrReindex X.snd j, ...⟩]
```

Since `ccrReindex X.fst j` and `ccrReindex X.snd j` can differ, index
extraction is **not well-defined on equivalence classes**. We cannot use
`Quot.lift`; only `Quot.out` (which requires choice) would work.

This applies equally to:

- Direct inverse construction
- Fullness proofs (which require constructing lifts)
- Any approach requiring a function from quotient-indexed types

### Constructive Alternative: Setoid-Valued Copresheaves

The quotient is the source of noncomputability. By keeping the setoid
structure instead of quotienting, we obtain a fully constructive result.

#### Setoid-Valued Evaluation

For a presentation X, define `X.toSetoidCopresheaf : D ⥤ Setoid`:

- `obj A := (ccrEval X.tgt A, coequalizer equivalence)`
- The carrier is the pre-quotient type
- The equivalence is tracked separately

#### Setoid Density Presentation

For `F : D ⥤ Setoid`, define `densityPresentationSetoid F`:

- Target indexed by `Σ A, (F.obj A).carrier` (pre-quotient elements)
- Source indexed by morphisms respecting setoid equivalences
- Parallel morphisms as before

#### Constructive Inverse

For `(A, y)` where `y : (X.toSetoidCopresheaf.obj A).carrier = ccrEval X.tgt A`:

- `y = ⟨i, h⟩` for concrete `i : ccrIndex X.tgt` and `h`
- `base(A, y) := i` (directly accessible)
- `fiber(A, y) := h`

No quotient extraction required.

#### The Constructive Equivalence

```text
PolyPresentationLoc D ≃ (D ⥤ Setoid)
```

This equivalence is fully constructive and mathematically natural:
presentations inherently produce setoid-valued functors.

### Relationship to Type-Valued Copresheaves

The categories relate via the quotient functor `Q : Setoid → Type`:

```text
PolyPresentationLoc D ≃ (D ⥤ Setoid) --Q∘--> (D ⥤ Type)
```

The composite is an equivalence, but `Q` requires choice for its inverse
(selecting a setoid structure for a given type). The noncomputability is
isolated to this final step, which is external to the presentation theory.

### Derived Properties

With the Setoid approach:

- **E is faithful**: By quotient construction
- **E is essentially surjective**: Via density isomorphism
- **E is full**: Constructively provable
- **comparisonMorphism is an isomorphism**: Constructively provable
- **Full equivalence**: Assembles without choice

## References

- Category of elements: `Mathlib.CategoryTheory.Grothendieck`
- Colimit of representables: `Mathlib.CategoryTheory.Limits.Presheaf`
- Co-Yoneda lemma / density theorem
