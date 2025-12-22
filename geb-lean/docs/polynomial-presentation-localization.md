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

## References

- Category of elements: `Mathlib.CategoryTheory.Grothendieck`
- Colimit of representables: `Mathlib.CategoryTheory.Limits.Presheaf`
- Co-Yoneda lemma / density theorem
