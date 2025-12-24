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

## Proving the Equivalence via Fullness

The equivalence can be established by proving that the evaluation functor
`E : PolyPresentationLoc D ⥤ (D ⥤ Type)` is fully faithful and essentially
surjective.

### Already Established

- **Faithfulness**: By construction of the quotient, `E([f]) = E([g])`
  implies `[f] = [g]`.
- **Essential surjectivity**: The density isomorphism shows every copresheaf
  `F` is isomorphic to `E(S(F))`.

### Fullness Proof Strategy

To prove `E` is full, we show: for any natural transformation
`α : E(X) → E(Y)`, there exists `f : X → Y` in `PolyPresentationLoc` with
`E(f) = α`.

#### Approach 1: Direct Construction

Given `α : X.toCopresheaf → Y.toCopresheaf`, construct `tgtHom : X.tgt → Y.tgt`
in `CoprodCovarRepCat` such that the induced map equals `α`.

For each index `i : ccrIndex X.tgt`, consider the universal element
`[⟨i, id⟩] ∈ X.toCopresheaf.obj (ccrFamily X.tgt i)`.

Apply α to get `α_i := α.app (ccrFamily X.tgt i) [⟨i, id⟩]`, an element of
`Y.toCopresheaf.obj (ccrFamily X.tgt i)`.

By naturality of α, for any `f : ccrFamily X.tgt i → A`:

```text
α.app A [⟨i, f⟩] = Y.toCopresheaf.map f α_i
```

Since `α_i` is a quotient element, let `α_i = [⟨j_i, h_i⟩]` for some
`j_i : ccrIndex Y.tgt` and `h_i : ccrFamily Y.tgt j_i → ccrFamily X.tgt i`.

Then:

```text
α.app A [⟨i, f⟩] = [⟨j_i, h_i ≫ f⟩]
```

This determines `tgtHom` with `base i = j_i` and `fiber i = h_i`.

#### Approach 2: Via Triangle Identities

Using the adjunction-like structure:

1. `comparisonMorphism X : X → S(E(X))` satisfies
   `E(comparisonMorphism X) = (densityIso E(X))^{-1}`
2. This means `E(comparisonMorphism X) ≫ densityIso_{E(X)} = id` (first
   triangle identity at E level)
3. For faithful functors with this property, fullness follows from
   constructing the inverse of comparisonMorphism

#### The Inverse Morphism

To complete either approach, we need a morphism `g : S(E(X)) → X` with
`E(g) = densityIso_{E(X)}`.

Construction of `tgtHom : densityTgt(E(X)) → X.tgt`:

- For each `(A, y) ∈ E(X).Elements` where `y : typeCoeq ...`, pick a
  representative `⟨i, h⟩` of `y`
- Set `base(A, y) = i` and `fiber(A, y) = h`

This morphism induces `densityIso.hom` as the induced map.

#### Constructivity Consideration

The construction above requires extracting representatives from quotient
elements. This can be done using `Quot.out`, which requires the quotient
type to be nonempty (automatically satisfied for coproduct-covariant-rep
evaluations) but is inherently noncomputable.

Two options:

1. **Accept noncomputable**: Mark the inverse morphism and subsequent
   equivalence proof as `noncomputable`. The mathematical validity is
   unchanged.

2. **Alternative formulation**: Work with a different characterization
   of the equivalence that avoids explicit representative extraction,
   possibly using abstract properties of the adjunction.

### Derived Properties

Once fullness is established:

- **E is an equivalence**: Fully faithful + essentially surjective
- **comparisonMorphism is an isomorphism**: E reflects isomorphisms (for
  fully faithful functors, this is automatic)
- **Adjunction**: The equivalence forms an adjoint equivalence with unit
  `comparisonMorphism` and counit `densityIso`

## References

- Category of elements: `Mathlib.CategoryTheory.Grothendieck`
- Colimit of representables: `Mathlib.CategoryTheory.Limits.Presheaf`
- Co-Yoneda lemma / density theorem
