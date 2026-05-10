# Judgment Sections and the Bicategorical Structure of Cat

This document describes the relationship between judgment sections, category
copresheaves, and the bicategorical structure of Cat under various
representations.

## Overview

Three equivalent representations of categorical structure connect through a
web of equivalences and adjunctions:

1. **JudgmentUniverse sections**: Sections of the functor
   `JudgmentUniverse : JudgmentLevel ⥤ Cat`
2. **CatJudgCopr**: Bundled category-structure copresheaves with explicit
   coherence conditions
3. **Polynomial presentations**: Coequalizers of polynomial functors via
   `PolyPresentationLoc JudgmentLevel`

The central result is a categorical equivalence:

```text
JudgmentSectionCat ≃ CatJudgCopr ↪ [J, Type] ≃ PolyPresentationLoc J
```

where the embedding into [J, Type] is via the right adjoint Φ of the
L ⊣ Φ adjunction.

## The Judgment Category

The judgment category J = `JudgmentLevel` has three objects representing
levels of categorical structure:

|Level|Object|Structure|
|---|---|---|
|obj|`ObjCopr`|A type (objects of a would-be category)|
|quiv|`ObjMorCopr`|A quiver (objects + morphisms + dom/cod)|
|cat|`CatJudgCopr`|Full category (quiver + id + comp + axioms)|

Morphisms in J are forgetful: `cat → quiv → obj`. These form a total order.

## Judgment Sections

A section of `JudgmentUniverse : J ⥤ Cat` assigns compatible structures at
each level:

```lean
structure JudgmentSection where
  objData : ObjCopr
  quivData : ObjMorCopr
  catData : CatJudgCopr
  quiv_to_obj : forgetObjMorToObj.obj quivData = objData
  cat_to_quiv : forgetCatJudgToObjMor.obj catData = quivData
```

The equivalence `JudgmentSection.equivCatJudgCopr` shows that sections are
determined by their cat-level data.

## Morphisms of Judgment Sections

### Definition

A morphism between judgment sections is a morphism at the cat level that
induces compatible morphisms at lower levels:

```lean
def JudgmentSectionHom (s t : JudgmentSection) :=
  Mor.CatJudgNatTrans s.catData t.catData
```

This is strict (not lax/oplax) because:

1. Lower-level data is uniquely determined by cat-level data
2. Forgetful functors are strict, so compatibility is automatic
3. A morphism at cat-level determines morphisms at all lower levels

### Category Structure

The category of judgment sections has:

- **Objects**: `JudgmentSection`
- **Morphisms**: `JudgmentSectionHom s t`
- **Identity**: `CatJudgNatTrans.id s.catData`
- **Composition**: `CatJudgNatTrans.comp`

Category laws follow from the category laws for `CatJudgCopr`.

### Categorical Equivalence

The type equivalence extends to a categorical equivalence:

```text
JudgmentSectionCat ≃ CatJudgCopr
```

The functors are:

- **Forward**: `F(s) = s.toCatJudgCopr`, `F(f) = f`
- **Inverse**: `G(c) = JudgmentSection.ofCatJudgCopr c`, `G(f) = transport f`

The natural isomorphisms are provided by `toCatJudgCopr_ofCatJudgCopr` and
`ofCatJudgCopr_toCatJudgCopr`.

## The Bicategorical Structure of Cat

Cat is a 2-category (strict bicategory):

|Level|Elements|Notation|
|---|---|---|
|0-cells|Small categories|C, D|
|1-cells|Functors|F : C → D|
|2-cells|Natural transformations|α : F ⇒ G|

The functor categories `Fun(C, D)` have:

- Objects: Functors C → D
- Morphisms: Natural transformations

### The 1-Categorical Collapse

The L ⊣ Φ adjunction operates at the 1-categorical level:

```text
L : [J, Type] → Cat    (left adjoint, free category)
Φ : Cat → [J, Type]    (right adjoint, embedding)
```

Under this adjunction:

|Cat|[J, Type]|
|---|---|
|Categories|Copresheaves|
|Functors|Natural transformations|
|Nat. trans.|**No correspondent**|

The 2-cells of Cat are "collapsed" because [J, Type] is a 1-category.

### Recovering 2-Cells via Cat-Enrichment

To preserve 2-categorical structure, use Cat-valued copresheaves [J, Cat]:

|Cat|[J, Cat]|
|---|---|
|Categories (0-cells)|Cat-valued copresheaves|
|Functors (1-cells)|Natural transformations|
|Nat. trans. (2-cells)|**Modifications**|

A **modification** Γ : α ⇛ β between natural transformations
α, β : F ⇒ G (where F, G : A → B are functors into Cat) consists of:

- For each object a ∈ A, a 2-cell Γ_a : α_a ⇒ β_a in B
- Subject to coherence conditions

### JudgmentUniverse and 2-Cells

Since `JudgmentUniverse : JudgmentLevel ⥤ Cat` is Cat-valued:

|JudgmentUniverse structure|Corresponds to|
|---|---|
|Sections|Categories (0-cells)|
|Section morphisms|Functors (1-cells)|
|Modifications between section morphisms|Natural transformations (2-cells)|

The hom-categories at each level provide the 2-categorical structure:

- `JudgmentLevel.toCat j` is a category
- Morphisms between sections at level j form a set
- "Morphisms between morphisms" at each level would be modifications

## Connection to Polynomial Presentations

### The Equivalence Chain

```text
JudgmentSection ≃ CatJudgCopr --Φ--> [J, Type] ≃ PolyPresentationLoc J
```

For D = JudgmentLevel:

- `PolyPresentationLoc JudgmentLevel ≃ [JudgmentLevel, Type]`
- The density formula gives canonical presentations
- Morphisms in PolyPresentationLoc identify presentations inducing the same
  copresheaf map

### Setoid Structure as Pre-2-Cells

The setoid machinery (`SetoidNatTrans`, `SetoidNatIso`, `SetoidEquivalence`)
provides structure analogous to 2-cells:

|Setoid structure|Cat-valued analogue|
|---|---|
|`SetoidNatTrans` (naturality up to ≈)|Lax natural transformation|
|Pre-quotient morphisms|Modifications|
|`SetoidNatIso`|Pseudonatural isomorphism|

The pre-quotient data in `PolyPresentationLoc` (before quotienting by
induced-map equivalence) tracks "different ways to represent the same
functor", analogous to 2-cells.

### Unified View

Both enrichment approaches recover the "missing" 2-cells:

1. **[J, Cat]**: Modifications as 2-cells (categorical answer)
2. **[D, SetoidBundle]**: Equivalence classes track pre-quotient structure

The connection:

```text
                    (forget to Type)
[J, Cat] ────────────────────────────> [J, Type]
    |                                      |
    | (discrete at each level)             | (quotient)
    v                                      v
[J, SetoidBundle] ──────────────────> PolyPresentationLoc J
                    (counit)
```

## Construction Approaches

### Approach 1: Currying + L

Use [J × J, Type] with currying and pointwise L:

1. Define F : J × J → Type encoding "hom-structure"
2. Curry to get F̃ : J → [J, Type]
3. Post-compose with L: L ∘ F̃ : J → Cat

The 16-object category J × J provides room for:

- Diagonal: basic structure (objects, morphisms, etc.)
- Off-diagonal: "hom" structure for 2-cells

### Approach 2: Enriched Hom-Categories

Enrich [J, Type] over Cat directly:

- Hom_{[J,Type]}(F, G) becomes a category
- Objects: natural transformations
- Morphisms: modifications

This is the internal-hom perspective.

## Implementation Path

### Phase 1: Category of Judgment Sections

1. Define `JudgmentSectionHom` as `CatJudgNatTrans` at cat level
2. Define identity and composition
3. Prove category laws
4. Build categorical equivalence with `CatJudgCopr`

### Phase 2: Functor Category Connection

1. Define `JudgmentSectionFunCat` for sections over a base category
2. Show morphisms correspond to functors
3. Build functor `JudgmentSectionCat → Cat`

### Phase 3: 2-Categorical Structure

1. Define modifications between section morphisms
2. Show correspondence with natural transformations in Cat
3. Verify 2-categorical laws

### Phase 4: Polynomial Presentation Connection

1. Show JudgmentSection embeds into PolyPresentationLoc J via Φ
2. Track setoid structure through the embedding
3. Verify pre-quotient data corresponds to modifications

## References

### Internal

- `GebLean/PLang/JudgmentUniverse.lean`: JudgmentLevel, JudgmentSection
- `GebLean/PLang/CatJudgment.lean`: CatJudgCopr, morphism types
- `GebLean/CatJudgmentAdjunction.lean`: L ⊣ Φ adjunction
- `GebLean/PolyPresentation.lean`: Polynomial presentations
- `GebLean/Utilities/SetoidCat.lean`: SetoidNatTrans, SetoidEquivalence

### External

- nLab: modification, transfor, 2-category, bicategory
- Lack, S. "A 2-Categories Companion" (IMA notes)
- Johnson & Yau, "2-Dimensional Categories" (arXiv:2002.06055)
