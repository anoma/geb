# Over/Arrow Category Equivalences

## Goal

Prove categorical equivalences between the Over/Arrow-based category structures
(with proof-irrelevant constraints) and the dependently-typed structures in
`Category.lean`. This enables interaction with mathlib's `Category` using
Over/Arrow categories instead of dealing with casts, `eqToHom`, and
heterogeneous equality.

## Mathematical Foundation

The equivalence is based on the discrete Grothendieck construction. For a type
family `P : A → Type`:

- The total space is `Σ a, P a`
- The projection `π : Σ a, P a → A` is given by `π ⟨a, p⟩ = a`
- The fiber over `a` is `{ x : Σ a', P a' // π x = a } ≃ P a`

This round-trip is an equivalence:

- `P → Σ → fiber(Σ) ≃ P`
- `Σ → fiber(Σ) → Σ' ≃ Σ`

## Structures to Connect

### Dependently-typed (existing in Category.lean)

- `HomSet U := U → U → Sort v` (morphism type family)
- `CategoryData U hs` (operations + laws)
- `FunctorData dataC dataD` (obj map, mor map, laws)
- `NatTransData F G` (components, naturality)

### Over/Arrow-based (newly added)

- `OverQuiver` with `Obj : Type` and `Mor : Over (Obj × Obj)`
- `OverCategoryData Q` with `id` and `comp` as Over morphisms
- `OverFunctorData C₁ C₂` with Arrow morphism
- `OverNatTransData F G` with Over morphism for components

## Implementation Plan

### Phase 1: Quiver-level equivalences

1. `HomSet.SigmaMor`: Define `Σ (a b : U), hs a b`
2. `HomSet.toOverQuiver`: Bundle morphisms into an OverQuiver
3. `OverQuiver.toHomSet`: Extract fibers as a HomSet
4. `HomSet.fiber_equiv`: Show `(hs.toOverQuiver.toHomSet a b) ≃ hs a b`
5. `OverQuiver.sigma_equiv`: Show `Q.MorType ≃ Σ ab, Q.toHomSet ab.1 ab.2`

### Phase 2: Category equivalences

1. `CategoryData.toOverCategoryData`: Convert to OverCategoryData
   - Identity maps `a` to `⟨a, a, id_a⟩`
   - Composition maps composable `⟨f, g⟩` to `⟨f ≫ g⟩`
2. `OverCategoryData.toCategoryData`: Convert back
   - Identity extracts from `id.left a`
   - Composition extracts from `comp.left ⟨f, g, proof⟩`
3. Verify laws are preserved in both directions
4. Show round-trips give equivalent data

### Phase 3: Functor equivalences

1. `FunctorData.toOverFunctorData`: Convert to OverFunctorData
   - Object function is the same
   - Arrow morphism maps `⟨a, b, f⟩` to `⟨obj a, obj b, map f⟩`
2. `OverFunctorData.toFunctorData`: Convert back
   - Extract object and morphism maps from Arrow morphism
3. Show functor laws are preserved

### Phase 4: Natural transformation equivalences

1. `NatTransData.toOverNatTransData`: Convert to OverNatTransData
   - Over morphism maps `X` to `⟨F.obj X, G.obj X, app X⟩`
2. `OverNatTransData.toNatTransData`: Convert back
   - Extract component from `componentHom.left`
3. Show naturality is preserved

## Universe Level Considerations

- `HomSet.{v, u} U` has `hs a b : Sort v`
- `OverQuiver.{uOver}` uses `Type uOver`
- For compatibility, need `v = uOver + 1` (morphisms in Type, not Prop)
- May need to parameterize some constructions by universe levels

## Connection to mathlib

The full chain will be:

```
OverCategoryData ↔ CategoryData ↔ Category (mathlib)
```

Existing round-trip theorems:

- `categoryDataOfCategory_of_CategoryOfData`
- `CategoryOfData_of_categoryDataOfCategory`

## Files to Create/Modify

- New file: `GebLean/Utilities/OverCategoryEquiv.lean`
- Update: `GebLean/Utilities.lean` (add import)
- Update: `GebLean.lean` (if needed for public API)

## Status

- [x] Phase 1: Quiver-level equivalences
- [x] Phase 2: Category equivalences
- [x] Phase 3: Functor equivalences
- [x] Phase 4: Natural transformation equivalences

## Implementation Notes

All four phases have been implemented in `GebLean/Utilities/OverCategoryEquiv.lean`.

### Phase 1: Quiver-level equivalences
- `HomSet.SigmaMor`: The sigma type bundling all morphisms from a HomSet
- `HomSet.toOverQuiver`: Bundle morphisms into an OverQuiver
- `OverQuiver.toHomSet`: Extract fibers as a HomSet
- `HomSet.fiber_equiv`: Round-trip equivalence HomSet → OverQuiver → HomSet
- `OverQuiver.sigma_equiv`: Round-trip equivalence OverQuiver → HomSet → OverQuiver

### Phase 2: Category-level equivalences
- `CategoryData.toOverCategoryData`: Convert CategoryData to OverCategoryData
- `OverCategoryData.toCategoryData`: Convert OverCategoryData to CategoryData

### Phase 3: Functor-level equivalences
- `FunctorOps.toArrowHom`: Arrow morphism for a functor between bundled OverQuivers
- `FunctorOps.toOverQuiverMorphism`: Convert FunctorOps to OverQuiverMorphism
- `FunctorData.toOverFunctorData`: Convert FunctorData to OverFunctorData
- `OverFunctorData.toFunctorOps`: Convert OverFunctorData to FunctorOps
- `OverFunctorData.toFunctorData`: Convert OverFunctorData to FunctorData

### Phase 4: Natural transformation equivalences
- `NatTransData.toComponentHom`: Component as Over morphism
- `NatTransData.toOverNatTransData`: Convert NatTransData to OverNatTransData
- `OverNatTransData.extractApp`: Extract component to fiber HomSets
- `OverNatTransData.toNatTransData`: Convert OverNatTransData to NatTransData
