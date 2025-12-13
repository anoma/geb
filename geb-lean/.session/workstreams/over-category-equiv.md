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

```text
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

### Quiver-level equivalences (Phase 1)

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

### Natural transformation equivalences (Phase 4)

- `NatTransData.toComponentHom`: Component as Over morphism
- `NatTransData.toOverNatTransData`: Convert NatTransData to OverNatTransData
- `OverNatTransData.extractApp`: Extract component to fiber HomSets
- `OverNatTransData.toNatTransData`: Convert OverNatTransData to NatTransData

### Round-trip isomorphisms

The round-trip conversions preserve the underlying data, expressed via the
fiber equivalences:

**FunctorData round-trips:**

- `FunctorData.roundtrip_obj_eq`: Object map preserved
- `FunctorData.roundtrip_map_val_eq`: Morphism map preserved (up to fiber equiv)
- `OverFunctorData.roundtrip_objFn_eq`: Object function preserved
- `OverFunctorData.roundtrip_morFn_val_eq`: Morphism function preserved

**NatTransData round-trips:**

- `NatTransData.roundtrip_app_val_eq`: Component preserved (underlying sigma)
- `NatTransData.roundtrip_app_component_eq`: Full component preserved
- `OverNatTransData.roundtrip_app_val_eq`: Component preserved

## Phase 5: Category Structures for Over/Arrow Types

### 5a. OverNatTransData Operations

Add the following operations (mirroring NatTransData):

- `OverNatTransData.id`: Identity natural transformation
- `OverNatTransData.vcomp`: Vertical composition
- `OverNatTransData.whiskerLeft`: Left whiskering (H ◁ α)
- `OverNatTransData.whiskerRight`: Right whiskering (α ▷ H)
- `OverNatTransData.hcomp`: Horizontal composition (α ⊗ β)
- `OverNatTransData.hcomp'`: Alternative horizontal composition
- `OverNatTransData.hcomp_eq_hcomp'`: Interchange law

### 5b. OverFunctor Category

For fixed `C₁ : OverCategoryData Q₁` and `C₂ : OverCategoryData Q₂`:

- `OverFunctorHomSet C₁ C₂`: HomSet where morphisms are OverNatTransData
- `OverFunctorCategoryOps`: id = identity, comp = vertical composition
- `OverFunctorCategoryLaws`: associativity and identity laws
- `OverFunctorCategoryData`: CategoryData for the functor category

### 5c. BundledOverCategoryData

Analogous to `BundledCategoryData`:

- `BundledOverCategoryData`: Structure bundling OverQuiver + OverCategoryData
- `idOverFunctorData`: Identity functor
- `compOverFunctorData`: Functor composition
- Laws: associativity, left/right identity
- `homSet`, `categoryOps`, `categoryLaws`, `categoryData`

### 5d. Categorical Equivalences

**OverFunctor category ↔ Functor category:**

- The conversions `toFunctorData`/`toOverFunctorData` form functors
- Round-trips are naturally isomorphic to identities

**BundledOverCategoryData ↔ BundledCategoryData:**

- Forward: using `toCategoryData`
- Backward: using `toOverCategoryData`
- Establish categorical equivalence

## Status (Phase 5)

- [x] 5a: OverNatTransData operations
- [x] 5b: OverFunctor category structure
- [x] 5c: BundledOverCategoryData and its category
- [x] 5d: Categorical equivalences (partial - see Phase 6)

## Phase 6: Universe Generalization and Full Categorical Equivalence

### 6a. Universe Generalization

The structures now use two independent universe parameters:

- `OverQuiver.{v, u}` has `Obj : Type u` and `MorType : Type v`
- `OverCategoryData`, `OverFunctorData`, `OverNatTransData` all work with
  `OverQuiver.{v, u}`
- `BundledOverCategoryData.{v, u}` bundles `OverQuiver.{v, u}` with category data

Universe level behavior for conversions:

- `OverQuiver.{v, u}.toHomSet` produces `HomSet.{v + 1, u}`
- `HomSet.{v + 1, u}.toOverQuiver` produces `OverQuiver.{max v u, u}`
- `BundledOverCategoryData.{v, u}.toBundledCategoryData` produces
  `BundledCategoryData.{v, u}`
- `BundledCategoryData.{v, u}.toBundledOverCategoryData` produces
  `BundledOverCategoryData.{max v u, u}`

For clean round-trips, we work with `v ≥ u`. When `v ≥ u`, `max v u = v`, so both
directions of the equivalence operate at universe `{v, u}`.

### 6b. Conversion Functors

The conversions are functorial with general universe parameters:

**BundledOverCategoryData → BundledCategoryData:**

- `toBundledCategoryData_map`: Maps OverFunctorData to FunctorData
- `toBundledCategoryData_map_id`: Preserves identity
- `toBundledCategoryData_map_comp`: Preserves composition
- `toBundledCategoryDataFunctorData`: The functor for general `{v, u}`
  - Type: `FunctorData BundledOverCategoryData.categoryData.{v, u}
    BundledCategoryData.categoryData.{v, u}`

**BundledCategoryData → BundledOverCategoryData:**

- `toBundledOverCategoryData_map`: Maps FunctorData to OverFunctorData
- `toBundledOverCategoryData_map_id`: Preserves identity
- `toBundledOverCategoryData_map_comp`: Preserves composition
- `toBundledOverCategoryDataFunctorData`: The functor for general `{v, u}`
  - Type: `FunctorData BundledCategoryData.categoryData.{v, u}
    BundledOverCategoryData.categoryData.{max v u, u}`
  - When `v ≥ u`: `max v u = v`, giving same universes on both sides

### 6c. Universe-Polymorphic Equivalence

By parameterizing both sides with `{max v u, u}`, we get functors between the
same categories without any constraints:

- `overToCatFunctorData : BundledOverCategoryData.{max v u, u} →
  BundledCategoryData.{max v u, u}`
- `catToOverFunctorData : BundledCategoryData.{max v u, u} →
  BundledOverCategoryData.{max v u, u}`

The key observation is that `max (max v u) u = max v u`, so the sigma
construction doesn't bump the universe level on the round-trip.

Round-trip functors:

- `overCatOverFunctorData`: Over → Cat → Over (composition)
- `catOverCatFunctorData`: Cat → Over → Cat (composition)

Round-trip properties:

- `catOverCat_obj_eq`: Objects preserved definitionally
- `overCatOver_obj_eq`: Quiver objects preserved definitionally
- `catOverCat_homEquiv`: Hom-sets isomorphic via `fiber_equiv`

### Status (Phase 6)

- [x] 6a: Universe generalization
- [x] 6b: Conversion functors (generalized to `{v, u}`)
- [x] 6c: Universe-polymorphic equivalence at `{max v u, u}`
- [ ] 6d: Natural isomorphisms for round-trips (future work)

## Phase 7: Category-Copresheaf Adjunction

This phase implements the adjunction between:

- **Cat**: The category of small categories (via `OverCategoryData`)
- **[J, Type]**: The category of copresheaves on CategoryJudgments
  (via `CategoryJudgments.FunctorData`)

### 7a. Free Morphisms (FreeMor)

File: `GebLean/CatJudgmentAdjunction.lean`

The approach uses free morphisms as binary trees (inspired by Idris-2
`DiagramCat.idr`) rather than paths (linear lists). This avoids circular
dependencies in proving congruence properties.

- `FreeMor Q a b`: Free morphisms in a quiver, represented as binary trees:
  - `var f`: Inject a base morphism from the quiver
  - `id a`: Identity morphism at object a
  - `comp g f`: Composition g . f (f first, then g)
- `FreeMor.size`: Size of a free morphism (number of constructors)
- `FreeMor.map`: Map a free morphism through a quiver morphism

### 7b. Equivalence Relations (FreeMorEquiv)

- `FreeMorEquivGen`: Generating relations including:
  - Category axioms: `id_left`, `id_right`, `assoc`
  - Copresheaf relations: `id_witness`, `comp_witness`
  - Congruence: `cong_left`, `cong_right`
- `FreeMorEquiv`: Equivalence closure (refl, symm, trans)
- `FreeMorEquiv.cong_left`, `cong_right`: Congruence propagates through closure
- `freeMorSetoid`: Setoid on free morphisms

### 7c. Category Quotient Data

- `CategoryQuotientData`: Data for quotienting free morphisms to form a category
  - `quiver`: The underlying quiver
  - `IdWitness`, `idObj`, `idMor`: Identity witnesses
  - `CompWitness`, `compRight`, `compLeft`, `compComposite`: Composition witnesses
- `QuotMor`: Quotient type of free morphisms
- `quotQuiver`: OverQuiver for the quotient category
- `quotComp`, `quotId`: Composition and identity on quotients
- `quotComp_id_left`, `quotComp_id_right`, `quotComp_assoc`: Category laws
- `quotCategoryOps`: Operations structure
- `toOverCategoryData`: Full OverCategoryData from CategoryQuotientData

### 7d. Embedding Functor Phi

- `OverCategoryData.toJudgmentFunctorData`: Convert a category to a copresheaf
  - Objects, morphisms, identities map directly
  - Composition type is `Q.ComposablePairsType`
  - Proofs follow from category data properties

### 7e. Reflection Functor L

- `CategoryJudgments.FunctorData.toQuiver`: Extract quiver from copresheaf
- `CategoryJudgments.FunctorData.toCategoryQuotientData`: Construct quotient
  data from copresheaf, using identity and composition witnesses
- `CategoryJudgments.FunctorData.toOverCategoryData`: Full conversion to category

### Status (Phase 7)

- [x] 7a: Free morphisms (`FreeMor`)
- [x] 7b: Equivalence relations (`FreeMorEquivGen`, `FreeMorEquiv`)
- [x] 7c: Category quotient (`CategoryQuotientData`, `toOverCategoryData`)
- [x] 7d: Embedding Phi (`toJudgmentFunctorData`)
- [x] 7e: Reflection L (`toOverCategoryData`)
- [ ] 7f: Functoriality of Phi and L
- [ ] 7g: Round-trip L(Phi(C)) isomorphic to C
- [ ] 7h: Full adjunction L -| Phi
