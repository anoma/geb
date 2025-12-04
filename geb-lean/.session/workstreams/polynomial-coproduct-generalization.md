# Workstream: Polynomial Composition with Coproduct-Complete Categories

## Status

Completed - All phases investigated/completed. Phase 8 found code already well-factored.

## Context

The composition of polynomial functors `f : D → Over Y` with `g : Over Y → Over Z`
currently requires `D = Over X`. Analysis shows the constraint comes from needing
to form "dependent sums" of representables — which is exactly the coproduct in
the slice category.

The generalization: if `D` has all small coproducts, composition should work.

## Research Findings

### Mathlib Definitions (FOUND)

From `Mathlib.CategoryTheory.Limits.Shapes.Products`:

- `HasCoproduct f` — category has coproduct of family `f`
- `HasCoproducts C` — category `C` has all small coproducts
- `∐ f` or `sigmaObj f` — the coproduct object
- `Sigma.ι f b` — the b-th injection `f b ⟶ ∐ f`
- `Sigma.desc` — construct morphisms out of the coproduct

### Over X Has Coproducts (CONFIRMED)

From `Mathlib.CategoryTheory.Limits.Over`:

```lean
instance [HasColimits C] : HasColimits (Over X)
instance [HasFiniteCoproducts C] : HasFiniteCoproducts (Over X)
```

Since `Type u` has all colimits, `Over X` for `X : Type u` automatically has all
coproducts. The forgetful functor `forget X : Over X ⥤ Type` creates colimits.

### Remaining Questions

3. ~~Does `FamilyCat C X` (free coproduct completion) satisfy `HasCoproducts`?~~
   **RESOLVED**: `FreeCoprodCompletionCat C` has `HasCoproducts` instance.
4. ~~Is `CoprodCovarRepCat C ≃ FamilyCat C^op X` for appropriate X?~~
   **RESOLVED**: `CoprodCovarRepCat C ≌ FreeCoprodCompletionCat (C^op')` via identity
   functors (the categories are definitionally equivalent).

## Tasks

### Phase 1: Import Mathlib Definitions (COMPLETED)

- [x] Find mathlib's `HasCoproducts` definition
- [x] Confirm `Over X` already has an instance
- [x] Add imports to our codebase
- [x] Understand the API for constructing coproducts in code

### Phase 2: Generalize Composition (PENDING)

- [ ] Define generalized `polyToOverCompFamily` using categorical coproducts
- [ ] Define generalized `polyToOverComp` for `D` with small coproducts
- [ ] Prove composition properties (associativity, identity)
- [ ] Specialize to `Over X` and verify existing code still works

### Phase 3: FreeCoprodCompletionCat Coproduct Completeness (COMPLETED)

- [x] Define coproduct structure on `FreeCoprodCompletionCat C`
- [x] Prove `HasCoproducts (FreeCoprodCompletionCat C)` instance
- [ ] Instantiate polynomial composition with `FreeCoprodCompletionCat`

### Phase 4: CoprodCovarRepCat Definitional Equality (COMPLETED)

- [x] Prove `CoprodCovarRepCat C = FreeCoprodCompletionCat (C^op')` via `rfl`
- [x] Derive coproduct completeness for `CoprodCovarRepCat` by reusing `fcCofan`/`fcIsColimitCofan`

### Phase 5: Refactor Existing Code to Use Generalized Composition (IN PROGRESS)

Turn existing uses of polynomial composition into specializations of the generalized
composition, except for those depending specifically on properties of `Over X`.

- [ ] Identify all current uses of polynomial composition in `Polynomial.lean`
- [ ] Refactor each to use the generalized composition where possible
- [ ] Keep specialized versions only where `Over X`-specific properties are needed

### Phase 6: Remove `noncomputable` from Composition Definitions (COMPLETED)

The *definition* of composition only needs the signature/structure of coproducts
(types and morphisms), not the proof of the universal property. Only proofs about
composition need the universal property, and proofs don't require `noncomputable`.

**Implementation**: Defined `CoprodData` typeclass in `Families.lean` that provides:
- `coprod : {I : Type*} → (I → D) → D` — the coproduct object
- `ι : (F : I → D) → (i : I) → F i ⟶ coprod F` — injection morphisms

For `Over X`, the instance uses direct sigma type construction (computable).
Notation `∐' F` is provided for `CoprodData.coprod F`.

**Result**: `polyToOverCompFamily` and `polyToOverComp` are now computable
(no `noncomputable` markers). The lemma `polyBetweenCompFamily_eq_polyToOverCompFamily`
proves by `rfl` that the specialized and generalized versions are definitionally equal.

- [x] Define `CoprodData` typeclass with coprod object and injections
- [x] Define instance for `Over X` using direct sigma construction
- [x] Redefine `polyToOverCompFamily` using `CoprodData.coprod` (`∐'`)
- [x] Remove `noncomputable` markers
- [x] Verify specialization: `polyBetweenCompFamily = polyToOverCompFamily` by `rfl`

### Phase 7: Implement HasProducts for Free Product Completion (COMPLETED)

Mirror the `HasCoproducts` implementation for `FreeCoprodCompletionCat` to implement
`HasProducts` for `FreeProdCompletionCat` (and `ProdContravarRepCat`).

**Approach**: Use `ProdData` typeclass (parallel to `CoprodData`) to separate
product structure from universal property proofs, enabling computable definitions.

- [x] Define `ProdData` typeclass (parallel to `CoprodData`)
- [x] Define computable `ProdData` instance for `Over X` (using fiber products)
- [x] Remove noncomputable `ProdData` instance from `HasProducts` (project is a compiler)
- [x] Define product structure on `FreeProdCompletionCat C`
- [x] Prove `HasProducts (FreeProdCompletionCat C)` instance
- [x] Define `fpProdData : ProdData (FreeProdCompletionCat C)`
- [x] Derive `HasProducts (ProdContravarRepCat C)`
- [x] Define `pcrProdData : ProdData (ProdContravarRepCat C)`

Additional instances (products distribute over coproducts):
- [x] Define `fcCoprodData : CoprodData (FreeCoprodCompletionCat C)`
- [x] Define `ccrCoprodData : CoprodData (CoprodCovarRepCat C)`
- [x] Define `fcProdData : ProdData (FreeCoprodCompletionCat C)` (requires `ProdData C`)
- [x] Define `ccrProdData : ProdData (CoprodCovarRepCat C)` (requires `ProdData C^op'`)
- [x] Define `fcpCoprodData : CoprodData (FreeCoprodProdCat C)`
- [x] Define `fcpProdDataMatching : ProdData (FreeCoprodProdCat C)` (when w₁ = w₂)
- [x] Define `ccrsCoprodData : CoprodData (CoprodCovarRepSquaredCat C)`
- [x] Define `ccrsProdDataMatching : ProdData (CoprodCovarRepSquaredCat C)` (when w₁ = w₂)

**Note**: The `ProdData` instances for `FreeCoprodProdCat` and `CoprodCovarRepSquaredCat`
require matching universe levels (`w₁ = w₂`) because `fcProdData` requires `ProdData.{w}`
on the underlying category where `w` is the same universe as the coproduct index.

**Universe constraint investigation**: The matching universe constraint `w₁ = w₂` is
fundamental. Products indexed by `J : Type w` create Pi types `∀ j, fcpOuterIndex (F j)`
at universe `max w w₁`. For the result to stay in the same category, we need
`max w w₁ = w₁`, which combined with the inner product constraint gives `w = w₁ = w₂`.

### Phase 7b: Distributivity of Products over Coproducts (COMPLETED)

Implemented computable isomorphism `A × (∐ᵢ Fᵢ) ≅ ∐ᵢ (A × Fᵢ)` in `FreeCoprodCompletionCat`.

- [x] Define index types `distLhsIndex`/`distRhsIndex` and conversion functions
- [x] Define family functions `distLhsFamily`/`distRhsFamily` (using `ULift Bool` for universe)
- [x] Define objects `distLhsObj`/`distRhsObj` and morphisms `distToRhs`/`distToLhs`
- [x] Prove round-trip lemmas `distToRhs_toRhs` and `distToLhs_toLhs`
- [x] Define isomorphism `distIso : distLhsObj A F ≅ distRhsObj A F`

**Note**: Uses `ULift.{w} Bool` instead of `Bool` for the binary product index to
match the `ProdData.{w} C` universe level.

### Phase 8: Code Factoring via Type-Level Polynomial Functors (INVESTIGATED)

`Over X` for `X : Type` is equivalent to `FamilyCat Type X`. This means polynomial
functors to `Over X` are equivalently families of polynomial functors to `Type`.

**Investigation findings:**

The code is already well-factored:
- `PolyToOverCat D Y = FamilyCat (CoprodCovarRepCat D) Y` - already a family of polynomials
- `polyToOverEvalFamily` = `fun y => ccrEval (P y) A` - pointwise evaluation at Type level
- `polyToOverEval` = `familySliceForward.obj (polyToOverEvalFamily Y P A)` - uses equivalence
- Specialized definitions (`polyBetweenEval`, etc.) are defined in terms of general versions

**Remaining optional tasks:**

- [ ] Define composition for `CoprodCovarRepCat Type` (polynomials `Type → Type`)
  - Note: This would be `(f ; g)(A) = g(f(A))` where `g` acts on `Type` itself
  - Requires treating `Type u` as a category (with functions as morphisms)
  - Different from `polyToOverComp` which requires `Over Y` domain for indexing
- [ ] Prove that `CoprodCovarRepCat Type` corresponds to polynomial endofunctors on `Type`
- [ ] Factor `Over Y` composition in terms of `Type → Type` composition (if useful)

## Notes

### Why Coproducts, Not Products

The composed representable at position `(ig, pf)` is:
```
Σ (eg : g-directions), (f-representable at pf(eg))
```

Elements are pairs `(eg, ef)` — a tagged union / coproduct, not a product.

In `Over X`, the coproduct of `(A_i, h_i)` is `(Σ i, A_i, copairing)`.

### The Generalized Construction

For `D` with coproducts, the composed representable would be:
```lean
∐ (eg : (ccrFamily (g z) ig).left), ccrFamily (f ((ccrFamily (g z) ig).hom eg)) (pf eg)
```

This requires:
- `D` has coproducts indexed by types (small coproducts)
- The indexing type is `(ccrFamily (g z) ig).left`

### Free Coproduct Completion

`FamilyCat C X = X → C` is the free coproduct completion of `C` when `C = Type`.
More generally, it adds formal coproducts indexed by `X`.

The coproduct of `F : I → FamilyCat C X` is `fun x => Σ i, F i x`.

### CoprodCovarRepCat as Free Completion

`CoprodCovarRepCat C` represents "formal coproducts of covariant representables
from C". This is equivalent to the free coproduct completion of `C^op`,
since covariant representables `Hom(c, -)` correspond to objects `c : C^op`.

**Implementation**: The equivalence `CoprodCovarRepCat C ≌ FreeCoprodCompletionCat (C^op')`
uses identity functors on both objects and morphisms because:

- `CoprodCovarRepCat C = GrothendieckContra' (familyFunctor C ⋙ Cat.opFunctor')`
- `FreeCoprodCompletionCat (C^op') = GrothendieckContra' (familyFunctor (C^op'))`

The functors `familyFunctor C ⋙ Cat.opFunctor'` and `familyFunctor (C^op')` produce
definitionally equal categories: both map `X : Type^op'` to the category with objects
`X → C` and morphisms `f ⟶ g` being families `∀ x, g x ⟶ f x`.

## References

- `GebLean/Polynomial.lean` - Current polynomial functor definitions
- `GebLean/Utilities/Families.lean` - FamilyCat and CoprodCovarRepCat
- Mathlib: `CategoryTheory.Limits.HasLimits` or `CategoryTheory.Limits.Coproducts`
