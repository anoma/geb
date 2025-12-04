# Workstream: Polynomial Composition with Coproduct-Complete Categories

## Status

Active - Coproduct instances proven, refactoring to use generalized composition

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

### Phase 6: Remove `noncomputable` from Composition Definitions

The *definition* of composition only needs the signature/structure of coproducts
(types and morphisms), not the proof of the universal property. Only proofs about
composition need the universal property, and proofs don't require `noncomputable`.

**Approach**: Define a `CoprodData` typeclass that provides:
- `coprod : {I : Type*} → (I → D) → D` — the coproduct object
- `ι : (F : I → D) → (i : I) → F i ⟶ coprod F` — injection morphisms

But does NOT require the universal property (uniqueness, factorization proofs).

Then `polyToOverCompFamily` uses `CoprodData.coprod` instead of `∐`:
- For `Over X`: provide computable instance using sigma type construction
- For general `D` with `HasCoproducts`: derive (noncomputable) instance from `∐`

This separates:
- Computation (definition using `CoprodData`) — computable
- Proofs about composition — can use `HasCoproducts` for universal property

- [ ] Define `CoprodData` typeclass with coprod object and injections
- [ ] Define instance for `Over X` using direct sigma construction
- [ ] Redefine `polyToOverCompFamily` using `CoprodData.coprod`
- [ ] Remove `noncomputable` markers
- [ ] Verify proofs still work (they may need explicit `HasCoproducts` assumptions)

### Phase 7: Implement HasProducts for Free Product Completion

Mirror the `HasCoproducts` implementation for `FreeCoprodCompletionCat` to implement
`HasProducts` for `FreeProdCompletionCat` (and `ProdContravarRepCat`).

- [ ] Define product structure on `FreeProdCompletionCat C`
- [ ] Prove `HasProducts (FreeProdCompletionCat C)` instance
- [ ] Prove `ProdContravarRepCat C = FreeProdCompletionCat (C^op')` via `rfl`
- [ ] Derive `HasProducts (ProdContravarRepCat C)`

### Phase 8: Code Factoring via Type-Level Polynomial Functors

`Over X` for `X : Type` is equivalent to `FamilyCat Type X`. This means polynomial
functors to `Over X` are equivalently families of polynomial functors to `Type`.

- [ ] Investigate current overlap between `PolynomialFunctorsToType` and `Over X` versions
- [ ] Define composition for `PolynomialFunctorsToType` (post-composing with `Type → Type`)
- [ ] Note: `Type → Type` functors are equivalently `CoprodCovarRep Type`
- [ ] Factor composition for `Over Y` codomain in terms of `Type` codomain composition
- [ ] Identify and eliminate code duplication

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
