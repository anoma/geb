# Cat-Copresheaf Adjunction Workstream

## Status: Complete

The adjunction L ⊣ Φ between categories and copresheaves on CategoryJudgments
has been fully constructed, verified, and connected to mathlib's categorical
infrastructure.

## Completed Tasks

### Task 6: Direct Proof of PhiFunctor Fully Faithful (Complete)

Proved computationally that `PhiFunctor` is fully faithful.

1. `phiPreimage` - constructs preimages as `ε_X⁻¹ ≫ L(f) ≫ ε_Y`
2. `adjunctionUnit_app_isIso` - proves unit at `Φ(Z)` is an isomorphism using
   triangle identity
3. `phi_map_counit_inv_eq_unit` - shows `Φ(ε⁻¹) = η`
4. `phi_map_counit_eq_unit_inv` - shows `Φ(ε) = inv(η)`
5. `phi_map_preimage` - proves `Φ(preimage f) = f` using unit naturality
6. `phi_preimage_map` - proves `preimage(Φ(g)) = g` using counit naturality
7. `phiFunctorFullyFaithful : PhiFunctor.FullyFaithful` - the final structure

### Task 5: Connect to Mathlib's Reflective Adjunction (Complete)

Connected the counit isomorphism to mathlib's standard formulations:

1. `counitComponentIso` - lifts `OverFunctorData` isomorphism to mathlib `Iso`
2. `adjunctionCounit_app_isIso` - instance showing each counit component is `IsIso`
3. `adjunctionCounit_isIso` - instance showing the full counit natural transformation
   is `IsIso`
4. `catCopresheafCounitNatIso` - the natural isomorphism form of the counit

### Task 4: Universe Polymorphism Analysis (Complete)

Investigation revealed that the copresheaf adjunction chain is intrinsically
constrained to `{u, u}` because:

1. The copresheaf is valued in `Type u`
2. `FunctorData.toOverCategoryData` produces `OverCategoryData.{u, u}`
3. This propagates through `LFunctor`, `PhiFunctor`, and all compositions

Changes made:

- Generalized the `Category` instance for `BundledOverCategoryData` from `.{u, u}`
  to `.{v, u}` (useful for other applications of `BundledOverCategoryData`)
- The `{max v u, u}` pattern from `OverCategoryEquiv.lean` applies to the
  equivalence `BundledOverCategoryData ≌ BundledCategoryData` independently
  of the copresheaf chain

The full adjunction `LFunctorFull ⊣ PhiFunctorFull` uses `Cat.{u, u}` on the
category side, matching the `Type u` copresheaf values.

### Task 1: Comment Audit (Complete)

All three files (`Category.lean`, `OverCategoryEquiv.lean`,
`CatJudgmentAdjunction.lean`) were audited. No style violations found.

### Task 2: Universe Level Analysis (Complete)

Analysis revealed the constraint comes from sigma type construction:

1. `BundledCategoryData.toBundledOverCategoryData` outputs
   `BundledOverCategoryData.{max v u, u}` due to sigma type construction
2. For a round-trip equivalence, we need `max v u = v`, requiring `v >= u`
3. The current `{uLeft, uLeft}` is the simplest case, but `{max v u, u}` works

### Task 3: Prove Reflectivity Core (Complete)

The counit ε is proven to be an isomorphism at the `OverFunctorData` level:

- `counitQuiverMor_inv` - inverse quiver morphism
- `counitFunctorData_inv` - inverse functor data (preserves id and comp)
- `counit_comp_inv_eq_id` - proves ε⁻¹ ∘ ε = id as OverFunctorData
- `inv_comp_counit_eq_id` - proves ε ∘ ε⁻¹ = id as OverFunctorData

## Phase 2 - Left-Side Extension (Complete)

The equivalence chain on the left side is now complete:

1. `overBundledCatEquiv : BundledOverCategoryData ≌ BundledCategoryData` - Done
   - `overToBundledCatFunctor` and `bundledCatToOverFunctor`
   - `overBundledCatUnitIso` and `overBundledCatCounitIso`
   - Triangle identity `overBundledCat_functor_unitIso_comp` proven
   - Helper lemmas in `OverCategoryEquiv.lean`:
     - `OverQuiver.fiber_equiv_sigma_equiv_val`
     - `OverQuiver.sigma_equiv_apply`
     - `OverQuiver.fiber_equiv_roundtrip_val`

2. `equivCat : BundledCategoryData ≌ Cat` - Already complete in `Category.lean`

3. `overCatEquiv : BundledOverCategoryData ≌ Cat` - Composition of the above

## Phase 1 - Right-Side Extension (Complete)

The equivalence `functorDataEquivCat : FunctorData C ≌ (Obj ⥤ C)` is complete
in `CategoryJudgments.lean`. The extension was implemented by:

1. Using `Equivalence.symm.toAdjunction` to get `E.inverse ⊣ E.functor`
2. Composing with `catCopresheafMathlibAdjunction` using `Adjunction.comp`
3. Result: `(E.inverse ⋙ LFunctor) ⊣ (PhiFunctor ⋙ E.functor)`

New definitions in `CatJudgmentAdjunction.lean`:

- `copresheafEquiv` - the equivalence `FunctorData (Type u) ≌ (Obj ⥤ Type u)`
- `copresheafEquivAdjunction` - forward adjunction from the equivalence
- `copresheafEquivSymmAdjunction` - reversed adjunction from the equivalence
- `LFunctorExt` - extended L functor: `(Obj ⥤ Type u) ⥤ BundledOverCategoryData`
- `PhiFunctorExt` - extended Φ functor: `BundledOverCategoryData ⥤ (Obj ⥤ Type u)`
- `catCopresheafExtAdjunction` - the extended adjunction `LFunctorExt ⊣ PhiFunctorExt`

## Completed Components

1. **Core Adjunction** - Done
   - `LFunctor : Functor (FunctorData (Type u)) BundledOverCategoryData`
   - `PhiFunctor : Functor BundledOverCategoryData (FunctorData (Type u))`
   - `unitNT` and `counitNT` natural transformations
   - `catCopresheafMathlibAdjunction : LFunctor ⊣ PhiFunctor`

2. **Functor Construction** - Done
   - `NatTransData.toOverFunctorData` - L functor on morphisms
   - `toOverFunctorData_id` - L preserves identity
   - `toOverFunctorData_comp` - L preserves composition

3. **Triangle Identities** - Done
   - Second triangle (Φε) ∘ (ηΦ) = id_Φ
   - First triangle (εL) ∘ (Lη) = id_L

4. **Equivalences** - Done
   - `overBundledCatEquiv : BundledOverCategoryData ≌ BundledCategoryData`
   - `equivCat : BundledCategoryData ≌ Cat`
   - `overCatEquiv : BundledOverCategoryData ≌ Cat`
   - `copresheafEquiv : FunctorData (Type u) ≌ (Obj ⥤ Type u)`

5. **Reflectivity** - Done
   - `counitFunctorData_inv` - inverse of the counit functor
   - `counit_comp_inv_eq_id` and `inv_comp_counit_eq_id` - round-trip identities
   - Counit is an isomorphism at OverFunctorData level

6. **Fully Faithful Right Adjoint** - Done
   - `phiPreimage` - constructs preimages using counit isomorphism
   - `phi_map_preimage` and `phi_preimage_map` - round-trip properties
   - `phiFunctorFullyFaithful : PhiFunctor.FullyFaithful` - computational proof

## Related Files

- `GebLean/CatJudgmentAdjunction.lean` - Main adjunction and equivalences
- `GebLean/Utilities/Category.lean` - BundledCategoryData and equivCat
- `GebLean/Utilities/OverCategoryEquiv.lean` - Quiver/HomSet equivalences
- `GebLean/CategoryJudgments.lean` - CategoryJudgments and FunctorData

## Technical Notes

### Composability Proof Pattern

When proving properties about composable pairs:

1. Use `rcases p with ⟨⟨g, f⟩, hcomp⟩` to destructure the pair
2. Use `have heq : g_tgt = f_src := hcomp` to convert Composable to Eq
3. Use `cases heq` to substitute and reduce to the reflexivity case
4. Now transports by `hcomp` become definitionally trivial

Do NOT use `simp at hcomp` as this creates a duplicate hypothesis.

### fiber_equiv Round-Trip

When proving round-trip properties through `fiber_equiv` and `sigma_equiv`:

- Use `convert` instead of `exact` to handle proof irrelevance
- The lemma `OverQuiver.fiber_equiv_sigma_equiv_val` handles the composition

### Build Status

The file builds with no errors or warnings. Run `lake build` and `lake test`
to verify clean build.
