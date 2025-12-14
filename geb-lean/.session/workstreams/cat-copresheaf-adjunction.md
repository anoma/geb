# Cat-Copresheaf Adjunction Workstream

## Status: In Progress - Code Cleanup and Reflectivity

The adjunction L ⊣ Φ between categories and copresheaves on CategoryJudgments
has been fully constructed and verified. The equivalence
`overBundledCatEquiv : BundledOverCategoryData ≌ BundledCategoryData` is
complete, establishing the left-side extension. Current work focuses on
code cleanup, universe polymorphism, and proving reflectivity.

## Current Work

### Task 1: Comment Audit (Complete)

All three files (`Category.lean`, `OverCategoryEquiv.lean`,
`CatJudgmentAdjunction.lean`) were audited. No style violations found - the
comments are appropriate mathematical docstrings and section headers.

### Task 2: Universe Level Polymorphism (Analyzed - Deferred)

Analysis revealed the constraint is fundamental:

1. `BundledCategoryData.toBundledOverCategoryData` outputs
   `BundledOverCategoryData.{max v u, u}` due to sigma type construction
2. For a round-trip equivalence, we need `max v u = v`, requiring `v ≥ u`
3. The simplest satisfying case is `v = u`, hence `{uLeft, uLeft}`
4. The copresheaf side `FunctorData (Type u)` is inherently single-universe

Full generalization would require restructuring `FunctorData` and
`CategoryJudgments` with additional universe parameters - a substantial change
affecting the entire codebase. The current single-universe implementation is
mathematically complete and covers the standard case where morphism and object
universes match.

### Task 3: Prove Reflectivity (In Progress)

Prove that the adjunction is reflective. According to nLab, this can be shown
by either:
1. Showing that the right adjoint Φ is fully faithful, or
2. Showing that the counit ε is a natural isomorphism

Approach:
1. Check if mathlib has theorems relating these two characterizations
2. Determine which is easier to prove for `catCopresheafMathlibAdjunction`
3. Prove that characterization
4. Obtain the other from the general theorem
5. Compose through equivalences to get reflectivity for the full adjunction

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

## Key Files

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
