# Internal Presheaf--Grothendieck Equivalence

## Status: In Progress (Tasks 1-8 complete, Task 9 partial)

### Task 9 progress

Compiling definitions added:

- `grothBaseMor_comp` -- composition law for base morphisms
- `inverseFiberMap_comp` -- functoriality of inverse fiber
- `inverseFiberFunctor` -- the `Cᵒᵖ ⥤ Type w` functor
- `inverseProj` -- projection natural transformation
- `grothFiberMor` -- fiber morphism in Grothendieck category

## Completed

- **Task 1**: Pointwise category extraction (`fiberObj`, `fiberCategory`)
- **Task 2**: Externalization functor (`externalize : Cᵒᵖ ⥤ Cat`)
- **Task 3**: Discrete Unit compatibility (all `rfl`)
- **Task 4**: `PshInternalPresheaf` structure
- **Task 5**: `PshInternalPresheafHom` and `Category` instance
- **Task 7**: Grothendieck construction via mathlib's `Grothendieck`
- **Task 8**: `comparisonFunctor : PshInternalPresheaf X ⥤ (X.groth ⥤ Type w)`

## Files

- `GebLean/PshInternalExternalize.lean` (~620 lines)
- `GebLean/PshInternalPresheaf.lean` (~270 lines)
- `GebLean/PshInternalGrothendieck.lean` (~570 lines)

## Current blocker: `grothFiberMor_naturality`

The `inverseAction` naturality proof requires a lemma
`grothFiberMor_naturality` showing that two paths around
the naturality square for `grothFiberMor` (with respect to
base change) agree up to `eqToHom`.

The `Grothendieck.ext` + `fiberHom_ext` approach reduces to
showing two compositions of fiber morphisms have the same
underlying `.val`. Each side involves `eqToHom`, identity
morphisms, and the morphism `X.morPresheaf.map f m`. After
`simp [Grothendieck.comp_fiber, grothBaseMor, grothFiberMor,
fiberHom_val_eqToHom_comp, externalize, fiberRestrict]`,
the remaining goal has compositions of subtypes with
identity and `eqToHom` terms that need `Category.assoc`,
`fiberHom_val_comp_eqToHom`, and `Category.id_comp`/
`Category.comp_id` at the Subtype.val level. The linter
`unusedSimpArgs` interferes with the `warningAsError` build
setting, requiring either careful simp set tuning or
`set_option linter.unusedSimpArgs false`.

Once `grothFiberMor_naturality` compiles, the
`inverseAction` naturality proof follows using
`Sigma.ext` + `heq_of_cast_eq` + `G.map_comp` +
`eqToHom_trans` + `eqToHom_refl'`.

## Design decisions

- Used mathlib's standard `Grothendieck` (covariant) on
  `Cᵒᵖ ⥤ Cat`, avoiding the project's `op'` construction
- The equivalence target is `X.groth ⥤ Type w`
  (copresheaves, covariant), matching the LEFT action of
  `PshInternalPresheaf`
- Key proof technique for fiber category functor equality:
  `fiberHom_val_eqToHom_comp` / `fiberHom_val_comp_eqToHom`
  using `subst` to eliminate `eqToHom`

## Remaining tasks

- Task 9: Complete inverse functor and equivalence
  - `grothFiberMor_naturality` (blocker)
  - `inverseAction` (depends on above)
  - Axioms: `action_tgt`, `action_id`, `action_assoc`
  - Assemble `inversePresheaf`
  - Build `inverseFunctor` on morphisms
  - Unit/counit isomorphisms
  - `pshInternalGrothendieckEquiv`
- Task 6: Span-bicategory module interpretation (skipped)
- Tasks 10-12: FunctorData generalization (pending)
- Task 13: Tests and integration (pending)

## Plan document

`docs/superpowers/plans/2026-03-28-internal-presheaf-grothendieck.md`
