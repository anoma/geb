# Arrow-Span Adjunction Generalization

## Plan

`docs/superpowers/plans/2026-03-25-arrow-span-adjunction.md`

## Status

Tasks 1-4 complete. Tasks 5-7 remain.

## Completed

- Task 1: Arrow-span inclusion functor (commit d40891db)
- Task 2: Span-arrow reflector functor (commit 899b3230)
- Task 3: Arrow-span reflective adjunction (commit f92cc7f9)
- Task 4: Presheaf pushout instantiation (commit 0ad2eda4)

All in `GebLean/Utilities/ArrowSpanAdjunction.lean`.

## Remaining

- Task 5: Refactor `PshRelEdgeFunctionalize.lean` to use
  the general adjunction. Redefine
  `pshRelEdgeFunctionalizeFunctor` as
  `pshRelEdgeInclusionFunctor C ⋙
  spanArrowReflector (pshSpanPushouts C)`.
  Rebuild the `pshRelEdgeFunctionalizeAdj` adjunction
  from scratch (not via `Adjunction.comp`).
  The composition type-checks (verified).
- Task 6: Update `PshRelEdgeReflectiveChain.lean`.
- Task 7: Final verification.

## Notes

- `colimit_hom_ext` helper in ArrowSpanAdjunction.lean
  provides general extensionality for colimits (two
  morphisms from a colimit are equal if they agree when
  composed with all cocone legs).
- `PushoutCocone.IsColimit.hom_ext` only works when
  the diagram is literally `span f g`, not an arbitrary
  `WalkingSpan ⥤ C`.
- The `Functor.associator` in `mkOfUnitCounit` triangle
  identities simplifies to `𝟙` via
  `simp only [Functor.associator, Category.id_comp]`.
  Use `convert ... using 1` to bridge the gap.
- WalkingSpan cocone naturality: use
  `induction h with | id => simp | init j => cases j`
  to handle all morphism cases.
