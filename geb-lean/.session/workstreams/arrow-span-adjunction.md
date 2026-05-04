# Arrow-Span Adjunction Generalization

## Plan

`docs/superpowers/plans/2026-03-25-arrow-span-adjunction.md`

## Status

All tasks complete.

## Completed

- Task 1: Arrow-span inclusion functor (commit d40891db)
- Task 2: Span-arrow reflector functor (commit 899b3230)
- Task 3: Arrow-span reflective adjunction (commit f92cc7f9)
- Task 4: Presheaf pushout instantiation (commit 0ad2eda4)
- Task 5: Refactor PshRelEdgeFunctionalize (commit dee6fd77)
- Task 6: Update reflective chain (commit 944d1911)
- Task 7: Final verification (clean build, tests, axiom
  hygiene)

All in `GebLean/Utilities/ArrowSpanAdjunction.lean`,
`GebLean/PshRelEdgeFunctionalize.lean`, and
`GebLean/PshRelEdgeReflectiveChain.lean`.

## Notes

- `pshRelEdgeFunctionalizeFunctor` is now an `abbrev`
  defined as `pshRelEdgeInclusionFunctor C ⋙
  spanArrowReflector (pshSpanPushouts C)`.
- The adjunction proofs use pointwise `rfl` at the
  `Quot` level for naturality and triangle identities.
- The reflective chain now uses `arrowSpanInclusion`
  and `spanArrowReflector` directly instead of going
  through `PshRelEdge`.
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
- WalkingSpan cocone naturality: use
  `induction h with | id => simp | init j => cases j`
  to handle all morphism cases.
