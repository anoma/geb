# YonedaRel Category Instance

## Status: Refactoring complete

## Refactoring (completed)

`PshRel` (and therefore `YonedaRel`) has been changed from
`Skeleton (PshProdOver P Q)` (isomorphism classes of spans) to
`Subfunctor (pshProdPresheaf P Q)` (subobjects of the product
presheaf).  All downstream files compile with no warnings.

### Completed in PshRelDouble.lean

- Core definitions (`PshRel`, `pshRelId`, `pshRelComp`,
  `pshRelGraph`, `pshRelDagger`, `pshRelRelated`) rewritten
  to use `Subfunctor`.
- `pshBarrLiftRel` (formerly `pshBarrLiftSkel`): changed
  from `Skeleton.lift` to
  `pshProdOverToRel (pshBarrLift G (Over.mk R.ι))`.
- `pshBarrLiftRel_graph` (formerly
  `pshBarrLiftSkel_graph`): rewritten using
  `pshProdOverToRel_iso` and `pshProdOverToRel_graph`.
- `pshArrowRel` (formerly `pshArrowRelSkel`): changed
  from `Skeleton.lift2` to
  `pshProdOverToRel (pshArrowRel ...)`.
- Helper lemmas added: `pshRelGraph_ι_fst_iso`,
  `pshRelGraph_ι_snd`, `pshProdOverToRel_iso`,
  `pshProdOverToRel_graph`,
  `pshRelRelated_toPshProdOverRelated`,
  `pshProdOverRelated_topshRelRelated`.

### Completed in YonedaRelDouble.lean

- `YonedaRel X Y` changed from
  `Skeleton (YonedaProdOver X Y)` to
  `PshRel (yoneda.obj X) (yoneda.obj Y)`.
- `relId`, `relComp`, `yonedaRelGraph` now
  delegate directly to `pshRelId`, `pshRelComp`,
  `pshRelGraph`.
- `relRelated` now delegates to `pshRelRelated`.
- `YonedaRelCat` category instance changed from
  `Category.{max u (v + 1)}` to
  `Category.{max u v}`.
- All proofs updated and compiling.

### Completed in ParamPoly.lean

- `functorYonedaRelLift` rewritten from
  `Skeleton.lift` to
  `pshProdOverToRel (functorYPOLift F (Over.mk R.ι))`.
- `functorYonedaRelLift_graph` rewritten using
  `pshProdOverToRel_iso` and
  `pshProdOverToRel_graph`.
- `functorYonedaRelLift_related` rewritten using
  `pshProdOverRelated_topshRelRelated` and
  `pshRelRelated_toPshProdOverRelated`.

### Completed in ParanaturalTopos.lean

- `propRelToYonedaRel` changed from
  `toSkeleton` to `pshProdOverToRel`.
- `arrowRel_graphRel_iff_yonedaRelSQS` rewritten
  with direct proof via `arrowRel_graphRel_iff`.
- `arrowRel_iff_relRelated_propRel` rewritten
  using `pshProdOverRelated_topshRelRelated` and
  direct backward proof.

### Completed in PshTypeExpr.lean

- `pshRelSectionsRelated` rewritten as direct
  membership in `Subfunctor`: `∀ c, (s₀.val c,
  s₁.val c) ∈ R.obj c`.
- `yonedaULiftRel` changed from `toSkeleton` to
  `pshProdOverToRel (yonedaULiftRelOver R)`.
- `fullRelInterp_pshRep_eq` rewritten by induction
  using `pshProdOverToRel_pshBarrLift_le`,
  `pshBarrLiftSkel_mono`, and
  `pshArrowRelSkel_pshProdOverToRel`.
- `yonedaULiftRel_graphRel` rewritten using
  `Subfunctor.ext` and `Set.mem_range`.
- New bridge lemmas:
  `pshProdOverToRel_pshBarrLift_le`,
  `pshBarrLiftSkel_mono`,
  `pshArrowRelSkel_pshProdOverToRel`.

## Summary

`Category` instance on `YonedaRelCat C`, a wrapper type
whose morphisms are
`YonedaRel X Y = Subfunctor (pshProdPresheaf (yoneda.obj X) (yoneda.obj Y))`.

## What was added

### GebLean/Utilities/Presheaf.lean

Pullback utilities inside `PresheafPullback` section:

- `presheafPullbackCondition` (@[simp]): exposes the
  pullback cone's condition
- `presheafPullbackIdLeftIso`: `presheafPullback (id) g ≅ G`
  via the second projection
- `presheafPullbackIdLeftIso_inv_fst` (@[reassoc, simp])
- `presheafPullbackIdRightIso`: `presheafPullback f (id) ≅ F`
  via the first projection
- `presheafPullbackIdRightIso_inv_snd` (@[reassoc, simp])
- `presheafPullbackAssocIso`: associativity isomorphism for
  iterated presheaf pullbacks
- `presheafPullbackAssocIso_hom_fst` (@[reassoc, simp])
- `presheafPullbackAssocIso_hom_snd_fst` (@[reassoc, simp])
- `presheafPullbackAssocIso_hom_snd_snd` (@[reassoc, simp])

### GebLean/ParamPoly.lean

Product eta and identity simp lemmas:

- `yonedaProdLift_fst_snd` (@[simp]): eta for product lift
- `yonedaProdOverId_fst` (@[simp]): rfl
- `yonedaProdOverId_snd` (@[simp]): rfl

Over-level isomorphisms:

- `yonedaProdOverComp_id_left`: `comp(id, R) ≅ R`
- `yonedaProdOverComp_id_right`: `comp(R, id) ≅ R`
- `yonedaProdOverComp_assoc`: `comp(comp(R,S),T) ≅ comp(R,comp(S,T))`

Skeleton-level laws:

- `relComp_relId_left`
- `relComp_relId_right`
- `relComp_assoc`

Wrapper type and category instance:

- `YonedaRelCat C`: structure wrapping `C` objects
- `Category.{max u (v + 1)} (YonedaRelCat C)` instance
