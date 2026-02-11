# YonedaRel Category Instance

## Status: Complete

## Summary

Built a `Category` instance on `YonedaRelCat C`, a wrapper
type whose morphisms are `YonedaRel X Y = Skeleton (YonedaProdOver X Y)`.

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
