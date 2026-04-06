# Workstream: Tree Equality via Goedel Encoding

## Status

Active

## Context

Proving properties of `treeEqG` (tree equality via Goedel
encoding), with the goal of making `treeEqG_ββ` unconditional
(currently depends on `NatEqCantorPair`) and proving
`treeEqG_trans`.

## Completed

In `GebLean/NatArith.lean`:

- `natSucc_isRSpineNatNorm`: `natSucc` preserves right-spine
  normalization.
- `toRSpineNat_step_eq_natSucc`: the step morphism of
  `toRSpineNat` equals `cfpSnd ≫ natSucc`.
- `natSucc_toRSpineNat_comm`: `natSucc` commutes with
  `toRSpineNat`.
- `natPlus_ℓ_left_eq_toRSpineNat`: `natPlus(ℓ, t) =
  toRSpineNat(t)` for all `t`.
- `natPlus_ℓ_left_rsn`: `natPlus(ℓ, m) = m` for right-spine
  normalized `m`.
- `natPlus_toRSpineNat_first`: `cfpMap toRSpineNat (𝟙 T) ≫
  natPlus = natPlus ≫ toRSpineNat`. Post-composing natPlus
  with toRSpineNat equals pre-composing toRSpineNat on the
  first argument.
- `natPlus_rsn_comm_aux`: auxiliary lemma showing
  `cfpLift (cfpSnd ≫ toRSpineNat) (cfpFst ≫ a) ≫ natPlus
  = cfpMap a (𝟙 T) ≫ natPlus` for rsn `a`. Proved via
  `p.elim_uniq`, using `natPlus_ℓ_left_rsn` for the base
  and `toRSpineNat_β` + `natPlus_succ_left` for the step.
- `natPlus_comm_rsn`: commutativity of `natPlus` for
  right-spine normalized inputs:
  `cfpLift c a ≫ natPlus = cfpLift a c ≫ natPlus`
  for rsn `a`, `c`. Uses `natPlus_rsn_comm_aux`.
- `natPlus_cancel_left_rsn`: left cancellation of `natPlus`
  under `natEq` for rsn inputs:
  `natEq(c + a, c + b) = natEq(a, b)`.
  Follows from `natPlus_comm_rsn` + `natPlus_cancel_right`.
- `natPlus_isRSpineNatNorm`: if `a` is rsn, then
  `cfpLift a b ≫ natPlus` is rsn (for any `b`).
  Uses `natPlus_toRSpineNat_first`.
- `β_toRSpineNat_eq`: `β ≫ toRSpineNat =
  cfpSnd ≫ toRSpineNat ≫ natSucc`. The normalization
  of β(l, r) is natSucc(toRSpineNat(r)).
- `natPlus_toRSpineNat_second`:
  `cfpMap (𝟙 T) toRSpineNat ≫ natPlus = natPlus`.
  The fold walks only the right spine, so normalizing the
  second argument has no effect.
- `natTriStepSingle_toRSpineNat_comm`:
  `natTriStepSingle` commutes with
  `cfpMap toRSpineNat toRSpineNat`. Proved by showing
  both projections agree: the first via
  `natSucc_toRSpineNat_comm`, the second via
  `natPlus_toRSpineNat_first` and
  `natPlus_toRSpineNat_second`.
- `natTriStep_toRSpineNat_comm`:
  `natTriStep` commutes with the double-pair normalization
  map. Follows from `natTriStep_factor` (natTriStep uses
  only cfpSnd) and `natTriStepSingle_toRSpineNat_comm`.
- `natTriHelper_isRSpineNatNorm`:
  `natTriHelper ≫ cfpMap toRSpineNat toRSpineNat =
  natTriHelper`. Both components of the triangular
  number helper are rsn. Proved via
  `elim_algebra_morphism` with
  `natTriStep_toRSpineNat_comm` as the algebra morphism
  condition, and `toRSpineNat_ℓ` for the base.
- `natTri_isRSpineNatNorm`:
  `natTri ≫ toRSpineNat = natTri`. The output of
  `natTri` is right-spine normalized. Follows from
  `natTriHelper_isRSpineNatNorm` by projecting the
  second component.
- `cfpMap_id_comp'`: `cfpMap (𝟙 A) (f ≫ g) =
  cfpMap (𝟙 A) f ≫ cfpMap (𝟙 A) g`.
- `cfpMap_id_cfpSnd_eq_cfpAssocSnd`:
  `cfpMap (𝟙 A) (cfpSnd B D) = cfpAssocSnd A B D`.
- `cfpMap_id_cfpLift_cfpAssocSnd`:
  `cfpMap (𝟙 A) (cfpLift f (𝟙 D)) ≫ cfpAssocSnd = 𝟙`.
- `natSucc_natTriHelper`:
  `cfpMap (𝟙 1) natSucc ≫ natTriHelper =
  natTriHelper ≫ natTriStepSingle`.
- `toRSpineNat_natTriHelper`:
  `cfpMap (𝟙 1) toRSpineNat ≫ natTriHelper =
  natTriHelper`. Proved via `p.elim_uniq`.
- `toRSpineNat_natTri`:
  `toRSpineNat ≫ natTri = natTri`.
- `natPlus_toRSpineNat_both`:
  `cfpMap toRSN toRSN ≫ natPlus = natPlus ≫ toRSN`.
- `cantorPair_toRSpineNat_comm`:
  `cfpMap toRSN toRSN ≫ cantorPair =
  cantorPair ≫ toRSpineNat`.

In `GebLean/TreeGoedel.lean`:

- `treeToNatParam_rsn`:
  `treeToNatParam ≫ toRSpineNat = treeToNatParam`.
- `treeToNat_isRSpineNatNorm`:
  `treeToNat ≫ toRSpineNat = treeToNat`.

## Remaining

### `NatEqCantorPair` / unconditional `treeEqG_ββ`

Cantor pairing injectivity under `natEq`. Requires
order-theoretic properties of `natTri` and `natPlus`
(the triangular-number gap property) or a direct
compositional argument using rsn cancellation lemmas.
The gap property states that `natTri(n+1) > n + natTri(n)`,
which ensures unique decomposition of
`cantorPair(m,n) = natPlus(natTri(natPlus(m,n)), m)`.

### `treeEqG_trans`

Transitivity of `treeEqG`, using `natTruncSub_fold_comp`
and the right-spine preservation lemmas.
