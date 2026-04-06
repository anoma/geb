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

## Remaining

### `iterNat_toRSpineNat`

Statement: `cfpMap (𝟙 T) toRSpineNat ≫ iterNat f = iterNat f`.
The fold ignores left subtrees, so normalizing the fold variable
does not change the result.

Proof outline: by `elim_uniq`. Base case: `cfpInsertSnd ℓ T ≫
cfpMap (𝟙 T) toRSpineNat = cfpInsertSnd ℓ T` (since `ℓ ≫
toRSpineNat = ℓ`). Step case: reduces to `M_assocSnd`, i.e.,
`cfpMap (𝟙 T) (cfpLift K (cfpSnd ≫ toRSN)) ≫ cfpAssocSnd =
cfpAssocSnd ≫ cfpMap (𝟙 T) toRSN`.

### `treeToNat_isRSpineNatNorm`

Requires `iterNat_toRSpineNat` plus
`cantorPair ≫ natSucc ≫ toRSpineNat =
cfpMap toRSpineNat toRSpineNat ≫ cantorPair ≫ natSucc`.

### `NatEqCantorPair`

Cantor pairing injectivity under `natEq`.

### `treeEqG_trans`

Transitivity of `treeEqG`, using `natTruncSub_fold_comp` and
the right-spine preservation lemmas.
