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

Cantor pairing injectivity under `natEq`. The standard
proof uses the fact that `natTri(s+1) = natTri(s) + s + 1`
to show `cantorPair` is injective, decomposing via
order properties:

- If `m + n = m' + n'` (same diagonal), then
  `natPlus_cancel_left_rsn` cancels the common `natTri`
  term, reducing to `natEq(m, m')`.
- If `m + n ≠ m' + n'`, the natTri gap exceeds the
  m-offset, so the cantor pair values differ.

This proof requires `treeToNat_isRSpineNatNorm` plus
order-theoretic properties of `natTri` and `natPlus`.

### `treeEqG_trans`

Transitivity of `treeEqG`, using `natTruncSub_fold_comp` and
the right-spine preservation lemmas.
