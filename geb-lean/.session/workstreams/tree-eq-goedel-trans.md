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
  second argument has no effect. Proved via `p.elim_uniq`;
  the step uses `β_toRSpineNat_eq`, `natPlus_succ`, and
  `cfpLift_snd` to reduce both sides to
  `cfpAssocSnd ≫ cfpMap (𝟙) toRSN ≫ natPlus`.

## Remaining

### `natTriHelper_cfpFst_rsn`

Statement: `natTriHelper ≫ cfpFst ≫ toRSN =
natTriHelper ≫ cfpFst`. The first component of the
triangular number helper is already right-spine normalized.

Proof: by `elim_algebra_morphism`. The first component is
`p.elim ℓ (cfpSnd ≫ natSucc)` (by `natTriHelper_cfpFst`).
The algebra morphism condition reduces to
`natSucc_toRSpineNat_comm` via `cfpMap_snd`.

### `natTri_isRSpineNatNorm`

Statement: `natTri ≫ toRSN = natTri`.

Requires `natTriHelper_cfpFst_rsn` and
`natPlus_toRSpineNat_second` (already proved). The proof
shows `natTriHelper ≫ cfpSnd ≫ toRSN = natTriHelper ≫
cfpSnd` by a paired `elim_uniq` argument: the second
component step `natPlus(natSucc(idx), sum)` normalizes to
itself because `natSucc(idx)` is rsn (from
`natTriHelper_cfpFst_rsn`) and `natPlus_isRSpineNatNorm`
depends only on the first argument.

### `treeToNat_isRSpineNatNorm`

Statement: `treeToNat ≫ toRSN = treeToNat`.

Via `elim_algebra_morphism` on `treeToNatParam`. Requires
`cfpMap toRSN toRSN ≫ cantorPair ≫ natSucc =
cantorPair ≫ natSucc ≫ toRSN`, which requires
`cfpMap toRSN toRSN ≫ cantorPair = cantorPair ≫ toRSN`.
That in turn requires `natTri_isRSpineNatNorm` plus
`natPlus_toRSpineNat_first` and
`natPlus_toRSpineNat_second`.

### `NatEqCantorPair` / unconditional `treeEqG_ββ`

Cantor pairing injectivity under `natEq`. Requires
`treeToNat_isRSpineNatNorm` plus order-theoretic properties
of `natTri` and `natPlus`, or a direct compositional
argument using rsn cancellation lemmas.

### `treeEqG_trans`

Transitivity of `treeEqG`, using `natTruncSub_fold_comp` and
the right-spine preservation lemmas.
