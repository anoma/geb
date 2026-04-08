# Workstream: natEq Transitivity + ElegantPairing

## Status

Active

## Context

Proving `natEq` transitivity and ElegantPairing
injectivity to make `treeEqG_ββ` unconditional.

## Plan

See `docs/superpowers/plans/2026-04-07-natEq-trans-elegantPairing.md`.

## Current Progress

### Completed

- `isLeafEndo_natTruncSub_mono`:
  `boolAnd(ile(w), ile(nts(w,c))) = ile(w)`
- `natTruncSub_natPred_first`:
  `nts(natPred(a), b) = natPred(nts(a, b))`
- `NatElegantPair.lean`: definitions of
  `natSquare`, `elegantPair`, `isqrtStep`,
  `isqrtState`, `isqrt`, `elegantUnpair`,
  plus boundary-condition fix (Task 0)
- `NatNNO.lean`:
  - `nnoElim_fold_compose`: iterate additivity
    `g^n(g^m(f(a))) = g^(m+n)(f(a))`
  - `cfpMap_comm_snd`, `nnoElim_absorbs_toRSN`
- `TreeLogic.lean`:
  - `iteFold_cfpMap_comm`: naturality of iteFold
  - `iteBranches_postcomp`:
    `iteBranches thn els cnd ≫ g =
    iteBranches (thn ≫ g) (els ≫ g) cnd`
- `NatElegantPair.lean` (continued):
  - `isqrtState_natPlus`: fold composition for
    isqrtState
  - `isqrtStep_fst`, `isqrtStep_snd`: projection
    rules
  - `isqrtLevelState` def + `_ℓ` + `_s`
  - `isqrtStep_at_ℓ`: boundary behavior
  - `isqrtStep_at_β`: one-step countdown when
    remaining > 0
  - `isqrtStep_fst_stable`: one-step root
    stability
  - `isqrtCountdown`, `nnoElim_countdown_fst`:
    unconditional root preservation under
    countdown
  - `natSquareGap`: `2k + 1` definition

### Blocked

- **Within-level stability (multi-step)**: showing
  `isqrtStep^j(s, r) = countdown^j(s, r)` when
  `j ≤ r`.  The one-step case (`isqrtStep_at_β`)
  and the unconditional countdown root stability
  (`nnoElim_countdown_fst`) are proved, but
  extending to `j` steps requires conditional
  fold reasoning.  `nnoElim_uniq` only proves
  unconditional equalities.
  See plan file for approach options.

### Deferred

- `leq_trans` / `natEq_trans`: blocked by
  reconstruction lemma.  May not be needed for
  ElegantPairing injectivity.

### Next Steps

1. **Resolve within-level stability** (see plan
   for three candidate approaches)
2. Level transition:
   `natSquare ≫ isqrtState = isqrtLevelState`
3. Band property:
   `isqrt(EP(x,y)) = max(x,y) ≫ toRSN`
4. Section: `elegantPair ≫ elegantUnpair = 𝟙`
5. ElegantPairing injectivity
6. Unconditional `treeEqG_ββ`

## Notes

- `natTruncSub_toRSpineNat_second` (nts absorbs
  toRSN on second arg) is available.
- `natTruncSub_toRSpineNat_first` gives
  `cfpMap toRSN (𝟙 T) ≫ nts = nts ≫ toRSN`.
