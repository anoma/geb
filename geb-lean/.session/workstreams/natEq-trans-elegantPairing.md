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
  (fold on w via swap + p.elim_uniq)
- `natTruncSub_natPred_first`:
  `nts(natPred(a), b) = natPred(nts(a, b))`
- `NatElegantPair.lean` created with:
  - `natSquareStep`, `natSquare`
  - `elegantPair` (two-phase dispatch via
    `iteBranches` on `isLeafEndo(nts(x,y))`)
  - `isqrtStep`, `isqrtState`, `isqrt`
  - `elegantUnpairRemainder`, `elegantUnpair`
- `GebLean.lean` updated with import

### Deferred

- `leq_trans` / `natEq_trans`: the abstract
  categorical proof is blocked by the
  reconstruction lemma
  (`natPlus(y, z-y) = z` when `y ≤ z`) not
  giving morphism equality.  Multiple approaches
  tried (fold on z, mono+assoc, natPred
  congruence); all hit the same wall that
  `nts(succ(a), b)` in the first argument
  doesn't simplify cleanly.  May not be needed
  for ElegantPairing injectivity — congruence
  of each primitive NNO operation may suffice.
  Needed for PER transitivity (Task 6).

### Next Steps

1. Computation rules for `natSquare`
   (`natSquare_ℓ`, `natSquare_succ`)
2. Computation rules for `elegantPair`
   (column/row phases via `iteBranches_ℓ`/`β`)
3. Band property:
   `isqrt(EP(x,y)) = max(x,y) ≫ toRSN`
4. ElegantPairing injectivity
5. Unconditional `treeEqG_ββ`

## Notes

- `natTruncSub_toRSpineNat_second` (nts absorbs
  toRSN on second arg) is available and may
  enable congruence proofs without natEq_trans.
- `natTruncSub_toRSpineNat_first` gives
  `cfpMap toRSN (𝟙 T) ≫ nts = nts ≫ toRSN`.
