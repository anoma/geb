# Adversarial review 2: Phase C inter-definability sub-plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Blockers](#blockers)
- [Majors](#majors)
- [Minors](#minors)
- [Nits](#nits)
- [Verified without defect](#verified-without-defect)
- [Disposition](#disposition)
- [Overall](#overall)

<!-- END doctoc generated TOC -->

Round 2, 2026-07-20. One fresh-context reviewer verifying that every
round-1 disposition landed, regression-scanning the edited regions,
and sweeping for missed defects, against source at branch
`feat/ramified-poly-er`.

## Blockers

None.

## Majors

None.

## Minors

- m1 (plan C.13 Consumes). `rTypeSliceEquiv_curried` still attributed
  to Task C.12; the round-1 knock-on moved it to Task C.10 (the
  applying edit missed the backticked occurrence). Fix: re-attribute
  to Task C.10.
- m2 (plan C.18 Consumes). `objFromNat` mis-attributed to
  `Examples.lean`; it is in `Definability/Top.lean` (round 1's n2
  corrected only `objToNat`). Fix: split the attribution.

## Nits

- n1 (plan C.1 Step 1). The spike's W-equivalence statement kept the
  pre-round-1 orientation `(reindex e F).W ≃ F.W`; the fixed
  orientation is `F.W ≃ (reindex e F).W`. Fix: flip.
- n2 (plan C.10 Produces). Residual conditional and garbled phrasing
  about `RType'.interp_isObj`'s provenance, superseded by the fixed
  C.12 → C.10 → C.11 order. Fix: state the provenance
  unconditionally.

## Verified without defect

- All round-1 dispositions landed apart from the two residuals above:
  zero occurrences of `List.get_map`, `tmMapSigEquiv`,
  `tmMapSig_eval`, `presentationSynCatEquiv`, `Equiv.not`,
  `ObjectProperty.FullSubcategory.lift`, `rTypeInterpCongr`, and
  "alphabetical" in either document; `SortedSig.Equiv` only in the
  one naming-rationale mention per document; `TowerSorts` /
  `ShapeFO` renames in place; all eighteen commit first lines
  measured 49–71 characters; `RType.interpCongr` present in both
  `PolyFix.ind` whitelist enumerations; the design s12 delivery
  annotation present with the `TODO.md` bullet in place.
- The `get_map` helper route verified realizable against core
  (`List.get_eq_getElem`, `List.getElem_map`, `List.length_map` all
  present, composing to the stated statement; the repo's
  `barTy_get_map` precedent confirms core lacks the `get` form).
- Re-hosting consistent across both documents
  (`freeAlgSliceEquiv_recurse` and `RType'.interp_isObj` in
  `Polynomial/RType.lean`; `natFreeAlgEquiv'_slice` in
  `Polynomial/FreeAlg.lean`, its `rfl` claim verified against the
  Phase A definition).
- Design cross-references resolve after the renames; the C.18/C.19
  Consumes re-attributions spot-verified against source
  (`objToNat`, `kToERFunctor`, `kToERFunctor_map_interp`,
  `erToKFunctor`, `LawvereKSimDCat`, `ccrObjMk`,
  `FreeAlg'.induction`, `Ctx`, `erKSimEquiv`, `finApp_cases`,
  `FreeAlg.recurse`).

## Disposition

All four findings applied in the follow-up commit on this branch:
C.13 re-attributed to Task C.10; the C.18 `objFromNat` attribution
split to `Definability/Top.lean`; the C.1 spike orientation flipped;
the C.10 provenance phrasing made unconditional.

## Overall

Zero blockers, zero majors, two minors, two nits — all single-line
residuals of the round-1 application, repaired. With the round-1
substance verified sound against source and the residuals closed,
the review is converged; the documents proceed to user line-by-line
review.
