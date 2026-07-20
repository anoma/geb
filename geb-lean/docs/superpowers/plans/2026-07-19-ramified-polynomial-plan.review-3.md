# Adversarial review 3: Ramified-on-vendored-stack plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Confirmed correct](#confirmed-correct)
- [Minors (applied)](#minors-applied)
- [Overall](#overall)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Summary

Round 3, 2026-07-19. One fresh-context reviewer, narrowly scoped to the
two edits made after round 2: the `tupleFold_snd` / `recurse_mk`
paramorphism deliverable and the rebuilt Phase C boundary. Both verified
correct against source. 0 blockers, 0 majors, 4 minors (all applied),
markdownlint clean. The review cycle has converged.

## Confirmed correct

- The reconstruction identity `FreeAlg'.tupleFold_snd : (tupleFold p
  t).2 = t` is provable by `W.induction` via `mk_dest` (`W.lean:262`),
  and `recurse_mk` follows from `W.elim_mk` plus that identity applied
  pointwise; the legacy `FreeAlg.recurse_mk` is `rfl` while the vendored
  side genuinely needs the lemma.
- The `P` parameter is not dropped: `tupleFold` is `p`-parametrized with
  `p` captured in the `W.elim` algebra, so the fold target
  `C × FreeAlg' A` (not `(P → C) × …`) is intentional and well-typed.
- The Phase C rebuild boundary matches source: `higherOrder'` needs
  `RType'.IsObj` / `RType'.interp` (Task A.4), the Phase A→C dependency
  is real and stated, and the deliverable names track their legacy
  counterparts.

## Minors (applied)

- M-r1. A.3 Consumes listed `elim_polyFixSliceEquiv` while A.2 marks it
  optional; removed from A.3 Consumes.
- M-r2. `FreeAlg'.tupleFold` was referenced by `tupleFold_snd` but not
  enumerated; added as an explicit A.3 Produces `def`.
- M-r3. A.2 module-docstring section order put `## References` before
  `## Main statements`; reordered to definitions → statements →
  references.
- M-r4. Phase C's "reused unchanged (rides the equivalence)" understated
  the `collapseDenotation'`-across-equivalence compatibility lemma;
  named it as an explicit Task C.0 obligation in both plan and spec.

## Overall

The spec (revision 4) and plan (revision 3) are converged:
zero-blocker / zero-major across the last round, all findings from three
rounds applied, markdownlint clean, TOCs current. Ready for user
line-by-line review and, on approval, execution beginning with the Task
A.0 spike.
