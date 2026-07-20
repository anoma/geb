# Adversarial review 2: Ramified-on-vendored-stack plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Regression](#regression)
- [New majors](#new-majors)
- [New minors](#new-minors)
- [Disposition](#disposition)
- [Overall](#overall)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Summary

Round 2, 2026-07-19. Two fresh-context reviewers (revised-construction
feasibility; regression and consistency) against source at branch
`feat/ramified-polynomial` after the revision-2 plan / revision-3 spec.
All 17 round-1 findings confirmed fixed. New: 0 blockers, 2 majors, and
minors. Every claim re-verified against source.

## Regression

All round-1 findings (B1, B2, M1-M6, N1-N9) verified fixed in the
revised documents. The Phase A/B construction fixes are correct: the
fiber-motive forward fold typechecks (`PolyFix.ind`'s motive is
`Sort`-valued; the child `.2` supplies exactly `W.mk`'s `Compatible`
field under `toSlice_r` / `toSlice_q`); `interp` via `W.elim` at
`Y := Type` has no universe blowup (the `Y` binder is independent of
`uA uB uI`); the `Prop`-predicate and paramorphic routings are correct.

## New majors

- P1 (Task A.3 / A.0). `FreeAlg'.recurse_mk` does not follow from
  `W.elim_mk` alone and is not definitional. Legacy `FreeAlg.recurse_mk`
  is `rfl` (`AlgSig.lean:114-118`, via `PolyFix.ind`'s iota). The
  vendored paramorphism folds into `C × FreeAlg' A`; `W.elim_mk`
  (`W.lean:364`, itself `rfl`) gives the step applied to the children's
  reconstructed `.2` subtrees, so matching the legacy shape needs a
  reconstruction identity `(tupleFold t).2 = t`. That re-wraps every
  subtree through `FreeAlg'.mk` and holds only via `mk_dest`
  (`W.lean:262`) at each level — a lemma proved by `W.induction`, not a
  definitional reduction. Fix: add the reconstruction-identity lemma as
  an explicit A.3 deliverable; state `recurse_mk` as a theorem depending
  on it; reword A.0 Step 2 (validate the lemma, not "reduces"). Every
  paramorphic `RType'` compatibility (`objTarget'`, `domains'`) rests on
  this.
- P2 (Phase C). The revised "obtained by transport … not rebuilt from
  scratch" over-claims and reopens round-1 M4. Source: `SynCat (P :
  Presentation) _ := Ctx P.S` (`SynCat.lean:223`), `HomTuple P Γ Δ =
  ∀ i, Tm P.sig Γ (Δ.get i)` (`SynCat.lean:115-116`, hardwired to legacy
  `Tm`), `RMRecCat A = SynCat (higherOrder A) …` (`HigherOrder.lean:533`),
  `higherOrder A : Presentation` (`HigherOrder.lean:520`), `Presentation`
  a structure bundling sort type, signature, `IsObj`, and standard model
  (`Interp.lean:183`). There is no seam to `Equiv.trans` a type
  equivalence `RType' ≃ RType` into a category. A primed `SynCatFO'` over
  `RType'` requires rebuilding a primed `Presentation'` (a primed
  `higherOrder'` and standard model), after which the A/B equivalences
  prove `RMRecCat' ≌ RMRecCat` and the endpoints transfer across that
  equivalence of categories. The ER definability / soundness proofs are
  still reused (they ride the equivalence), but Phase C is a
  parallel-presentation build, not a free transport. Fix: correct the
  Phase C framing to "rebuild the primed presentation, then relate by an
  equivalence of categories and transfer"; make the rebuild scope (and
  whether `SynCat'` uses legacy `Tm` over the primed signature or the
  vendored `Tm'`) the first Task C.0 decision. Requires a user decision
  before C.0 (see below).

## New minors

- Q1. `elim_polyFixSliceEquiv` (A.2 Produces) has no named consumer: the
  `FreeAlg'` round-trips use `Equiv` laws and the `RType'`
  compatibilities use `W.induction` + `recurse_mk`. Either name a
  consumer (the useful form is a `FreeAlg'`-level recurse-agreement
  lemma `FreeAlg'.recurse g p t = FreeAlg.recurse g p (freeAlgSliceEquiv t)`)
  or drop it (code-is-cost).
- Q2. A.4 Consumes omits `W.dest` and `wIndex` (used for `RType'.shape`).
  Add them.
- Q3. A.0 Step 2 wording "confirm `recurse_mk` reduces" presumes a
  definitional reduction contradicted by P1; reword.
- Q4. Plan Architecture over-specifies the round-trip closers: they fold
  via `PolyFix.ind` and `W.induction`; `RecProp` / `recProp_mk` is the
  `RecProp` reduction rule, not folded in either round-trip.
- Q5. The A.2 / A.3 / A.4 module-docstring steps name
  `## Main definitions` / `## References` but omit `## Main statements`,
  though those files produce theorems. Add `## Main statements`.
- Q6. Task A.0 is ordered before A.1 yet references `toSlice` (A.1) /
  `FreeAlg'.recurse` (A.3): note it builds throwaway stubs inline, or
  renumber after A.1.

## Disposition

- Fix now (unambiguous): P1, Q1-Q6.
- User decision (blocks Task C.0): P2. The primed-stack inter-definability
  is a rebuild of the presentation layer plus an equivalence of
  categories (reusing the ER proofs), not a free transport. Options: (a)
  commit to that rebuild (genuine primed `SynCatFO'` inter-definable with
  ER; larger than the original "two data structures" framing); (b) keep
  Phase C carrier-agnostic (deliver `RType'` / `Tm'` and their
  equivalences; note the endpoints do not mention the numeric carrier).

## Overall

Phase A / B remain feasible as revised. P1 is a tractable missing lemma
the A.0 spike must actually validate. P2 corrects an over-claim: the
transport-based Phase C has no source seam and is really a
parallel-presentation build; the scope decision is reopened for the
user.
