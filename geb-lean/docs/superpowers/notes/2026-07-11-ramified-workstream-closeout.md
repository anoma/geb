# Ramified workstream closeout (2026-07-11, Phase 7 merged)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Unfired relocation triggers](#unfired-relocation-triggers)
- [Standing mathematical consequence](#standing-mathematical-consequence)
- [Follow-up candidates outside the workstream](#follow-up-candidates-outside-the-workstream)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Status: the ramified-recurrence workstream is complete. Phases 1-7 of
the master plan
(`docs/superpowers/plans/2026-07-02-ramified-recurrence-plan.md`) are
merged to `main`; Phase 7 (PR #252, branch `feat/ramified-p7-assembly`)
delivered `GebLean/Ramified/Characterization.lean` — the pair
`ramified_definability` / `collapseFunctor` (with `Faithful`), the
K^sim_2 transfer (`collapseKFunctor`, `ramified_definability_kSim`),
the area doc, and the spec reconciliation. The persistent record of
what exists is the area doc, `docs/areas/ramified-recurrence.md`; the
deferred and future work is catalogued there and in the spec's
sections 9-10. This note records only the items that belong to no
committed artifact: relocation-trigger outcomes and follow-up
candidates outside the workstream's scope.

## Unfired relocation triggers

The 6.5 handoff
(`docs/superpowers/notes/2026-07-10-ramified-p6.5-handoff.md` and the
Phase 7 handoff following it) keyed two deferred relocations on Phase
7 consumption. Phase 7's proof route — `erMorN_ramified_definable`
composed through `ramifiedDenotation_cast` and the `arityCongr`
transport — consumed neither, so both trigger conditions remain open:

- `collapseDenotation_comp` (`GebLean/Ramified/Soundness/Collapse.lean`)
  still has no consumer; the composition law's expected first consumer
  was Phase 7.
- The Phase-5-subject helpers homed in `Collapse.lean` (`Hom.eval_id`,
  `ramifiedDenotation_id` / `_comp` / `_apply` / `_injective`,
  `objFromNat_objToNat`) still await a second consumer before
  relocating to `Definability` / `SynCat`.

Both remain listed in the area doc's deferred section; a future
consumer, not a calendar, fires them.

## Standing mathematical consequence

Correction 5 — no rank-uniform internal ER normalizer exists; budgets
and rank are explicit inputs — carries its durable record in the 6.5
handoff and in the 6.4 spec/plan amendments. Nothing in Phase 7
touched it; it binds any future work that would seek a uniform
normalizer at the ER level.

## Follow-up candidates outside the workstream

Surfaced during the Phase 7 reviews; each is its own branch under the
one-concern-per-branch rule, none blocks anything:

- `docs/index.md` § Coverage bookkeeping is stale: it records a
  215-file partition (the non-test count is now 270), the referenced
  `check-area-coverage.sh` does not exist, and `_partition-notes.md`
  has no entries for the `Ramified` tree. A re-partition pass should
  include the `Ramified` modules and point them at the new area doc.
- `.claude/rules/lean-coding.md` § "Lean 4 module system" prescribes a
  `module`-keyword convention that no `.lean` file in the repository
  satisfies; reconcile the rule with the codebase (amend the rule, or
  plan a repo-wide migration).
- A public `@[simp]` unfolding lemma for `erToKFunctor.map` would
  remove the `change`-to-`erToKFunctor_map` step used in
  `GebLeanTests/Ramified/Characterization.lean`, if a second consumer
  of that step appears.
- The area doc's deferred-work paragraph reads densely; reformat as a
  list on the next docs touch.
