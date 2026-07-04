# Ramified recurrence plan review, round 3

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Fix verification (round 2)](#fix-verification-round-2)
- [Dependency-site consistency check](#dependency-site-consistency-check)
- [Regression hunt around the round-2 edits](#regression-hunt-around-the-round-2-edits)
- [Verification coverage](#verification-coverage)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Verdict: CONVERGED (0 blocker, 0 major, 0 minor, 0 nit).

Document under review:
`docs/superpowers/plans/2026-07-02-ramified-recurrence-plan.md` at
commit `4ff3d8502` ("docs(plans): address ramified-recurrence plan
review round 2"). Reviewed against the user-approved spec
(`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`),
the round-1 and round-2 reviews, `CLAUDE.md`,
`.claude/rules/lean-coding.md`, `.claude/rules/markdown-writing.md`,
the mathlib naming and style guides (re-fetched this round), and the
round-2 fix diff (`81b22fe18..4ff3d8502`).

## Fix verification (round 2)

| Round-2 ID | Status | Note |
| --- | --- | --- |
| R2-M1 | resolved | Task 5.0 Step 1 now reads "after Phases 2 and 3 land ... content depends on Phases 2 and 3 only — the example ladder and `natFreeAlgEquiv`", matching the how-to bullet and the phase map row |
| R2-M2 | resolved | Phase 6 map row now "2, 3; G1, G2, G4; Phase 5 sub-plan converged (branch stacked after 5)"; the how-to bullet and Task 6.0 Step 1 carry the same three conditions, with the rationale (Collapse.lean consumes `natFreeAlgEquiv`; `collapseDenotation` stated against the Phase 5 sub-plan's `ObjCtx` bookkeeping) in the how-to bullet |
| R2-m1 | resolved | `Term.lean` row: `QuotRel` added, `eval` removed; `Interp.lean` row: `Tm.eval` and `interpQuotRel` added; table now matches the Task 1.3/1.4 assignments |
| R2-m2 | resolved | Task 7.1 Step 1 restated as an `example` proved from the interpretation lemmas, with the kernel-reduction rationale citing the pitfalls section's first item |
| R2-N1 | resolved | the `RType.IsObj` docstring now reads "Object sorts: `o` and every `Omega tau` (paper section 2.3)"; the casing commentary is gone |
| R2-N2 | resolved | decision 5 splits the attribution: s4.2 names (`SortedSig`, `Tm`, `standardModel`, `interpSetoid`, `QuotRel`, `SynCat`, `RType`, `higherOrder`) versus s6.1 names (`SynCatFO`, `collapseFunctor`, `ramified_definability`); verified against the spec (s4.2 lines 781-861, s6.1 lines 955-977) |
| R2-N3 | resolved | the `SynCatFO` docstring states the copy-of-the-carrier fact generically ("morphisms denote functions on the carrier") and scopes the numeric reading ("through natFreeAlgEquiv, at the natAlgSig instantiation") |

## Dependency-site consistency check

All dependency-statement sites were checked pairwise and agree:

- How-to Phase-order bullet: G1-G4 close before any Phase 1 commit
  (G3 decisive); Phase 5 sub-plan after Phases 2 and 3 land; Phase 6
  sub-plan after G1/G2/G4 closed, Phases 2 and 3 landed, and the
  Phase 5 sub-plan converged; Phase 7 consumes Phases 5 and 6.
- Phase map rows: Phase 1 "G1-G4 closed (G3 decisive)"; Phase 5
  "2, 3 (branch stacked after 4)"; Phase 6 "2, 3; G1, G2, G4;
  Phase 5 sub-plan converged (branch stacked after 5)".
- Task 5.0 Step 1 and Task 6.0 Step 1 restate their phases' map-row
  conditions exactly; Task 6.0 points at the how-to bullet for the
  rationale, which is present there.
- The Phase 5 and Phase 6 preambles make no dependency claims that
  could contradict the above (Phase 6's "content branches on gates
  G1/G2/G4" describes route selection, not the full dependency set).
- No stale wording remains: grep finds no "after Phase 2 lands",
  "Phase 2 has landed", or "depends on Phase 2 only" anywhere.
- Phase 6 execution's consumption of the Phase 5 code artifact
  `ObjCtx` is covered by "branch stacked after 5" together with the
  branch-creation rule in "How to work this plan"; the sub-plan-level
  wait (Task 5.0 convergence) is what the `collapseDenotation`
  signature needs, as R2-M2's required fix prescribed.

## Regression hunt around the round-2 edits

- The reworded dependency sentences introduce no new artifact claims
  beyond `natFreeAlgEquiv` (Phase 3, Task 3.1) and the `ObjCtx`
  bookkeeping (Phase 5 sub-plan / Task 5.5), both of which exist at
  the cited sites.
- The file-structure table edits: `QuotRel` is produced by Task 1.3
  in `Term.lean` and `interpQuotRel`/`Tm.eval` by Task 1.4 in
  `Interp.lean`; the rows now match. The rows remain summaries
  (e.g. `Tm.weaken` and `subst_id`/`subst_subst` are subsumed under
  the row's named items and "clone laws"), which contradicts nothing.
- Task 7.1 Step 1's revised wording cites the pitfalls section's
  first item, which is the `#guard`-on-heavy-composites rule it
  invokes; the faithfulness `example` clause is unchanged.
- The `SynCatFO` docstring revision is consistent with the generic
  signature `SynCatFO (P : Presentation) (r : QuotRel P.sig)` and
  with spec s6.1's paper-section-2.7 reading; the `collapseDenotation`
  comment retains the instantiation-specific `natFreeAlgEquiv`
  reading, so no content was lost.
- Decision 5's split attribution introduces no name not present in
  the cited spec sections (`RType` and `higherOrder` appear in s4.2
  at lines 733/855; the three s6.1 names at lines 961/967/975).
- No round-2 edit introduced a new Lean identifier, so the naming
  assessments of rounds 1-2 stand under the re-fetched guides
  (`ramified_definability`/`erMor_ramified_definable` theorems in
  snake_case; `collapseDenotation`/`natFreeAlgEquiv` defs in
  lowerCamelCase; `IsObj`/`QuotRel`/`SynCatFO` Prop-/Type-valued in
  UpperCamelCase).

## Verification coverage

Checked this round and found correct (fresh-eyes pass; not repeated
as findings):

- `markdownlint-cli2 --config .markdownlint-cli2.jsonc --no-globs`
  passes on the plan (0 errors) and
  `doctoc --dryrun --update-only` reports the TOC current.
- Every remaining `#guard` site (Tasks 1.1-1.5, 2.1, 2.2, 2.4, 3.1,
  3.2, 4.1) operates on small structural values or decidable
  predicates, with Task 2.2 carrying the explicit "small inputs
  only; pitfalls section" annotation; the sole heavy-composite site
  (Task 7.1) is the one R2-m2 fixed.
- Task 7.1's produced statement matches spec s6.1 verbatim modulo
  the recorded `higherOrder natSig` to `higherOrder natAlgSig`
  mapping and the `ObjCtx` bookkeeping deferral it states.
- The file-structure table, the Phase 6 "Final boundary item" block,
  Task 7.1's consumes list, and the self-review checklist agree on
  the `Collapse.lean` contents (`SynCatFO`, `collapseDenotation`,
  `collapseFunctor`, faithfulness).
- Spec s8's dependency-ordered items 1-7 still map one-to-one onto
  Phases 1-7 after the dependency-row edits; no boundary or
  deliverable statement moved.
- The G3 spike commit message and the abandon/bookmark-delete
  sequence, the pre-commit/pre-push invocations, and the lint/doctoc
  command forms are unchanged from the forms rounds 1-2 verified.
