# Adversarial review 4: Verso ramified-recurrence manual plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Round and protocol](#round-and-protocol)
- [Blockers](#blockers)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Findings against the review artefacts](#findings-against-the-review-artefacts)
- [Verified without defect](#verified-without-defect)
- [Convergence](#convergence)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Round and protocol

Round 4, 2026-07-22, against the plan at branch
`docs/verso-ramified-manual`. One fresh `Agent` invocation covering
both lenses, instructed to verify each round-3 fix by grep rather than
on the author's word, the previous round having found two recorded
fixes absent from the file. Findings are categorised per
`docs/process.md` § Defect categorisation, each with a one-line author
response.

## Blockers

None.

## Serious

None.

## Minor

- M1 (Task 1.1, a numbering hole). Round 3's own M1 fix removed the
  duplicated `/_out` step and left the task running 1, 2, 4, 5, 6, 7,
  where every other task is contiguous — residue at the fix site, the
  class the fix answered. **Fix**: renumbered 1 to 6.
- M2 (Task 1.1, an undeclared file in the first commit). Task 0.2
  appends `/_out` to `.gitignore` and has no commit of its own, and
  `jj commit` commits the working copy, so the line lands in Task
  1.1's commit while its Files list and commit message named only the
  lakefile and the manifest. **Fix**: both now name it.
- M3 (Task 5.1, column sources). The task states a source for the
  paper's symbol and name on the six eq. (1) rows and leaves the other
  ten — three fragment names, three algebra classifications, four type
  terms — without one, though §6 supplies eight of them in prose.
  **Fix**: the sources are named and the em-dash rule extended to the
  symbol column.

## Cosmetic-taste

- c1 (Phase 4, the step range). The preamble labels six steps A, B, C,
  C2, D, E while each task line reads "Steps A–E", so C2 — the
  `lake lint` step whose omission the plan says would push the
  `nolints.json` entries into CI — sits outside the range every task
  cites. **Fix**: the task lines read "Steps A–E, C2 included".
- c2 (Task 5.1, "where" for "whereas"). **Fix**.
- c3 (Tasks 2.1 and 3.1, undeclared transient edits). Both modify
  `GebLeanTests/Ramified/Characterization.lean` and restore it, and
  neither Files list named it. **Fix**.
- c4 (rewrap raggedness at Task 5.1). **Defer with rationale**, as at
  round 3: the file is markdownlint-clean and reading is unaffected; a
  further programmatic pass risks more than it repairs.

## Findings against the review artefacts

- A1 (review 2, the strike that did not land). Review 3's A1 recorded
  "the claim is struck", and review 2 still read "Appendix A's twelve
  plus five rows agree with Task 5.1's seventeen" — the fourth
  instance of the recorded-fix-that-did-not-land pattern, and the
  second in which the author's verification statement held for the
  plan but not for the artefact edited beside it. It does not bear on
  the plan's convergence, the plan being the artefact under review.
  **Fix**: applied and verified by grep, which now reports zero
  occurrences.
- A2 (Appendix A, one further unsupported referrer). Round 3's M4
  deferral named `tier` and `r-type`; applying the rule independently,
  `flat`'s Part II chapter 4 citation is in the same position, Task
  5.4's content not naming flat recurrence. All three rows retain an
  independent referrer that does check out. **Defer with rationale**:
  the recorded rationale extends unchanged — no row's status turns on
  the unsupported claim, and the chapter descriptions fix content at a
  coarser grain than every term occurrence.
- A3 (review 3, protocol). One severity and one permitted response per
  finding; every deferral carries a rationale; no blocker or serious
  finding deferred. **No defect.**

## Verified without defect

- **Every round-3 fix is present**, each grepped rather than taken on
  trust: Task 4.1's twelve terms and its Depends-on line, with the
  word "sole" that defeated round 2's substitution now absent; Task
  5.1's derived row set, with no surviving "seventeen rows"; Appendix
  A's `closed` row reconciled with its exception; Task 1.1's duplicate
  ignore step gone; "Expected exactly" gone; `series` named; Task 3.1
  Step 4 on `jj restore` with `rm -f` on every path; and no in-sentence
  emphasis markup anywhere.
- **Appendix A holds sixteen rows, twelve plus four.** Task 4.1's
  enumeration matches the first table term for term and Task 4.3's the
  second. Applying the appendix's rule and its exception independently:
  `closed` is the only row without an outside referrer and the
  exception covers it; the other fifteen each have at least one
  referrer the chapter descriptions bear out.
- **The external facts hold for a third consecutive round**, this time
  read from a checkout at the pinned tag rather than inferred: both
  bibliography structures and their defaults, the `export` that makes
  the unqualified `Article` resolve, `:::table +header`,
  `manualMain`'s named-argument form, `RenderConfig`'s link fields,
  `OutputConfig.destination`, `verso.code.warnLineLength` and its
  block-only reading, `#doc`'s parser replacement grounding both the
  module-docstring ordering and the one-`#doc`-per-module rule, the
  generated document object name verbatim, and the non-`public` `def`
  grounding the `module` exemption.
- **Every repository fact holds**: 312 raw matches with the three
  wrapped docstring lines confirmed as comment continuations, 925
  nolints entries, the `plausible` revision, `GebLeanTests`'s roots and
  linter setting, the test module's namespace closing at line 76, both
  instance sites in their quoted shapes, the lakefile's trailing
  subtable, the CI workflow's working directory and insertion point,
  and the guard script's anchored regex and existing locals.
- **Every declaration the chapters name resolves**, and the §7
  signature presentation is definitionally equal to the real
  declaration with all four outer binders matching by name.
- **The five walked tasks execute end to end** — 0.1, 1.2, 3.1, 4.1
  and 5.1 — with consistent import graphs, correct `open` forms, clean
  restore paths, and Task 6.2's eight grep titles matching the spec's
  chapter names verbatim.
- **Project-rule compliance**: all eight commit messages use
  documented types, imperative and lower-case with no trailing period
  and subjects within length; no prose line exceeds 80 columns outside
  fenced blocks, tables and the doctoc block; every rule citation
  checks out against the file cited.

## Convergence

Converged. Zero blockers and zero serious findings, the criterion in
`docs/process.md` § Convergence criterion.

The record across four rounds, as blockers and serious findings: 3 and
12, 1 and 4, 0 and 3, 0 and 0. Two phases are visible. Round 1 removed
defects of execution — a scratch clone larger than its filesystem, a
guard depending on a later task, commit types outside the documented
list — a class the spec's own review could not produce, since a spec
asserts where a plan runs. Rounds 2 and 3 then removed defects that
the previous round's fixes had introduced, the repair being the
unreviewed surface each time, exactly as the spec's eight rounds
established.

What broke the pattern at round 3 was mechanical rather than
editorial: verifying each substitution individually instead of in
bulk, and deriving a count from its source rather than restating it.
Round 4 confirms both held.
