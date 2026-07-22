# Adversarial review 2: Verso ramified-recurrence manual plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Round and protocol](#round-and-protocol)
- [Blockers](#blockers)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Findings against the review artefact](#findings-against-the-review-artefact)
- [Verified without defect](#verified-without-defect)
- [Convergence](#convergence)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Round and protocol

Round 2, 2026-07-22, against the plan at branch
`docs/verso-ramified-manual`. One fresh `Agent` invocation covering
both lenses, directed at the text round 1 introduced. Findings are
categorised per `docs/process.md` § Defect categorisation, each with a
one-line author response.

## Blockers

- B1 (Task 0.2's probe and Task 5.1, `:::table (header := true)`).
  Verso parses the header argument as a flag, and the named-argument
  form takes the deprecated path, which emits `Deprecated flag
  syntax` through `logWarningAt`. `warningAsError` promotes it, so
  Task 0.2 Step 3's stated expectation does not hold and Task 5.1's
  chapter would not elaborate. The plan's own remedy taxonomy has no
  entry for this class, since §3.2 records these warnings as governed
  by no option — and §3.2 names this exact case, "every argument the
  chapters write to a role or directive". **Fix**: `:::table +header`
  at both sites.

## Serious

- S1 (Task 1.2 Step 1 and the References section, `InProceedings`).
  `InProceedings` has `title`, `authors`, `year`, `booktitle`,
  `editors`, `series` and `url`, and no `pages`. The step stated
  "`pages` is `Option (Nat × Nat)`" without confining it to `Article`,
  and the new References table supplied page ranges for all three
  `InProceedings` entries, so transcribing as instructed produces an
  invalid-field error. This is round 1's S1 class, reintroduced by
  S1's own fix. **Fix**: the claim is confined to `Article`, the three
  `InProceedings` rows read "n/a", and `clote`'s `booktitle` and
  `series` are separated — Crossref records the handbook title and the
  series as distinct container titles.
- S2 (Task 0.2 against Task 1.1, the generated output). The probe runs
  the generator, and `/_out` was not added to `geb-lean/.gitignore`
  until Task 1.1. This repository sets `snapshot.auto-track = "all()"`,
  so the generated tree would be snapshotted into the working copy,
  and `snapshot.max-new-file-size = "1MiB"` would make `jj` itself
  fail on a larger asset. Task 0.2 Step 7's stated expectation was
  therefore false. **Fix**: the ignore line moves to Task 0.2 Step 1,
  before anything generates, and Step 7 removes `_out`.
- S3 (Task 3.1 Step 4, the Appendix B check). The step wrote a new
  module under `GebLeanTests/` and built the library, but
  `lakefile.toml` declares `GebLeanTests` with `roots =
  ["GebLeanTests"]` and no `globs`, so Lake builds only the root
  module's import closure and a file nothing imports is never
  elaborated. The check passed whatever Appendix B contained — which
  is round 1's S7 verbatim, reintroduced by S7's fix. **Fix**: the
  `#check` lines are appended to
  `GebLeanTests/Ramified/Characterization.lean`, which the root
  reaches, and the file is restored afterwards.
- S4 (Appendix A, internal consistency). Three defects in the table
  round 1 added. `clone` was assigned to Part I chapter 3, which
  discusses no clones, so the executor would have introduced a term
  the chapter never uses or omitted it and failed Part II chapter 3's
  reference. `closed` had no referrer outside its own chapter and so
  failed Appendix A's own stated rule. The three algebra
  classifications were assigned to chapter 1 while Task 4.1's content
  named only nine terms. And no Phase 4 task referenced Appendix A, so
  under subagent execution the terms would not have been defined.
  **Fix**: `clone` moves to plain prose, its only occurrence being
  Part II chapter 3; `closed` is retained under a stated exception,
  Leivant III section 2.1 naming the three fragments as one taxonomy
  that would read as an oversight if split; the algebra terms are
  named in Task 4.1's content; and Tasks 4.1 and 4.3 carry a
  "Depends on: Appendix A" line.

## Minor

- M1 (Task 1.3's Interfaces). The clause still named Task 1.4 as the
  guard and 1.5 as the CI step, the roles the reordering swapped.
  **Fix**.
- M2 (Task 1.2 Step 7). The prose still said "output under
  `_out/html-multi/`" beside the sentence explaining that nothing
  below `_out` is asserted. **Fix**.
- M3 (Phase 4 preamble). "The same five steps" preceded a list of six.
  **Fix**.
- M4 (Tasks 0.1 and 0.2, Step 7 each). One said the lakefile edit
  stays in the working copy, the other reverts it. Harmless, since
  Task 1.1 rewrites it, but contradictory. **Fix**.
- M5 (Task 0.1 Step 4). "Expected exactly … added: [three names]"
  conflicts with the criterion it implements, additions only: a
  further package Verso's manifest contributes would read as a
  failure. **Fix**.
- M6 (References, two entries). `clote`'s "Journal or book" column
  held the series rather than the book, and `dalLagoMartiniZorzi` lost
  the EPTCS volume. **Fix**: the handbook title is the `booktitle`,
  the series is named separately, and the EPTCS volume is in the
  proceedings title.
- M7 (Task 5.1, the fourth column). "Lean declaration" does not fit
  the six rows naming positions inside `g`'s type. **Fix**: the column
  takes a declaration, a position, or an em dash.
- M8 (Task 3.1 Step 2 and Phase 5). Round 1's S12 response claimed
  both were split; only Task 3.1 was, and it remained one checkbox.
  **Fix**: the step states that each module's list is recorded before
  the next begins. The Phase 5 tasks stay one checkbox each, the
  commit being the review gate and a per-module split adding
  bookkeeping without adding a gate.
- M9 (Task 0.2, the provisional modules). They carried no module
  docstring though Global Constraints, added at round 1, make one
  mandatory. **Fix**.
- M10 (Task 0.1, `manifest-before.json`). The fallback exit path did
  not remove it, leaving an untracked file that `auto-track` would
  snapshot. **Fix**.

## Cosmetic-taste

- c1 (register). Round 1 recorded "go/no-go", "whole purpose" and
  "falls far outside that band" as fixed; all three survived, two of
  them in text round 1 rewrote. **Fix**: applied and verified by
  grep.
- c2 (markup for emphasis). Four occurrences survived round 1's
  recorded fix. **Fix**: applied and verified by grep.
- c3 (the absolute path, 42 occurrences). **Defer with rationale**, as
  at round 1: the reviewer's own count finds the same form in 44
  files, 36 of them under `docs/superpowers/`, so changing it here
  alone would make this document the outlier. The substitution is a
  repository-wide question.

## Findings against the review artefact

- A1 (review 1, three responses recorded as "Fix"). c1 and c2 were
  only partly applied, and S12's response addressed Task 3.1 while
  silently abandoning the Phase 5 half of the finding it recorded.
  `docs/process.md` § Author response requires the corrected text or a
  pointer to the resulting edit, so a partial fix needs a recorded
  deferral for the remainder. **Fix**: c1 and c2 are now applied; M8
  above records the Phase 5 half explicitly, with its rationale.
- A2 (review 1, protocol). Every finding carries one severity and one
  permitted response; both rejections are on cosmetic-taste findings;
  the four deferrals each carry a rationale and none is on a blocker
  or serious finding. **No defect.**

## Verified without defect

- **`jj restore <paths>` is the right command** for an uncommitted
  working-copy change, path-limited, restoring from the parent.
- **Task 0.1 Step 4's manifest diff runs and produces the stated
  shape**; every manifest entry carries `name` and `rev`, and the
  sort order matches.
- **`Article`'s fields, `inlines!`, and the string-gap continuation
  all check out.** `stringToInlines` sees the decoded string, so the
  Lean gap in `leivant3`'s title elides before Verso's markup parser
  reads it.
- **`{citep key}[]` matches Verso's own tests**, and a key defined in
  the same module as the `#doc` is resolvable, being elaborated first.
- **`{margin}[…]`, `{deftech}[…]`, `{tech}[…]` and the `signature`
  block** are all well-formed as written, and the presentation is
  definitionally equal to the real declaration with all four outer
  binders matching by name.
- **The counts reproduce**: 312 raw matches with the three wrapped
  docstring lines named, 925 nolints entries so the `>= 940` assertion
  holds, and Appendix A's twelve plus five rows agree with Task 5.1's
  seventeen.
- **`linter.hashCommand` and `linter.style.longLine` are both in
  `mathlibStandardSet`**, so the option entry and the column-limit
  claim are correct; `linter.style.header` returns early outside
  mathlib, so the templates' `open` before the module docstring is
  safe.
- **CI needs no preceding build**: `runLinter` spawns `lake build` for
  a missing olean and reaches every `GebLeanDocs.*` module.
- **All six Crossref records match the References table** by DOI.
- **Tasks 1.4 and 1.5 as reordered are coherent**, and the guard's
  per-library generalisation is implementable — the script's `vroot`
  and `workflow` are already locals, and the import regex's prefix is
  the library name in both rows.
- The plan is markdownlint-clean and doctoc-current.

## Convergence

Not converged. One blocker and four serious findings, all fixed at
this branch, with one cosmetic-taste finding deferred with rationale.

Two of the four serious findings — S1 and S3 — are the defect classes
round 1 diagnosed, reintroduced by round 1's own fixes, which is the
pattern the spec's eight rounds established and which round 1's
closing note predicted in terms. The blocker is of the same kind: the
plan triggered a warning class its own governing spec names, in text
written after that spec converged.
