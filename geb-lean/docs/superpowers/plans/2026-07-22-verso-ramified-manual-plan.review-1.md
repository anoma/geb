# Adversarial review 1: Verso ramified-recurrence manual plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Round and protocol](#round-and-protocol)
- [Blockers](#blockers)
- [Serious](#serious)
- [Minor](#minor)
- [Cosmetic-taste](#cosmetic-taste)
- [Verified without defect](#verified-without-defect)
- [Convergence](#convergence)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Round and protocol

Round 1, 2026-07-22, against the plan at branch
`docs/verso-ramified-manual`. Two fresh `Agent` invocations, one on
executability and external fact verification, one on internal
consistency, spec fidelity, scope and project-rule compliance.
Findings are deduplicated across both and categorised per
`docs/process.md` § Defect categorisation, each with a one-line author
response. Where the two assigned different severities, the higher
governs.

## Blockers

- B1 (Task 0.1, the scratch clone). `cp -r … /tmp/verso-spike` copies
  8.7 GB into a tmpfs of 7.9 GB total and 7.8 GB free, so the plan's
  first executable step fails with ENOSPC; what did fit would occupy
  RAM the subsequent build needs, and the `rm -rf .lake/build` that
  would shrink it runs after the copy. The step also contravenes
  `.claude/rules/lean-coding.md` § Lake / build workflow, which
  directs experiments into the codebase rather than `/tmp`. **Fix**:
  Phase 0 runs in the working copy and undoes a failed trial with
  `jj restore`, nothing being committed until Task 1.1. Task 0.2's
  probe moves with it.
- B2 (Tasks 1.4, 1.5, ordering). The lint-driver guard greps a
  workflow file for the invocation line, and the `GebLeanDocs` line is
  added by the CI task, which the plan ordered second. The guard's
  step could not pass when run. Two further under-specifications rode
  along: the plan never said which workflow each library's check
  reads, and the orphan check's module-to-file mapping is hard-coded
  to the vendored source root. **Fix**: the CI task becomes 1.4 and
  the guard 1.5; the guard's step now carries a per-library table of
  library, source root and workflow.
- B3 (seven commit messages, types outside the documented list). The
  documented set is `feat | fix | doc | style | refactor | test |
  chore | perf | ci`, and `.claude/rules/ci-and-workflow.md`
  disambiguates this exact confusion: the commit type is `doc`,
  singular, while `docs/<topic>` is the branch prefix, "deliberately
  distinct". The plan used `docs(…)` five times and invented
  `build(…)`, which occurs zero times in the last 400 commits.
  **Fix**: `doc(…)` throughout; `chore(deps)` for the dependency
  change. One reviewer rated this serious and the other blocker; the
  higher governs.

## Serious

- S1 (Task 1.2, the bibliography sketch). Wrong in every field.
  Verso defines no `Coe String (Doc.Inline Manual)`, so each string
  field must be `inlines!"…"`; `pages` is `Option (Nat × Nat)`, not a
  string pair; neither `Article` nor `InProceedings` has a DOI field,
  so the DOI belongs in `url`; `InProceedings` requires a `booktitle`
  the plan never named; and the sketch's title line was 116 columns,
  which `linter.style.longLine` rejects under `warningAsError`.
  **Fix**: the step is rewritten with the real types, and the values
  come from a new References section.
- S2 (seven `citep` occurrences). `{citep}[key]` is backwards: the
  citation key is a role argument, so `many1` sees none and errors,
  and the key renders as literal text. Verso's own tests and the Lean
  reference manual write `{citep hoare69}[]`. **Fix**: `{citep
  key}[]` throughout.
- S3 (all eighteen file templates, module docstrings).
  `.claude/rules/lean-coding.md` states twice that a `/-! … -/` module
  docstring is mandatory after imports, and §3.1 confirms it as an
  authored obligation for this library precisely because no linter
  reaches it — so nothing in the plan would ever detect the omission.
  It is also ordering-sensitive: `#doc` replaces the command parser
  for the rest of the module, so the docstring cannot be retrofitted
  below it. **Fix**: every template carries one, and Global
  Constraints records the ordering.
- S4 (Phases 4 and 5, the linter). Steps A–E never run
  `lake lint -- GebLeanDocs`, and `scripts/pre-commit.sh` runs a bare
  `lake lint` that does not reach the library. But §3.3 requires a
  `nolints` entry per declaration a Part I `lean` block introduces,
  and Task 4.3 adds such a block. The first detection would have been
  twelve commits later. **Fix**: Step C2 runs the linter and appends
  the reported pairs.
- S5 (Task 1.1, a knowable option). `linter.hashCommand` belongs to
  `mathlibStandardSet`, which the package enables, and every `#doc` is
  a `#`-command; the lakefile already disables it twice for that
  reason. Deferring it to discovery was unnecessary. **Fix**:
  `weak.linter.hashCommand = false` is stated from the start.
- S6 (Task 0.2, the probe). Its purpose is open questions 2 and 3, and
  it exercised neither. `verso.code.warnLineLength` is checked by the
  `lean` block alone — §3.2 records that `signature` does not check
  it — so the one option the plan hard-codes went unvalidated; and
  "how many entries the Part I `lean` blocks add" is unanswerable from
  a probe with no `lean` block. The probe also omitted
  `deftech`/`tech`, `margin`, `:::table` and `citep`, and never ran
  the generator, so every generation-time diagnostic and every
  option-less warning of §3.2 went unprobed. **Fix**: the probe now
  carries all of them, the spike gains the executable, and Step 4 runs
  the generator.
- S7 (Task 3.1 Step 4). Both lines after the `cd` were shell comments,
  so the only verification that Appendix B — which drives all six
  Phase 5 tasks — is correctly transcribed executed nothing and passed
  unconditionally. **Fix**: names are emitted as `#check` lines into a
  temporary `GebLeanTests` module and built.
- S8 (Task 3.1 Step 1, the count). The plan's own loop yields 312, not
  309; §4.3's figure is taken after stripping comments, and three
  matches are wrapped docstring lines beginning at column zero with a
  declaration keyword. The executor's first quantitative checkpoint
  would have failed. **Fix**: 312 stated, with the three named.
- S9 (Tasks 3.1 and 4.0, the plan's own TOC). Both edit this file's
  appendices, adding `###` headings, and neither ran doctoc.
  `scripts/pre-push.sh` exits non-zero if any TOC would change, so the
  push gate would fail up to fourteen commits later. **Fix**: Task 3.1
  gains a doctoc and markdownlint step; Task 4.0 is deleted (M1).
- S10 (Task 5.1, the correspondence table). "From §6's terminology
  table extended with the Lean names" yields six rows — the eq. (1)
  vocabulary alone — where §4.2 item 1 calls for the paper-to-code
  correspondence for the whole vocabulary. **Fix**: one row per
  Appendix A term, seventeen, with the columns stated.
- S11 (Task 5.1, the terminology-index pointer). §4.2 item 1 requires
  one and §2.2's facility table lists no cross-page addressing role,
  so the executor would have invented a construct whose failure
  nothing in Steps A–E detects. **Fix**: the chapter names the index
  in prose rather than linking, with a note to use a role if execution
  finds one.
- S12 (granularity, Tasks 3.1 and 5.2–5.5). "For each declaration
  decide covered or excluded" was one checkbox over 309 declarations;
  each Phase 5 chapter task was one checkbox over twenty to forty
  `docstring` blocks. **Fix**: Task 3.1's classification is one step
  per source module, plus a pass for the endpoint modules; the commit
  stays at task granularity so the review gate is unchanged.

## Minor

- M1 (Appendix A and Task 4.0). One reviewer argued both sides and
  split the verdict: Appendix B is legitimate — a work product with an
  owner, a rule and a numeric acceptance band, placed where §4.3
  requires — while Appendix A defers five binary decisions that cost
  nothing to make now, to a task with no Files block, no Interfaces
  block, no verification and no commit message. **Fix**: Appendix A is
  filled, with the rule that settles §13 open question 4 stated — a
  term earns a `deftech` when a chapter other than its own refers to
  it — and Task 4.0 is deleted.
- M2 (Task 3.1, the endpoint declarations). The enumeration ranged
  over the ten covered modules only, so the seven endpoint
  declarations, which §4.3 places outside the 309, never entered it
  though the rule's clause 5 covers them. **Fix**: a final pass over
  the two endpoint modules.
- M3 (Tasks 1.2 and 6.2, the output subdirectory). `_out/html-multi`
  was asserted where the spec fixes only `_out`. **Fix**: the checks
  now `find` under `_out` without naming a subdirectory.
- M4 (Task 6.2 Step 3). "Open … in a browser" is not executable by an
  agent, and it was the only check on chapter nesting, the terminology
  index and the bibliography. **Fix**: a grep over the emitted HTML
  for the chapter titles, a `deftech` term and a bibliography entry.
- M5 (Task 1.3 Step 3). "At least fifteen greater than the count
  before the edit" had no recorded baseline. **Fix**: 925 stated, so
  the assertion is `>= 940`.
- M6 (Task 6.1 Step 5). The markdownlint invocation omitted the
  `--config` and `--no-globs` flags `scripts/pre-push.sh` uses, and
  `npx` where both tools are on `PATH`; the expected output string was
  also wrong. **Fix**: matched to `pre-push.sh`.
- M7 (Task 2.1 Step 3, rule attribution). The `lake env lean` ban is
  in `.claude/rules/lean-coding.md` § Lake / build workflow, not in
  `CLAUDE.md`. **Fix**.
- M8 (Task 1.2 Step 6). The `docBlame` cross-reference named Task 1.4,
  which is the CI step; the nolints work is Task 1.3. **Fix**.
- M9 (File structure). The appendix row paired A and B with their
  tasks in the wrong order. **Fix**: only Appendix B remains
  task-produced.
- M10 (Task 0.1, `lake build verso`). Lake resolves `verso` to Verso's
  own CLI executable, building more than this design uses. **Fix**:
  `lake build VersoManual`.
- M11 (Task 0.1, `rm -rf .lake/build`). Clearing the root package's
  build products forces a `GebLean` rebuild before the probe, which
  imports `GebLean.Ramified.AlgSig`, can elaborate. **Fix**: subsumed
  by B1 — no copy is made, so nothing is cleared.
- M12 (Global constraints, the column limit). "100-column limit" was
  unqualified; it binds `.lean`, while the Markdown this plan writes
  is bound by `MD013`'s 80. **Fix**: both stated, with the note that
  `linter.style.longLine` reaches prose inside a `#doc` body.
- M13 (the acceptance criterion's breadth). It checked `plausible`
  alone, though `lake update` re-resolves every root require and
  Verso's manifest may also pin `batteries`, `aesop`, `Qq`,
  `proofwidgets` or `Cli`. **Fix**: Task 0.1 Step 4 diffs the whole
  manifest and requires additions only.
- M14 (the branch). The plan named no branch though decision 10 fixes
  one plan on one branch and `CLAUDE.md` binds spec, plan and code to
  it. **Fix**: stated in the header.
- M15 (Phase 5 preamble, `elabMarkdown`). Only the missing-docstring
  failure was named; an inline code span in a rendered docstring that
  no heuristic accepts also warns, and `warningAsError` promotes it.
  **Defer with rationale**: §3.2 records the exposure as currently
  zero, no docstring in the twelve contributing modules containing a
  fence, and Step C2 now surfaces any instance at the chapter that
  introduces it. Recording a remedy for a diagnostic that cannot
  currently fire would be speculative.
- M16 (`{include N …}` levels). `closePartsUntil` is a no-op at the
  level the part indexes use, so `{include 0 …}` and `{include 1 …}`
  behave identically there, and the plan's "0 for parts, 1 for
  chapters" reads as load-bearing when it is not. **Defer with
  rationale**: the values are harmless and match Verso's own
  `Releases.lean`; changing them would be churn. The plan does not
  claim they are load-bearing.

## Cosmetic-taste

- c1 ("go/no-go", "warm cache", "surfaces here", "whole purpose",
  "falls far outside that band"). Colloquialism and metaphor.
  **Fix**: restated where the phrasing survived the Phase 0 rewrite.
- c2 (markup for emphasis). `**before**`, `**end**`, `**same**`,
  `**not**` used for emphasis rather than delineation. **Fix**.
- c3 ("gate" throughout). `docs/process.md` names it in an example
  list qualified by "where not specific technical terms", and it is
  this repository's specific technical term for a mechanical
  build-time check, used as such in `CLAUDE.md` and both rule files.
  **Reject as cosmetic-taste**: the carve-out applies.
- c4 (the absolute path in roughly twenty commands). It carries a
  first name and local-machine detail, against `CLAUDE.md` and
  `.claude/rules/markdown-writing.md`. **Defer with rationale**: about
  twenty other committed plans and specs use the same form, so
  changing it here alone would make this document the outlier; the
  substitution is a repository-wide question, not this plan's.
- c5 (`open Verso.Genre.Manual` against `open Verso.Genre Manual`).
  Both are correct and both match upstream practice — the former in
  modules defining terms, the latter in `#doc`-bearing modules.
  **Reject as cosmetic-taste**: the distinction is real.
- c6 (the stub body "This chapter is not yet written"). Transient
  text, bounded to the branch. **Fix**: "Written by Task N", which
  names the owner rather than describing a state.
- c7 (line-number references in the File structure table). They drift
  with any edit above them. **Defer with rationale**: they locate two
  anonymous instances that have no name to cite until Task 2.1 gives
  them one, which is the task those references serve.

## Verified without defect

- **Spec coverage is complete.** Every one of §11's thirteen
  deliverables has an owning task; all eleven §1 decisions and all
  four §13 open questions are discharged. No scope creep: the only
  additions beyond the spec are the guard's negative test, the final
  verification, and the `sourceLink`/`issueLink` values filling §3.1's
  ellipses.
- **`#doc (Manual) "…" =>`, `{name}`, `{docstring}`, `:::table` and
  the `signature` fence** are the real syntaxes; `open Verso.Genre
  Manual` and `open Verso.Genre.Manual` are both correct in their
  places; `manualMain (%doc …) (options := …) (config := {…})`
  typechecks, and `sourceLink`/`issueLink` are reachable `HtmlConfig`
  fields.
- **The `signature` presentation** reproduced in the probe and Task
  4.1 is definitionally equal to the real `FreeAlg.recurse`, differs
  only in binder names inside `g`'s type, and matches all four outer
  binders by name.
- **The `docBlame` nolints name** round-trips through
  `toString`/`String.toName`; `runLinter` reads
  `scripts/nolints.json` at the relative path CI's working directory
  resolves; `--update` does rewrite it wholesale.
- **Every declaration the plan names across Phases 4 and 5 resolves**
  in `GebLean/Ramified/`, and every module named as absent exists.
- **Repository facts** — the four scripts, the test module, the
  lakefile's positional subtable behaviour, the CI workflow's shape,
  and both instance sites — hold as described. `jj commit` is correct
  for this repository.
- **Module counts close**: seventeen library modules, eighteen files,
  fifteen carrying a `#doc`.
- The plan is markdownlint-clean and doctoc-current.

## Convergence

Not converged. Three blockers and twelve serious findings, all fixed
at this branch except M15, M16, c4 and c7, deferred with rationale,
and c3 and c5, rejected as cosmetic-taste.

Two observations. The blockers are of a kind the spec's own review
never produced, because a spec asserts and a plan executes: B1 fails
on a filesystem measurement, B2 on task ordering. And the largest
cluster — S1, S2, S5, S8 — is the same class that dominated the spec's
early rounds, external facts asserted rather than read: Verso's
bibliography types, `citep`'s argument position, a linter option
already visible in the file being edited, and a count produced by a
command the plan itself gives.
