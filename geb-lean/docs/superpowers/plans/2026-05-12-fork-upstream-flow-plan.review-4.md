# Adversarial review of fork-upstream flow plan (round 4)

## Scope

Round 4 reviews the plan after Task A insertion.

The convergence criterion is zero blocker, zero serious,
and zero minor findings; cosmetic-taste findings may
remain.

## Summary

Zero blocker, two serious, three minor, two cosmetic-taste
findings. **This round does not converge.**

The two serious findings concern (1) Task A Step A.1's
"failing test" not providing a TDD signal that isolates
the config change from the file move, and (2) Task A's
premise being incomplete — the existing
`docs/superpowers/plans/` directory already contains 58
historical plan files (dated 2026-03-19 through
2026-05-06) that the plan does not mention, so the actual
asymmetry is "plans split between `plans/` and
`docs/superpowers/plans/`" rather than "specs at A, plans
at B".

## Defects

### 1. Step A.1 Test 1 does not isolate the config change

**Severity**: Serious.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
lines 218-228 (Test 1 of Step A.1).

**Defect**: The test invokes `markdownlint-cli2` with the
literal-path prefix on
`:docs/superpowers/plans/2026-05-12-fork-upstream-flow-plan.md`.
That file does not exist at the new path until A.4 moves
it, so the test's pre-fix state is dominated by the
absent-file ENOENT error rather than the config state.
The post-fix state (after A.4 moves the file AND A.2
updates the config) reports `Linting: 1 file(s)` /
`Summary: 0 error(s)`. The test distinguishes before from
after, but the distinguishing factor is "did the file
move?", not "did the config change?". Step A.1's claim to
provide a TDD signal for the config update is misleading.

**Suggested fix**: drop the TDD failing-test framing for
Step A.1; describe A.1 as a non-TDD config edit and rely
on Step A.6's lint runs after the move for verification.

### 2. Task A's premise omits the existing destination contents

**Severity**: Serious.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
lines 186-196 (Task A preamble) and lines 273-289
(Step A.3).

**Defect**: Task A's premise — "a workstream-time
observation that specs live at `docs/superpowers/specs/`
but plans live at `plans/`" — and Step A.3's heading
"Move the historical (pre-cutover) plans" together imply
that all historical plan files live at `plans/`. The
working copy contradicts this: `docs/superpowers/plans/`
already contains 58 dated plan files (2026-03-19 through
2026-05-06), none of which the plan mentions or accounts
for. The actual asymmetry is not "specs at A, plans at
B" but "plans split between A and B"; Task A's effect is
to consolidate `plans/` into the established
`docs/superpowers/plans/`. Additionally, "6 historical
pre-cutover" mis-classifies the 2026-05-09
cutover-effecting plan and its reviews (which are not
strictly pre-cutover).

**Suggested fix**: rewrite Task A's preamble to state
that `docs/superpowers/plans/` already exists with
historical content (58 files dated 2026-03-19 to
2026-05-06), and that the move consolidates the
remaining 10 plan files from `plans/` (created in or
around the cutover window) into the established
directory. Replace "6 historical pre-cutover, 4 current
workstream" with the precise breakdown: 1 pre-cutover
(2026-05-07), 5 cutover-effecting (2026-05-09 plus 4
reviews), 4 current workstream (2026-05-12 plus 3
reviews).

### 3. Task A defers lint and register-sweep for CLAUDE.md and README.md

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step A.7 and Step A.8.

**Defect**: Task A modifies `CLAUDE.md` (four sites) and
`README.md` (three sites) but does not run
markdownlint-cli2 or the register sweep against either
file after the edits. The next lint of `CLAUDE.md` is in
Task 5, and the next lint of `README.md` is in Task 8. A
markdownlint violation introduced by Task A would be
attributed to Task 5 or Task 8 and would require
unwinding intervening commits to isolate.

**Suggested fix**: add a lint-and-sweep step at the end
of Step A.7 (for CLAUDE.md) and at the end of Step A.8
(for README.md), each running the same
`markdownlint-cli2` and register-grep commands used in
Tasks 5 and 8.

### 4. Step A.9 grep pattern under-matches

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step A.9.

**Defect**: The grep pattern in Step A.9 catches only a
subset of the seven references that Steps A.7 and A.8
edit. Specifically, it misses CLAUDE.md line 91 (starts
with a bullet character), line 116 (in inline backticks),
line
198 (in a table cell), and README.md lines 60 and 95
(use "under" rather than "at"). If any of those edits
were omitted, the Step A.9 sweep would not flag the
omission.

**Suggested fix**: broaden the grep to cover the bullet,
table-cell, and "under" forms, or restate Step A.9 as a
re-read of the seven specific edits.

### 5. CLAUDE.md lines 114-116 replacement produces awkward wrap

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step A.7's third find/replace.

**Defect**: The replacement splits "Adversarial-review
iterations" onto its own short line after a four-line
block, breaking the original paragraph's 80-column-wrap
discipline. Markdownlint-clean (no MD013 violation), but
the paragraph reads less uniformly than the surrounding
prose.

**Suggested fix**: re-flow the paragraph after the
replacement so that line lengths approach the 80-column
limit consistently.

### 6. README.md replacements produce short leading lines

**Severity**: Cosmetic-taste.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step A.8 second and third replacements.

**Defect**: The replacement at line 60 leaves `plans live
under` on a 16-character line. The replacement at line
95 leaves a short fragment on a line. Both replacements
satisfy MD013 but produce ragged wrap.

**Suggested fix**: re-wrap the affected paragraphs after
the replacements.

### 7. Step A.6's predicted message text does not match output

**Severity**: Cosmetic-taste.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step A.6 (pre-cutover ignore check).

**Defect**: Step A.6 predicts "`0 file(s) match the
patterns` or similar". The actual markdownlint-cli2
v0.22.1 output is `Linting: 0 file(s)` / `Summary: 0
error(s)`. The "or similar" hedge covers the
discrepancy, but the quoted text is not what appears.

**Suggested fix**: replace the predicted text with the
actual output, dropping the hedge.

## Confirmed-correct claims (sample)

- Task A's quoted source text at lines 51 and 64 of
  `.markdownlint-cli2.jsonc` matches verbatim.
- CLAUDE.md lines 61, 91, 116, 198 contain the
  `plans/` references the plan cites; the find blocks
  at Step A.7 match verbatim.
- README.md lines 53, 60, 95 contain the `plans/`
  references the plan cites; the find blocks at
  Step A.8 match verbatim.
- The commit count in Step 11l (ten commits) is
  consistent with the per-task pattern.
- Task A's `jj describe + bookmark set + jj new`
  pattern matches Tasks 1-8.
- jj 0.41.0 supports the rename-detection output the
  plan expects at Step A.5.
- The new ignore pattern `2026-05-0[1-8]-*.md` covers
  the 2026-05-07 file and the existing May-1-to-May-6
  plan files in `docs/superpowers/plans/`, while not
  covering 2026-05-09 and 2026-05-12 files.
- The 2026-05-09 plan and its four review files lint
  clean under the current config.
- The JSONC syntax of the proposed two-entry
  replacements remains valid.
