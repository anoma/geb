# Adversarial review of fork-upstream flow plan (round 5)

## Scope

Round 5 reviews the plan after round-4 fixes to Task A.

The convergence criterion is zero blocker, zero serious,
and zero minor findings; cosmetic-taste findings may
remain.

## Summary

Zero blocker, two serious, three minor, one cosmetic-taste
finding. **This round does not converge.**

The two serious findings are: (1) Task A's enumeration of
files to move is stale — the 2026-05-12 set now contains
four review files (`.review-1.md` through `.review-4.md`),
not three, so Step A.3 leaves `.review-4.md` behind in
`plans/`; and (2) Step A.5's Test 1 uses the literal-path
prefix `:`, which bypasses the config's `ignores` array
entirely, so the test does not actually discriminate
"linted (NOT ignored)" from "linted because ignores were
bypassed". Round-4 fixes 1, 2, 3, 5, 6 are in place and
correct; fix 4 introduced a new sed-based re-read whose
expected output overstates what `sed -n` will print; fix
7 left the prose grammatically self-contradictory.

## Defects

### 1. Step A.3 omits `.review-4.md`; counts are stale

**Severity**: Serious.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
lines 201-211, 280-292, and other places that cite "10
files" or "ten rename entries".

**Defect**: The plan enumerates the current-workstream
group as four files (the plan plus three reviews). The
working copy now contains four review files at that
prefix (the round-4 review became `.review-4.md`). Step
A.3's `mv` invocations move only `.review-1` through
`.review-3`, so executing the plan leaves the round-4
review behind. The Files-this-plan-touches summary, the
**Files:** block, and Step A.9's description message all
say "10 files".

**Suggested fix**: switch the move commands to globs
(`mv plans/2026-05-12-*.md docs/superpowers/plans/`)
so the move is robust against additional review files
created by further review rounds, and restate the file
counts as "≥10, plus any additional review files
created before execution".

### 2. Step A.5 Test 1 bypasses ignores via literal-path

**Severity**: Serious.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step A.5 Test 1.

**Defect**: Test 1 invokes
`markdownlint-cli2 … --no-globs
':docs/superpowers/plans/2026-05-12-fork-upstream-flow-plan.md'`.
Empirical check shows that the literal-path prefix `:`
causes the tool to lint the named file without consulting
the `ignores` array. The test therefore confirms only
that the moved file lints clean; it does not discriminate
"the date-glob ignore admits this file" from "the
catch-all ignore was never replaced".

**Suggested fix**: drop the literal-path prefix on Test
1 (invoke
`markdownlint-cli2 --config .markdownlint-cli2.jsonc
'docs/superpowers/plans/2026-05-12-fork-upstream-flow-plan.md'`).
With ignores active, the expected output becomes
`Linting: 1 file(s)` post-fix and would be
`Linting: 0 file(s)` pre-fix.

### 3. Step A.8 sed re-read expectation overstates output

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step A.8 second check.

**Defect**: After Step A.6's preceding edits to CLAUDE.md
(line 91 expanding 1→2 lines, lines 114-118 expanding
5→6 lines), line numbers in the edited file shift.
`sed -n '61p;91p;115,116p;198p'` against the edited
CLAUDE.md prints content that no longer spans the
intended replacement regions; the expected output "all
printed lines reference `docs/superpowers/plans/`" is
unsatisfiable. The README sed expectation has the same
shape.

**Suggested fix**: replace the sed line specs with a
grep-based check on the literal `docs/superpowers/plans/`
strings, or restate the verification as "no remaining
bare `plans/` references" with a count assertion.

### 4. Files-summary line-citations stale relative to A.6 / A.7

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
**Files:** block under Task A.

**Defect**: The Files summary lists "`CLAUDE.md` lines
61, 91, 115-116, 198" and "`README.md` lines 53, 60,
95". Round-4 fixes 5 and 6 broadened the actual
find/replace blocks in Step A.6 to lines 114-118 (a
five-line span) and in Step A.7 to lines 58-61 and
93-96. The summary still cites the pre-fix narrower
spans.

**Suggested fix**: bring the Files summary in line with
the broadened spans actually used in Steps A.6 and A.7.

### 5. Step A.6 expected-output prose grammatically inverts

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step A.6's expected-output paragraph.

**Defect**: The text reads "the register grep returns
only the pre-existing line that enumerates the forbidden
words as a style rule (matched by the `| grep -v` filter
excluding the 'value-laden adjectives' sentence)." A
reader parses this as either "the grep returns one
line", or "the filter excludes that line". These are
contradictory: the actual chained grep returns zero
lines.

**Suggested fix**: replace with "the register grep
returns no output (the one match on the style-rule
line is removed by the `grep -v 'value-laden
adjectives'` filter)."

### 6. Spec coverage map's Task A row is out of place

**Severity**: Cosmetic-taste.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Spec coverage map last row.

**Defect**: Task A is a process-self-update consequent on
a workstream-time observation, not on the fork-upstream
spec. Listing it in the spec-coverage map blurs the
map's purpose.

**Suggested fix**: separate this row into a Process
self-update note below the spec-coverage map, or label
the row as out-of-spec.

## Confirmed-correct claims (sample)

- The cited CLAUDE.md line numbers 61, 91, 114-118, 198
  contain the expected source text verbatim; the find
  blocks in Step A.6 match.
- The cited README.md line numbers 53, 58-61, 93-96
  contain the expected source text verbatim; the find
  blocks in Step A.7 match.
- The Step A.8 grep alternation matches the seven
  current bare-`plans/` references in CLAUDE.md and
  README.md.
- The internal A.5 / A.2 / A.3 cross-references in
  Step A.1 point at the renumbered steps consistently.
- The new ignore pattern
  `docs/superpowers/plans/2026-05-0[1-8]-*.md` covers
  the 2026-05-07 pre-cutover file and excludes the
  2026-05-09 and 2026-05-12 sets.
- `docs/superpowers/plans/` currently contains 58
  files dated 2026-03-19 through 2026-05-06.
- `docs/process.md` § Repository structure exists at
  the cited line 10.
- The lint-and-register-sweep additions at the end of
  Steps A.6 and A.7 are present.
