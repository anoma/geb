# Adversarial review of fork-upstream flow plan (round 6)

## Scope

Round 6 reviews the plan after round-5 fixes to Task A.

The convergence criterion is zero blocker, zero serious,
and zero minor findings; cosmetic-taste findings may
remain.

## Summary

One serious finding. Round 5's fixes to defects 1, 2, 4,
5, and 6 are correctly in place. Round 5's fix to defect
3 introduced a new serious defect: the `jj diff --summary`
rename format under jj 0.41.0 uses brace expansion
(`R {old => new}/<file>`) rather than two whitespace-
separated paths, so the grep pattern selected by the fix
returns 0 in all cases and aborts execution. Round 6 does
not converge.

## Defects

### 1. Step A.4 grep pattern returns 0 under jj 0.41.0

**Severity**: Serious.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step A.4.

**Defect**: Step A.4 instructs the executor to verify
the rename count with
`jj diff -r @ --summary | grep -c '^R plans/'`,
expecting the value of `$n` from Step A.2. Under jj
0.41.0 (the version pinned in `CLAUDE.md` and confirmed
locally via `jj --version`), `jj diff --summary` formats
renames as
`R {plans => docs/superpowers/plans}/<file>.md`, with
the old and new path-prefixes brace-expanded inside a
single token. The token after the leading `R` is the
literal `{plans` — not `plans/<file>.md`. The
accompanying
prose describes the format inaccurately ("`R plans/
<file>.md docs/superpowers/plans/<file>.md`"); the
actual format has no second whitespace-separated path
field. The executor will see exit-status 1 with stdout
`0` and treat the step as a failed verification,
halting the workstream at A.4. The move itself succeeded
— only the verification check is broken — so the failure
mode is benign but blocks execution. Defect 3 from round
5 is therefore not resolved; the fix substituted one
stale check for a syntactically-broken one.

**Suggested fix**: replace the grep pattern with
`'^R {plans => docs/superpowers/plans}/'`, or with the
remote-agnostic `'^R '` plus a separate check that the
file count of `docs/superpowers/plans/` increased by
`$n`. Update the prose to reproduce the brace-expanded
format verbatim.

## Confirmed-correct claims (sample)

- The glob `mv plans/*.md docs/superpowers/plans/`
  expands to every `.md` file in `plans/` at execution
  time, including all `.review-N.md` files.
- `markdownlint-cli2 --config .markdownlint-cli2.jsonc
  '<path>'` without the `:` literal-path prefix and
  without `--no-globs` honours the `ignores` array:
  `2026-05-12-...` produced `Linting: 1 file(s)`,
  `2026-05-07-...` produced `Linting: 0 file(s)`.
- The line citations in the Files block (CLAUDE.md 61,
  91, 114-118, 198; README.md 53, 58-61, 93-96) match
  the current file content.
- The Step A.8 alternation grep currently flags exactly
  the seven pre-edit bare-`plans/` references in
  `CLAUDE.md` and `README.md` and does not false-match
  on `docs/superpowers/plans/**` in `docs/process.md`.
- Step A.6's grammatical phrasing of "the spans at lines
  114-118 and 91 are widened by Steps A.6" reads cleanly
  (round-5 defect 5 is resolved).
- The Task A row no longer appears in the spec-coverage
  map; it is separated into a paragraph below the table
  (round-5 defect 6 is resolved).
- Lines 55-64 and 335-342 of
  `scripts/hooks/block-mutating-git.sh` match the
  find-blocks quoted in Tasks 1 and 2 verbatim.
- The `deny` function is defined at line 144 of
  `block-mutating-git.sh`, after the jj-pass-through
  block; the plan's rationale for a hand-rolled deny in
  Task 2 is consistent with the file structure.
- The plan correctly omits matching `-r` as `--remote`:
  in jj 0.41.0 `-r` is the short form of `--revisions`.
