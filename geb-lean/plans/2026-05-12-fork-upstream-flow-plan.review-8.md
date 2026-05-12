# Adversarial review of fork-upstream flow plan (round 8)

## Scope

Round 8 reviews the plan after round-7 parametrization
fixes.

The convergence criterion is zero blocker, zero serious,
and zero minor findings; cosmetic-taste findings may
remain.

## Summary

Round 7's three serious findings concerning hard-coded
counts and round-number assertions in commit-log text
are all addressed by parametric shell-substituted values
and compositional prose. The substitutions are
syntactically valid bash, and the rename-detection
pattern was confirmed against jj 0.41.0. Round 8 finds
no blocker or serious defects but raises three minor
internal-consistency issues.

Counts: 0 blocker, 0 serious, 3 minor. Round 8 does not
converge.

## Defects

### 1. Step 0c title stale: refers to Task 1, not Task A

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step 0c bullet title.

**Defect**: The Step 0c bullet title reads "Open a new
empty change on top of the spec change for Task 1's hook
work." The body states "Task A edits land here." The
body is correct (Task A is between Task 0 and Task 1);
the title is stale. A scanner reading only titles would
miss Task A.

**Suggested fix**: change the title to refer to Task A's
plan-directory normalisation.

### 2. Step 0a forward-reference to Step 0a' is misleading

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step 0a Expected paragraph.

**Defect**: Step 0a's expected-state text concludes with
"The exact file count depends on how many review rounds
were needed and is verified by Step 0a' rather than
asserted as a literal here." Step 0a' verifies the
divergent change_id state, not a file count. The
cross-reference misleads.

**Suggested fix**: remove or relocate the forward
reference; the count itself does not need an assertion
since the working-copy state has been managed across the
review loop.

### 3. Step A.9 description counts inconsistent under collision

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step A.4 and Step A.9.

**Defect**: Step A.4 admits a benign failure mode:
"a content hash collision that defeated rename detection
... the move still happened correctly at the filesystem
level and the executor proceeds to Step A.5." Step A.9
then computes `n_total` and `n_plan_reviews` from the
same rename-detection grep that A.4 allows to fail. Under
the collision path, both counts are smaller than the
actual file count and the breakdown
`1 + 5 + n_plan_reviews` does not equal `n_total`. The
description writes an inconsistent claim to the
permanent commit log.

**Suggested fix**: either compute the counts from a
collision-immune source (filesystem ls after the move,
minus the pre-existing destination contents), or drop
the count from the commit message and rely on the
compositional prose alone.

## Confirmed-correct claims (sample)

- Round-7 fix to Step 0a: the literal "five" has been
  replaced by parametric language.
- Round-7 fix to Step 0b: the description body uses
  `${n_spec}` substituted from `ls docs/superpowers/
  specs/...review-*.md | wc -l`.
- Round-7 fix to Task A intro and Step A.9: prose uses
  compositional ranges and `ls plans/*.md | wc -l` for
  totals.
- The rename-detection pattern `^R {plans =>
  docs/superpowers/plans}/` is verified against jj
  0.41.0 empirically.
- `.markdownlint-cli2.jsonc` lines 51 and 64, `CLAUDE.md`
  lines 61, 91, 114-118, 198, `README.md` lines 53,
  58-61, 87-89, 93-96, `docs/process.md` lines 200-205
  and 217-220, `scripts/hooks/block-mutating-git.sh`
  lines 55-64 and 335-342, and `scripts/pre-push.sh`
  lines 57-63 all match their respective find-blocks
  verbatim.
- Step 11l's "ten commits" matches the task structure
  (Tasks 0, A, 1-8) after Step 11k abandons the
  trailing wip change.
- The plan is markdownlint-clean.
