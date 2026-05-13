# Adversarial review of fork-upstream flow plan (round 9)

## Scope

Round 9 reviews the plan after round-8 minor-defect fixes.

The convergence criterion is zero blocker, zero serious,
and zero minor findings; cosmetic-taste findings may
remain.

## Summary

Round-8's three minor defects are all fixed. A fresh pass
surfaces three new minor defects: a register-list word in
plain prose, a stale commit_id in the Branch-and-bookmark
section, and stale `main`-bookmark claims that drift
between the plan's introductory snapshot and the current
state of the working copy.

Counts: 0 blocker, 0 serious, 3 minor. Round 9 does not
converge.

## Defects

### 1. "actually" in plain prose (register-list word)

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step A.5 Test 1 explanation paragraph.

**Defect**: The line reads "that don't actually verify
the config change." The word "actually" is on the
markdown-writing register list. Other "actually" hits
flagged by the register grep sit inside the grep command
literals themselves and are self-referential filter
text; this one is plain prose.

**Suggested fix**: rephrase, e.g. "false positives that
do not verify the config change".

### 2. Stale commit_id snapshot in Branch-and-bookmark

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Branch-and-bookmark section.

**Defect**: The plan asserts the bookmark
`docs/fork-upstream-flow` is "currently at commit_id
`a26a4ecc`". The actual current commit_id has drifted
under jj's amend / describe flow. Commit_ids are
inherently ephemeral; the snapshot has drifted between
plan authoring and the current state.

**Suggested fix**: drop the specific commit_id from the
prose, or replace with a stable reference (the
change_id `tqmusvlq` already serves this purpose).

### 3. Stale `main`-bookmark claims in Step 0a / preamble

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
preamble's "on top of `main` at `dc02dea6`" and Step 0a's
Expected paragraph "`@-` is `main`".

**Defect**: The local `main` bookmark is no longer at
`dc02dea6` (the spec's "State at spec time" notes the
catch-up to upstream as a routine operation outside the
plan's scope). `@-`'s commit_id is still `dc02dea6` but
no longer carries the `main` bookmark; the literal
expectation "`@-` is `main`" does not match.

**Suggested fix**: rephrase the preamble and Step 0a to
identify `@-` by its parent role (the merge commit on
which the spec change is based) rather than by the
moving `main` bookmark.

## Confirmed-correct claims (sample)

- Round-8 fix to Step 0c title: the bullet now reads
  "Open a new empty change on top of the spec change
  for Task A's plan-directory normalisation".
- Round-8 fix to Step 0a's Expected paragraph: the
  forward reference to Step 0a' is removed.
- Round-8 fix to Step A.9 message: the commit-log body
  uses compositional prose with no `${n_total}` or
  `${n_plan_reviews}` substitution.
- `.markdownlint-cli2.jsonc`, `CLAUDE.md`, `README.md`,
  `docs/process.md`, `scripts/hooks/block-mutating-git.sh`,
  and `scripts/pre-push.sh` line citations all match
  their find-blocks verbatim.
- Step A.5 Test 1's discriminator is correct given the
  new date-glob.
- The plan is markdownlint-clean.
- All historical files at `docs/superpowers/plans/` are
  dated 2026-03-19 to 2026-05-06 and match the
  date-glob ignore.
