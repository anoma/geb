# Adversarial review of fork-upstream flow plan (round 10)

## Scope

Round 10 reviews the plan after round-9 minor-defect
fixes.

The convergence criterion is zero blocker, zero serious,
and zero minor findings; cosmetic-taste findings may
remain.

## Summary

Round-9's three minor defects are all fixed. A fresh
pass surfaces one new minor defect: Step 0b's commit
description body enumerates the spec and spec-review
files but omits the plan and plan-review files, even
though Step 0a explicitly states they are part of the
same change.

Counts: 0 blocker, 0 serious, 1 minor. Round 10 does
not converge.

## Defects

### 1. Step 0b body omits the plan and plan-review files

**Severity**: Minor.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step 0b.

**Defect**: Step 0a expressly enumerates the working-
copy content of the change as "the spec, the spec-
review files... the plan and its plan-review files (at
`plans/`, one per plan adversarial-review round through
convergence), and the process-self-update edits to
`CLAUDE.md` and `docs/process.md`." Step 0b then
instructs the executor to "update the change
description to reflect the final content of the change,"
but the description body only mentions the spec, the
`${n_spec}` rounds of spec adversarial review, and the
process self-update. The plan file and the plan-review
files are absent from the description body. The commit
message therefore does not reflect the final content of
the change.

**Suggested fix**: extend the description body with a
parametric reference parallel to the spec line, for
example: "together with the plan at
`plans/2026-05-12-fork-upstream-flow-plan.md` and its
plan-review files (one per plan adversarial-review round
through convergence)". Do not pin a numeric count.

## Confirmed-correct claims (sample)

- Round-9 fix 1: Step A.5 Test 1 prose now reads "false
  positives that do not verify the config change".
- Round-9 fix 2: the Branch-and-bookmark section names
  the bookmark and change_id `tqmusvlq` only; no
  ephemeral working-copy commit_id is pinned.
- Round-9 fix 3: Step 0a's Expected paragraph identifies
  `@-` by its parent role on the merge commit
  `dc02dea6`, with explicit acknowledgement that the
  `main` bookmark may have moved forward.
- `dc02dea6` is the merge commit of PR #11 (verified
  via `git log` and `jj log`).
- `main` (bookmark) is at `ba7309be` (PR #191's merge);
  the plan correctly avoids pinning `main` to
  `dc02dea6`.
- The divergent change_id state at `tqmusvlq` holds
  (two bookmarks share it).
- `jj 0.41.0` is the active version.
- `.markdownlint-cli2.jsonc`, `CLAUDE.md`, `README.md`,
  `docs/process.md`, `scripts/hooks/block-mutating-git.sh`,
  and `scripts/pre-push.sh` line citations match their
  find-blocks verbatim.
- The date-glob `2026-05-0[1-8]-*.md` correctly excludes
  only files dated 2026-05-01 through 2026-05-08.
- Step 11l's ten-commit count matches the task structure.
