# Adversarial review of fork-upstream flow plan (round 2)

## Scope

Round 2 reviews the plan at
`plans/2026-05-12-fork-upstream-flow-plan.md`.

The convergence criterion is zero blocker, zero serious,
and zero minor findings; cosmetic-taste findings may
remain.

## Summary

One serious finding. Round 1's seven defects are otherwise
resolved, but the round-1 fix for the divergent-state
surfacing (defect 2) introduced a new serious defect: the
verification command in Step 0a' errors on a divergent
change_id and cannot produce the expected two-line output
as written. This round does not converge.

## Defects

### 1. Step 0a' `jj log` errors on divergent change_id

**Severity**: Serious.

**Where**: `plans/2026-05-12-fork-upstream-flow-plan.md`
Step 0a' (the `jj log -r 'tqmusvlq' --no-graph -T ...`
command).

**Defect**: With `tqmusvlq` divergent in the current
working copy, `jj log -r 'tqmusvlq' ...` exits 1 with
`Error: Change ID 'tqmusvlq' is divergent` and a hint
suggesting either `tqmusvlq/0`, `tqmusvlq/61`, or
`change_id(tqmusvlq)`. The plan's expected output ("two
lines, both with change_id prefix `tqmusvlq` ...")
cannot be observed. The form that returns the expected
two lines is
`jj log -r 'change_id(tqmusvlq)' --no-graph -T '...'`.

**Suggested fix**: replace the revset `'tqmusvlq'` with
`'change_id(tqmusvlq)'` in Step 0a'.

## Confirmed-correct claims (sample)

- Eight `jj bookmark set docs/fork-upstream-flow -r @`
  occurrences are present, one after each task's
  `jj describe` for Tasks 1-8. Task 0's `jj describe`
  correctly omits the advance because the bookmark
  already sits on the spec change at session start.
- After Task 8 the bookmark points at Task 8's commit.
  Step 11k abandons the trailing empty `wip` change at
  `@`, but the bookmark is not on `@` (it is on Task 8's
  named commit); abandon leaves the bookmark intact.
- Task 6d's quoted find block matches `docs/process.md`
  lines 200-205 verbatim, including line-wrap.
- Task 6e's quoted find block matches `docs/process.md`
  lines 217-220 verbatim.
- Task 3 cites lines 57-63 of `scripts/pre-push.sh`; the
  step-6 heredoc occupies lines 57-63 verbatim.
- Step 8b' is present and reconciles the
  § Contribution pointers contradiction by offering both
  fork and upstream clone URLs, naming the
  single-developer entry path as the fork. The quoted
  source (lines 87-89) matches `README.md` verbatim.
- Step 1f's pipeline uses `2>&1 | tee /dev/stderr |
  grep -F "origin" | grep -F "upstream"`. Verified by
  invoking the pre-fix hook with the same payload: the
  chained greps verify the conjunction on a single line,
  which is the stronger property the plan claims.
- `jj git remote list` lists both `origin` and
  `upstream`, satisfying T1's precondition.
- The plan reads markdownlint-clean: bullet structure
  and code-fence nesting (four-backtick outer fences
  around three-backtick content in Task 4) are consistent
  with `.markdownlint-cli2.jsonc`.
- Bookmark list confirms `docs/fork-upstream-flow` and
  `chore/axiom-check-fail-mode` are both marked
  `(divergent)` at change_id `tqmusvlq` with distinct
  commit_ids; the prose in Step 0a' describes this state
  accurately.
