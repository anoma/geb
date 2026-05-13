# Adversarial review of fork-upstream flow spec (round 4)

## Scope

Round 4 reviews:

- The whole spec.
- The § Adversarial review of specs and plans in
  `docs/process.md`.
- The adversarial-review bullet in `CLAUDE.md` § Hard rules
  and the two rows in § Phase-driven workflow.

The convergence criterion is zero blocker, zero serious,
and zero minor findings; cosmetic-taste findings may
remain.

## Summary

One minor finding identified: an underspecified
interaction between the new "git clone or jj git clone"
precondition note and the existing step 1
(`jj git init --colocate`) of the onboarding sequence. The
four round-3 defects are otherwise resolved. This round
does not converge.

## Defects

### 1. `jj git clone` precondition does not match step 1

**Severity**: Minor.

**Where**:
`docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`
lines 476-484 (§ Documentation changes, `docs/process.md`
bullet); together with `docs/process.md` lines 200-219
(§ jj colocated mode onboarding sequence, step 1).

**Defect**: The round-3 fix introduces a precondition note
at the top of the onboarding sequence stating "the
sequence below assumes the working copy was created by
`git clone ssh://git@github.com/rokopt/geb.git geb` or by
`jj git clone`". Step 1 of the existing sequence is
`jj git init --colocate`. That step is appropriate after
`git clone` (it adds `jj` to an existing git working
copy) but is not appropriate after `jj git clone`:
`jj git clone` with `--colocate` produces a colocated
working copy directly, and `jj git clone` without
`--colocate` produces a non-colocated jj working copy
that the rest of the sequence is not written for. A
reader following the documented sequence after
`jj git clone` either re-runs an already-completed init
step or proceeds with a working copy structure the
sequence does not address.

**Suggested fix**: either restrict the precondition to
`git clone` only (and require a `--colocate` flag on any
`jj git clone` variant before the rest of the sequence
applies), or annotate step 1 with a conditional ("skip
this step when the working copy was created by
`jj git clone --colocate`").

## Confirmed-correct claims (sample)

- The hard-rule bullet in `CLAUDE.md` no longer lists
  subsection names that mismatch `docs/process.md`; it
  references the section as a whole. Round-3 defect 2 is
  resolved.
- `docs/process.md` § Reviewer protocol now spells out
  read-only operations the reviewer may invoke and forbids
  mutating operations of any kind. Round-3 defect 3 is
  resolved.
- The last bullet of § State at spec time is now prefixed
  "External fact (not narrowed by the spec):" and is
  unambiguously distinguishable from "Pre-spec" bullets.
  Round-3 defect 4 is resolved.
- The § Documentation changes bullet for `docs/process.md`
  now names `git clone`/`jj git clone` as predecessors
  that register `origin`, plus a fallback
  `git remote add origin ...` if `origin` is absent.
  Round-3 defect 1 is substantively addressed (minor
  residue captured in defect 1 above).
- `jj git push --remote` has no documented short form;
  `-r` resolves to `--revisions`. Verified by
  `jj git push --help` on jj 0.41.0.
- `gh repo set-default --view` exits 0 with empty stdout
  when no default is set in the current clone. Verified
  by direct invocation.
- `origin` URL is `ssh://git@github.com/rokopt/geb` and
  `upstream` URL is `git@github.com:anoma/geb.git`.
  Verified via `git remote -v` and `jj git remote list`.
- The hook today permits `jj git push --remote upstream`
  (exit 0) and denies `git fetch upstream` (exit 2).
  Verified by direct hook invocation.
- `gh api repos/anoma/geb/compare/main...rokopt:geb:main`
  reports `status=identical, ahead_by=0, behind_by=0`.
  Verified by direct invocation.
- The CLAUDE.md § Phase-driven workflow rows for
  "Adversarial review (spec)" and "Adversarial review
  (plan)" reference the convergence threshold consistently
  with the § Hard rules bullet and with
  `docs/process.md` § Convergence criterion.
- The pre-push checklist as described by
  `.claude/rules/ci-and-workflow.md` § Pre-push checklist
  matches the spec's characterisation in § State at spec
  time of `scripts/pre-push.sh`.
