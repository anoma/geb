# Adversarial review of fork-upstream flow spec (round 5)

## Scope

Round 5 reviews:

- The whole spec.
- The § Adversarial review of specs and plans in
  `docs/process.md`.
- The adversarial-review bullet in `CLAUDE.md` § Hard
  rules and the two rows in § Phase-driven workflow.

The convergence criterion is zero blocker, zero serious,
and zero minor findings; cosmetic-taste findings may
remain.

## Summary

Zero blocker, zero serious, and zero minor findings. The
round-4 minor defect about the `jj git clone` precondition
note is resolved: the spec now restricts the precondition
to `git clone ssh://git@github.com/rokopt/geb.git geb` and
annotates `jj git clone --colocate` as an alternative that
skips step 1 (`jj git init --colocate`) and continues from
step 2. This matches the first option in the round-4
suggested fix. **This round converges.**

## Defects

None.

## Confirmed-correct claims (sample)

- Round-4 fix is in place at
  `docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`
  lines 477-487: the precondition note specifies
  `git clone ssh://git@github.com/rokopt/geb.git geb` as
  the assumed entry path; the `jj git clone --colocate`
  alternative is documented as arriving at an equivalent
  state but skipping step 1 and continuing from step 2.
  Step 1 of the onboarding sequence in `docs/process.md`
  § jj colocated mode is `jj git init --colocate`, which
  is the correct step to skip under
  `jj git clone --colocate`.
- `jj git clone` in jj 0.41.0 treats `--colocate` as the
  default per `jj git clone --help` ("This is the default,
  and this option has no effect, unless the git.colocate
  config is set to `false`"). Naming `--colocate`
  explicitly remains correct and is robust to a later
  user-level config that flips the default.
- `jj git push --remote` has no documented short form;
  `-r` resolves to `--revisions`. Verified by
  `jj git push --help` on jj 0.41.0. The spec's
  § Hook and configuration changes deliberate exclusion
  of `-r upstream` from the deny match is consistent.
- `gh repo set-default --view` exits 0 with empty stdout
  when no default is set in the current clone. Verified
  by direct invocation. T10's corrective-trigger semantics
  hold.
- `origin` URL is `ssh://git@github.com/rokopt/geb` and
  `upstream` URL is `git@github.com:anoma/geb.git`.
  Verified via `git remote -v` and `jj git remote list`.
  Matches the § Remote roles table.
- The hook today denies `git fetch upstream` (exit 2,
  message "only 'git fetch origin' is on the allowlist")
  and permits `jj git push --remote upstream` (exit 0).
  Verified by direct invocation of
  `scripts/hooks/block-mutating-git.sh`. The hook's two
  changes proposed in § Hook and configuration changes
  match the current behaviour the spec narrows.
- `scripts/pre-push.sh` runs check-jj-setup, lake test,
  lake lint, markdownlint-cli2, and check-axioms.sh in
  that order, then prints step-6 reminders. Matches the
  spec's characterisation in § State at spec time and
  the § scripts/pre-push.sh change description.
- `scripts/check-jj-setup.sh` asserts
  `git.private-commits = "conflicts()"` and
  `remotes.origin.fetch-tags = "glob:cutover-*"` but
  does not assert any `remotes.upstream.fetch-tags`
  value. Matches the § scripts/check-jj-setup.sh
  statement that no new mandatory assertion is added.
- The `CLAUDE.md` § Hard rules adversarial-review bullet
  states the convergence threshold (zero blocker, zero
  serious, zero minor) and references
  `docs/process.md` § Adversarial review of specs and
  plans as a whole, rather than naming subsections. The
  two § Phase-driven workflow rows are consistent.
- `docs/process.md` § Convergence criterion text matches
  the `CLAUDE.md` § Hard rules adversarial-review bullet
  (zero blocker, zero serious, zero minor; cosmetic-taste
  may remain).
- `docs/process.md` § Reviewer protocol enumerates the
  read-only operations the reviewer may invoke and
  forbids mutating operations of any kind. The protocol
  is consistent with this round's procedure.
