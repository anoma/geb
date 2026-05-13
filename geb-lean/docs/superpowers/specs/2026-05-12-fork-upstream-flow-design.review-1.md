# Adversarial review of fork-upstream flow spec (round 1)

## Summary

Eleven defects identified: two factual errors, one internal
inconsistency, four missing cases or under-specified
mechanics, three ambiguities, and one scope/test gap. The
spec's foundational shape is sound; most defects concentrate
in the hook-change description, in Op 3 / Op 6 merge-strategy
coverage, and in jj-CLI accuracy.

## Defects

### 1. `-r upstream` is not a `jj git push` remote flag

**Where**: spec line 254 (Hook and configuration changes,
`block-mutating-git.sh` deny clause).

**Defect**: The spec instructs the deny clause to match
`--remote upstream` or `-r upstream`, but in `jj git push`
the short flag `-r` is `--revisions`, not `--remote`
(`jj git push --help` confirms `--remote <REMOTE>` has no
short form; `-r/--revision <REVSETS>` is unrelated).
Matching `-r upstream` would (a) miss the actual remote
syntax `--remote=upstream` with an equals sign, and (b)
produce a false positive if any revset or bookmark is
literally named `upstream`.

**Suggested fix**: drop `-r upstream`; cover `--remote
upstream`, `--remote=upstream`, and any short form
documented later for `jj git push --remote`.

### 2. Op 3 PR-to-origin merge strategy is unspecified

**Where**: spec lines 161-176 (Op 3, divergence branch).

**Defect**: The merge-commit-strategy invariant (lines
73-79) is scoped explicitly to "cross-repository pull
requests" against upstream. Op 3 opens an
`origin`-to-`origin` PR for the
`chore/upstream-sync-<date>` branch and does not specify
its merge strategy. Squash or rebase on this internal PR
would discard the true merge commit whose parents are
`origin/main` and `main@upstream`, defeating the entire
purpose of the divergence branch.

**Suggested fix**: state explicitly that the Op 3 PR is
also merged with `--merge`, and add the same restriction
to the invariants section as a generalised "merge-commit
strategy on any PR that synchronises with upstream".

### 3. Op 6 fast-forward depends on an unstated precondition

**Where**: spec lines 210-226 (Op 6) and the lockstep
paragraph at lines 98-102.

**Defect**: Op 6 asserts that `origin/main` can
fast-forward to `upstream/main` after an upstream PR
merges. This holds only when the PR's head branch was
descended from `origin/main` at the time of the merge.
The spec does not state this precondition. If between
opening the upstream PR and merging it any new commit
landed on `origin/main` (for example, a routine topic
branch merged through Op 1's fork-first flow), then
`origin/main` is no longer an ancestor of the new
`upstream/main` and the fast-forward fails.

**Suggested fix**: either prohibit pushes to `origin/main`
while an upstream PR is open (an additional invariant),
or describe a fallback to the Op 3 divergence-branch flow
when Op 6's fast-forward refuses.

### 4. Missing case — upstream change conflicts with open topic branches

**Where**: § Operations as a whole (lines 104-226).

**Defect**: The six operations cover the main-to-main
synchronisation channel. They do not cover the case where
an upstream change has landed on `upstream/main` and is
already merged into `origin/main` via Op 3, but an
existing topic branch on `origin` (open work) was branched
from an earlier `origin/main` and now needs to incorporate
the upstream movement before it can be opened as an
upstream PR. There is no Op for "rebase or merge the
upstream movement into an in-progress topic branch".

**Suggested fix**: add an Op covering rebase or merge of
the synchronised `origin/main` into open topic branches.

### 5. Permissions test does not match the operation requirement

**Where**: spec lines 398-408 (T8) and Op 5 at lines
199-208.

**Defect**: T8 asserts `.permissions.push == true` and
the prose claims this verifies "the gh authentication
context can push to upstream (required for Op 5)". But
Op 5 (`gh pr merge --merge`) on a protected branch
(`upstream/main` is protected, confirmed by
`gh api repos/anoma/geb/branches/main`) typically
requires either admin permission or a specific bypass
role under branch-protection rules; pull-request merging
on a protected branch is not implied by `permissions.push
== true`. The current authenticated context returns
`admin=false, push=true`, so T8 passes while Op 5 may
still be rejected at merge time.

**Suggested fix**: T8 either checks for an admin-equivalent
permission, queries the branch-protection ruleset
directly, or is replaced by a dry-run-style probe; the
prose is corrected to reflect that push permission alone
does not guarantee merge capability on a protected
default branch.

### 6. "Current state" claim invalidated by the spec's own changes

**Where**: spec lines 50-52 (Current state).

**Defect**: The Current state bullet states "The hook
lets every `jj git …` invocation through unconditionally."
The Hook and configuration changes section (lines 249-255)
explicitly inserts a deny clause that breaks this
universality. Although "current" is true at spec time, the
contradiction with the spec's own change makes it easy
for a later reader to take the Current-state claim out
of context.

**Suggested fix**: either move this bullet into a "Pre-spec
state" header that is explicit about its temporal scope,
or note inline that the spec's Hook changes section
narrows this property.

### 7. `jj` divergence merge instructions are imprecise

**Where**: spec lines 162-170 (Op 3 divergence branch).

**Defect**: The line `jj new main main@upstream -m "..."`
relies on the local bookmark `main` and the remote
reference `main@upstream`, but the spec does not require
that the remote bookmark be tracked beforehand
(`jj bookmark track main@upstream`). Without tracking,
the `main@upstream` revset alias resolves but downstream
operations on the local `main` bookmark may not see the
intended state. Additionally, "mark the change resolved"
is not a jj idiom; jj treats a change as resolved once
all conflict markers are removed.

**Suggested fix**: insert a `jj bookmark track
main@upstream` step (or document that fetching
auto-tracks), and replace "mark the change resolved" with
the explicit jj workflow (resolve conflicts via editing
or `jj resolve`, then verify with `jj status`).

### 8. Ambiguity about which `main` is the merge parent

**Where**: spec line 165 (`jj new main main@upstream`).

**Defect**: `main` here is the local bookmark name. The
local bookmark and `main@origin` may have drifted apart
in operations the user has performed (jj does not move
the local bookmark automatically on fetch). The spec
does not say whether the intended merge parent is the
local `main`, `main@origin`, or both must coincide.

**Suggested fix**: spell out the precondition
(`main == main@origin`) and the corrective command if
they differ, or use `main@origin` explicitly in the
merge invocation.

### 9. T4 does not exercise any new spec behaviour

**Where**: spec lines 360-368 (T4).

**Defect**: `git push upstream main` is denied by the
current hook unconditionally under the catch-all `*` case
that rejects every non-allowlisted subcommand
(`block-mutating-git.sh` lines 443-490). The denial
message already contains `block-mutating-git: blocked`
and a `jj equivalent:` line. T4's expectations are met
without any spec-introduced change, so T4 does not
validate the spec's hook modifications.

**Suggested fix**: replace T4 with a test that specifically
exercises the upstream-aware behaviour the spec adds (for
example, that the `jj equivalent:` line for the upstream
push case names the spec or mentions the upstream
restriction explicitly), or remove T4 as redundant.

### 10. `--remote=upstream` equals-form not covered

**Where**: spec line 254 (Hook deny clause).

**Defect**: The deny clause is described as inspecting
"the remainder of the argument vector for `--remote
upstream` or `-r upstream`". Both forms are space
separated. The equivalent equals form `--remote=upstream`
is a standard GNU long-flag syntax that jj accepts and
the spec does not exclude.

**Suggested fix**: include `--remote=upstream` as an
additional match form, or describe the matching at the
level of "any argument-vector occurrence whose effect
selects `upstream` as the push remote".

### 11. Upstream `fetch-tags` parallelism is unjustified and inert

**Where**: spec lines 263-269 and 283-285 (per-repo jj
config).

**Defect**: The spec asserts that
`remotes.upstream.fetch-tags = "glob:cutover-*"` should
be set parallel to the existing
`remotes.origin.fetch-tags`, and that
`check-jj-setup.sh` should fail if the value differs.
But § State at spec time confirms that the
`cutover-2026-05-10` tag exists on the fork only, not
upstream; § Out of scope notes that tag synchronisation
is governed by the `fetch-tags` settings. Setting an
`upstream` glob that matches no upstream tags adds a
maintained assertion in `check-jj-setup.sh` with no
observable effect. The spec does not justify the
parallelism, and the strict-equality assertion creates a
trap if either the glob or upstream's tag namespace
later diverges.

**Suggested fix**: either justify the assertion (for
example, "in case later cutover tags propagate to
upstream") or relax it to a recommended-but-not-required
setting that `check-jj-setup.sh` does not enforce.

## Confirmed-correct claims (sample)

- `origin` URL is `ssh://git@github.com/rokopt/geb` and
  `upstream` URL is `git@github.com:anoma/geb.git`: both
  verified via `git remote -v` and `jj git remote list`.
- `remotes.origin.fetch-tags = "glob:cutover-*"` and
  `git.private-commits = "conflicts()"` are set per-repo:
  verified via `jj config list --repo`.
- No `upstream/*` refs in the local working copy: verified
  via `jj bookmark list` returning no remote-upstream
  bookmarks and `.git/refs/remotes/` containing only
  `origin/`.
- Fork-upstream divergence: rokopt/geb 5 ahead of
  anoma/geb on `main`, 0 behind; verified via
  `gh api repos/anoma/geb/compare/anoma:main...rokopt:main`.
- `cutover-2026-05-10` exists on rokopt/geb but not on
  anoma/geb: verified via `gh api` calls on each refs
  endpoint.
- `anoma/geb` default branch is `main` and the branch is
  protected: verified via `gh api repos/anoma/geb` and
  `gh api repos/anoma/geb/branches/main`.
- The pre-tool hook permits `jj git fetch --remote upstream`
  today and denies `git fetch upstream` today: verified
  by direct hook invocation.
- `gh api repos/rokopt/geb` reports
  `parent.full_name = anoma/geb`: verified by direct
  query.
