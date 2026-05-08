# Adversarial review cycle 5 — author responses

Review dispatched: fresh-context Agent reading only the spec (not
prior cycles' responses).

## Blocker

### B1 — `jj config get --repo` is not a valid invocation

**Finding.** Verification item 11 prescribes `jj config get
--repo git.private-commits` returning `conflicts()`, but per
<https://docs.jj-vcs.dev/latest/cli-reference/>, `jj config get
<NAME>` accepts no scope flag. `--repo`, `--user`, `--workspace`
are accepted by `jj config set`, `jj config edit`, `jj config
path`, and `jj config list`.

**Response: fixed.** Item 11 rewritten to use
`jj config list --repo git.private-commits` (which lists the
per-repo setting in the per-repo layer specifically — diagnostic
for verification purposes) plus
`jj config path --repo` (which prints the resolved file path
and confirms it is in user-config-dir, not under `.jj/`).

## Minor

### M1 — On-boarding lacks a self-verifier

**Finding.** A new developer runs the per-repo and per-user
`jj config set` commands, but the spec has no mechanism to
detect *whether* they ran. The pre-push diff-review gate
catches missing signing eventually, but only after several
unsigned commits may have been authored.

**Response: fixed.** Extend `scripts/pre-push.sh` with a
self-check at the top of the script:

1. `jj config list --repo git.private-commits` returns
   `conflicts()`.
2. At least one of `jj config get signing.behavior` or `git
   config --get commit.gpgsign` indicates signing is active.
3. The cutover tag is fetched locally
   (`git tag -l 'cutover-*'` is non-empty).

If any check fails, `pre-push.sh` exits non-zero with a message
pointing the developer at the on-boarding section of
`docs/process.md`. The same checks may also be run as a one-shot
`scripts/check-jj-setup.sh` invocation that the on-boarding
section instructs the developer to run after their `jj config
set` commands; this gives an immediate signal rather than
waiting for first push.

### M2 — Cutover tag fetch not in on-boarding sequence

**Finding.** Item 17's verification reads `git log --first-parent
main` against the remote, anchored at the cutover SHA recorded
in the signed tag. A fresh clone via `jj git clone` may not
mirror tags depending on remote-tracking configuration, and the
`block-mutating-git` allowlist explicitly blocks `git fetch
--tags`.

**Response: fixed.** On-boarding sequence gains an explicit
step: `jj git fetch --remote origin` after
`jj git init --colocate` (or as part of an initial `jj git
clone`). The spec verifies empirically (in the plan) that
`jj git fetch --remote origin` mirrors annotated tags from
origin into the local repo by default; if jj 0.40 does not
do this, the plan's smoke test discovers the gap, the
`block-mutating-git.sh` allowlist gains an explicit
`git fetch origin 'refs/tags/cutover-*:refs/tags/cutover-*'`
exception (with rationale recorded), and the on-boarding
sequence picks the right invocation. Both branches are
documented; the choice is made empirically at plan-execution
time.
