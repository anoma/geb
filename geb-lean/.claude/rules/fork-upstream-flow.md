# Fork–upstream flow rules

This file is the working-time reference for the
fork–upstream flow. The rationale layer lives in
`docs/process.md` § Fork–upstream relationship; the
design spec is at
`docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`.

## Invariants

- **Fork-first.** Push every local commit to `origin`
  before any further interaction with `upstream`.
- **No direct push to upstream.** Send commits to
  `upstream` only through merged pull requests opened
  from `origin`. The mechanical denial lives in
  `scripts/hooks/block-mutating-git.sh`.
- **Merge-commit strategy on synchronising PRs.** Use
  the merge-commit strategy (`gh pr merge --merge`) for
  every pull request that updates `origin/main` or
  `upstream/main`. Avoid squash and rebase: they
  rewrite history and break the append-only and
  fast-forward-sync contracts.
- **Append-only on both default branches.** Never
  rewrite the history of `origin/main` or
  `upstream/main`.
- **No `origin/main` movement while an upstream PR is
  open.** Pause topic-branch merges into `origin/main`
  between opening an upstream PR (Op 4) and the
  resulting sync (Op 6).
- **Lockstep after merge.** After an upstream PR
  merges, fast-forward `origin/main` to
  `upstream/main` before opening any further upstream
  PRs.

## Remote roles

| Remote | URL | Role | Mutating ops permitted from here? |
| --- | --- | --- | --- |
| origin | `ssh://git@github.com/rokopt/geb` | Daily fork; push target for topic branches. | Yes (gated by user line-by-line review). |
| upstream | `git@github.com:anoma/geb.git` | Canonical repository; PR target only. | No (fetch only; PRs via `gh`). |

## Operations

### Op 1 — Push a topic branch to the fork

```sh
bash scripts/pre-push.sh
jj git push --remote origin -b <bookmark>
```

For the PR that follows, ignore the "Create a pull
request" URL printed by `jj git push` (it defaults to
upstream); use `gh pr create --base main --head <branch>`
with `gh repo set-default rokopt/geb` configured.

### Op 2 — Fetch from upstream

```sh
jj git fetch --remote upstream
```

### Op 3 — Synchronise fork main from upstream

Fast-forward case (`origin/main` is purely behind):

```sh
jj git fetch --remote upstream
jj bookmark set main -r main@upstream
bash scripts/pre-push.sh
jj git push --remote origin -b main
```

Divergence case (both have unique commits):

```sh
jj git fetch --remote upstream
jj new main@origin main@upstream \
  -m "chore(sync): merge upstream/main into origin/main"
jj bookmark create chore/upstream-sync-<date> -r @
# resolve conflicts via editing or `jj resolve`;
# verify with `jj status` that no conflict markers remain
bash scripts/pre-push.sh
jj git push --remote origin -b chore/upstream-sync-<date>
```

Open an internal PR against `origin/main` and merge
with `--merge`.

### Op 4 — Open a cross-repository PR to upstream

```sh
gh pr create \
  --repo anoma/geb \
  --base main \
  --head rokopt:<branch-name> \
  --title '<user-authored title>' \
  --body  '<user-authored body>'
```

Title and body are authored by the user (no
LLM-drafted text in user-facing channels). The
invocation is gated by the user-line-by-line-review
rule (`CLAUDE.md` § Hard rules).

### Op 5 — Merge the upstream PR

```sh
gh pr merge <pr-number> --repo anoma/geb --merge
```

Use `--merge` (merge-commit strategy). Requires that
the authenticated `gh` context satisfies the upstream
branch-protection ruleset.

### Op 6 — Synchronise fork main back after upstream merge

```sh
jj git fetch --remote upstream
jj bookmark set main -r main@upstream
bash scripts/pre-push.sh
jj git push --remote origin -b main
```

Falls back to Op 3's divergence branch if
`origin/main` moved during the upstream PR's open
window.

### Op 7 — Propagate upstream movement to open topic branches

```sh
jj git fetch --remote origin
jj rebase -s <topic-branch-base> -d main@origin
```

Rebase each topic branch onto the new `origin/main`.
Pushed branches undergo line-by-line review for the
force-update.
