# Fork–upstream flow design (2026-05-12)

## Motivation

The local `geb/` working copy is a `jj`-colocated clone of the
fork at <https://github.com/rokopt/geb> ("origin"). That fork is
itself a fork of <https://github.com/anoma/geb> ("upstream").
The user administrates both repositories. The existing process
documentation (`CLAUDE.md`, `docs/process.md`,
`.claude/rules/ci-and-workflow.md`) covers the relationship
between the local working copy and `origin`, but says nothing
about `upstream`. This spec adds the fork–upstream layer.

The desired steady-state flow is:

1. All local work is pushed first to `origin`.
2. Periodic fetches from `upstream` surface any independent
   changes that may have landed there.
3. Cross-repository pull requests carry stabilised material
   from `origin` to `upstream`.
4. After an upstream merge, `origin/main` is synchronised back
   to `upstream/main` so the two heads stay in lockstep.

The spec covers documentation, mechanical hook and configuration
changes, and a verification surface. Every command described
below is testable from the command line in the geb-lean working
copy.

## State at spec time

The following invariants and configuration items are already in
place at session start and are inputs to this spec rather than
deliverables of it. Items prefixed "Pre-spec" describe behaviour
that the spec's Hook and configuration changes section narrows.

- `jj` runs in colocated mode at the parent `geb/` root; the
  geb-lean subdirectory is one level below the jj root.
- `origin` is registered both as a git remote (visible in
  `git remote -v`) and as a jj remote (visible in `jj git
  remote list`).
- `upstream` is registered both as a git remote and as a jj
  remote.
- `git fetch upstream` has not yet been performed in this
  working copy: no `upstream/*` refs exist in `git branch -r`.
- The per-repo jj config `remotes.origin.fetch-tags =
  "glob:cutover-*"` is set; no analogous setting exists for
  `upstream`.
- `git.private-commits = "conflicts()"` is set per-repo.
- Pre-spec: the pre-tool-use hook
  `scripts/hooks/block-mutating-git.sh` closes the bare-`git`
  allowlist on `origin` only: `git fetch origin` and
  `git fetch origin refs/pull/*/head:*` are permitted; any
  other remote name is denied. The hook lets every
  `jj git …` invocation through unconditionally; the deny
  clause added by § Hook and configuration changes narrows
  this for `jj git push` to upstream.
- The pre-push checklist `scripts/pre-push.sh` runs build,
  test, lint, axiom-check, and markdown-lint, then prints
  user-driven gate reminders. It does not currently inspect the
  push target.
- Fork–upstream alignment at spec time: `origin/main` and
  `upstream/main` are at identical SHA `ba7309becb8e`, the
  merge commit of upstream PR #191
  (`rokopt:main → anoma:main`, merged 2026-05-12).
  `gh api repos/anoma/geb/compare/main...rokopt:geb:main`
  reports `status=identical`, `ahead_by=0`, `behind_by=0`.
  PR #191 used the merge-commit strategy, matching this
  spec's synchronising-PRs invariant.
- The local jj `main` bookmark is at `dc02dea6` (the merge
  of PR #11), two commits behind both `origin/main` and
  `upstream/main`. The catch-up is a routine
  `jj git fetch --remote origin` followed by
  `jj bookmark set main -r main@origin`; it is not a
  deliverable of this spec.
- The upstream default branch is `main`, protected.
- The cutover tag `cutover-2026-05-10` exists on the fork
  but not upstream.
- External fact (not narrowed by the spec): GitHub's push
  response to a push against the fork includes a "Create a
  pull request" URL whose base defaults to `anoma/geb:main`
  (the fork's parent repository). The URL is generated
  server-side from the fork relationship and is not
  affected by jj or git client configuration. § Per-clone
  `gh` configuration introduces an alternative
  PR-creation path (`gh pr create`) that the operator uses
  in place of the printed URL when the PR's intended base
  is the fork.

## Invariants

The spec adds the following invariants to the project's
existing rule set.

- **Fork-first.** Every commit produced locally is pushed to
  `origin` before any further interaction with `upstream` is
  considered.
- **No direct push to upstream.** `upstream` receives commits
  only through merged pull requests opened from `origin`.
  Direct pushes — whether via `git push upstream`, `jj git push
  --remote upstream`, or any other route — are forbidden.
- **Merge-commit strategy on synchronising PRs.** Every pull
  request whose merge updates `origin/main` or
  `upstream/main` uses the merge-commit strategy. This covers
  cross-repository PRs against upstream (Op 4) and the
  in-fork `chore/upstream-sync-<date>` PRs of Op 3. Squash
  and rebase are excluded because they rewrite history and
  would break the append-only contract on both default
  branches and the fast-forward synchronisation contract on
  `upstream/main` → `origin/main`. Topic-branch PRs that do
  not synchronise with upstream are unconstrained by this
  invariant.
- **No `origin/main` movement while an upstream PR is open.**
  Between opening an upstream PR (Op 4) and synchronising
  `origin/main` to the merge result (Op 6), no other PR is
  merged into `origin/main`. The invariant exists so Op 6's
  fast-forward precondition is preserved; the corrective if
  the invariant is violated is in Op 6's prose.
- **Append-only on both default branches.** Both
  `origin/main` and `upstream/main` are append-only. Their
  histories are never rewritten. GitHub Rulesets enforce this
  on `origin/main` already; mirroring the configuration on
  `upstream/main` is out of scope here and recorded in § Out
  of scope.
- **Lockstep after merge.** After an upstream PR merges,
  `origin/main` is synchronised to `upstream/main` before any
  further upstream PRs are opened. The merge-commit strategy
  ensures this is a fast-forward operation.

## Remote roles

| Remote | URL | Role | Mutating ops permitted from here? |
| --- | --- | --- | --- |
| origin | `ssh://git@github.com/rokopt/geb` | Daily fork; push target for topic branches | Yes (gated by user line-by-line review) |
| upstream | `git@github.com:anoma/geb.git` | Canonical repository; PR target only | No (fetch only; PRs via `gh`) |

The fork's `main` and the upstream's `main` are kept in
lockstep by construction: every upstream PR uses the
merge-commit strategy, so after upstream merge,
`upstream/main` reaches a SHA whose history contains the fork
branch's tip, and `origin/main` can fast-forward to that SHA.

## Operations

Each operation below is a self-contained command sequence. The
command sequences are the testing surface defined in § Testing
and verification.

### Op 1 — Push a topic branch to the fork

Existing flow, unchanged. The pre-push checklist
(`scripts/pre-push.sh`) runs to completion, the user reviews
the diff line by line, then:

```sh
bash scripts/pre-push.sh
jj git push --remote origin -b <bookmark>
```

The push goes to `origin` only. No further action is required
for changes that are not yet ready to upstream.

The push response includes a "Create a pull request" URL
whose base defaults to `anoma/geb:main` (see § State at spec
time). When the next step is a PR into `origin/main` rather
than upstream, ignore that URL and create the PR with:

```sh
gh pr create --base main --head <branch>
```

With `gh repo set-default rokopt/geb` configured (see
§ Per-clone `gh` configuration), this defaults to a
fork-internal PR against `origin/main`. The alternative is
to navigate to
`https://github.com/rokopt/geb/compare/main...<branch>?expand=1`
directly. For an Op 4 PR against upstream, pass
`--repo anoma/geb` explicitly.

### Op 2 — Fetch from upstream

Run from any directory inside the geb working copy:

```sh
jj git fetch --remote upstream
```

This creates or updates the jj-side `<bookmark>@upstream`
refs and the git-side `upstream/<bookmark>` refs. The
operation is read-only and does not modify the working copy
or any local bookmark. It is safe to run at any time.

### Op 3 — Synchronise fork main from upstream

Used when upstream has moved independently of the fork. The
operation depends on whether the fork has diverged.

If the fork's `main` is purely behind `upstream/main` (i.e.
`git log origin/main..upstream/main` is non-empty and
`git log upstream/main..origin/main` is empty), the
synchronisation is a fast-forward. Run, with user line-by-line
review of the resulting push:

```sh
jj git fetch --remote upstream
jj bookmark set main -r main@upstream
bash scripts/pre-push.sh
jj git push --remote origin -b main
```

If the fork's `main` has diverged from `upstream/main` (both
have commits the other lacks), the synchronisation requires a
topic branch carrying a true merge commit whose parents are
`main@origin` and `main@upstream`. The append-only invariant
on `origin/main` excludes rebase: the operation is a merge,
not a replay.

Preconditions:

- The local `main` bookmark equals `main@origin` (verify
  with `jj bookmark list main | head -2`). If they differ,
  reconcile first via `jj bookmark set main -r main@origin`
  or by resolving the divergence on a separate change.
- The remote-tracking bookmark `main@upstream` is current
  (run `jj git fetch --remote upstream` immediately before).

The merge happens on a topic branch named
`chore/upstream-sync-YYYY-MM-DD`:

```sh
jj git fetch --remote upstream
jj new main@origin main@upstream \
  -m "chore(sync): merge upstream/main into origin/main"
jj bookmark create chore/upstream-sync-<date> -r @
# resolve conflicts via editing or `jj resolve`; verify with
# `jj status` that no conflict markers remain
bash scripts/pre-push.sh
jj git push --remote origin -b chore/upstream-sync-<date>
```

The topic branch is then opened as a pull request against
`origin/main` via `gh pr create --base main --head
chore/upstream-sync-<date>` (user-gated), reviewed, and merged
with the merge-commit strategy (`gh pr merge <n> --merge`)
per the synchronising-PRs invariant.

### Op 4 — Open a cross-repository PR to upstream

The PR draft (title and body) is authored by the user, not by
Claude (see `CLAUDE.md` § Hard rules: "No LLM-drafted text in
user-facing channels"). The command below shows the structural
form; the actual `--title` and `--body` content is the user's:

```sh
gh pr create \
  --repo anoma/geb \
  --base main \
  --head rokopt:<branch-name> \
  --title '<user-authored title>' \
  --body  '<user-authored body>'
```

The invocation is a `gh` write operation and is gated by the
existing rule (`CLAUDE.md` § Hard rules) requiring user
line-by-line review before any `gh` write call.

### Op 5 — Merge the upstream PR

Performed by the user (or by Claude only with explicit user
authorisation) using the merge-commit strategy:

```sh
gh pr merge <pr-number> --repo anoma/geb --merge
```

The `--merge` flag selects the merge-commit strategy; `--squash`
and `--rebase` are excluded by invariant. The merge requires
that the authenticated `gh` context satisfies the
branch-protection ruleset on `upstream/main`; the actual
capability is established conclusively by the first real
merge (see T8 for the non-destructive permission probe).

### Op 6 — Synchronise fork main back to upstream main

After the upstream PR merges, `upstream/main` has moved
forward. Under the "no `origin/main` movement while an
upstream PR is open" invariant, the fork branch tip is the
sole non-trivial commit on the fork side, so the fork's
`main` can fast-forward to `upstream/main` without
divergence:

```sh
jj git fetch --remote upstream
jj bookmark set main -r main@upstream
bash scripts/pre-push.sh
jj git push --remote origin -b main
```

If the invariant was violated (a topic branch landed on
`origin/main` between Op 4 and the merge of the upstream PR),
the fast-forward refuses because `main@upstream` is no longer
a descendant of `main@origin`. The corrective is the
divergence branch of Op 3: merge `main@upstream` into
`main@origin` on a `chore/upstream-sync-<date>` topic branch
and proceed through that flow.

The fast-forward path is structurally the same as the
fast-forward branch of Op 3 and shares the same testing
surface.

### Op 7 — Propagate upstream movement to open topic branches

When `origin/main` has moved forward (via either branch of
Op 3 or via Op 6) and topic branches are open against the
earlier `origin/main`, each topic branch is updated to be
based on the new `origin/main`. The corrective is per-branch
and runs from the topic branch's working copy:

```sh
jj git fetch --remote origin
jj rebase -s <topic-branch-base> -d main@origin
```

`jj rebase` rewrites the topic branch's commits onto the new
base. Topic branches not yet pushed may be rebased freely;
topic branches that have been pushed to `origin` undergo the
same line-by-line review for the force-push that follows. If
a topic branch's PR is already open against `origin/main`,
the rebase produces a force-update on the PR head; the
reviewer accounts for this in the next review pass.

This Op is not required when `origin/main` is unchanged
relative to the topic branch's base.

## Hook and configuration changes

### `.claude/rules/` additions

A new path-scoped file
`.claude/rules/fork-upstream-flow.md` records the invariants
above and the command sequences from § Operations. It loads
unconditionally (no `paths:` frontmatter), so its presence is
visible from session start.

### `scripts/hooks/block-mutating-git.sh`

Two changes:

1. **Allow `git fetch upstream`.** Extend the `fetch`
   subcommand's positional-argument allowlist to permit the
   remote name `upstream` in addition to `origin`. The
   `refs/pull/*/head:*` two-positional form remains restricted
   to `origin` (no analogous use case for fetching upstream
   PRs). The change is approximately five lines.

2. **Deny `jj git push --remote upstream`.** Add a clause at
   the top of the hook (before the unconditional `jj git`
   pass-through) that matches the prefix `jj git push` and
   inspects the remainder of the argument vector for any of
   the following forms: `--remote upstream` (space-separated)
   or `--remote=upstream` (equals-form). The short flag `-r`
   in `jj git push` resolves to `--revisions`, not
   `--remote`, so it is deliberately excluded from the match
   (matching `-r upstream` would be a false positive on a
   revset or bookmark literally named `upstream`). On match,
   exit 2 with a diagnostic that names this spec by path.
   The clause is approximately twenty lines.

The hook's existing test conventions (one positional payload,
no flags) are preserved: the new clauses match exact forms
rather than open-ended option parsing.

### `scripts/check-jj-setup.sh`

No new mandatory assertion. `remotes.upstream.fetch-tags` is
a recommended setting (see § Per-repo `jj` configuration) but
not enforced: the cutover tag `cutover-2026-05-10` exists on
the fork only, so the parallel setting on `upstream` is
operationally inert today. A later cutover tag that
propagates to upstream would make the assertion load-bearing,
at which point this section is revisited. Adding an inert
assertion now would be maintenance overhead without behaviour.

### `scripts/pre-push.sh`

No mechanical change. The user-driven gate reminders printed
in step 6 gain one additional line: "the push target is
`origin`, not `upstream`". The reminder is informational; the
mechanical denial lives in `block-mutating-git.sh`.

### Per-repo `jj` configuration

The onboarding sequence in `docs/process.md` § jj colocated
mode adds one recommended (not enforced) step:

```sh
jj config set --repo remotes.upstream.fetch-tags 'glob:cutover-*'
```

The setting is parallel to the existing
`remotes.origin.fetch-tags`. It is recommended for the case
that a later cutover tag propagates to upstream; absent that,
it is inert. `check-jj-setup.sh` does not assert it.

### Per-clone `gh` configuration

The onboarding sequence adds one step, run after the
`origin` git remote is in place and after the first
`jj git fetch --remote origin`:

```sh
gh repo set-default rokopt/geb
```

This writes the git config entry `remote.origin.gh-resolved`
with literal value `base` into `.git/config` at the
colocated parent `geb/` root. The `base` value is a
`gh`-CLI sentinel that directs `gh` to resolve the default
target through the `origin` remote URL at command time.

After it is set, `gh pr create`, `gh issue ...`,
`gh release ...`, and other `gh` subcommands that resolve
a default base repository (`pr`, `issue`, `release`,
`workflow`, `secret`) target `rokopt/geb` rather than the
fork's parent. Subcommands that take an explicit repository
argument (`gh repo view <owner>/<repo>`, `gh api <path>`,
`gh auth status`, `gh config`) are unaffected. The
most-used effect is that Op 1's PR-into-`origin/main`
becomes `gh pr create --base main --head <branch>` without
a `--repo` flag.

Properties to note:

- The setting is per-clone (stored in `.git/config` for
  the `origin` remote); each fresh clone re-runs the
  command. Prerequisite: the `origin` git remote exists
  and its URL points at `rokopt/geb`.
- `gh-resolved = base` follows the live `origin` URL.
  Rewriting `origin`'s URL via `git remote set-url origin
  <other>` silently retargets every default-base `gh`
  command to the new URL without touching `gh-resolved`.
  The operator-level gate is to re-run T10 and to confirm
  `git remote -v` after any `origin` URL change.
- The active `gh auth` account must have write access to
  `rokopt/geb` for Op 1's PR-creation command to succeed;
  `gh auth switch` to an account without that access
  silently shifts Op 1's failure mode from "wrong target"
  to "permission denied at PR creation".
- Op 4 (cross-repository PR to upstream) still requires
  `--repo anoma/geb` on `gh pr create` to override the
  fork-default.
- The setting is reversed by `gh repo set-default --unset`.

The setting does not affect the "Create a pull request"
URL that GitHub prints in its push response (§ State at
spec time); that link continues to default to upstream.
Op 1's documentation directs the operator to `gh pr
create` rather than the printed link.

## Documentation changes

The following files are updated. The phrasing is the user's
domain; the spec records only the locations and the topics
covered.

- **`CLAUDE.md`** — § Hard rules: extend "No `git push`
  without user line-by-line review" to name both `origin` and
  `upstream` explicitly, and add a sentence stating that
  `upstream` receives commits only through PRs. § Pointers
  table: add a row for the new
  `.claude/rules/fork-upstream-flow.md` and for
  `docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`.

- **`docs/process.md`** — new § Fork–upstream relationship
  immediately after § Repository structure. It records the
  invariants, the remote roles table, and a pointer to this
  spec. § jj colocated mode gains a precondition note at
  the top of the onboarding sequence ("the sequence below
  assumes the working copy was created by `git clone
  ssh://git@github.com/rokopt/geb.git geb`, which
  registers `origin` as a git remote pointing at
  `rokopt/geb` and places `geb/` as the parent of
  `geb-lean/`. If `origin` is absent, register it with
  `git remote add origin
  ssh://git@github.com/rokopt/geb` before continuing.
  Users who prefer `jj git clone --colocate` arrive at an
  equivalent state but skip step 1
  (`jj git init --colocate`) and continue from step 2.").
  The same section gains two new onboarding steps, in
  this order: (a) `jj config set --repo
  remotes.upstream.fetch-tags 'glob:cutover-*'`, immediately
  after the existing per-repo jj config items and before
  the first `jj git fetch --remote origin`; (b)
  `gh repo set-default rokopt/geb`, immediately after the
  first `jj git fetch --remote origin` (so that the
  `origin` remote URL is in place when `gh` resolves it).

- **`.claude/rules/fork-upstream-flow.md`** — new file. It
  restates the invariants in directive form ("Do X." rather
  than "X holds.") and lists the seven operations with their
  command sequences. It is the working-time reference; the
  rationale layer lives in `docs/process.md`.

- **`.claude/rules/ci-and-workflow.md`** — § Pre-push
  checklist gains a line noting that step 6 includes the
  push-target reminder.

- **`README.md`** — § Pointers to upstream and sibling
  projects: a short paragraph stating that `anoma/geb` is the
  canonical repository and that the local working copy is a
  fork at `rokopt/geb`. Cross-references this spec.

## Testing and verification

The following commands constitute the spec's acceptance test.
Each one is non-destructive and is runnable from the geb-lean
working copy.

### T1 — Both remotes are registered

```sh
jj git remote list
```

Expected: the output contains exactly two lines, one whose
first token is `origin` and one whose first token is
`upstream`.

### T2 — `check-jj-setup.sh` passes after the configuration change

```sh
jj config set --repo remotes.upstream.fetch-tags 'glob:cutover-*'
bash scripts/check-jj-setup.sh
```

Expected: exit 0 and the line `check-jj-setup: OK`.

### T3 — `block-mutating-git.sh` permits `git fetch upstream`

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"git fetch upstream"}}' \
  | bash scripts/hooks/block-mutating-git.sh
```

Expected: exit 0 and no stderr output.

### T4 — Regression: `block-mutating-git.sh` denies `git push upstream`

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"git push upstream main"}}' \
  | bash scripts/hooks/block-mutating-git.sh
```

Expected: exit 2; stderr contains `block-mutating-git: blocked`
and a `jj equivalent:` line. This case is denied by the
existing catch-all on non-allowlisted subcommands and is not
modified by this spec; T4 is a regression test that the
catch-all behaviour survives the spec's other hook edits.

### T5 — `block-mutating-git.sh` denies `jj git push --remote upstream`

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"jj git push --remote upstream -b main"}}' \
  | bash scripts/hooks/block-mutating-git.sh
```

Expected: exit 2; stderr names this spec by path.

### T6 — `block-mutating-git.sh` permits `jj git fetch --remote upstream`

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"jj git fetch --remote upstream"}}' \
  | bash scripts/hooks/block-mutating-git.sh
```

Expected: exit 0 and no stderr output.

### T7 — `jj git fetch --remote upstream` succeeds

```sh
jj git fetch --remote upstream
git branch -r | grep '^  upstream/main$'
```

Expected: the first command exits 0; the second command prints
exactly one line.

### T8 — `gh` authentication can interact with upstream

```sh
gh api repos/anoma/geb --jq '.permissions'
gh api repos/anoma/geb/branches/main \
  --jq '.protected'
```

Expected: a JSON permissions object on stdout from the first
call, with at minimum `pull=true` (sufficient for Op 4 PR
creation). `push=true` and `admin=true` are progressively
stronger and bear on Op 5 merge capability. The second call
prints `true`, confirming that `upstream/main` is protected;
under the protection rules, Op 5 merge requires either
`admin=true` or an explicit bypass allowance configured on
the protected branch. Because the actual merge capability is
governed by GitHub's branch-protection ruleset rather than a
single permission bit, T8 is a partial probe: it confirms
the PR-creation prerequisite mechanically and surfaces the
permissions context for Op 5 review, but does not
conclusively predict whether `gh pr merge` will succeed.

### T9 — `block-mutating-git.sh` denies `--remote=upstream` equals-form

```sh
printf '{"tool_name":"Bash","tool_input":{"command":"jj git push --remote=upstream -b main"}}' \
  | bash scripts/hooks/block-mutating-git.sh
```

Expected: exit 2; stderr names this spec by path. The test
exists to confirm that the deny clause covers both
space-separated `--remote upstream` and equals-form
`--remote=upstream` syntaxes.

### T10 — `gh` default base repository is set to the fork

```sh
gh repo set-default --view
```

Expected: exit 0 with stdout exactly `rokopt/geb\n` (one
line, no leading or trailing whitespace beyond the
newline). When the default is unset, the command also
exits 0 but emits empty stdout; that is the corrective
trigger to run `gh repo set-default rokopt/geb`.

T10 verifies the configuration directly. It does not
exercise Op 1's downstream claim that `gh pr create
--base main --head <branch>` targets `rokopt/geb`;
`gh pr create` has no non-mutating dry-run
mode in the current `gh` CLI, so that claim is left
unverified by the acceptance suite and is exercised on
the first real Op 1 PR.

The destructive subset of the flow — Op 4 (`gh pr create`
against upstream), Op 5 (`gh pr merge`), the resulting sync
(Op 6), and any propagation under Op 7 — is not part of the
spec's acceptance test.

Ops 4, 5, and 6 were exercised in practice on 2026-05-12
via upstream PR #191 (`rokopt:main → anoma:main`), merged
with the merge-commit strategy. The post-merge state
(`origin/main == upstream/main == ba7309becb8e`) confirms
that the synchronising-PRs invariant and the lockstep
property hold in practice. The exercise predates the spec
text and was not performed by following the operations
verbatim, but the GitHub mechanics it validates are the
same. Op 7 (topic-branch propagation) was not exercised,
since no topic branches were open against an earlier
`origin/main` at the time; the first qualifying topic
branch serves as Op 7's acceptance test.

## Out of scope

The following are deliberately deferred to separate workstreams.

- **GitHub Rulesets on `upstream/main` parity.** The fork has
  rulesets enforcing append-only and protecting the cutover
  tag. Whether upstream has the same rulesets is the user's
  decision and outside this spec's surface.
- **Automated drift detection.** A CI job that compares
  `origin/main` to `upstream/main` after each push and warns
  on unexpected divergence is plausible but not part of this
  spec.
- **Multi-developer onboarding.** The spec assumes a single
  developer (the user) with admin or write access to both
  repositories. Multi-developer flows (PR review on the fork,
  reviewer assignment, etc.) are out of scope.
- **Tag synchronisation.** Whether and how tags propagate
  between fork and upstream is governed by the
  `fetch-tags = "glob:cutover-*"` settings on both remotes;
  no further automation is proposed.
- **CSLib and mathlib pin synchronisation.** Library pins
  (`lake-manifest.json`, `lean-toolchain`) are project-local;
  fork and upstream may legitimately hold different pins
  during an upstream PR's review window. Reconciliation is
  the PR review's responsibility, not the flow's.

## References

- `CLAUDE.md` — repository-wide instructions; § Hard rules,
  § Tooling, § Repo structure.
- `docs/process.md` — § Repository structure, § jj colocated
  mode, § Main / integration / topic-branch model.
- `.claude/rules/ci-and-workflow.md` — pre-push checklist,
  hook conventions, commit-message convention.
- `scripts/hooks/block-mutating-git.sh` — closed-allowlist
  bare-`git` gate.
- `scripts/check-jj-setup.sh` — per-repo configuration
  asserter.
- `scripts/pre-push.sh` — manual pre-push checklist runner.
- GitHub fork relationship between `rokopt/geb` and
  `anoma/geb`: `gh api repos/rokopt/geb` records
  `parent.full_name = "anoma/geb"`.
