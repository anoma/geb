---
paths:
  - ".github/workflows/**"
  - "scripts/**"
---

# CI and workflow conventions

Applies to GitHub Actions workflow files and scripts.

The `lean_action_ci.yml` and `markdown-lint.yml` workflows live
at the parent `geb/.github/workflows/` level and are
path-filtered to `geb-lean/**`; the `update.yml` and
`create-release.yml` workflows remain inert at
`geb-lean/.github/workflows/`. The rules in this file apply to
both locations.

## Commit-message convention (mathlib-derived)

```text
<type>(<optional-scope>): <subject>

<body>

<footers>
```

Types: `feat | fix | doc | style | refactor | test | chore | perf | ci`.
Imperative present tense, no capital, no trailing period. Subject
under 72 characters when possible.

Documented footers: `Closes #123, #456`, `BREAKING CHANGE: ...`,
`- [ ] depends on: #XXXX`. Mathlib's published convention does not
include `Moves:` or `Deletions:`, so nor does ours.

The commit-message type is `doc:` (singular, mathlib-mandated)
while the topic-branch prefix for documentation work is
`docs/<topic>` (plural, project-local convention adopted from
`geb-mathlib`). The two forms are deliberately distinct and used
in distinct contexts (`git commit -m "doc: ..."` vs branch name
`docs/<topic>`).

## Pre-commit checklist

Run by `scripts/pre-commit.sh` before any commit that touches a
`.lean` file:

1. `lake test` succeeds (builds `GebLean` and `GebLeanTests` via
   the test driver's dependency graph; explicit `lake build` is
   redundant against current lakefile targets — see § Pre-push
   checklist below).
2. `lake lint` quiet.
3. `lake build GebLeanAxiomChecks` succeeds (runs the
   `GebLeanMeta.detectNonstandardAxiom` env_linter over `GebLean`,
   `GebLeanTests`, and the vendored `Geb` tree).

The script is scoped to `.lean`-touching commits: for commits
that touch only Markdown, scripts, or other non-Lean files it is
not required, since the Lean triad's outputs cannot change. The
full pre-push superset below remains mandatory before every push,
regardless of which file types changed.

`GebLeanDocs`, the Verso manual library, lies outside all three
steps: outside `testDriver`'s dependency graph, outside
`lake lint`'s default-target coverage, and outside the
`GebLeanAxiomChecks` gates (which name `GebLean`, `GebLeanTests`,
and the vendored `Geb`). It is built and linted only in CI
(`lake lint -- GebLeanDocs`, then `lake exe geblean-docs`, in
`geb/.github/workflows/lean_action_ci.yml`), a deliberate exception
to `scripts/pre-commit.sh`'s comment instructing that a target
outside the test driver's dependency graph be added there and to
`scripts/pre-push.sh` in lockstep, so that no contributor builds
Verso on every commit or push. The same exception applies to the
pre-push checklist below.

## Pre-push checklist

Run by `scripts/pre-push.sh`:

1. `bash scripts/check-jj-setup.sh` passes.
2. `lake test` succeeds locally (builds `GebLean` and
   `GebLeanTests` via the test driver's dependency graph;
   explicit `lake build` is redundant against current lakefile
   targets).
3. `lake lint` quiet.
4. `doctoc --check '**/*.md'` quiet (skipped if `doctoc` is not
   installed).
5. `markdownlint-cli2 '**/*.md'` quiet.
6. `lake build GebLeanAxiomChecks` succeeds, then
   `bash scripts/tests/test-axiom-linter.sh` passes. The
   `GebLeanAxiomChecks` library runs the
   `GebLeanMeta.detectNonstandardAxiom` env_linter over `GebLean`,
   `GebLeanTests`, and the vendored `Geb` tree via `#lint only`
   gates; a non-standard axiom dependency fails the build. CI
   repeats the build and smoke test in
   `geb/.github/workflows/lean_action_ci.yml`.
7. `bash scripts/tests/test-lint-driver.sh` passes. The guard
   covers every library that `lake lint` reaches only by its root
   module (`batteries/runLinter` loads one flat environment per
   invocation, so linting per module instead scales memory with
   module count): the vendored `Geb` tree, linted by
   `lake lint -- Geb` in
   `geb/.github/workflows/geb-mathlib-refresh.yml`, and
   `GebLeanDocs`, linted by `lake lint -- GebLeanDocs` in
   `geb/.github/workflows/lean_action_ci.yml`. For each, the guard
   checks that its workflow keeps the root-module invocation and
   that no module under its root is orphaned from the umbrella (an
   orphan would silently escape the linter).
8. User-driven gate reminders surfaced as prompts: `lean4:golf`
   and `lean4:review` ran on changed Lean code; line-by-line
   user diff review of every change about to be pushed; the
   push target is `origin`, not `upstream`. Upstream receives
   commits only via PRs opened from origin (see
   `.claude/rules/fork-upstream-flow.md`).

The single-quotes around `'**/*.md'` are load-bearing — without
them, the shell would expand the glob before
`markdownlint-cli2` (or `doctoc`) sees it. The same applies
wherever a glob is passed: always quote the glob argument.

## Hook-script conventions

Hook scripts in `scripts/hooks/` follow Claude Code's hook contract
(verified against
`https://code.claude.com/docs/en/hooks-overview` and
`https://code.claude.com/docs/en/hooks-reference`):

- Read JSON from stdin when invoked.
- Exit 0 to allow; exit 2 to hard-block (with stderr message). For
  PreToolUse hooks that prefer to surface the decision to the user,
  exit 0 with a `hookSpecificOutput.permissionDecision` JSON
  document on stdout (e.g., `permissionDecision: "ask"`); other
  non-zero exits are errors.
- Smoke-test in `scripts/hooks/tests/test-<hook>.sh`; CI runs the
  smoke tests.

`scripts/hooks/block-mutating-git.sh` blocks raw mutating `git`
and translates blocked commands to their `jj` equivalents in
stderr. `scripts/hooks/check-signing-key.sh` checks at session
start that the configured signing key is usable (gpg-agent
passphrase cache, or ssh-agent identities) and emits a hook-JSON
note on a miss.

## Action pinning policy

All third-party actions in `.github/workflows/*.yml` are pinned to
a specific commit SHA, with the SHA followed by a comment naming
the corresponding tag for human readers. Update via review of the
upstream action's release notes (Dependabot-style).
