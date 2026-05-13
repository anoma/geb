---
paths:
  - ".github/workflows/**"
  - "scripts/**"
---

# CI and workflow conventions

This rule applies to CI and workflow files inside the geb-lean
subdirectory. Parent-level workflow files at
`geb/.github/workflows/` are outside the geb-lean project's
`paths:` scope; when editing those files, load
`geb-lean/docs/process.md` § CI as the reference.

## Workflow conventions

The `lean_action_ci.yml` and `markdown-lint.yml` workflows live
at the parent `geb/.github/workflows/` level and are
path-filtered to `geb-lean/**`. The `update.yml` and
`create-release.yml` workflows remain inert at
`geb-lean/.github/workflows/` as forward prep.

Third-party action references are SHA-pinned where the security
gain warrants the maintenance cost; major-version pinning is
acceptable for actions whose maintainers have a
release-discipline track record.

## Pre-push checklist

`scripts/pre-push.sh` runs the following commands:

- `bash scripts/check-jj-setup.sh`
- `lake test` (builds `GebLean` and `GebLeanTests`; explicit
  `lake build` is omitted as redundant against current lakefile
  targets)
- `lake lint`
- `markdownlint-cli2 --config .markdownlint-cli2.jsonc
  --no-globs '**/*.md'`
- `bash scripts/check-axioms.sh GebLean/ GebLeanTests/ || true`
  (`|| true` is informational pre-Milestone-B; Milestone B item
  B5 removes the suffix to make the check a hard gate)

The single-quotes around `'**/*.md'` are load-bearing — without
them, the shell would expand the glob before
`markdownlint-cli2` sees it, defeating `--no-globs`. The same
applies wherever a glob is passed: always quote the glob
argument.

The script additionally surfaces user-driven gates as
reminders:

- `lean4:golf` and `lean4:review` ran on changed Lean code;
- line-by-line user diff review of every change about to be
  pushed;
- the push target is `origin`, not `upstream`. Upstream
  receives commits only via PRs opened from origin (see
  `.claude/rules/fork-upstream-flow.md` and
  `docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`).

## Hook-script conventions

Scripts under `scripts/hooks/*.sh` exit 0 by default; explicit
blocks exit 2 with a stderr message. `block-mutating-git.sh`
blocks raw mutating `git` and translates blocked commands to
their `jj` equivalents in stderr. `check-signing-key.sh` warms
the gpg-agent or ssh-agent at session start.

## Commit-message convention

Adopt mathlib's `<type>(<optional-scope>): <subject>` form
(`feat | fix | doc | style | refactor | test | chore | perf |
ci`), imperative present, no capital, no period.

The commit-message type is `doc:` (singular, mathlib-mandated)
while the topic-branch prefix for documentation work is
`docs/<topic>` (plural, project-local convention adopted from
`geb-mathlib`). The two forms are deliberately distinct and
used in distinct contexts (`git commit -m "doc: ..."` vs branch
name `docs/<topic>`). Consistency with `geb-mathlib` and
mathlib motivates the convention even though this repository
does not currently target mathlib upstream.

The convention applies forward from the cutover commit (see
`docs/process.md` § Branch model); pre-cutover commits remain
in their original forms (mixed style, per `git log`).
