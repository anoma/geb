# Adversarial review — cycle 5

**Spec**: `2026-05-09-process-bootstrap-monorepo-design.md`\
**Date**: 2026-05-09\
**Reviewer**: fresh-context agent (no access to prior review logs)

---

## Finding counts

- **Blockers**: 0
- **Serious**: 1
- **Minor**: 6
- **Cosmetic-taste**: 0

---

## Serious findings

### S1 — A10 cross-reference collision in cleanup table

Location: § Cleanup tasks, `C-hook-amend` row and
`C-gitignore-revert` row.

`C-gitignore-revert`'s ordering constraint states
"Before A10 (parent `.gitignore` fix)", assigning A10 to the
parent `.gitignore` fix plan task. `C-hook-amend`'s body then
states "re-run A10's smoke-test cases (all five must produce
expected exits)". A10 cannot simultaneously be the parent
`.gitignore` fix and the hook smoke-test: the two plan tasks are
distinct operations with distinct artefacts. The plan author
inherits an ambiguous ordering constraint that cannot be satisfied
as written. Either the hook smoke-test lives in a different task
(whose ID is given here incorrectly as A10), or A10's scope
is dual-use (which the "atomic and self-contained" preamble
prohibits). This makes the `C-hook-amend` ordering constraint
incoherent.

**Fix**: assign a distinct task ID (e.g. A10 stays as the
`.gitignore` fix; label the hook smoke-test task and reference it
by that label in `C-hook-amend`'s ordering constraint), or
explicitly state that the hook smoke-test is verification
checklist item 12 (not A10).

---

## Minor findings

### M1 — Stale cross-reference label "V11"

Location: § `.gitignore` change at the parent, line ending "These
two outcomes are confirmed by verification checklist item V11."

The verification checklist uses plain integer labels (1, 2, …,
17a). No item is labelled "V11". The `.gitignore` checks — with
three sub-cases (a), (b), (c) — appear in item **10**, not V11.
The prose also describes only "two outcomes" whereas item 10 has
three sub-cases, so the description does not fully enumerate what
the checklist tests. Change "verification checklist item V11" to
"verification checklist item 10" and note all three sub-cases.

---

### M2 — `jj config list` output format inconsistent with bare-value assertion

Location: § `scripts/check-jj-setup.sh`, items (a) and (b);
verification checklist item 11.

The spec asserts that
`jj config list --repo git.private-commits` produces output that
"equals `conflicts()` exactly". `jj config list` outputs TOML
format: `git.private-commits = "conflicts()"` — not the bare
string `conflicts()`. The anchored string match as specified
would therefore always fail. The correct command for a bare value
is `jj config get git.private-commits`, whose output in jj 0.41
is the raw string value (without the key name or TOML quotes for
simple strings; verify empirically). The spec should either
change `list` to `get` and confirm the exact output format, or
document the parsing step that extracts the value from `list`'s
TOML output.

The same applies to `remotes.origin.fetch-tags`.

---

### M3 — `lean_action_ci.yml` removal from `geb-lean/` not in any cleanup task

Location: § New file and directory layout (layout shows
`geb-lean/.github/workflows/lean_action_ci.yml` as
`- moved to parent`); § Cleanup tasks table.

The layout marks the file for removal from `geb-lean/`, but no
cleanup task performs this removal. `C-workflow-rm` removes only
`markdown-lint.yml`. Since GitHub Actions only reads workflow
files from the repository root's `.github/workflows/`, the
`geb-lean/.github/workflows/lean_action_ci.yml` file has always
been inert to GitHub (it never triggered CI); leaving it in place
after promotion creates dead code. Add a cleanup task
(e.g. `C-lean-action-rm`) for removing the `geb-lean/` copy, or
explicitly state in the layout that the geb-lean/ copy is left
inert on purpose (with rationale). Verification checklist item 13
should then also assert the geb-lean/ copy is absent.

---

### M4 — `.claude/memory/` markdown files not in `ignores`; pre-push gap

Location: § `.markdownlint-cli2.jsonc`, `ignores` array.

The `pre-push.sh` runs
`markdownlint-cli2 --no-globs '**/*.md'` from `geb-lean/` CWD.
The `ignores` array covers `.lake/**`, `.jj/**`, `node_modules/**`,
and `.session/**`, but not `.claude/memory/**` or `.claude/docs/**`.
Those directories contain markdown files locally
(`.claude/memory/MEMORY.md`, `.claude/memory/lean-patterns.md`)
that are git-ignored and therefore absent from CI checkouts, but
present in a developer's working tree. The pre-push run would
attempt to lint them. If either file has markdownlint findings,
`pre-push.sh` fails on every push despite the content being
untracked. Add `.claude/memory/**` and `.claude/docs/**`
(and their `geb-lean/`-prefixed forms) to the `ignores` array.

---

### M5 — Line-87 reference in a script not yet written

Location: § CI changes, axiom\_check job description, line
"aliases implemented in the vendored script at line 87 of
`scripts/check-axioms.sh`".

The script does not yet exist. Specifying a precise line number
in a to-be-authored script is speculative and will almost
certainly be wrong. The spec should reference the interface
(`--exit-zero-on-findings` / `--report-only` are aliases
for the report-only mode flag) without pinning a line number,
or mark the line number as "approximately".

---

### M6 — CI `markdown-lint.yml` snippet omits the `markdownlint-cli2` install step

Location: § CI changes, `markdown-lint.yml` YAML snippet.

The spec states that `markdownlint-cli2` must be installed in
the CI environment ("e.g. via `npm install -g markdownlint-cli2`
in a preceding step or pre-installed in the runner image").
`markdownlint-cli2` is not pre-installed on `ubuntu-latest`
GitHub Actions runners. The YAML snippet shows only the `run:`
invocation step; no install step is shown or deferred to the
plan with explicit language. The snippet as shown would produce
a `command not found` error in CI. Either include the install
step in the snippet, or add explicit "plan resolves the install
step" language to the deferred-decisions section.

---

## Items verified clean

- Gitignore pattern chain (`/geb-lean/.claude/*` with negations
  `!/geb-lean/.claude/rules/` and `!/geb-lean/.claude/settings.json`):
  the negations operate on direct children of `.claude/` (not on
  a parent-directory exclusion), so git descends into `rules/`
  after negation. Correct.
- `geb-lean/.claude/memory/` is git-ignored by
  `/geb-lean/.claude/*` and absent from CI checkouts; the CI
  markdownlint invocation is clean (M4 applies to pre-push only).
- Licence coherence: Apache 2.0 (mathlib dependency) is
  compatible with a GPLv3 project. The in-flight A5
  `geb-lean/LICENSE` (Apache 2.0) is in-flight only (not yet
  on `main`), so `C-license-rm` does not retroactively alter
  any landed commit.
- `jj root` discovery in `block-mutating-git.sh` and
  `check-jj-setup.sh`: correct portable mechanism — walks up
  from CWD, exits 0 when `.jj/` is found anywhere in the
  ancestor chain.
- GitHub Actions workflow scope: `.github/workflows/` at the
  repo root is the only location GitHub reads; the
  `geb-lean/.github/workflows/` files have always been inert
  to GitHub, making the "promotion" a corrective move.
- `defaults.run.working-directory: geb-lean` at workflow level
  applies to all `run:` steps and does not affect `uses:` steps
  (`actions/checkout`, `leanprover/lean-action`); the
  `lake-package-directory: geb-lean` input is the correct
  mechanism for the lean-action step.
- `jj git push` is lease-protected by default in jj 0.41;
  no explicit flag is required for `integration` force-push.
- `remotes.origin.fetch-tags` marked experimental in jj 0.41
  docs; the spec acknowledges this and documents the fallback.
- `--no-globs` in markdownlint-cli2 invocations suppresses
  config-file `globs` expansion; dual-form `ignores` (unprefixed
  and `geb-lean/`-prefixed) correctly handles both CWD modes.
- Banned words: no disallowed value-laden adjectives found in
  spec prose (technical uses of "key", "important" appear only
  in enumeration contexts).
