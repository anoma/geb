# Adversarial review — cycle 10

**Spec**: `docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md`\
**Reviewer**: fresh-context agent\
**Date**: 2026-05-09

## Finding counts

Blockers: 1 | Serious: 0 | Minor: 1 | Cosmetic: 0

---

## Findings

### B-1 — `markdownlint-cli2` npm version pin is incompatible with `--no-globs`

**Location**: § CI changes, markdown-lint workflow snippet
(install step `npm install -g 'markdownlint-cli2@^0.18.0'`);
and the inline note "the `--no-globs` flag was introduced in
markdownlint-cli2 v3.0.0".

**Finding**: The pin `@^0.18.0` resolves, under npm semver rules for
a 0.x major, to `>=0.18.0 <0.19.0`. This range is entirely below
v3.0.0. The installed binary would therefore not recognise `--no-globs`,
causing the CI `markdownlint` step to fail with an unrecognised-flag
error on every run. The correct pin, consistent with the stated version
lower bound, is `'markdownlint-cli2@^3.0.0'` (or a tighter explicit
version such as `@3.4.0` if the exact minimum release is known).

**Effect on implementation**: CI is broken on day one. The markdown-lint
workflow cannot pass until the version pin is corrected.

---

### M-1 — `.gitignore` cleanup: prose and task table disagree on the fourth pattern

**Location**: § `.gitignore` change at the parent (prose, lines
describing `C-gitignore-revert`) and the Cleanup tasks table (row
`C-gitignore-revert`).

**Finding**: The prose in § `.gitignore` change at the parent states
that `geb-lean/.gitignore` carries "three patterns from commit
`69123dd0`" (`/.claude/*`, `!/.claude/rules/`, `!/.claude/settings.json`)
plus "the pre-A12 `/.claude` line" — implying a bare `/.claude` entry
is the fourth item. The cleanup task table states the current HEAD file
contains `/.claude/*`, `!/.claude/rules/`, `!/.claude/settings.json`,
and `/docs/.claude` — making `/docs/.claude` the fourth item. These two
descriptions name different strings for the fourth pattern. An
implementer relying on the table alone might leave `/.claude` (if it
exists); one relying on the prose alone might leave `/docs/.claude` (if
it exists). Either scenario leaves a stale `.claude`-related pattern in
`geb-lean/.gitignore`, undermining the cleanup task's goal.

**Recommended resolution**: inspect `geb-lean/.gitignore` at HEAD,
enumerate the exact set of `.claude`-related lines, and update both
the prose and the table to match the actual file contents.
