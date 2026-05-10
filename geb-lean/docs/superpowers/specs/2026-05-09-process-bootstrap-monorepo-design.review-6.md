# Adversarial review — cycle 6

**Spec**: `2026-05-09-process-bootstrap-monorepo-design.md`\
**Date**: 2026-05-09\
**Reviewer**: fresh-context agent (no access to prior review logs)

---

## Finding counts

- **Blockers**: 0
- **Serious**: 0
- **Minor**: 3
- **Cosmetic-taste**: 0

---

## Minor findings

### M1 — `C-gitignore-revert` describes a pattern that no longer exists

**Location**: § Cleanup tasks, `C-gitignore-revert` row; §
`.gitignore` change at the parent, paragraph beginning "The
existing in-flight commit `69123dd0`…"; verification checklist
item 10.

The task body says to "remove the `/.claude` line present in the
pre-A12 state". Commit `69123dd0` did not preserve the bare
`/.claude` line alongside the new patterns; it replaced it with
`/.claude/*`. The current `geb-lean/.gitignore` therefore
contains three `.claude`-related patterns (`/.claude/*`,
`!/.claude/rules/`, `!/.claude/settings.json`), not four. The
description implies removing four things (the "pre-A12 line"
plus the three from `69123dd0`), which would confuse an
implementer.

Additionally, the `geb-lean/.gitignore` currently contains a
fourth `.claude`-related pattern (`/docs/.claude`) that is not
mentioned in `C-gitignore-revert` at all. The task's stated
goal is that the file contain "no `.claude`-related patterns",
yet `/docs/.claude` would remain after the task as described.

**Fix**: Change the task body to describe what is actually
in the current file: remove all four current `.claude`-related
lines (`/.claude/*`, `!/.claude/rules/`, `!/.claude/settings.json`,
`/docs/.claude`). Drop the historical reference to the "pre-A12
`/.claude` line" (it no longer exists in `HEAD`). Update
verification checklist item 10 accordingly if it references
the pre-A12 line.

---

### M2 — Stale cross-reference label "V10"

**Location**: § `.gitignore` change at the parent, last sentence:
"These two outcomes are confirmed by verification checklist item
V10."

The verification checklist uses plain integer labels (1, 2, …,
17a). No item is labelled "V10". The `.gitignore` verification
— with three sub-cases (a), (b), (c) — appears in checklist
item **10**. The prose also says "two outcomes" but item 10 has
three sub-cases.

**Fix**: Change "verification checklist item V10" to
"verification checklist item 10". Reconcile the "two outcomes"
count with the three sub-cases actually listed in item 10.

---

### M3 — Top-level `plans/` directory absent from the layout tree

**Location**: § New file and directory layout (the `geb-lean/`
tree diagram); § Repository structure (line listing
`geb-lean/plans/*`); CLAUDE.md content item 9 ("plan at
`plans/<date>-<topic>-plan.md`").

The tree diagram under § New file and directory layout does not
include a top-level `geb-lean/plans/` entry, though that
directory exists, is listed in § Repository structure as the
home of the implementation plan, and is referenced as the plan
target in CLAUDE.md item 9 and the adversarial review procedure.
The diagram shows `docs/superpowers/plans/` (for geb-mathlib
reference material) but omits `plans/` at the root of
`geb-lean/`.

**Fix**: Add `├── plans/  (existing; new entries)` to the
`geb-lean/` section of the layout tree.

---

## Items verified clean

The following claims were independently cross-checked and found
correct:

- **S1 from cycle 5 (A10 collision)**: fixed. `C-gitignore-revert`
  ordering constraint now says "Before the new plan's parent-`.gitignore`
  task" (no longer references A10). `C-hook-amend` references
  the hook smoke-test cases correctly as verification checklist
  item 12.
- **M2 from cycle 5 (`jj config list` TOML format)**:
  fixed. The script description now says it "strips the TOML
  wrapper via `sed`" before the anchored comparison.
- **M3 from cycle 5 (`lean_action_ci.yml` removal)**:
  `C-lean-action-ci-promote` uses `git mv`, which removes
  the `geb-lean/` copy as part of the move. Functionally
  correct; verification item 13 could additionally assert
  the `geb-lean/` copy is absent, but this is not a gap
  that prevents implementation.
- **M4 from cycle 5 (`.claude/memory/**` in ignores)**:
  fixed. Both `.claude/memory/**` and `.claude/docs/**` are
  now present in the `ignores` array in both unprefixed and
  `geb-lean/`-prefixed forms.
- **M5 from cycle 5 (line-87 pinning)**:
  fixed. "line 87" replaced with "near the argument-parsing
  section".
- **M6 from cycle 5 (CI snippet missing install step)**:
  fixed. The YAML snippet now includes the `npm install -g
  markdownlint-cli2` install step.
- **Gitignore pattern chain** (`/geb-lean/.claude/*` with
  negations `!/geb-lean/.claude/rules/` and
  `!/geb-lean/.claude/settings.json`): git resolves these
  correctly. The wildcard `*` does not cross directory
  boundaries, so `rules/` as a directory entry is negated
  and git traverses into it, tracking its contents.
- **`geb-lean/.claude/memory/**` and `.claude/docs/**`**:
  git-ignored by `/geb-lean/.claude/*` and absent from CI
  checkouts; the CI markdownlint invocation is clean; the
  pre-push case is covered by the `ignores` array.
- **Licence coherence**: Apache 2.0 (mathlib, CSLib) is
  compatible as a dependency of the GPLv3 project. The
  in-flight A5 `geb-lean/LICENSE` (Apache 2.0) is cleaned
  up by `C-license-rm`. The governing `geb/LICENSE` (GPLv3)
  is not modified.
- **`defaults.run.working-directory: geb-lean` scope**:
  correctly described as workflow-level (applies to all
  `run:` steps, not `uses:` steps). `actions/checkout` and
  `leanprover/lean-action` are `uses:` steps and unaffected.
  `lake-package-directory: geb-lean` is the correct mechanism
  for the lean-action step.
- **`jj root` portability**: correctly described as walking
  up from CWD to locate `.jj/`; portable whether `.jj/` is
  at the parent or at a subdirectory.
- **`fetch-tags` experimental status**: acknowledged in the
  spec with a documented fallback.
- **`git.private-commits = "conflicts()"` semantics**:
  spec correctly notes that resolved conflicts are no longer
  in `conflicts()` at push time and are therefore not blocked.
- **Banned words check**: no disallowed value-laden adjectives
  found in spec prose (uses of "key" and "important" are in
  enumeration or technical contexts).
- **`--no-globs` in markdownlint-cli2 invocations**: correctly
  suppresses config-file `globs` expansion. The dual-form
  `ignores` (unprefixed and `geb-lean/`-prefixed) correctly
  handles both CWD modes (pre-push at `geb-lean/`; CI at
  `geb/`).
- **`git mv` in `C-lean-action-ci-promote`**: the hook is
  not wired until A27, which is after all cleanup tasks;
  `git mv` is therefore not blocked when the cleanup runs.
