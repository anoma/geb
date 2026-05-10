# Adversarial Review — cycle 8

**Spec**: `2026-05-09-process-bootstrap-monorepo-design.md`\
**Reviewer**: fresh-context agent\
**Date**: 2026-05-09\
**Prior cycles read**: none (hard rule)

---

## Summary

| Severity | Count |
| --- | --- |
| Blocker | 0 |
| Serious | 2 |
| Minor | 2 |
| Cosmetic | 2 |

---

## Findings

### S1 — Orphaned SHA-pinning paragraph in `markdown-lint.yml` section (Serious)

**Location**: § CI changes, `markdown-lint.yml` sub-section, final
paragraph ("The action reference is SHA-pinned…").

The paragraph states: "The action reference is SHA-pinned (not
tag-pinned) per the project's general action-pinning policy; the SHA is
resolved at workflow-authoring time and committed verbatim."

The `markdown-lint.yml` workflow in the spec consists of exactly two
`run:` steps — `npm install -g markdownlint-cli2` and a
`markdownlint-cli2 ...` invocation. Neither is a `uses:` step. There is
no action reference in this workflow to SHA-pin.

The paragraph appears to be a survivor of an earlier design revision
that used `DavidAnson/markdownlint-cli2-action` (and the spec's own
rationale for switching to `run:` is given two paragraphs earlier). The
paragraph now refers to a non-existent artefact and misleads an
implementor into looking for an action reference that does not exist.
Either remove the paragraph or reframe it to note that no third-party
action reference is used in this workflow.

---

### S2 — Smoke-test case (b) contradicts "no real commands run" claim (Serious)

**Location**: § CI changes (verification matrix item 12), and §
Cleanup tasks (C-hook-amend), and § Hooks (`block-mutating-git.sh`
description).

Verification item 12 says: "No real `git` or `jj` commands run."
C-hook-amend says the amended hook "uses `jj root` (exit 0 = jj is
initialised somewhere up the tree)" to detect jj availability, which it
invokes directly from inside the script. Smoke-test case (b) —
`jj git push --remote origin -b feat/x` → exit 0 — depends on the
hook stripping `jj git X` forms, which only happens when `jj root`
exits 0.

So smoke-testing case (b) via JSON-stdin payloads does cause the hook
to run `jj root`. If jj is not installed in the test environment (or
the CWD at smoke-test time is not under a jj repo), `jj root` exits
non-zero, the strip does not happen, and `jj git push` is likely
blocked rather than allowed — producing exit 2 instead of the expected
exit 0, causing case (b) to fail.

The spec needs to either: (a) acknowledge that `jj root` runs during
smoke tests and require the test environment to have jj initialised; or
(b) make `jj root` a configurable or mockable dependency in the hook
for testing purposes; or (c) revise the "no real commands run" claim to
"no real `git` commands run; `jj root` runs as a presence check."

---

### M1 — `block-mutating-git.sh` else-branch unspecified (Minor)

**Location**: § Hooks, `block-mutating-git.sh` description, third
paragraph.

The spec says: "it checks whether `jj root` exits 0 — … and if so
strips `jj git X` forms … and applies the allowlists below."

The else branch (when `jj root` exits non-zero — jj not installed or
no `.jj/` ancestor) is not specified. Does the hook: (a) still apply
the read-only / fetch / config allowlists against raw `git` commands
(which would be the natural fallback); (b) pass all commands through
(exit 0, hook inactive); or (c) block everything (exit 2)? Given the
hook's default-deny policy, (c) seems implied, but the spec does not
state it. A developer who has not yet run `jj git init --colocate`
would find Claude completely unable to run even `git status`. That
consequence should be acknowledged and the else branch named.

---

### M2 — `upload-artifact` `path:` outside `GITHUB_WORKSPACE` (Minor)

**Location**: § CI changes, report-only mode YAML snippet and
surrounding text.

The `axiom_check` report-only step writes to `/tmp/axiom-check-report.txt`
and uploads it via `actions/upload-artifact@<SHA>` with
`path: /tmp/axiom-check-report.txt`. `actions/upload-artifact@v4`
requires paths to be within the GitHub Actions workspace
(`$GITHUB_WORKSPACE`). Paths in `/tmp` are outside the workspace, and
the action may reject them. The spec explicitly notes the path is
"absolute and does not depend on `defaults.run.working-directory`" but
does not address whether `upload-artifact` can read from `/tmp`.

A safe fix is to write the report to a workspace-relative path such as
`$GITHUB_WORKSPACE/axiom-check-report.txt` or use a
`working-directory`-relative path (e.g. `../axiom-check-report.txt`
from `geb-lean/`), then pass that path to `upload-artifact`.

---

### C1 — Orphaned pipe characters in ASCII tree (Cosmetic)

**Location**: § New file and directory layout, tree block, `plans/`
and `scripts/` entries.

Both entries have `│   │` on their continuation lines — the extra `│`
character is extraneous. The tree renders:

```text
├── plans/                       (existing; carries the 2026-05-07
│   │                               plan ...)
```

The correct continuation for a wrapped comment without children is
`│` followed by spaces, not `│   │`. The same bug appears for
`scripts/`.

---

### C2 — `AXIOM_ALLOW` example has open parenthesis on continuation line (Cosmetic)

**Location**: § Auxiliary scripts, `check-axioms.sh` sub-section,
`AXIOM_ALLOW` comment syntax.

The spec states "the `AXIOM_ALLOW` line itself must be a single line"
and immediately shows an example where the parenthetical rationale
string opens on the AXIOM_ALLOW line and closes on the next `--` line:

```lean
-- AXIOM_ALLOW: Classical.choice (transitive via
--   Mathlib.CategoryTheory.Equivalence; required by
--   mathlib's Equivalence.functor.PreservesLimits)
```

An open parenthesis `(transitive via` spans the first line and the
closing `)` is on the third. The spec's text and example are not
contradictory in meaning (the script presumably key-matches on the
axiom name, not on the parenthetical text), but the example looks like
the AXIOM_ALLOW declaration spans multiple lines. The example would
be clearer if the parenthetical text were complete on one line, or if
the spec explicitly notes that continuation `--` lines are for human
readability and are not parsed as part of the AXIOM_ALLOW directive.

---

## Verified as correct

- `.gitignore` replacement block: empirically verified. The negation
  pattern `!/geb-lean/.claude/settings.json` correctly un-ignores
  `settings.json`; `settings.local.json` remains ignored via
  `/geb-lean/.claude/*`; `rules/lean-coding.md` is untracked (not
  ignored).
- `--no-globs` suppresses the config `globs` key only, not `ignores`;
  `ignores` applies in both CWD modes. The doubled
  unprefixed/`geb-lean/`-prefixed pattern strategy is sound.
- `markdown-lint.yml` runs from the parent `geb/` root (no
  `defaults.run.working-directory` in that workflow), so
  `--config geb-lean/.markdownlint-cli2.jsonc` and
  `'geb-lean/**/*.md'` resolve correctly.
- `lean_action_ci.yml`'s `defaults.run.working-directory: geb-lean`
  applies to `run:` steps only; `uses:` steps (`actions/checkout`,
  `leanprover/lean-action`) are unaffected. `lake-package-directory:
  geb-lean` is the correct mechanism for the lean-action step.
- `axiom_check` job declares `needs: [build]`; the
  `--exit-zero-on-findings` / `--report-only` alias pair is internally
  consistent with the script's argument-parsing description.
- Allowlist: `propext`, `Quot.sound`, `quot.sound` matches the
  vendored `check-axioms.sh` on disk.
- Verification item 5 is correctly referenced as "item 5 of the
  checklist" in the CLAUDE.md section (it is the CLAUDE.md line-count
  item).
- jj `fetch-tags` experimental status is acknowledged with a concrete
  fallback documented.
- `check-signing-key.sh` ssh-signing path is deliberately deferred
  (non-portable key discovery) with informational-only exit 0.
- `docs/process.md` section 4 "Order of artefact production"
  references match the § Order of artefact production flow diagram.
