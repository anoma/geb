# Adversarial review cycle 4 — 2026-05-09 process-bootstrap monorepo spec

**Reviewer**: fresh-context Agent.
**Spec under review**:
`docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md`.
**Convergence threshold**: zero blocker / serious / minor findings
(cosmetic-taste excluded).

## Summary

One blocker and one serious finding remain. The blocker is in the
`C-gitignore-revert` cleanup task: it directs the implementer to restore
`/.claude` to `geb-lean/.gitignore`, but a sub-directory `.gitignore`
pattern takes precedence over a parent `.gitignore` pattern for paths
beneath it, so the restored `/.claude` line would re-ignore
`geb-lean/.claude/settings.json` and `geb-lean/.claude/rules/` even after
the parent `.gitignore` unignore exceptions are applied — defeating the
entire purpose of the parent fix. The serious finding is in the
`.markdownlint-cli2.jsonc` ignore patterns: the spec claims the
`geb-lean/`-prefixed ignores are "harmless" when `pre-push.sh` runs from
`geb-lean/` CWD, but in practice they are ineffective — they match
`geb-lean/geb-lean/.lake/**` (non-existent) rather than
`geb-lean/.lake/**`, so `.lake/` (64 `.md` files) and `.session/` (80
`.md` files, known lint issues) are scanned by the pre-push markdownlint
invocation and will cause failures on every run during the
Milestone A → B period. Three minor findings cover: (M1) `scripts/` is
labelled `(+ new directory)` in the file layout but already exists; (M2)
an internal inconsistency about whether plans live at `geb-lean/plans/`
(§ Repository structure) or `docs/superpowers/plans/` (CLAUDE.md
§ Specs and plans live on the feature branch); (M3) the CLAUDE.md
§ Style guidelines example list includes `crucial` as a forbidden word,
but `crucial` does not appear in the project's current banned-word list.

## Blocker findings

**B1 — `C-gitignore-revert` renders the parent `.gitignore` fix
ineffective.**

§ Cleanup tasks, row `C-gitignore-revert`.

The task directs: "Revert `geb-lean/.gitignore` to pre-A12 state (remove
the three … patterns … added in commit `69123dd0`)." The pre-A12 state of
`geb-lean/.gitignore` (confirmed via `git show 69123dd0~1:.gitignore`)
contained the line `/.claude`, meaning the `.claude` directory at the
`geb-lean/` root is ignored.

The problem: per the gitignore specification, a `.gitignore` file in a
lower (deeper) directory takes precedence over one in a higher directory
for the same path. After the proposed two-step sequence:

1. `C-gitignore-revert`: restore `geb-lean/.gitignore` → includes
   `/.claude`.
2. Apply parent `.gitignore` fix: add
   `!/geb-lean/.claude/settings.json` and
   `!/geb-lean/.claude/rules/` to `geb/.gitignore`.

For the path `geb-lean/.claude/settings.json`, `geb-lean/.gitignore`
is the inner (deeper) file and its `/.claude` pattern takes precedence
over `geb/.gitignore`'s `!/geb-lean/.claude/settings.json`. The
unignore pattern in the parent never fires; `settings.json` and
`rules/` remain git-ignored. Verified empirically: `git check-ignore
-v geb-lean/.claude/settings.local.json` from the parent `geb/` root
currently reports `.gitignore:7:.claude` as the controlling rule, not
any rule from `geb-lean/.gitignore` — confirming the parent's pattern
takes precedence in the current (pre-fix) state. After the proposed
fix, `geb-lean/.gitignore`'s `/.claude` would instead be the
controlling rule, still blocking the files.

The correct resolution is for `C-gitignore-revert` to **remove** the
`/.claude` line from `geb-lean/.gitignore` entirely (not restore it),
so that only the parent's selective patterns govern `.claude` contents
under `geb-lean/`. After the parent fix, the sub-directory `.gitignore`
needs no `.claude`-related patterns.

(A separate minor point: the task description calls `/.claude/*` "a
negation pattern", but `/.claude/*` does not start with `!` and is not
a negation. Only `!/.claude/rules/` and `!/.claude/settings.json` are
negation patterns. This mislabelling is minor; the blocker above is the
substantive issue.)

## Serious findings

**S1 — `pre-push.sh` markdownlint invocation scans `.lake/` and
`.session/`.**

§ Auxiliary scripts (`pre-push.sh` description); § `.markdownlint-cli2.jsonc`.

The spec states the `geb-lean/`-prefixed ignore patterns in
`.markdownlint-cli2.jsonc` (`"geb-lean/.lake/**"`, `"geb-lean/.jj/**"`,
`"geb-lean/.session/**"`) are "harmless when CWD is `geb-lean/`
(the patterns simply match nothing)." "Match nothing" is correct, but
the consequence is not harmless: with those ignores ineffective, the
`pre-push.sh` invocation of

```sh
markdownlint-cli2 --config .markdownlint-cli2.jsonc \
  --no-globs '**/*.md'
```

(run from `geb-lean/` CWD) scans all `.md` files under `geb-lean/`,
including `.lake/packages/**/*.md` (64 files, from mathlib, batteries,
aesop, importGraph — each with upstream lint issues) and
`.session/**/*.md` (approximately 80 files with known lint issues).
`pre-push.sh` will fail on every run during the Milestone A → B period.

The CI `markdown-lint.yml` workflow is not affected (it runs without an
explicit `working-directory`, so CWD is the parent `geb/` root, and
`geb-lean/**/*.md` as the glob argument with `geb-lean/`-prefixed ignores
behaves correctly from that CWD).

The fix options include: (a) use `.lake/**`, `.session/**` as additional
ignore patterns without the `geb-lean/` prefix (makes local invocation
work; parent-CWD invocation unaffected since those patterns match nothing
from `geb/`); (b) change `pre-push.sh` to pass explicit file arguments
covering only the refactor's own artefacts; or (c) have the
`C-markdownlint-config-rewrite` task add a dual-form ignore list covering
both CWD contexts.

## Minor findings

**M1 — File layout marks `scripts/` as `(+ new directory)` but it already
exists.**

§ New file and directory layout, `scripts/` entry.

`geb-lean/scripts/` is an existing committed directory containing
`check-axioms.sh`, `check-jj-setup.sh`, `hooks/`, and `nolints.json`
(all present at the start of the refactor). The `(+)` marker is
inaccurate. The `nolints.json` file is also absent from the layout
diagram (it appears in the § Repository structure bullet list at line 35
but not in the tree). The layout entry should read `(~ existing
directory; new files: pre-push.sh)` and should include `nolints.json`
in the tree.

**M2 — Internal inconsistency: plan file location.**

§ Repository structure (line 39) vs § CLAUDE.md section 9 (line 441).

The § Repository structure bullet says: `geb-lean/plans/*` (the
implementation plan lives here). § CLAUDE.md section 9 says the plan
path is `docs/superpowers/plans/<date>-<topic>-plan.md`. The file layout
diagram shows only `docs/superpowers/plans/` (under `docs/`) with no
top-level `plans/` entry. The actual existing plan for this refactor
lives at `geb-lean/plans/2026-05-07-process-bootstrap-plan.md`
(confirmed on disk), matching the § Repository structure bullet.
The spec needs one canonical answer for where plans live; the current
text gives two contradictory answers.

**M3 — CLAUDE.md § Style guidelines example list includes `crucial`, which
is not a project-banned word.**

§ CLAUDE.md, section 6 (line 421).

The spec states CLAUDE.md will give "a few examples (`key`, `important`,
`core`, `complex`, `crucial`) with a pointer to the full list." However,
`crucial` does not appear in the project's current banned-word list in
`CLAUDE.md` (verified). If the intent is to give examples drawn from the
existing list, `crucial` should be replaced with a word that is actually
on the list (e.g. `fundamental` or `complicated`). If the intent is to
expand the banned list to include `crucial`, that expansion should be
stated explicitly.

## Cosmetic-taste (NOT counted toward convergence; report only if obvious)

None.
