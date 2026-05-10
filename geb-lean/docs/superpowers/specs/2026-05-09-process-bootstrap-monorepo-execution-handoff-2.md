# Hand-off prompt — monorepo process-bootstrap, session 2

This file is the entry-point briefing for the second Claude
session executing the implementation plan for the
monorepo-aware geb-lean process-bootstrap refactor. It
supersedes the original entry-point at
`2026-05-09-process-bootstrap-monorepo-execution-handoff.md`,
which described the state at session-1 start.

## Read first

1. `2026-05-09-process-bootstrap-monorepo-execution-handoff.md`
   — the session-1 entry-point. Its closed-decisions list,
   user-direct-step list, and ordering constraints remain
   in force.
2. `plans/2026-05-09-process-bootstrap-monorepo-plan.md` —
   the plan being executed. C1–C6 cleanup and Milestone-A
   tasks A1–A23 are complete on `chore/process-refactor`.
3. `CLAUDE.md` (the rewritten ≤200-line version landed in
   session 1) for the prose register.

## State at session-2 start

Branch `chore/process-refactor` carries the prior planning
commits, plus session-1's commits below.

### Cleanup phase (C1–C6)

- `0a6d3f07` C1 — remove geb-lean/LICENSE
- `7ffa0048` C2 — remove geb-lean-local markdown-lint.yml
- `78f13f66` C3 — remove .claude patterns from geb-lean .gitignore
- `c8a5fa91` C4 — rewrite .markdownlint-cli2.jsonc
- `bbb37222` C5 — block-mutating-git.sh uses `jj root`
- `ff5becda` C6 — promote lean_action_ci.yml to parent

### Milestone A through A23

- `6530f02c` A4 — parent markdown-lint.yml workflow
- `4c10e7e3` A12 — parent .gitignore allows geb-lean/.claude
  /{rules/,settings.json}
- `47980d91` A13 — axiom_check job (report-only)
- `b60fb27a` A14 — lean-disciplines rule (unconditional)
- `45295182` A15 — lean-coding rule (paths: `**/*.lean`)
- `27652fb9` A16 — markdown-writing rule (paths: `**/*.md`)
- `88d8bc23` A17 — ci-and-workflow rule (workflows + scripts)
- `3ace6d07` A16-followup — rephrase one borderline word use
- `0a5ee5b2` A18 — docs/process.md (eighteen sections)
- `6ec5fcc8` A19 — docs/index.md (workstream narrative)
- `614e6df9` A20 — docs/lean-resources.md (lifted from CLAUDE.md)
- `a2e065e1` A21 — TODO.md (repository-root index)
- `24b12cfe` A22a — new geb-lean/README.md
- `8693ed61` A22b — parent README.md pointer paragraph
- `c711e306` A23 — rewrite CLAUDE.md to ≤200 lines

### Session-1 wrap-up

- `6be466b7` chore(gitignore) — close A12 omission of four
  .claude paths
- `3f22c0c6` doc(spec) — commit twelve design adversarial
  review logs
- `5f6589a2` doc(plan) — commit four plan adversarial
  review logs
- this commit — session-2 hand-off prompt

A1, A2, A3, A5, A6, A7, A8, A9, A10, A11 were
verification-only and produced no commits; their checks
are recorded in session-1 conversation history.

## Discovered defects (closed in session 1)

1. **A12 omitted four .claude paths.** The original
   geb-lean-local `.gitignore` had `/docs/.claude` (removed
   at C3 expecting the parent to take over), and
   `.markdownlint-cli2.jsonc` has `.claude/{memory,docs,
   tools}/**` ignores; both sets were missing from A12's
   consolidated patterns. Closed by `6be466b7`.

2. **A2 Step 3 probe procedure under-specified.** The
   plan's instruction creates `GebLean/Utilities/_LintProbe
   .lean` and runs `lake lint`. As written, this does not
   flag the probe because the `runLinter` driver checks
   declaration-level mathlib-style lints, not unused-
   variable warnings. The build-time
   `linter.unusedVariables` warning-as-error path DOES
   flag it, but only if the probe is added to
   `GebLean.lean`'s import graph transiently. Session 1
   verified the linter is operational via the build path;
   the plan should be amended for session 2 if A2 needs to
   be re-run.

3. **A7 / A13 path mismatch.** The plan's smoke-test
   command and CI body both reference `test/` for the test
   directory; the actual project test dir is
   `GebLeanTests/`. Session 1 used `GebLeanTests/` in
   A13's CI workflow (commit `47980d91`).

4. **A24 jj initialization disrupted git index.** When
   `jj git init --colocate` was attempted, jj's snapshot
   produced a 155-path swap in the git index (removed
   tracked geb-lean files; added intent-to-add stubs for
   the un-ignored `docs/.claude` content). Root cause was
   defect 1 above. Fully unwound: `git read-tree HEAD`
   restored the index, `rm -rf .jj/` removed jj. Defect
   1's fix should make a retry succeed.

## Where to begin

The next task is **A24 retry**: `jj git init --colocate`
at the parent `geb/` root. With the gitignore defect
closed, jj's snapshot should now match HEAD's tree
exactly. After A24:

- **A25** — author `geb-lean/scripts/pre-push.sh` (Claude).
- **A26** — `conflicts()` smoke test (verification, no
  commit).
- **A27** — wire `geb-lean/.claude/settings.json` (the
  last Claude-direct commit before the hook activates).
- **A28** — run the Milestone-A verification checklist.
- **A29–A33** — USER-DIRECT (push topic branch, signed
  cutover tag, follow-up SHA-record PR, integration
  branch + bookmark, GitHub Rulesets).
- **A34** — surface Milestone-A completion gate.

## Order of operations for session 2

1. Read this file end-to-end.
2. Read `plans/2026-05-09-process-bootstrap-monorepo-plan
   .md` tasks A24 onward (lines 1768+).
3. Run a sanity build:
   `cd geb-lean && lake build && lake test`. Expect both
   clean.
4. Surface A24 to the user (jj init at parent root with
   the on-boarding `jj config set` sequence).
5. After user confirms A24, dispatch a subagent for A25.
6. Continue through A26 (smoke test), A27 (settings.json),
   A28 (verification).
7. Surface A29–A33 to the user with explicit commands.
8. Land A34's completion message and pause.

## What NOT to do

The original handoff's restrictions still apply: no push
without user authorization; do not work around the
block-mutating-git hook once A27 lands; do not begin
Milestone B until the user signs off Milestone A; do not
modify the spec or plan during execution — surface defects
as discoveries instead.
