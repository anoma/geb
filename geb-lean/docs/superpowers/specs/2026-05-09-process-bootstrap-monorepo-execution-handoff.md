# Hand-off prompt — monorepo-aware process-bootstrap plan execution

This file is the entry-point briefing for a fresh Claude
session whose job is to execute the implementation plan for
the monorepo-aware geb-lean process-bootstrap refactor.

This supersedes the prior hand-off at
`docs/superpowers/specs/2026-05-07-process-bootstrap-execution-handoff.md`,
which assumed the original (now-superseded) plan and a
standalone-repo premise. The redesign incorporates the
monorepo-subdirectory reality: `geb-lean/` is a subdirectory
of the larger `geb/` monorepo (which also contains
`geb-agda/`, `geb-idris/`, top-level Common Lisp `src/`,
`test/`, `geb.asd`, `Makefile`, parent `README.md`, parent
`LICENSE` (GPLv3), parent `.github/workflows/{ci,docs}.yml`,
parent `.gitignore`).

## Your task

Execute Milestone A of the implementation plan at:

`plans/2026-05-09-process-bootstrap-monorepo-plan.md`

Use `superpowers:subagent-driven-development` (recommended;
fresh subagent per task with two-stage review). The plan
opens with cleanup tasks **C1–C6** that prepare the in-flight
`chore/process-refactor` branch for the new plan, then runs
Milestone A tasks **A1–A34**. Run cleanup tasks first in the
order C1, C2, C3, C4, C5, C6 (subject to `Depends on:` lines
in each task body), then Milestone A in order, respecting
every `Depends on:` line.

Do **not** begin Milestone B until the user has explicitly
signed off Milestone A (the plan's Task A34 is the gate).

## Files to read first (in this order)

1. `plans/2026-05-09-process-bootstrap-monorepo-plan.md` —
   the plan being executed. Read end-to-end before starting
   Task C1.
2. `CLAUDE.md` — project conventions, including the
   forbidden-word list, the Lean-specific workflow, and
   the literature-citation discipline. Persistent prose
   you author during execution must respect this list.
3. `docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md`
   — the authoritative design (12 adversarial-review cycles
   to convergence + a user-direction follow-up that removed
   `.jj/**` from markdownlint ignores). The plan references
   its sections by name (e.g. "§ jj setup", "§ Hooks");
   whenever a task says "render per spec § X", read that
   section in the design.
4. `plans/2026-05-09-process-bootstrap-monorepo-plan.review-1.md`
   through `.review-4.md` — the four plan-review logs.
   These document closed decisions the plan already
   reflects; do not re-litigate them.

## Repository structure (load-bearing)

The git repo root is `/home/terence/git-workspaces/geb/`,
**not** `/home/terence/git-workspaces/geb/geb-lean/`. The
geb-lean codebase is a subdirectory. This affects every
infrastructure-level task in the plan:

- **Cross-cutting infrastructure operates on the parent
  `geb/` repo:** CI workflows at `geb/.github/workflows/`;
  parent `geb/.gitignore`; `jj git init --colocate` at
  parent `geb/`; cutover signed tag on parent's tag
  namespace; GitHub Rulesets on parent's `main` and tag
  pattern `cutover-*`; signed-tag pushes target the
  parent's `origin`. Append-only-`main` from cutover
  forward binds the **parent's** `main` (all subprojects).
- **Code and per-project content scoped to `geb-lean/`:**
  `CLAUDE.md`, `.claude/rules/`, `.claude/settings.json`,
  `lakefile.toml`, `scripts/`, `GebLean/`,
  `docs/superpowers/`, `plans/`, `.markdownlint-cli2.jsonc`,
  `TODO.md`, new `geb-lean/README.md`.
- **Untouched:** `geb-agda/`, `geb-idris/`, `src/`, `test/`,
  parent `README.md` (except for a brief pointer paragraph
  near its top), parent `LICENSE` (GPLv3; geb-lean inherits
  transitively), parent `.github/workflows/{ci,docs}.yml`.

## Entry point

The branch `chore/process-refactor` already exists and
carries the in-flight commits from the prior execution
session (committed before the monorepo-aware redesign was
ready). Confirm baseline before starting Task C1:

```sh
cd /home/terence/git-workspaces/geb/geb-lean
git status                           # should be clean
git rev-parse --abbrev-ref HEAD      # should be chore/process-refactor
git log --oneline -3                 # most recent: doc(plan): cycle-3 fixes
lake build && lake test              # both should succeed without warnings
```

The first task to execute is **C1** (`C-license-rm`), which
removes the redundant `geb-lean/LICENSE` (Apache 2.0)
committed at the prior plan's A5; the parent `geb/LICENSE`
(GPLv3) is the actual licence governing geb-lean content.

## Cleanup-task ordering (load-bearing)

The cleanup tasks have ordering constraints encoded in their
`Depends on:` lines. The aggregate order:

- **C1 (license-rm)**: independent; remove `geb-lean/LICENSE`.
- **C2 (workflow-rm)**: independent; remove
  `geb-lean/.github/workflows/markdown-lint.yml` (wrong
  location).
- **C3 (gitignore-revert)**: precedes the new plan's A12
  (parent-`.gitignore` edit). Strip all `.claude`-related
  patterns from `geb-lean/.gitignore`.
- **C4 (markdownlint-config-rewrite)**: precedes the new
  plan's A2 (markdownlint verification of `lake lint` and
  the markdownlint-cli2 invocation). Drop top-level `globs`,
  add doubled-pattern `ignores` (no `.jj/**`).
- **C5 (hook-amend)**: precedes A27 (settings.json wires the
  hook). Change `block-mutating-git.sh` `.jj/` discovery
  from `[[ -d $CLAUDE_PROJECT_DIR/.jj ]]` to `jj root`.
  Re-run the five smoke-test cases (block-mutating-git
  payloads (a)-(e), originally A10 in the 2026-05-07 plan).
- **C6 (lean-action-ci-promote)**: precedes A13 (axiom_check
  job goes into the promoted file). `git mv`
  `geb-lean/.github/workflows/lean_action_ci.yml` to
  `geb/.github/workflows/lean_action_ci.yml`; adapt path
  filter, working-directory, `lake-package-directory` input.

## Hook-wiring discipline (LOAD-BEARING for task ordering)

Task A27 wires `.claude/settings.json`, which activates the
`block-mutating-git` PreToolUse hook. The hook denies
`git add`, `git commit`, `git switch`, and every other
mutating raw-git form for Claude.

- Cleanup tasks C1–C6 and Milestone-A tasks A1–A23 land
  their commits with plain `git add` / `git commit`
  because the hook is unwired through that range.
- A24 is user-direct (`jj git init --colocate` at the
  parent `geb/` root).
- A25 (`pre-push.sh`) is the last Claude-direct
  `git add` / `git commit` step before A27.
- A27 is the **final** Claude-direct commit-producing
  task. After A27, you must not run `git add` /
  `git commit` from any tool call; subsequent
  commit-producing work is either user-direct or routed
  through `jj describe` (which the hook does not gate).

Treat this ordering as mandatory. If a step seems to
require a Claude-direct `git commit` after A27, surface
the conflict to the user rather than working around the
hook.

## User-direct steps (do NOT attempt as Claude)

These tasks are the user's. Claude must surface them and
wait, not perform them. The plan's body marks each one;
the canonical list:

- **A24**: `jj git init --colocate` and the
  `jj config set` on-boarding sequence — performed at the
  parent `geb/` root.
- **A29**: pushing the topic branch and merging to
  parent's `main` (the cutover commit).
- **A30**: creating, signing, and pushing the
  `cutover-YYYY-MM-DD` tag to the parent's tag namespace.
- **A31**: creating the follow-up topic branch
  `docs/cutover-sha-record`, recording the SHA in
  `docs/process.md`, pushing, opening a PR, merging.
- **A32**: the `ci/integration-trigger` topic branch
  (workflow trigger update + merge), the
  `integration` bookmark creation, and the bookmark
  push — all on the parent `geb/`.
- **A33**: configuring GitHub Rulesets in the parent
  repository's GitHub web UI.
- **B1, B4 (during Milestone B)**: per-workstream triage
  confirmations, plus the topic-branch pushes. Each B1/B4
  task creates a `jj bookmark` and surfaces the push form
  for the user to run.

For each user-direct step, surface a clear summary of
what the user needs to do, then pause until they confirm
completion before proceeding.

## Verification discipline

Each task names a **Verification:** line at the end. After
landing the task's commit (or, for non-commit tasks,
finishing the work), run the named check. Do not proceed
to the next task until the verification passes.

After every task that touches anything Lake compiles, run
`lake build && lake test`. After every task that creates
or modifies a `.md` file, run
`markdownlint-cli2 --no-globs <path-to-file>` on that file
(the `--no-globs` flag is load-bearing — without it, the
config's auto-discovered ignores can suppress findings on
explicitly-passed paths). The plan's per-task steps name
these explicitly; the guidance here is the global default.

## Commit-message convention

Pre-cutover commits use mathlib's
`<type>(<optional-scope>): <subject>` form voluntarily
(it becomes mandatory post-cutover per
`.claude/rules/ci-and-workflow.md` once that file lands
at A17). Types: `feat | fix | doc | style | refactor |
test | chore | perf | ci`. Imperative present, no capital,
no period.

The plan's task bodies already name suggested commit
messages; use them verbatim or refine if the diff scope
diverges.

## Closed decisions the plan already respects

Do not re-open these (see `plans/...-plan.review-1.md`
through `.review-4.md`, plus the spec's
`.review-1.md` through `.review-12.md`):

- Layered `CLAUDE.md` ≤ 200 lines plus four
  `.claude/rules/*.md` files (geb-lean-internal).
- `jj` 0.41 colocated mode at the parent `geb/` root with
  `git.private-commits = "conflicts()"` and
  `remotes.origin.fetch-tags = "glob:cutover-*"`.
- Default-deny `block-mutating-git` PreToolUse hook with
  closed allowlists; tag operations are user-direct.
- `check-signing-key` SessionStart hook.
- Cutover commit + signed `cutover-YYYY-MM-DD` tag on the
  parent's main / tag namespace + GitHub Rulesets on the
  parent.
- Append-only `main` from cutover forward, applying to the
  parent's main (binds all subprojects).
- Parent `geb/LICENSE` is **GPLv3**; the prior in-flight
  Apache-2.0 `geb-lean/LICENSE` is removed by C1.
- Parent `geb/README.md` is untouched except for a brief
  pointer paragraph near its top; a new `geb-lean/README.md`
  is authored fresh.
- `moreLeanArgs = ["-DwarningAsError=true"]` preserved.
- `axiom_check` job in report-only mode initially with
  `--exit-zero-on-findings`; Milestone B item B5 flips to
  fail-mode (drops the flag).
- pre-push.sh's axiom-check is informational
  (`--exit-zero-on-findings`) pre-Milestone-B; B5 also
  drops the flag.
- `integration` branch's CI triggers are landed at A32 in
  the same task as the bookmark creation.
- New MCPs (arxiv-mcp-server, memory, MCP Solver) are
  recorded in CLAUDE.md § Tooling at A23 and in
  `docs/process.md` § Phase-driven workflow at A18.
- markdownlint-cli2 invocations use `--no-globs` and a
  quoted glob argument; the workflow uses an `npm install
  -g 'markdownlint-cli2@^0.18.0'` step (the action's
  config-globs additivity bug is the rationale).
- The `.markdownlint-cli2.jsonc` ignores list deliberately
  omits `.jj/**` (jj manages its own git-visibility via
  `.jj/.gitignore`).
- The `block-mutating-git.sh` `.jj/` detection uses
  `jj root` exit-0 rather than directory existence.
- GitHub Actions: `actions/upload-artifact` `path:` is
  inside `$GITHUB_WORKSPACE`; `defaults.run.working-directory`
  applies to `run:` steps only (not `uses:`); the
  `leanprover/lean-action@v1` step takes
  `lake-package-directory: geb-lean`.

## What NOT to do

- **Do not push.** Push is a user-gated operation per
  `CLAUDE.md`'s hard rules. Surface a request to push;
  the user runs `jj git push` or `git push` themselves
  (from the parent `geb/` working tree).
- **Do not modify the spec or the plan** during
  execution. If you find what looks like a defect,
  surface it to the user as an open question.
- **Do not begin Milestone B** until the user signs off
  Milestone A at A34.
- **Do not attempt user-direct steps** (the list above).
- **Do not work around the `block-mutating-git` hook**
  if you hit it post-A27. The hook is the project's
  enforcement of "use jj"; surface the obstruction
  rather than bypassing.
- **Do not skip verification gates.** A task is not done
  until its verification check passes.
- **Do not touch other subprojects** (`geb-agda/`,
  `geb-idris/`, `src/`, `test/`, `geb.asd`, `Makefile`,
  parent `README.md` except for the small pointer
  paragraph at A22, parent `LICENSE`).

## End-state of the prior session

The prior (planning + revision) session ended with the
plan converged through 4 fresh-context adversarial-review
cycles. The plan and its review logs are committed on
`chore/process-refactor`; HEAD is `93c3202d`
("doc(plan): apply cycle-3 review fixes (S1, M1-M2)").
Working tree is clean.

The branch carries 25 commits on top of `main` since the
session started:

```text
Cleanup-prep + plan-revision commits (this session):
  93c3202d doc(plan): apply cycle-3 review fixes (S1, M1-M2)
  02169c4f doc(plan): apply cycle-2 review fixes
  fc2c81b6 doc(plan): apply cycle-1 review fixes
  21e0c6cc doc(plan): author monorepo-aware 2026-05-09 plan
  ede4c9ce doc(spec): remove .jj/** from markdownlint ignores
  699f47dd doc(spec): apply cycle-11 review fix
  86e186d5 doc(spec): apply cycle-10 review fixes
  47ce0900 doc(spec): apply cycle-9 review fixes
  520969c8 doc(spec): apply cycle-8 review fixes
  84f7e4f0 doc(spec): apply cycle-7 review fixes
  a3548922 doc(spec): apply cycle-6 review fixes
  2677568d doc(spec): apply cycle-5 review fixes
  a9a4fab2 doc(spec): apply cycle-4 review fixes
  c9d64bd8 doc(spec): apply cycle-3 review fixes
  2d0a3b6e doc(spec): apply cycle-2 review fixes
  fe838f5c doc(spec): apply cycle-1 review fixes
  91b98236 doc(spec): author monorepo-aware 2026-05-09 design

In-flight commits from the prior execution session (some
need cleanup; see C1-C6):
  69123dd0 chore(gitignore): whitelist committed .claude paths
            → C3 reverts (null-effect edit)
  813d70b7 chore(hooks): add check-signing-key.sh
            → kept as-is (geb-lean-internal)
  125c6d4e chore(hooks): add block-mutating-git.sh
            → C5 amends (.jj/ discovery → jj root)
  e6340e29 chore(scripts): add check-jj-setup.sh
            → kept as-is
  6bbd7d75 chore(scripts): vendor check-axioms.sh from lean4-skills
            → kept as-is
  079302ae chore: add Apache 2.0 LICENSE
            → C1 removes (parent has GPLv3)
  3d27311f ci: add markdown-lint workflow
            → C2 removes (wrong location)
  00284252 chore(lake): wire batteries/runLinter with nolints baseline
            → kept as-is (lakefile-internal)
```

The user has approved the plan and signaled execution
should begin in a fresh session (this hand-off prompt).

The repository's pre-existing state (CSLib pin, mathlib
`v4.29.0-rc6`, the in-flight `kToER` Step-5 work,
geb-agda/, geb-idris/, top-level CL files etc.) is
unchanged.
