# Hand-off prompt — process-bootstrap plan execution

This file is the entry-point briefing for a fresh Claude
session whose job is to execute the implementation plan for
the geb-lean process-bootstrap refactor.

## Your task

Execute Milestone A of the implementation plan at:

`plans/2026-05-07-process-bootstrap-plan.md`

Use `superpowers:subagent-driven-development` (recommended;
fresh subagent per task with two-stage review) or
`superpowers:executing-plans` (inline batch execution with
checkpoints). Run the plan's tasks A1 through A34 in order,
respecting every `Depends on:` line.

Do **not** begin Milestone B until the user has explicitly
signed off Milestone A (the plan's Task A34 is the gate).

## Files to read first (in this order)

1. `plans/2026-05-07-process-bootstrap-plan.md` — the
   plan being executed. Read end-to-end before starting
   Task A1.
2. `CLAUDE.md` — project conventions, including the
   forbidden-word list, the Lean-specific workflow, and
   the literature-citation discipline. Persistent prose
   you author during execution must respect this list.
3. `docs/superpowers/specs/2026-05-07-process-bootstrap-design.md`
   — the authoritative design. The plan references its
   sections by name (e.g. "§ jj setup", "§ Hooks") rather
   than reproducing content; whenever a task says "render
   per spec § X", read that section in the design.
4. `docs/superpowers/specs/2026-05-07-process-bootstrap-plan.review-1.md`,
   `.review-2.md`, `.review-3.md` — the three plan-review
   logs. These document closed decisions the plan already
   reflects; do not re-litigate them.

## Entry point

Task A1 of the plan:

```sh
git switch -c chore/process-refactor
lake build
lake test
```

Confirm both succeed before proceeding to Task A2.

## Hook-wiring discipline (LOAD-BEARING for task ordering)

Task A27 wires `.claude/settings.json`, which activates
the `block-mutating-git` PreToolUse hook. The hook denies
`git add`, `git commit`, `git switch`, and every other
mutating raw-git form for Claude.

- Tasks A1 through A23 land their commits with plain
  `git add` / `git commit` because the hook is unwired
  through that range.
- A24 is user-direct (`jj git init --colocate`).
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
  `jj config set` on-boarding sequence.
- **A29**: pushing the topic branch and merging to
  `main` (the cutover commit).
- **A30**: creating, signing, and pushing the
  `cutover-YYYY-MM-DD` tag.
- **A31**: creating the follow-up topic branch
  `docs/cutover-sha-record`, recording the SHA in
  `docs/process.md`, pushing, opening a PR, merging.
- **A32**: the `ci/integration-trigger` topic branch
  (workflow trigger update + merge), the
  `integration` bookmark creation, and the bookmark
  push.
- **A33**: configuring GitHub Rulesets in the GitHub
  web UI.
- **B1 through B5** (during Milestone B): per-workstream
  triage confirmations (Claude proposes a classification;
  the user confirms or amends), and the topic-branch
  pushes / merges in B4 and B5.

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
`markdownlint-cli2 <path-to-file>` on that file. The
plan's per-task steps name these explicitly; the
guidance here is the global default.

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

Do not re-open these (see plan-review-1.md, plan-review-2.md,
plan-review-3.md, plus the design's review-15.md,
review-16.md, review-17.md, review-jj-0.41.md):

- Layered `CLAUDE.md` ≤ 200 lines plus four
  `.claude/rules/*.md` files.
- `jj` 0.41 colocated mode with
  `git.private-commits = "conflicts()"` and
  `remotes.origin.fetch-tags = "glob:cutover-*"`.
- Default-deny `block-mutating-git` PreToolUse hook with
  closed allowlists; tag operations are user-direct.
- `check-signing-key` SessionStart hook.
- Cutover commit + signed `cutover-YYYY-MM-DD` tag +
  GitHub Rulesets.
- Append-only `main` from cutover forward.
- Apache 2.0 `LICENSE`; no per-file copyright headers.
- `moreLeanArgs = ["-DwarningAsError=true"]` preserved.
- `axiom_check` job in report-only mode initially;
  Milestone B item B5 flips to fail-mode.
- pre-push.sh's axiom-check is informational (`|| true`)
  pre-Milestone-B; B5 also drops the suffix.
- `integration` branch's CI triggers are landed at A32 in
  the same task as the bookmark creation (no follow-up
  session needed).
- New MCPs (arxiv-mcp-server, memory, MCP Solver) are
  recorded in CLAUDE.md § Tooling at A23 and in
  `docs/process.md` § Phase-driven workflow at A18.

## What NOT to do

- **Do not push.** Push is a user-gated operation per
  `CLAUDE.md`'s hard rules. Surface a request to push;
  the user runs `jj git push` or `git push` themselves.
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

## End-state of the prior session

Last action of the prior (planning) session: the
implementation plan was authored and converged through
three fresh-context adversarial-review cycles. The bundle
commit landed locally on `main` as commit `e98eabde`
("doc(plan): add process-bootstrap plan and
adversarial-review log"), containing the plan and the
three plan-review logs. Working tree was clean.

The user has (or is about to) push the bundle commit to
`origin/main`. By the time you start, `origin/main`
should be at-or-after `e98eabde`.

The repository's pre-existing state (CSLib pin, mathlib
`v4.29.0-rc6`, the in-flight `kToER` Step-5 work, etc.)
is unchanged. The refactor's structural work has not yet
begun; that is your task.
