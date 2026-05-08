# Hand-off prompt — process-bootstrap implementation plan

This file is the entry-point briefing for a fresh Claude
session whose job is to produce the implementation plan for
the geb-lean process-bootstrap refactor.

## Your task

Invoke `superpowers:writing-plans` to author the
implementation plan for the design at:

`docs/superpowers/specs/2026-05-07-process-bootstrap-design.md`

After the plan is drafted, run the same adversarial-review
discipline that produced the design: dispatch fresh-context
Agent reviewers cycle by cycle, log responses as
`docs/superpowers/specs/2026-05-07-process-bootstrap-plan.review-N.md`,
and iterate until convergence (defined below). Then surface
to the user.

## Files to read first (in this order)

1. `CLAUDE.md` — project conventions, including the forbidden-
   words list, the Lean-specific workflow, and the
   literature-citation discipline.
2. `docs/superpowers/specs/2026-05-07-process-bootstrap-design.md` —
   the design spec being implemented. This is the authoritative
   artefact. Read end-to-end before drafting the plan.
3. `docs/superpowers/specs/2026-05-07-process-bootstrap-design.review-15.md`,
   `.review-16.md`, `.review-17.md`, and `.review-jj-0.41.md` —
   the most recent review logs; these document closed decisions
   that the plan must respect (do not re-open them).

The earlier review logs (`design.review-1.md` through
`.review-14.md`) are available for context if you need to
trace why a particular spec wording is the way it is, but
you should not need to re-litigate any earlier-cycle
decisions.

## Output location

Write the plan to:

`plans/2026-05-07-process-bootstrap-plan.md`

The `plans/` directory is the user's chosen location for
implementation plans (distinct from `docs/superpowers/specs/`,
which holds design specs and review logs).

If `plans/` does not exist yet, create it.

## Convergence discipline (cap-free, per user instruction)

The user has been explicit: there is **no fixed cap** on
adversarial-review cycles. Iterate until either:

- All open findings are cosmetic-taste, OR rejected with
  rationale recorded in the cycle's response log, OR the
  reviewer concludes the goal is unachievable; OR
- The author concludes that convergence is impossible and
  surfaces that conclusion to the user with reasoning.

Each cycle's response log lives at
`docs/superpowers/specs/2026-05-07-process-bootstrap-plan.review-N.md`
and follows the same structure as the design's review logs:
findings categorised as **blocker / serious / minor /
cosmetic-taste**, each with the author's response (fixed,
rejected-with-rationale, or cosmetic-taste-rejected). The
last log states the convergence verdict explicitly.

Each cycle uses a **fresh-context** Agent invocation (a
`subagent_type: "general-purpose"` Agent), not a fork. The
reviewer prompt should brief the Agent on the task, point
it at the plan and the design, list closed decisions that
should not be re-litigated, and specify the four-category
output format.

After material edits to the plan, dispatch another cycle.
Cycles 16 and 17 of the design's review history illustrate
this: a material edit triggered by upstream news (jj 0.41
release) led to one further round, even though cycle 15 had
declared convergence.

## Closed decisions the plan must respect

The following are settled by the design (and the review
history) and the plan must NOT re-litigate them:

- **CLAUDE.md layered architecture**: slim `CLAUDE.md`
  (under 200 lines), with rule files
  `.claude/rules/lean-disciplines.md` (unconditional),
  `.claude/rules/lean-coding.md` (path-scoped to `.lean`
  files and to specs/plans containing Lean code),
  `.claude/rules/markdown-writing.md`,
  `.claude/rules/ci-and-workflow.md`, and `docs/process.md`
  carrying rationale.
- **jj 0.41 colocated mode** with `git.private-commits =
  "conflicts()"` and `remotes.origin.fetch-tags =
  "glob:cutover-*"`, both set per-repo. Per-developer
  signing/identity at user-level. (See spec § jj setup and
  § On-boarding.)
- **Two-milestone verification**: Milestone A (structural)
  and Milestone B (`.session/` retirement). The
  two-milestone split is settled.
- **Default-deny `block-mutating-git`** PreToolUse hook
  with closed allowlists. **Tag operations are user-direct,
  NOT allowlisted**; this was settled in cycle 11 and
  re-confirmed by cycle 12 dropping the tag-push allowlist
  entry. Do not propose re-adding a tag-push allowlist
  entry under any circumstances.
- **`check-signing-key`** SessionStart hook for per-session
  warnings.
- **Cutover commit + signed git tag (`cutover-2026-MM-DD`) +
  GitHub repository protection rules** (Rulesets, with
  legacy Tag protection rules as a deprecated fallback).
- **Append-only `main`** from cutover forward; verified by
  `git log --first-parent origin/main`.
- **Apache 2.0 LICENSE**; no per-file copyright headers.
- **`moreLeanArgs = ["-DwarningAsError=true"]`** (the spec
  cites this verbatim).
- **`axiom_check` job** initially in report-only mode;
  Milestone B item B7 flips it to fail-mode.
- **Adversarial-review discipline order**: self-review THEN
  adversarial review BEFORE surfacing to the user
  (per user's earlier instruction in the design phase).
- **`remotes.<name>.fetch-tags` is experimental** in jj
  0.41; the design documents the fallback (explicit raw-git
  refspec form + corresponding allowlist entry + on-boarding
  step). The plan should reference but not duplicate this
  fallback.

## Plan content guidance

The plan should:

- Decompose the implementation into discrete tasks, each
  small enough to verify independently.
- For each task, name the files it touches, the verification
  signal (test, lint, smoke-test, manual check), and any
  dependencies on prior tasks.
- Sequence tasks so each task's verification gate can pass
  in isolation. The user's coding discipline (`CLAUDE.md`
  workflow) emphasises one-change-at-a-time: build/test
  after each edit, fix problems before proceeding.
- Distinguish **Milestone A tasks** (structural — files,
  scripts, hooks, CLAUDE.md split, TODO.md, LICENSE,
  workflows, cutover) from **Milestone B tasks**
  (`.session/` triage and retirement). Milestone B depends
  on user-confirmed labels per the design's labelling
  scheme.
- Identify any "user-direct" steps (tag operations, GitHub
  Ruleset configuration, manual triage decisions) and
  flag them so Claude does not attempt them.
- Be markdownlint-clean. Run
  `markdownlint-cli2 plans/2026-05-07-process-bootstrap-plan.md`
  before declaring the plan ready.
- Avoid the forbidden-word list in `CLAUDE.md` for any
  persistent prose.

## User preferences relevant to this work

- Keep the tone of all persistent text dry, formal,
  unopinionated, mathematical (per `CLAUDE.md`).
- 80-character line limit on all markdown files.
- No emoji.
- No "TODO" / "FIXME" comments in the plan body; track
  work-in-progress through the plan's task list itself.
- The user is already familiar with the spec's content;
  the plan should not recap design decisions, only sequence
  their implementation.

## When to surface

After convergence, surface to the user a brief summary of:

- The plan's task count and rough sequencing
- Whether any closed-decisions need to be re-confirmed
  (you should not have any if the plan respected the
  closed-decisions list above)
- Any open questions the plan deferred to the user

The user will then either approve, request changes, or
direct execution.

## What NOT to do

- Do not begin executing the plan. The flow is brainstorm →
  spec → plan → user-approval → execution. The plan is the
  hand-off artefact, not the start of execution.
- Do not modify the design spec. If you find what looks
  like a defect in the spec while drafting the plan, surface
  it to the user as an open question rather than editing
  the spec; the spec has already passed 17 cycles of
  adversarial review and is treated as authoritative.
- Do not re-derive the jj 0.41 research; it is captured in
  `design.review-jj-0.41.md`.
- Do not attempt user-direct operations (tag pushes,
  GitHub UI configuration, manual triage decisions); these
  are explicitly out of Claude's scope per the design's
  § Hooks section.

## End-state of the prior session

Last action of the prior session: cycle-17 fixes applied,
`design.review-17.md` written, lint clean, surfaced to user
with the question "writing-plans in this session or fresh?".
The user chose fresh and asked for this hand-off prompt to
be written. No git commits have been made yet for any of
the spec or review-log work; the working tree carries:

- `docs/superpowers/specs/2026-05-07-process-bootstrap-design.md`
  (modified)
- `docs/superpowers/specs/2026-05-07-process-bootstrap-design.review-1.md`
  through `.review-17.md` and `.review-jj-0.41.md` (created
  during the prior session)
- `.markdownlint-cli2.jsonc` (created during the prior
  session)
- This file (`...plan-handoff.md`)

The user has not yet decided whether to commit the
spec-and-review work as a single commit or to bundle it
with the plan when both are ready. Do not commit anything
in your session unless the user explicitly asks; surface
this question if relevant.
