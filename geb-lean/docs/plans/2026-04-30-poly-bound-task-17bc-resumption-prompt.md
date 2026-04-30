# Session-resumption prompt for Task 17b/17c execution

> Copy the entire fenced block below into the next session's
> opening message.  The prompt is self-contained — it
> assumes the agent has zero conversation context but full
> file access to the geb-lean repository.

````text
You are resuming a Lean 4 formalization workstream in the
GebLean project.

Working directory: /home/terence/git-workspaces/geb/geb-lean
Branch: terence/develop

## What this workstream is

Formalizing Tourlakis's K^sim_2 ⊆ ER result via a recursive
bootstrap (K^sim_n ⊆ E^{n+1} for n = 0, 1, 2).  The forward
translation `kToER : KMor1 a → ERMor1 a` is defined; what
remains is proving its correctness (interp preservation +
linear bound) and the dominance lemma it consumes from
`boundedRec_eq_natRec_of_bounded` for the simrec case.

## Required reading (in order)

1. CLAUDE.md (project conventions — banned-words list,
   no-warnings policy, no-sorry policy, line-length 80,
   build with `lake build`/`lake test`, never `lake env lean`).
2. docs/plans/2026-04-30-poly-bound-task-17bc-completion-plan.md
   — THIS IS THE EXECUTABLE PLAN.  Read it end-to-end.
3. docs/plans/2026-04-30-er-polynomial-bound-plan.md (parent
   plan; "Brainstorm refinements" section provides strategic
   context R1–R6).
4. docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md (parent
   kToER plan; Task 14 consumes this workstream's final
   deliverable).
5. docs/research/2026-04-30-ksim-polynomial-bound-references.md
   (literature citations underpinning the proof structure).

## How to execute

Use the `superpowers:executing-plans` skill (or
`superpowers:subagent-driven-development` if you prefer
fresh-context per task).  The plan has bite-sized tasks A.1
through H.5; work through them in order.

For each task: read its steps, run the implementation,
verify with `lake build` and (where applicable)
`lake test`, then commit.

## State verification BEFORE starting

```bash
cd /home/terence/git-workspaces/geb/geb-lean
git log --oneline -10
lake build
lake test
```

Expected:
- HEAD commit: ce71093d "Add Task 17b/17c completion plan with adversarial review"
- Recent commits include: 9766ca12 (strengthened structural
  bound), 21defbab (plan refinements R1-R6), 9fb91aac
  (omega fix on structural lemma).
- Build clean: 1521 jobs successful.
- Tests pass.

If verification fails (e.g. build broken), STOP and report
back.  Do not proceed.

## Critical project conventions (CLAUDE.md highlights)

- NEVER use `sorry` or `admit` in committed code (the plan
  includes `sorry` markers as placeholders for sub-steps;
  these must all be discharged before commit).
- NEVER use `lake env lean` or `lake clean`.
- `warningAsError = true` — any warning fails the build.
- Banned words list: never use "fundamental", "actually",
  "key", "insight", "core", "advanced", "complex", "simple",
  "advantage", "benefit", "important", "challenge", "yes",
  "wait", "hmm", "sorry", "careful", "difficult", "blocked",
  "incomplete", "future", "issue", "problem", "block" in
  source code, comments, or commit messages — except as
  standard technical terms.  Code style is dry, formal,
  unopinionated.
- Line length ≤ 80 characters in code.
- No emojis.
- No "TODO" comments in code (track in `.session/` only).

## Highest-risk subtask: Task A.5

Phase I Task A.5 (tower-level absorption + structural
propagation) is the workstream's deepest part.  Read the
plan's "Risk assessment" section first.  Before starting
A.5, decide between:

- Strategy A (default): A.5.0 + A.5.1 + A.5.2 as planned.
- Strategy B (fallback): pivot to using
  `polynomial_iter_tower_bound` and
  `kSimPackedStep_polyBound`.  Plan documents the pivot
  cost.

If A.5 stalls for >2 days, surface the obstruction and
discuss before continuing.  Do not silently expand scope or
weaken interfaces.

## Use Lean MCP tools liberally

- `mcp__lean-lsp__lean_goal` after each tactic step to
  inspect goal state.
- `mcp__lean-lsp__lean_diagnostic_messages` to read errors.
- `mcp__lean-lsp__lean_multi_attempt` to test tactics
  without editing.
- `mcp__lean-lsp__lean_local_search` to find existing
  lemmas before reinventing.
- `mcp__lean-lsp__lean_loogle` for type-pattern searches.
- `lean4:sorry-filler-deep` skill on stubborn sorries
  (especially A.5.1 and A.5.2's log-arithmetic).

## Commit discipline

Commit after each Task (A.7, B.2.4, C.1.4, D.3.4, E.3,
F.4, G.3 per the plan).  Within a task, do not commit
intermediate sub-steps that contain sorry markers — only
commit when the task's final build is clean of warnings.

Commit messages: 1-2 sentences why; reference the plan task
(e.g. "Task 17b.2", "Task A.5.0").  Use HEREDOCs for
multi-line messages.

NEVER `--amend`, `--force-push`, or `--no-verify`.

## When you're done

Phase V Task H is final verification:

- Full `lake build` clean (1521+ jobs).
- Full `lake test` clean.
- No `sorry`/`admit` in source.
- Parent plan's task graph updated.

Then report back to the user with:

- Total commits made.
- Any deviations from the plan and why.
- Any blockers requiring user input.

Begin by reading the plan and verifying state.  Do not
start implementation until verification passes.
````

## Notes for the next session's user

The above prompt is verbatim what to paste in.  The plan
file referenced is at:
`docs/plans/2026-04-30-poly-bound-task-17bc-completion-plan.md`

Total estimated effort: 800-1200 lines of Lean across
~15 commits.  Highest risk in Phase I Task A.5; expect
to spend ~40% of total session time on that one subtask.

If executing across multiple sessions, the natural break
points are:

- After Phase I (Task A done): structural foundation +
  level-1 dominance proven.  Most of the heavy proof
  work landed.
- After Phase IV (Task D done): both level-1 and level-2
  dominance proven.  All math complete; only housekeeping
  remains.
- After Phase V (Tasks E-H done): workstream complete.
  Task 14 of the kToER plan is unblocked.
