# Instructions for Claude Code

This repository is `geb-lean`: an experimental Lean 4 + mathlib
formalisation hub for Geb, the active-experimentation
counterpart to the curated `geb-mathlib` repository. See
`README.md` for the full project identity and `docs/process.md`
for the rationale behind each rule below.

## Repository structure note

`geb-lean/` is a subdirectory of the `geb/` monorepo (parent
repo at `..`). Cross-cutting infrastructure — CI workflows, the
parent `.gitignore`, the colocated `jj` init, GitHub Rulesets,
and the signed cutover tag — lives at the parent level. Code and
per-project content are scoped to `geb-lean/`.

## Project status

Active experimentation. The 2026-05-09 process refactor is in
effect: phase-driven workflow, slim always-on layer, area-scoped
rules under `.claude/rules/`. See `TODO.md` for the running task
list and `docs/index.md` for the workstream-by-workstream
narrative.

## Hard rules — must not violate

- No `git push` without user line-by-line review. The same
  human-gate rule applies to `gh` write operations
  (`gh pr create`, `gh pr merge`, `gh release create`,
  `gh issue create`, `gh issue close`, etc.).
- No raw mutating `git` subcommands; the PreToolUse hook
  enforces a closed-allowlist default-deny policy. Use `jj`.
- No LLM-drafted text in user-facing channels (PR descriptions,
  GitHub comments, issue threads).
- Generic user references in committed text only — no embedded
  names, emails, or autobiographical details.
- No `noncomputable`, no `axiom`; minimise `Classical` (see
  Constructive-only Lean code below).
- Specs and plans pass through fresh-context adversarial review
  looped to convergence before user review. Convergence requires
  zero blocker, zero serious, and zero minor findings (only
  cosmetic-taste may remain). Each round's reviewer is a new
  `Agent` invocation reading only the artefact and its cited
  sources. See `docs/process.md` § Adversarial review of specs
  and plans for the full protocol.
- No `admit` anywhere — ever.
- No `sorry` in any commit. (`sorry` is a permitted transient
  working tool between commits; committed code must build under
  warnings-as-errors, which fails on `sorry`.)
- Use `_` (underscore), not `sorry`, when surfacing a hole's
  type as a goal-display error.
- No warnings in committed code: `lake build` must be clean.

## Phase-driven workflow

| Phase | Skills and helpers |
| --- | --- |
| Brainstorm | `superpowers:brainstorming` |
| Spec | author at `docs/superpowers/specs/` on topic branch |
| Adversarial review (spec) | fresh-context subagent per round, looped to convergence (zero blocker/serious/minor); see process |
| Plan | `superpowers:writing-plans` at `plans/` |
| Adversarial review (plan) | fresh-context subagent per round, looped to convergence (zero blocker/serious/minor); see process |
| Execute | `superpowers:subagent-driven-development` |
| Lean code | `lean4:*` (incl. `prove`, `golf`, `refactor`) |
| Mathlib search | Loogle, `lean_leansearch`, `lean_loogle` |
| Verify | `superpowers:verification-before-completion` |
| Review | `code-review:*`, `pr-review-toolkit:*` |
| Pre-commit | `commit-commands:*`; pre-push hook runs lints |
| Finish branch | `superpowers:finishing-a-development-branch` |

## Style guidelines

Use a formal, mathematical, dry, unopinionated register. Avoid
value-laden adjectives (`key`, `important`, `core`, `complex`,
and similar). The full word list and prose-tone rules live in
`.claude/rules/markdown-writing.md` (loaded unconditionally).
Detailed Lean-specific style rules live in
`.claude/rules/lean-coding.md` (loaded for `**/*.lean`). The
register binds repository content; conversational chat is
unrestricted.

## Repo structure

- `GebLean/` — Lean source; root namespace `GebLean`.
- `GebLean/Utilities/` — shared helpers; `GebLean.lean` is the
  index module that re-exports the public API.
- `GebLeanTests/` — `lake test` targets, including `#guard`
  assertions and Plausible property tests.
- `docs/` — research and process documentation; see
  `docs/index.md`.
- `plans/` — workstream plans, one per dated topic.
- `.claude/rules/` — area-scoped rules.
- `scripts/` — local lints and helpers (e.g.
  `check-axioms.sh`).
- `TODO.md` — running task list at the repository root.

`main` is append-only; `integration` is a regenerated fan-in
view; topic branches use `feat/`, `fix/`, `refactor/`, `chore/`,
`docs/`, `bump/` prefixes.

## Constructive-only Lean code

Never import or `open` `Classical`, never use the `classical`
attribute, never use `noncomputable`, never use `axiom`. Results
must depend only on Lean's native type theory. `Quotient`/`Quot`
are usable via the constructive API (`mk`, `lift`, `ind`,
`sound`); avoid `Quotient.out`/`Quot.out` (they require
`Classical.choice`). `scripts/check-axioms.sh` flags
non-allowlisted axioms in CI and pre-push.

## Specs and plans live on the feature branch

Each workstream's spec, plan, and code co-evolve on the same
topic branch. Specs live at
`docs/superpowers/specs/<date>-<topic>-design.md`; plans at
`plans/<date>-<topic>-plan.md`. Adversarial-review iterations
and self-review fixes are commits on the same branch. The
merge-commit cutover lands them on `main`.

## GebLean-specific disciplines

Substantive prose for these rules lives in
`.claude/rules/lean-disciplines.md` (unconditionally loaded).
This list is the human-readable index.

- **Literature-citation discipline** (transcription
  workstreams): every planned and implemented function,
  definition, or theorem in a transcription workstream cites the
  source proposition. Citations reference research documents in
  `docs/research/` for the cross-reference network.
- **Bottom-up named-composite discipline for categorical
  equivalences**: never add a constructor to a new category
  before its image in the target category has been built and
  named as a `def` with a `@[simp]` interp lemma.
- **Non-negotiable interfaces for categories formalising
  pre-existing mathematical objects**: object/morphism
  interfaces are fixed by the external mathematical source.
  Implementation strategy may change; interface may not.

## Cross-reference to file-edit-only Lean rules

Build discipline, mathlib comment / docstring rules, Lean
idioms, and other rules that apply only when editing `.lean`
source live in `.claude/rules/lean-coding.md` (scoped via
`paths: ["**/*.lean"]`). That file loads automatically when
Claude reads a `.lean` file. CI and workflow rules live in
`.claude/rules/ci-and-workflow.md`.

## Tooling

The entries below distinguish **phase-default skills** (loaded
on demand) from **always-loaded layers** (`CLAUDE.md` and
`.claude/rules/*.md` without `paths:` frontmatter, present from
session start).

- VCS: `jj` v0.41+ in colocated mode at the parent `geb/` root;
  lease-protected pushes; `.jj/` is git-ignored automatically by
  jj. Never run `git clean -xdf` (deletes `.jj/`).
- Build: `lake build`, `lake test`. Never `lake clean`, never
  `lake env lean`.
- CI: `lean_action_ci.yml`, `markdown-lint.yml` at the parent
  level; `update.yml`, `create-release.yml` inert under
  `geb-lean/.github/workflows/`.
- Linters: `markdownlint-cli2`, `lake lint`,
  `scripts/check-axioms.sh`.
- Skills: `superpowers:*`, `lean4:*`, `claude-md-management:*`,
  `code-review:*`, `pr-review-toolkit:*`, `commit-commands:*`,
  `security-review`, plus `dispatching-parallel-agents`,
  `systematic-debugging`, `test-driven-development`, `remember`,
  `session-report`, `fewer-permission-prompts`.
- MCP servers (attached at the session level):
  - `arxiv-mcp-server`
    (<https://github.com/blazickjp/arxiv-mcp-server>) — arXiv
    paper search, download, and reading.
  - `memory`
    (<https://github.com/modelcontextprotocol/servers/tree/main/src/memory>)
    — graph-shaped scratchpad persisted across restarts.
  - `MCP Solver` (<https://github.com/szeider/mcp-solver>) —
    constraint and SAT solving for combinatorial side-conditions.

## When to consider a project-specific skill

Default to waiting. If a friction pattern recurs across many
sessions and is not covered by any built-in skill, consider
authoring one under `~/.claude/skills/` or as a plugin component
(see `skill-creator:skill-creator`). One-off tasks do not
warrant new skills.

## Pointers

| Path | Content |
| --- | --- |
| `docs/process.md` | Process and conventions, with rationale |
| `.claude/rules/` | Area-scoped rules |
| `docs/index.md` | Workstream-by-workstream narrative |
| `docs/lean-resources.md` | mathlib and CSLib link list |
| `docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md` | Refactor spec |
| `plans/2026-05-09-process-bootstrap-monorepo-plan.md` | Refactor plan |
