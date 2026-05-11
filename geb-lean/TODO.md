# TODO

Active workstreams in this repository. Hierarchical,
topological: parents listed first, children indented under
them. A workstream is removed from this file when its work
is complete or when it moves into the "to be done in
geb-mathlib" section. Completed content's documentation
lands in `docs/index.md`.

## Active in geb-lean

### 2026-05-09 process-bootstrap monorepo refactor

- **Status**: executing
- **Spec**:
  `docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md`
- **Plan**: `plans/2026-05-09-process-bootstrap-monorepo-plan.md`
- **Scope**: Stand up the monorepo-aware process scaffolding
  (CLAUDE.md split, `.claude/rules/`, `docs/process.md`,
  `docs/index.md`, this `TODO.md`, hooks, jj layout) under
  Milestone A; perform `.session/` triage and removal under
  Milestone B.
- **Next**: Continue Milestone A task execution per the plan.
- **Note**: Status advances to `awaiting-Milestone-B-completion`
  once Milestone A is signed off (Task A34); the entry is
  removed from `TODO.md` once Milestone B concludes.

## To be done in geb-mathlib (not pending here)

Items intentionally deferred until after migration to the
new repository, where the curated context there applies.
**None of the items in this section are pending in the
present repository.** Listed here so the work is not lost.

- **cat-depcategorydata-reflective**: complete the reflective
  inclusion `Cat ↪ DepCategoryData` by reflecting the
  `Exists`, `CategoryLaws`, and `Unique` properties along the
  stacked subcategory chain `DepCategoryData ⊃ DepCompleteObj
  ⊃ DepCompleteCL ⊃ DepCompleteUCL ⊃ DepCategoryCat`.
