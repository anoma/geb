# geb-lean

`geb-lean` is a subproject of the `geb/` monorepo. It hosts the
Lean 4 formalisation of the categorical structures underlying
the Geb programming language. For the broader project — including
the Common Lisp reference implementation, the original Idris and
Agda artefacts, and the user-facing manual — see
[`../README.md`](../README.md). The licence under which both the
parent project and this subproject are distributed is recorded
at [`../LICENSE`](../LICENSE).

## Status

Active experimentation; process refactor of 2026-05-09 in
effect. The conventions, directory layout, and contribution
flow described below reflect that refactor and supersede earlier
arrangements. The Lean library itself continues to grow as the
formalisation programme advances.

## Dependencies

The Lean toolchain is pinned in [`lean-toolchain`](lean-toolchain).
External library pins are recorded in
[`lake-manifest.json`](lake-manifest.json) and declared in
[`lakefile.toml`](lakefile.toml). The two upstream libraries on
which this project depends are mathlib4 and CSLib; both are
required for the project to build and test.

## Licence

Distributed under the GNU General Public License version 3. The
licence text is in [`../LICENSE`](../LICENSE) at the parent
monorepo root. The same licence covers all files in this
subdirectory unless an individual file declares otherwise.

## Index of project documentation

The documentation tree under [`docs/`](docs) is organised so
that this README is a thin index over it. The entry points are:

- [`docs/index.md`](docs/index.md) — topological index of
  formalised workstreams: paths, mathematical content,
  dependencies among workstreams, and pointers into
  `docs/research/` and `docs/superpowers/specs/`.
- [`docs/process.md`](docs/process.md) — rationale for the
  conventions in `CLAUDE.md` and `.claude/rules/`, with
  cross-references to the spec that introduced them.
- [`docs/lean-resources.md`](docs/lean-resources.md) — curated
  pointers into mathlib4, CSLib, and external Lean material on
  the mathematical theories formalised here.
- [`docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md`](docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md)
  — design spec for the 2026-05-09 process refactor.
- [`docs/superpowers/plans/2026-05-09-process-bootstrap-monorepo-plan.md`](docs/superpowers/plans/2026-05-09-process-bootstrap-monorepo-plan.md)
  — the task-level plan executing that spec.
- [`TODO.md`](TODO.md) — short-horizon list of pending work
  outside the scope of any active spec/plan.

Workstream-specific specs live under
[`docs/superpowers/specs/`](docs/superpowers/specs); their
plans live under
[`docs/superpowers/plans/`](docs/superpowers/plans). The
topological index links to each active workstream by name.

## Index of project processes

The process and rule files live at the top of this directory and
under `.claude/rules/`. Their roles:

- [`CLAUDE.md`](CLAUDE.md) — repository-wide instructions for
  AI assistants and human contributors. Always loaded.
- [`.claude/rules/lean-coding.md`](.claude/rules/lean-coding.md)
  — Lean disciplines (hole marking, constructive-only,
  literature citation, bottom-up named composites,
  non-negotiable interfaces) together with source-editing
  conventions (build discipline, comment and docstring rules,
  Lean idioms, `lean4` skill mapping, universe and variable
  hygiene, no copyright headers). Always loaded.
- [`.claude/rules/markdown-writing.md`](.claude/rules/markdown-writing.md)
  — register, line length, and formatting conventions for
  every committed Markdown file.
- [`.claude/rules/ci-and-workflow.md`](.claude/rules/ci-and-workflow.md)
  — conventions for CI and workflow files governing the
  geb-lean subdirectory.

## Contribution pointers

The development flow used in this subproject:

1. Clone the fork at <https://github.com/rokopt/geb>
   (single-developer entry path) or the canonical
   repository at <https://github.com/anoma/geb>
   (external-contributor entry path); `geb-lean/` is a
   subdirectory in either case. The flow recorded in
   [`.claude/rules/fork-upstream-flow.md`](.claude/rules/fork-upstream-flow.md)
   assumes the fork.
2. Read [`CLAUDE.md`](CLAUDE.md) for the repository-wide
   instructions, then the rule files under `.claude/rules/`
   relevant to the area being touched.
3. Brainstorm a workstream and write a spec under
   `docs/superpowers/specs/<date>-<topic>.md`, then a plan
   under `docs/superpowers/plans/<date>-<topic>-plan.md`.
   Both are tracked with adversarial review cycles.
4. Implement the plan on a topic branch named
   `feat/<topic>`, `fix/<topic>`, or `chore/<topic>`. Use jj
   as the primary VCS; the colocated git repository is the
   integration channel for GitHub.
5. Run `lake build` and `lake test` after every edit; fix the
   first error first.
6. Open a pull request against `main`. Commits use the
   mathlib commit-message form: a short imperative subject
   line of the form `kind(scope): summary`, optional body,
   no trailing punctuation in the subject.

The reasoning behind these conventions is in
[`docs/process.md`](docs/process.md); the mechanical rules are
in `CLAUDE.md` and `.claude/rules/`.

## Pointers to upstream and sibling projects

This subproject is the active development home for the Lean
formalisation of Geb. Two pointers to related repositories:

- The canonical repository for this monorepo is
  `anoma/geb`. The local working copy is a clone of the
  fork at `rokopt/geb`. Daily work pushes to the fork;
  upstream receives commits only through merged pull
  requests opened from the fork. The flow's invariants,
  operations, and mechanical enforcement are recorded in
  [`.claude/rules/fork-upstream-flow.md`](.claude/rules/fork-upstream-flow.md);
  the design spec is at
  [`docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md`](docs/superpowers/specs/2026-05-12-fork-upstream-flow-design.md).
- `geb-mathlib` is the eventual upstream destination for
  results developed here. Material formalised in `geb-lean`
  that reaches a stable, peer-reviewable form is intended for
  migration into `geb-mathlib`, where it joins the broader
  mathlib ecosystem under mathlib's contribution process. The
  literature-citation discipline recorded in
  [`CLAUDE.md`](CLAUDE.md) supports that migration: every
  transcribed function, definition, and theorem carries a
  citation to its source that survives the move.
- The library dependencies — mathlib4 at
  <https://github.com/leanprover-community/mathlib4> and
  CSLib at <https://github.com/leanprover/cslib> — supply the
  ambient mathematical infrastructure on which the
  formalisation rests. Pinned versions are recorded in
  `lake-manifest.json`; bumps are made deliberately and in
  step with `lean-toolchain`.
