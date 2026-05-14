# geb-lean

`geb-lean` is a subproject of the `geb/` monorepo, hosting a
Lean 4 + mathlib experimental formalisation of Geb — a
categorical programming language whose first-class notions
include "programming language" itself. The curated counterpart
`geb-mathlib` holds material meeting upstream contribution
standards. For the broader project — including the Common Lisp
reference implementation, the original Idris and Agda artefacts,
and the user-facing manual — see [`../README.md`](../README.md).

## Dependencies

- [mathlib4](https://github.com/leanprover-community/mathlib4).
- [cslib](https://github.com/leanprover/cslib).
- Lean 4 toolchain (see `lean-toolchain`).

See `lakefile.toml` for the full dependency declaration.

## Licence

[GNU General Public License version 3](../LICENSE), at the
parent monorepo root.

## Documentation

- [`docs/index.md`](docs/index.md) — topological narrative of
  implemented mathematical content.
- [`docs/process.md`](docs/process.md) — process rationale and
  decision history.
- [`docs/lean-resources.md`](docs/lean-resources.md) — Lean
  library and mathematical reference catalog.

## Process

The contributor-binding rules live in
[`CLAUDE.md`](CLAUDE.md). Path-scoped conditional rules live in
[`.claude/rules/`](.claude/rules/):

- `lean-coding.md` — applies to all `.lean` files.
- `markdown-writing.md` — applies to all `.md` files.
- `ci-and-workflow.md` — applies to `.github/workflows/` and
  `scripts/`.
- `fork-upstream-flow.md` — fork–upstream invariants, always
  loaded.

## Contributing

### Setup

Suggested steps to run after cloning the parent `geb/`
repository. The jj configuration below is recommended local
config; the project does not run config commands on a
contributor's behalf.

1. Install `jj` via your preferred package manager.
2. Initialise jj's colocated mode at the parent `geb/` root:
   `jj git init --colocate`.
3. Apply the recommended local jj configuration. See
   [`docs/process.md`](docs/process.md) § `jj` colocated mode
   for the full sequence, including the fetch-tags pattern for
   cutover-tag mirroring and the fork-specific remote setup.
4. Configure your per-developer `~/.config/jj/config.toml`
   `[signing]` block (`behavior = "own"`,
   `backend = "gpg"` or `"ssh"`, `key = "..."`) so commits are
   signed.
5. Install the Lean toolchain via `elan` (the toolchain version
   is read from `lean-toolchain`).
6. Run `lake exe cache get` then `lake build` to verify the
   build chain.
7. Install `doctoc` to enable pre-push TOC regeneration of
   committed Markdown:
   `npm install -g doctoc` (or your preferred install path).
   The pre-push checklist skips the TOC check when `doctoc` is
   missing rather than failing, so this step is recommended but
   not blocking.
8. Run `bash scripts/check-jj-setup.sh` to verify the
   configuration.

### Working

1. Read `CLAUDE.md` from top to bottom; the rules there bind every
   contribution.
2. Pick a workstream from `TODO.md` (or propose a new one and
   brainstorm a spec following the process described in
   `docs/process.md`).
3. Develop on a topic branch (`feat/<topic>`, `fix/<topic>`, etc.);
   use `jj` (the working VCS).
4. Run `scripts/pre-push.sh` and have a contributor (or yourself)
   review the diff line-by-line before pushing.

## Upstream destination: geb-mathlib

Material formalised in `geb-lean` that reaches a stable,
peer-reviewable form is intended for migration into
`geb-mathlib`, the curated counterpart repository, where it
joins the broader mathlib ecosystem under mathlib's contribution
process. The literature-citation discipline recorded in
[`CLAUDE.md`](CLAUDE.md) supports that migration: every
transcribed function, definition, and theorem carries a citation
to its source that survives the move.

## Fork–upstream relationship

The local working copy is a clone of the fork at
[`rokopt/geb`](https://github.com/rokopt/geb); the canonical
repository is [`anoma/geb`](https://github.com/anoma/geb).
Daily work pushes to the fork; upstream receives commits only
through merged pull requests opened from the fork. The flow's
invariants, operations, and mechanical enforcement are recorded
in
[`.claude/rules/fork-upstream-flow.md`](.claude/rules/fork-upstream-flow.md).
