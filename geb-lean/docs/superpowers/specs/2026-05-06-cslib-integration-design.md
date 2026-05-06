# CSLib Integration — Design Spec

Date: 2026-05-06.
Topic: add the Lean Computer Science Library (CSLib, `leanprover/cslib`)
as a dependency of the GebLean project, parallel to mathlib.

## 1. Motivation

CSLib is a developing standard library for computer science in Lean 4
(<https://www.cslib.io/>, whitepaper <https://arxiv.org/abs/2602.04846>).
Its declared scope covers computational models, λ-calculus, automata,
register machines, programming-language semantics, algorithms and
data structures, and a verification framework (Boole). The GebLean
project is itself a programming-language and computability formalization
effort, so CSLib is at least as relevant to it as mathlib is, and is
on a trajectory to become a community standard.

The integration target is mechanical: make CSLib available, document
how to discover and use it, and verify the dependency resolves and
compiles. Migration of existing GebLean constructions to CSLib
equivalents is explicitly out of scope; that is a per-workstream
judgement to be made later.

## 2. Scope

### 2.1 In scope

- Add `cslib` as a `[[require]]` in `lakefile.toml`, pinned to a tag
  whose toolchain matches ours.
- Run `lake update cslib` to materialize the manifest entry, commit
  the updated `lake-manifest.json`.
- Verify that `lake build` and `lake test` continue to succeed
  with the new dependency present.
- Verify that a minimal smoke test using CSLib's URM module
  (`Cslib.Computability.URM.Defs`) compiles in our project. The
  smoke test is for verification only and is removed before
  committing.
- Update `CLAUDE.md`:
  - Direct future search-before-introducing-redundancy guidance to
    cover CSLib in addition to mathlib.
  - Add a CSLib resources section listing the docs site, the
    library's directory layout, and pointers to the subdirectories
    most relevant to active GebLean workstreams.
  - Update the Project Notes external-deps line to mention cslib.
  - Note constructive-discipline interaction with CSLib (same as for
    mathlib).
- Save a reference memory recording the chosen pin and the docs URL.
- Land the change via a feature branch (`cslib-integration`), in a
  worktree, then merge to `main` after manual review.

### 2.2 Out of scope

- Migrating any existing GebLean code (URM simulation in Tourlakis
  Appendix A proofs, primitive recursion infrastructure, etc.) to
  CSLib equivalents.
- Adding any code in `GebLean/` that uses CSLib.
- Editing `GebLean.lean` (no new public module is added by this
  integration).
- Bumping our toolchain to v4.30.0 to track CSLib's `main`. (A
  separate workstream for the v4.30 upgrade is already in flight.)
- Writing typeclass instances, wrappers, or bridges between GebLean
  and CSLib types.
- Updating any individual workstream's plans to use CSLib.

## 3. Compatibility surface

CSLib release tags follow Lean toolchain RCs one-for-one. Our
project's `lean-toolchain` is `leanprover/lean4:v4.29.0-rc6`. CSLib's
matching tag is `v4.29.0-rc6` (toolchain identical).

CSLib's `main` is on `v4.30.0-rc2` and is incompatible with our
toolchain. Tracking `main` therefore requires a toolchain bump.

| Aspect          | GebLean        | CSLib `main`   | CSLib `v4.29.0-rc6` |
| --------------- | -------------- | -------------- | ------------------- |
| Lean toolchain  | `v4.29.0-rc6`  | `v4.30.0-rc2`  | `v4.29.0-rc6`       |
| mathlib `Rev`   | `master`       | `master`       | `master`            |
| mathlib commit  | `815dd043…`    | `6cf3ab1c…`    | `5c8398df…`         |

`main` is incompatible with our toolchain; `v4.29.0-rc6` matches.

**Decision (P1).** Pin CSLib to tag `v4.29.0-rc6` (not `main`). Each
CSLib `v4.29.0-rc*` and `v4.29.0` tag has its `lean-toolchain` set to
the corresponding Lean RC, so `v4.29.0-rc6` is the only available CSLib
tag whose toolchain matches ours; later v4.29 tags (`-rc7`, `-rc8`,
release) require their own newer toolchains. Bump the pin deliberately
when the GebLean toolchain upgrade lands.

**Decision (P2).** Defer mathlib reconciliation to the actual build
attempt. Both CSLib and GebLean use `inputRev = "master"` for mathlib;
Lake resolves mathlib once for the whole dependency graph using
whatever rev sits in our `lake-manifest.json`. §10 documents a
concrete recovery ladder if our rev does not satisfy CSLib
v4.29.0-rc6.

## 4. Lakefile change

The CSLib README documents the standard `lake update`-based workflow
for downstream projects. Concretely, add to `lakefile.toml` adjacent
to the existing mathlib require:

```toml
[[require]]
name = "cslib"
scope = "leanprover"
rev = "v4.29.0-rc6"
```

The Reservoir form (`scope = "leanprover"`) matches the pattern of the
existing mathlib require (`scope = "leanprover-community"`). Unlike
mathlib, this require pins an explicit `rev`; the implementer must
not "clean up" by removing it. If Reservoir resolution fails,
substitute the equivalent git form
`git = "https://github.com/leanprover/cslib", rev = "v4.29.0-rc6"`.

After the edit, run `lake update cslib` to populate `lake-manifest.json`.
Commit both `lakefile.toml` and `lake-manifest.json`.

CSLib's own `lakefile.toml` carries linter overrides
(`weak.linter.flexible = true`, `weak.linter.pythonStyle = false`,
etc.). Lake applies `weak.*` options to the package they are declared
in; these do not propagate downstream. The implementer should
nevertheless verify after the first downstream build that no
unexpected linter behaviour surfaces in our compilation.

## 5. Verification (smoke test)

A throwaway Lean file, written into the worktree but **deleted before
commit**, performs the smoke test. Module paths and namespace
identifiers below are verified against `Cslib` at tag `v4.29.0-rc6`:
the namespace declared in `Cslib/Computability/URM/Defs.lean` is
`Cslib.URM`. Smoke test content:

```lean
-- This file is a CSLib integration smoke test. It is intentionally
-- not committed; it exists only to confirm that CSLib types and
-- definitions resolve and elaborate against our project's lakefile,
-- and that elementary URM behaviour evaluates as expected.
import Cslib.Computability.URM.Defs
import Cslib.Foundations.Data.HasFresh

open Cslib

#check (URM.Instr : Type)
#check (URM.Regs : Type)

-- Behavioural check: read register 5 of the all-zero state.
example : URM.Regs.read URM.Regs.zero 5 = 0 := by
  simp [URM.Regs.read, URM.Regs.zero]

-- Behavioural check: write 7 to register 0, then read it back.
example : URM.Regs.read (URM.Regs.write URM.Regs.zero 0 7) 0 = 7 := by
  simp [URM.Regs.read, URM.Regs.write, Function.update]

-- A second module from a different top-level subdirectory, to ensure
-- multi-area imports resolve. `HasFresh` is a typeclass.
#check @HasFresh
```

The two `example` proofs verify that CSLib URM definitions actually
evaluate via `simp` (not just typecheck against `sorry`). `simp` is
preferred over `#guard` because `URM.Regs.write` is `Function.update`,
which uses `Decidable` `if`/`then`/`else`; per the project memory note
on Gödel-numbering interp not being safe for `#guard`, `#guard`-style
kernel reduction can hang on such combinators. If the `simp` proofs
fail, an alternative is `:= by decide` or `:= rfl`; that substitution
is a verification finding, not a spec change.

The `HasFresh` check exercises a `Foundations/Data` import in addition
to `Computability/URM`, covering two top-level CSLib subdirectories.
`HasFresh` is a `class … where`, so its type is `Type u → Type u`;
`@HasFresh` prints the universe-polymorphic signature without
committing to a concrete instantiation.

CSLib uses Lean's experimental module system (`module` / `public
import` headers in CSLib files); our project files do not. Importing
a module-system file from a non-module file is supported in Lean
v4.29, but if the smoke-file import surfaces a module-system
diagnostic, that is a verification finding — adjust the smoke file
to start with `module` (or migrate to a `public import` form) and
document the substitution.

The verification gate is:

1. `lake build` succeeds with the new dependency.
2. `lake test` succeeds with the same number of tests run as on the
   pre-integration baseline.
3. The smoke file compiles, the `#check`s elaborate, and the
   `example` proofs close (no errors, no "unsolved goals").
4. After deleting the smoke file, `lake build` and `git status` are
   clean.

If step 1 or 2 fails, the recovery ladder in §10 is invoked. If the
ladder does not resolve the failure, the failure is surfaced to the
user (the "abort and surface" trigger).

## 6. CLAUDE.md edits

Three edits, scoped to the existing structure of `CLAUDE.md`.

### 6.1 Project Notes external-deps line

Replace the line

> External deps: mathlib and related tools are pinned in
> `lake-manifest.json`; see `lean-toolchain` for the toolchain.

with

> External deps: mathlib, CSLib, and related tools are pinned in
> `lake-manifest.json`; see `lean-toolchain` for the toolchain. CSLib
> tracks Lean toolchain RCs via tagged releases; bump the CSLib pin
> deliberately when the GebLean toolchain bumps.

### 6.2 Search guidance

The current "Lean 4 Library and Categorical Theory Resources" section
opens with Loogle/Reservoir under "Searchable" and frames the project
guidance as "search mathlib first." Extend that guidance to cover
CSLib in parallel:

- The remote-index search tools (Loogle, `lean_leansearch`,
  `lean_leanfinder`, `lean_state_search`, `lean_hammer_premise`) index
  mathlib + Lean core + batteries; **none currently index CSLib**. For
  CSLib content, use the CSLib API docs site
  (<https://api.cslib.io/docs/>) or grep the CSLib source under
  `.lake/packages/cslib/Cslib/`.
- When introducing a new computational construct (register machine,
  Turing machine, automaton, λ-calculus variant, programming-language
  semantics, etc.), search CSLib first, just as we search mathlib for
  general mathematical concepts.

### 6.3 CSLib resources section

Add a new top-level subsection alongside the existing mathlib
subsections. The directory layout below is verified against the
repository tree at tag `v4.29.0-rc6` (CSLib's `ORGANISATION.md`
itself notes its content is aspirational, so the live tree is the
ground truth and the layout may shift across tags):

```markdown
### CSLib

- [Homepage](https://www.cslib.io/) and
  [whitepaper (arXiv:2602.04846)](https://arxiv.org/abs/2602.04846)
- [API docs](https://api.cslib.io/docs/)
- [Repository](https://github.com/leanprover/cslib)
- Top-level directory layout under `Cslib/` (snapshot at
  `v4.29.0-rc6`; verify against the pinned tag when bumping):
  - `Algorithms/` — algorithm/data-structure formalizations.
  - `Computability/` — `Automata/`, `Languages/`, `Machines/`,
    `URM/` (Unlimited Register Machine; namespace `Cslib.URM`).
  - `Foundations/` — `Combinatorics/`, `Control/`, `Data/`,
    `Lint/`, `Logic/`, `Semantics/` (including `LTS/` and
    `FLTS/`), `Syntax/`.
  - `Languages/` — `Boole/`, `CCS/`, `CombinatoryLogic/`,
    `LambdaCalculus/`.
  - `Logics/` — `HML/`, `LinearLogic/`. (Plural directory name.)
- Constructive discipline: importing CSLib is fine in the same
  sense that importing mathlib is fine, but the project rule that
  bans `Classical`, `noncomputable`, and `axiom` applies to any
  *transitive* axiom dependency too: a GebLean term that depends on
  a CSLib (or mathlib) lemma using `Classical.choice` will surface
  that axiom under `#print axioms`. For results that must remain
  constructive, run `#print axioms` and refactor if a non-pure
  axiom appears. Cross-reference:
  `feedback_mathlib_choice_in_functor_cat.md`.
- Reuse discipline: prefer CSLib typeclasses and abstract
  structures (e.g. `LTS`, `HasFresh`) over reaching into concrete
  instances, so internal CSLib changes do not break our code.
```

(Whitespace/heading nesting matches the surrounding section; the
placement is "alongside other Lean 4 reference sections", not nested
below the mathlib list.)

## 7. Memory updates

A single new reference memory recording the durable integration facts:

- File: `reference_cslib.md`
- Type: `reference`
- Contents:
  - CSLib pin: `v4.29.0-rc6` (matching our toolchain;
    `v4.29.0-rc6` is the only `v4.29.0-*` tag whose `lean-toolchain`
    matches ours).
  - Docs URL: <https://api.cslib.io/docs/>.
  - Repository: <https://github.com/leanprover/cslib>.
  - Directory layout summary (`Algorithms/`, `Computability/`,
    `Foundations/`, `Languages/`, `Logics/`) with the verified
    sub-tree at `v4.29.0-rc6`.
  - Search guidance: remote-index search tools (Loogle / leansearch /
    leanfinder / state_search / hammer_premise) do not index CSLib;
    use the docs site or grep `.lake/packages/cslib/Cslib/`.
  - Bump note: CSLib release tags follow Lean toolchain RCs
    one-for-one; bump deliberately when our toolchain bumps.

`MEMORY.md` gets a new section `## CSLib` with one entry:

```markdown
## CSLib

- [CSLib pin and search guidance](reference_cslib.md) — pin
  `v4.29.0-rc6`, docs at <https://api.cslib.io/docs/>.
```

No other memory changes.

## 8. Branch / worktree / merge sequence

1. Create a worktree (via `EnterWorktree`) with branch
   `cslib-integration` based on `main`. Create
   `.session/workstreams/cslib-integration.md` with the brief and
   the active task list.
2. In the worktree, run `lake exe cache get` (per CLAUDE.md, before
   first build in any fresh worktree). This downloads mathlib
   `.olean`s; CSLib has no equivalent cache server, so CSLib will
   compile from source on its first build.
3. Run `lake build` and `lake test` once **without** the CSLib
   require, to establish a clean baseline (and to record the
   pre-integration `lake test` test-count for the §5 verification
   gate).
4. Apply the `lakefile.toml` edit (add the CSLib `[[require]]`).
5. Run `lake update cslib` to populate the manifest. Inspect the
   diff to `lake-manifest.json`: the *added* entry must be `cslib`.
   If the resolver also moves `mathlib` (or its transitive deps:
   `batteries`, `aesop`, `Qq`, `proofwidgets`, `plausible`), confirm
   the move is the resolver's choice for compatibility with cslib's
   master pin and proceed; if any *unrelated* package moves, treat
   as a yellow flag (see §10.2). If `mathlib` did move, re-run
   `lake exe cache get` before the next build to repopulate the
   mathlib `.olean` cache.
6. Run `lake build`, then `lake test`. If failures, follow the §10.1
   recovery ladder; if still failing, surface to the user.
7. Write the smoke test file (per §5). Run `lake build`. Confirm
   no errors and no "unsolved goals". Delete the smoke file.
   Confirm `git status` is clean.
8. Apply the `CLAUDE.md` edits (per §6). Run `markdownlint-cli2`
   on `README.md CLAUDE.md .github/copilot-instructions.md
   docs/superpowers/specs/2026-05-06-cslib-integration-design.md
   docs/superpowers/plans/2026-05-06-cslib-integration.md`
   (the project's standing convention plus the spec and plan files
   for this integration).
9. Create the new memory file `reference_cslib.md` (per §7), update
   `MEMORY.md`. Run `markdownlint-cli2` on both memory files.
10. Commit on `cslib-integration`, listing files explicitly (not
    `git add -A`): `lakefile.toml`, `lake-manifest.json`,
    `CLAUDE.md`. Memory files (`reference_cslib.md`,
    `MEMORY.md`) live outside the repo and are saved with their own
    write step. Push the branch with
    `git push -u origin cslib-integration` (the `-u` is required on
    first push to set the upstream).
11. Surface to the user for manual review.
12. After approval, integrate `cslib-integration` into `main`:
    fast-forward where `main` has not advanced; otherwise rebase
    `cslib-integration` onto current `main`, re-run `lake build` and
    `lake test`, and only then merge. Delete the branch with
    `git branch -d cslib-integration` (lowercase `-d`; if it
    refuses, surface the failure rather than escalating to `-D`),
    exit and remove the worktree, and remove
    `.session/workstreams/cslib-integration.md` (CSLib is now a
    standing dependency, not an active workstream).

## 9. Verification gate (final)

Before declaring the integration done:

- `lake build` clean (no warnings, no `sorry`, no `admit`).
- `lake test` clean and the test count matches the pre-integration
  baseline recorded in §8 step 3.
- `markdownlint-cli2` clean on the project markdown set (`README.md`,
  `CLAUDE.md`, `.github/copilot-instructions.md`,
  `docs/superpowers/specs/2026-05-06-cslib-integration-design.md`,
  `docs/superpowers/plans/2026-05-06-cslib-integration.md`) and on
  the new memory file (`reference_cslib.md`) and `MEMORY.md`.
- `git status` clean (no leftover smoke files).
- The new memory file and `MEMORY.md` entry exist and are
  consistent.
- One commit on the feature branch covering the lakefile +
  `CLAUDE.md` changes (single logical change). Memory files,
  living outside the repo, are saved separately.
- The CSLib docs URL (<https://api.cslib.io/docs/>) returns HTTP
  200 (a one-time HEAD check, sanity).

## 10. Risks, recovery ladder, and mitigations

### 10.1 Build-failure recovery ladder

Triggered by §8 step 6 (`lake build` after `lake update cslib`):

1. Inspect the failure. If the error is in *our* code (e.g. a hint
   that something we wrote broke independently), fix that first;
   the rest of the ladder assumes the failure originates inside the
   CSLib import chain.
2. If the error is a mathlib API mismatch surfaced by CSLib, run
   `lake update mathlib` (forward bump). This may also cascade
   updates to `batteries`, `aesop`, `Qq`, `proofwidgets`, `plausible`
   in `lake-manifest.json`. Inspect the diff.
3. Run `lake build` again.
4. If step 3 succeeds but our own code now fails, the mathlib bump
   broke us. Revert with `git checkout -- lake-manifest.json`,
   re-`lake update cslib`, and surface the conflict to the user
   (this is the "abort and surface" trigger; do not pin mathlib
   *backward* to CSLib's tested rev unilaterally).
5. If step 3 still fails inside CSLib, surface to the user.

### 10.2 Other risks

- **`lake update cslib` cascades manifest entries beyond cslib**
  (likelihood: medium). Lake's resolver may touch transitive
  dependencies. If only `cslib` is added, proceed; otherwise treat
  unexpected manifest churn as a yellow flag and inspect the diff
  before continuing.
- **Smoke-test namespace path differs from this spec**
  (likelihood: low; verified at the pinned tag, but still worth a
  check). Adjust the smoke test to whatever the elaborated module
  exports; namespace adjustments are a verification finding, not a
  spec change.
- **First CSLib build is slow (no cache)** (likelihood: medium).
  Acceptable; CSLib v0.1.0 is small relative to mathlib. Time-box
  and proceed.
- **`CLAUDE.md` edits misdirect future search** (likelihood: low).
  Keep edits additive (CSLib in addition to mathlib); do not remove
  existing mathlib guidance.
- **Smoke file accidentally committed** (likelihood: low). The
  plan's commit step lists files explicitly (no `git add -A`), and
  the §9 verification gate checks for a clean tree.
- **CSLib `weak.linter.*` propagation** (likelihood: low).
  Documented in §4; verify after the first downstream build that no
  unexpected linter behaviour surfaces.

## 11. Success criteria

- `import Cslib.Computability.URM.Defs` resolves cleanly in any
  GebLean module after the merge.
- A future workstream owner reading `CLAUDE.md` is told to search
  CSLib alongside mathlib before introducing a new CS construct.
- The CSLib pin is recorded in `lake-manifest.json`, the docs URL is
  available in memory, and the bump procedure is documented.
