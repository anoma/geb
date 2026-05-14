# Lean coding rules

This file is unconditionally loaded for the GebLean project. It
combines the project-shaping Lean disciplines that govern every
phase of work with the file-editing conventions that apply when
reading or modifying `.lean` source.

## Hole-marking discipline

Use `_` for unsolved goals: this surfaces the goal type as a build
error, which is what we want while a definition or proof is under
construction. The Lean keyword `sorry` is permitted as a transient
working tool only — committed code must build under
warnings-as-errors and therefore cannot contain `sorry`. The Lean
keyword `admit` is forbidden everywhere, always.

The warnings-as-errors mechanism is
`moreLeanArgs = ["-DwarningAsError=true"]` in `lakefile.toml`,
which promotes `declaration uses 'sorry'` (and every other
warning-class diagnostic) into a build error at the Lean kernel
level.

## Constructive-only Lean code

No `noncomputable`. No `axiom`. Minimise `Classical` usage. Use
the `Quotient` / `Quot` constructive API only; `Quot.out` and
`Quotient.out` (which require `Classical.choice`) are avoided.
The mechanical check for axiom dependencies is
`scripts/check-axioms.sh`.

## Build discipline

- Run `lake build` and `lake test` after every edit; fix the first
  error first, then rebuild.
- Never run `lake env lean` (it does not pick up project options
  from `lakefile.toml` and produces spurious diagnostics).
- Never run `lake clean` (it would force a full mathlib rebuild).
- In a freshly created git worktree, run `lake exe cache get`
  before the first `lake build` to populate the mathlib `.olean`
  cache.
- Write modules one definition at a time; build, then move on.
- Work both forwards (from available hypotheses) and backwards
  (from the goal); take one proof step at a time and re-check
  with an underscore goal hole.
- Use the `Write` tool, never shell heredocs, for experimental
  code. Place experiments inside the codebase (optionally in
  temporary files) rather than under `/tmp`.

## Comment and docstring rules

- A module docstring `/-! ... -/` is mandatory immediately after
  the imports of every file.
- A declaration docstring `/-- ... -/` is mandatory for every
  `def`, `structure`, `class`, `instance`, and major theorem.
- Markdown and LaTeX (`$...$`, `$$...$$`) are permitted inside
  docstrings.
- Do not record development history, prior states, or post-hoc
  axiom-free remarks in comments or docstrings.
- This project is stricter than mathlib on `instance` docstrings:
  mathlib's contribution guide
  (<https://leanprover-community.github.io/contribute/doc.html>)
  treats `instance` docstrings as encouraged; this project
  requires them, on the rationale that searchable docstrings on
  every typeclass instance pay off in navigability of a heavily
  category-theoretic codebase.

## Literature-citation discipline

In transcription workstreams (for example the ER ↔ K^sim_2
equivalence, which transcribes Tourlakis 2018 / Wagner-Wong /
Grzegorczyk-hierarchy literature), every planned function,
definition, or theorem in a plan document carries a reference to
the literature proposition or in-codebase lemma it corresponds
to; every implemented function, definition, or theorem includes
the literature reference in its docstring.

Citations are specific (for example "Tourlakis 2018 §0.1.0.27
(3)") and reference the project's research documents in
`docs/research/` for the cross-reference network.

## Lean idioms

- Add `@[ext]` to structure definitions whenever it compiles, to
  generate extensionality lemmas.
- Derive standard instances such as `Inhabited`, `DecidableEq`,
  and `Repr` where applicable.
- `extends` is composition, not classical OO inheritance; see
  *Functional Programming in Lean: Structures and Inheritance*.
- For object equalities in categories, use `eqToHom` and
  `eqToIso` with explicit transport functions (cf. mathlib's
  `Mathlib/CategoryTheory/EqToHom`).
- Sigma-of-dependent-fields pattern: split a structure with
  later fields depending on earlier ones into an independent
  base, a dependent fibre, and a sigma combining them via
  `extends` when that compiles.
- Typeclass-via-interface-structure pattern: define a structure
  with the interface fields, define the typeclass as a
  single-field wrapper around it, and provide both
  interface-structure and typeclass forms of every API
  function.
- Use `_root_` namespacing to disambiguate the mathlib
  `CategoryTheory.Functor` from `_root_.Functor`
  (`Control.Functor`) when the resolution shifts.
- When a proof gets long, factor out lemmas: pick an
  intermediate goal, prove the two halves separately, dispatch
  the original goal by transitivity. Recurse as needed.
- Reach for the `grind` tactic
  (<https://lean-lang.org/doc/reference/latest/The--grind--tactic/>)
  and `aesop` automation when applicable.
- Use `Plausible` (already a transitive dependency through
  mathlib) for property-based tests under `test/`.

## Bottom-up named-composite discipline for categorical equivalences

When building a new categorical structure that is to be proven
equivalent to an existing one, never add a constructor or
morphism to the new category before its image in the target
category has been built and named as a `def` (with a `@[simp]`
interp lemma).

Workflow:

1. Identify the image in the target category that the new
   construct will translate to.
2. If it is not already present, build it bottom-up as a
   composition of atomic constructors of the target category.
3. Give it a name and prove its interp lemma in `Utilities/`.
4. Only then add the corresponding constructor (or helper) to
   the new category, with its translation function pointing
   directly at the named composite.

If a proposed construct cannot be built ultimately out of
compositions of the target category's atomic generators, that is
a signal not to add it — not to build a workaround.

## Non-negotiable interfaces for pre-existing mathematical objects

The interface of a Lean category formalising a pre-existing
mathematical object (its objects, its primitive constructors,
its generators) is fixed by the external mathematical source and
is not a design choice open to the implementation.

Implementation design (proof strategies, auxiliary inductives,
choice of named composites) may change freely. Interface
changes are not a valid response to implementation difficulty.
If implementation gets stuck, the correct moves are:

1. Re-examine the implementation strategy.
2. Strengthen supporting infrastructure in `Utilities/`.
3. Surface the obstruction for discussion before continuing.

Weakening or redefining the interface so the implementation
becomes easier is not a valid move.

## `lean4` skill mapping

- Drafting from informal mathematics: `lean4:draft`,
  `lean4:formalize`, `lean4:autoformalize`.
- Proving a stated lemma: `lean4:prove`, `lean4:autoprove`.
- Polishing: `lean4:golf` — phase-default post-process for any
  new proof.
- Porting: `lean4:refactor` — phase-default during porting work.
- Pre-commit Lean review: `lean4:review` — phase-default for any
  Lean commit.
- Exploration and learning: `lean4:learn`.
- Diagnosis and cleanup: `lean4:doctor`.
- Save progress: `lean4:checkpoint`.

All `lean4` skills produce ordinary commits and are subject to
the same warnings-as-errors gate as any commit.
`lean4:checkpoint` cannot commit code that contains `sorry`.
"Phase-default" here refers to *when to invoke a skill at a
given phase*, not to whether the skill loads at session start.

## Universe and variable hygiene

- Keep universe levels as polymorphic as the file compiles
  with.
- After editing a file containing `universe` or `variable`
  declarations, prune any that the file no longer uses.

## No copyright or author headers in source files

- Source files do not carry copyright or author headers. This
  diverges intentionally from mathlib's per-file `Authors:`
  template.
- Licence coverage for the project lives at the repository-level
  `../LICENSE` file (GNU General Public License version 3, at
  the parent `geb/` root); per-file copyright headers are not
  required by GPLv3 for original GebLean code.
- Vendored upstream content (e.g. files copied verbatim from
  mathlib or `lean4-skills`, which carry Apache 2.0 notices —
  mathlib is Apache 2.0, a dependency of this GPLv3 project)
  preserves any per-file notices it carries, verbatim, per those
  upstream licences' requirements.
