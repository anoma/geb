---
paths:
  - "**/*.lean"
---

# Lean coding conventions

Applies whenever a `.lean` file is open or being edited.

## Authoritative upstream guides (mathlib)

These are the binding style references for new and modified
`.lean` content. Adversarial reviewers must check new and
modified `.lean` content for violations against each:

- Contributing index:
  `https://leanprover-community.github.io/contribute/index.html`
- Commit messages:
  `https://leanprover-community.github.io/contribute/commit.html`
- Coding style:
  `https://leanprover-community.github.io/contribute/style.html`
- Naming conventions:
  `https://leanprover-community.github.io/contribute/naming.html`
- Documentation conventions:
  `https://leanprover-community.github.io/contribute/doc.html`

Bullet-point highlights extracted from each guide appear below.
The full guides supersede this digest; re-fetch and re-verify
on every adversarial-review round (the guides are subject to
revision by the leanprover-community).

### Commit messages (from `commit.html`)

- Format: `<type>(<optional-scope>): <subject>` followed by an
  optional body and footers.
- Types: `feat | fix | doc | style | refactor | test | chore |
  perf | ci`.
- **Imperative present tense** in the subject and body
  ("change" — not "changed", not "changes", not "adds").
- **Do not capitalise** the first letter of the subject.
- **No trailing period** on the subject.
- Aim for the subject under ~72 characters.
- Body: same imperative present tense; include motivation and
  contrast with previous behaviour where useful.
- Documented footers include `Closes #N`, `BREAKING CHANGE: …`,
  and `- [ ] depends on: #N`. (`Moves:`/`Deletions:` are not
  documented and are NOT part of our convention.)

**Adversarial-reviewer instruction**: scan new commit messages
in the plan and on the active topic branch for indicative or
past-tense verbs ("Adds", "Carries", "Pins", "Creates", "Sets",
"Adopted"), capitalised first letters of subjects, trailing
periods, and out-of-list types; flag each occurrence.

### Coding style (see also mathlib's `style.html`)

- Indentation: 2 spaces; no tabs.
- Line length: 100 characters maximum (matches mathlib's
  `mathlibStandardSet` linter setting).
- One declaration per line; no semicolons separating
  declarations.
- Use Unicode notation where mathlib does (e.g., `∀`, `∃`, `→`,
  `↦`, `⟨ ⟩`, `≤`, `≥`, `≠`, `∈`, `⊆`).
- `pp.unicode.fun = true` is set project-wide in
  `lakefile.toml`.
- `autoImplicit = false` and `relaxedAutoImplicit = false` are
  set; declare every variable explicitly.
- Section / namespace structure: open and close namespaces
  explicitly; do not mix `namespace X` blocks with content
  outside them in the same file.
- Anonymous constructors `⟨ ... ⟩` and structure projections
  `.x` are preferred where unambiguous.

**Adversarial-reviewer instruction**: scan new and modified
`.lean` content for indentation drift, lines exceeding 100
characters, multi-declaration lines, ASCII forms where mathlib
uses Unicode, and namespace/section nesting violations.

### Naming conventions (see also mathlib's `naming.html`)

- `snake_case` for `Prop`-valued definitions
  (`theorem`, `lemma`).
- `lowerCamelCase` for `def`, `instance`, `example`,
  variables, anonymous constructors, and tactic names.
- `UpperCamelCase` for `structure`, `class`, `inductive`,
  type-class arguments, and Sort-valued constants.
- Compound names follow the pattern
  `<subject>_<verb>_<object>` or `<verb>_<subject>` for
  theorems (e.g., `add_comm`, `mul_assoc`,
  `Nat.succ_lt_succ`).
- Predicates use the suffix `_iff_…` to indicate "if and only
  if" relationships (`even_iff_two_dvd`).
- Do not include the namespace in the declaration body's
  identifiers; rely on `namespace` to scope.
- Discharging operator: `_left`, `_right`, `_self`, `_of_…`,
  `_iff_…` follow specific positional conventions; check the
  upstream guide for the full table before naming.
- Exception: `scripts/nolints.json` exempts the six bibliography
  citation-key definitions in `GebLeanDocs/Bibliography.lean`
  (`leivant3`, `leivant1`, `bellantoniCook`, `clote`, `ritchie`,
  `dalLagoMartiniZorzi`) from the `topNamespace` env_linter. They
  are bare top-level `def`s because Verso's `{citep}`/`{citet}`
  roles resolve a citation by its short global identifier, so
  namespacing them would require changing every citation site.

**Adversarial-reviewer instruction**: scan new and modified
`.lean` content for ALL_CAPS or `snake_case` identifiers (in
positions where another case applies), namespace prefixes
inside declarations, and non-standard operator suffixes; flag
each occurrence with a pointer to the upstream rule.

### Documentation (see also mathlib's `doc.html`)

- `/-! … -/` module docstring is mandatory after imports;
  required sections (in order): `# Title`, brief summary,
  `## Main definitions`, `## Main statements`,
  `## Notation` (if any), `## Implementation notes` (if any),
  `## References` (if any), and `## Tags`.
- `/-- … -/` declaration docstring is mandatory for every
  `def`, `structure`, `class`, `instance`, every field of a
  `structure`/`class`, and every theorem of public interest.
- Exception: Verso's `#doc` command emits, per document module, a
  `def` naming the canonical document object, with no doc comment
  attachable to it. These are exempted from `docBlame` through
  `scripts/nolints.json` rather than carrying a docstring.
- Markdown is supported in docstrings; LaTeX via `$…$` (inline)
  and `$$…$$` (display).
- Cross-references use `` `Foo.bar` `` for identifiers;
  doc-gen4 renders them as links.
- No development-history references in docstrings (e.g.,
  "previously did X"); history is for commit logs.

**Adversarial-reviewer instruction**: scan new and modified
`.lean` content for missing module/declaration docstrings,
missing required sections in module docstrings, history-
references inside docstrings, and post-hoc axiom-celebration.

## Comment and docstring rules

- `/-! ... -/` module docstring is mandatory after imports.
  Required sections (omit irrelevant ones rather than leave blank):
  title, summary, main definitions, main statements, notation (if
  any), implementation notes, references, tags.
- `/-- ... -/` declaration docstring is mandatory for every
  `def`, `structure`, `class`, `instance`, and major theorem; and
  for every field of a `structure` or `class`. Exception: Verso's
  generated document objects (see § Documentation) carry no
  docstring by construction.
- Markdown + LaTeX (`$...$`, `$$...$$`) inside docstrings.
- **No development-history references in docstrings**
  (e.g., "previously this used X; now uses Y"). Such notes belong
  in commit messages, not in docstrings, since docstrings are part
  of the public API and outlive their writing context.
- **Empty lines inside declarations are lint-discouraged**; use a
  brief comment (`-- ...`) as a structural separator if needed.

## Lean 4 module system

Every `.lean` file declares itself as a module using the `module`
keyword at the top of the file. Imports re-exported to
downstream users (typically the case for index/umbrella files
and for content needed by callers of this module) use
`public import`; imports whose contents are used only internally
use plain `import`.

Exception: the `GebLeanDocs` library and its `GebLeanDocsMain`
executable root carry no `module` keyword. Verso's `#doc` command
emits a plain, non-`public` `def`; under `module` that definition
would go unexported, so neither `%doc` nor a cross-module
`{include}` could reach it. Verso's own document modules carry no
`module` either.

## No copyright or author headers in source files

Source files do not carry copyright or author headers. This
diverges intentionally from mathlib's per-file `Authors:`
template. Licence coverage for the project lives at the
repository-level `LICENSE` file at the parent `geb/` root (GNU
General Public License version 3); per-file copyright headers
are not required by GPLv3 for original GebLean code. Vendored
upstream content (for example, files copied verbatim from
mathlib or `lean4-skills`, which carry Apache 2.0 notices —
mathlib is Apache 2.0, a dependency of this GPLv3 project)
preserves any per-file notices it carries, verbatim, per those
upstream licences' requirements.

## `lean4` sub-skill mapping

| Activity | Skill | Always-on? |
| --- | --- | --- |
| Drafting from informal math | `lean4:draft`, `lean4:formalize`, `lean4:autoformalize` | Try `autoformalize` early |
| Proving a stated lemma | `lean4:prove`, `lean4:autoprove` | Try `autoprove` when stuck |
| Filling stubborn `sorry`s | `lean4:sorry-filler-deep` | When fast pass fails or proofs are complex |
| Polishing a proof | `lean4:golf` | Yes, post-process |
| Refactoring existing Lean code | `lean4:refactor` | Yes, during refactors |
| Pre-commit Lean review | `lean4:review` | Yes, before any Lean commit |
| Exploring mathlib | `lean4:learn` | As needed |
| Diagnosis | `lean4:doctor` | As needed |
| Save progress | `lean4:checkpoint` | At milestones |

## Lake / build workflow

- Always use `lake build` and `lake test`. Avoid `lake clean`
  (it forces a full mathlib rebuild). Never use `lake env lean`
  (it fails to pick up options from `lakefile.toml` and produces
  spurious errors).
- Before any commit that touches a `.lean` file, run
  `bash scripts/pre-commit.sh`. The script runs `lake test`
  (which subsumes `lake build` against current lakefile targets)
  followed by `lake lint`, then `lake build GebLeanAxiomChecks`.
  Catching `lake lint` regressions at
  commit time rather than push time keeps the linter from
  silently accumulating debt between pushes.
- `scripts/pre-push.sh` is the full superset (`pre-commit.sh`'s
  Lean triad, plus `doctoc --check`, `markdownlint-cli2`,
  `lake build GebLeanAxiomChecks`,
  `scripts/tests/test-axiom-linter.sh`, and user-driven-gate
  reminders) and is mandatory before every push, regardless of
  which file types changed.
- In a fresh worktree, run `lake exe cache get` before the first
  `lake build` to pull mathlib's precompiled artifacts. Without
  this, lake falls back to building mathlib from source (hours of
  work).
- Avoid bash process substitution (`<(...)`, `>(...)`); these
  trigger manual approval prompts. Write intermediate output to a
  file under `/tmp` or in the working tree and read it back.
- Use the `Write` tool / direct file edits rather than shell
  commands for experimental code; place experiments inside the
  codebase, not under `/tmp`.

## Coding technique

### Constructive-only

No `noncomputable`. This is the operative constructive guarantee:
Lean forces `noncomputable` on any definition whose body uses
`Classical.choice`, so the project-wide ban (enforced by
`lake build` under `-DwarningAsError`) confines `Classical.choice`
to proofs and keeps every computational object executable.

`Classical.choice` is accepted in proofs. Mathlib is classical
from its foundations up — even the arithmetic primitives this
project builds on carry it (`Nat.unpair_left_le` /
`Nat.unpair_pair` underpinning Gödel numbering; `NatTrans.id` /
`Functor.comp` via `aesop_cat`; `Fin.lastCases_castSucc`) — so
forbidding it is unachievable while building on mathlib, and the
`noncomputable` ban already secures the only guarantee that
affects computation. Ground-up per-axiom vetting (including
`Classical.choice`) is the job of the public-facing `geb-mathlib`
port. See `CLAUDE.md` § Constructive-only Lean code.

Prefer the constructive `Quotient` / `Quot` API
(`mk` / `lift` / `ind` / `sound`); `Quotient.out` / `Quot.out`
are `noncomputable` and therefore banned anyway.

#### Axiom audit

`GebLeanMeta.detectNonstandardAxiom` (an `@[env_linter]` built on
`Lean.collectAxioms`) accepts `propext`, `Quot.sound`, and
`Classical.choice`; it rejects `sorryAx` and every other non-standard
axiom. It is invoked over `GebLean`, `GebLeanTests`, and the vendored
`Geb` tree by the `GebLeanAxiomChecks` library's
`#lint only detectNonstandardAxiom in <Pkg>` gates, so a forbidden
axiom fails `lake build GebLeanAxiomChecks`. The permitted set is
fixed in `GebLeanMeta.lean`; permitting any further non-standard axiom
means editing that set there (there is no per-declaration comment
escape hatch).

### Proof guidelines

- **First errors first.** When `lake build` reports multiple
  errors or warnings, fix the first one before later ones. Later
  errors may be caused by earlier ones, or fixes for them may
  depend on earlier fixes.
- **Underscores expose holes.** When you want to see the type of
  a goal you're working on, insert `_` (underscore). Building
  produces an "unsolved goals" error and prints the goal type.
- **`#check`** to inspect the type of an expression in-place.
- **One definition at a time.** When developing a new module,
  write one definition / function / theorem and get it completely
  working (no underscores, no `sorry`, clearly corresponding to
  its intended meaning) before moving to the next. Building a
  whole module at once produces compounding misconceptions.
- **Work both forwards and backwards.** Forward: how do the
  inputs / locals build toward the goal? Backward: what previous
  step would let us reach the goal? Often the easiest path is
  from both directions toward the middle.
- **One proof step at a time when stuck.** If a multi-step
  rewrite or compound tactic fails, decompose into single steps
  and re-check the goal at each. Recombine after each step works
  individually.
- **Factoring-out-lemmas technique.** When a proof gets stuck:
  identify a good intermediate goal — either a forward step you
  can prove, or a backward step that would let you reach the
  overall goal. Factor out two lemmas (current → intermediate,
  intermediate → overall) as `_` placeholders, dispatch the
  overall goal by transitivity to confirm they compose, then
  prove each lemma separately. Recurse if the lemmas themselves
  are still too large.
- **Stuck-and-ask template.** When unable to fill an underscore,
  making no progress, or not understanding what's wrong: pause
  and explain (1) what you're trying to accomplish, (2) what
  problems you're encountering, (3) what you've tried, (4) why
  you're stuck on a particular underscore. Don't silently abandon
  the task.

### Higher-order constructions

Be suspicious of piece-by-piece constructions. For example, when
constructing a functor, always seek a way to build it out of
compositions of existing functors and functorial operations on
functor categories rather than writing explicit object maps,
morphism maps, and functor-law proofs — higher-order operations
provide all of those at once. The same applies broadly: prefer
composition of established abstractions over hand-rolling. See
`docs/process.md` § Code is cost for the rationale.

### One step at a time

Definitions and proofs are written as small compositions, one
step at a time, so each intermediate step yields a reusable
component. See `docs/process.md` § Code is cost for the
rationale.

### Bottom-up named-composite discipline for categorical equivalences

When building a new categorical structure to be related by an
equivalence or functor to an existing one, no constructor is
added to the new category before its image in the target
category exists as a named `def` (with a `@[simp]` interpretation
lemma) built bottom-up from the target's atomic generators.
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

### Structure and typeclass patterns

- **`@[ext]` reflex.** Always add `@[ext]` to structure
  definitions (when it compiles) so extensionality lemmas
  auto-generate.
- **Standard derivations.** When defining a structure, derive
  `Inhabited` / `DecidableEq` / `Repr` where applicable.
- **`extends` is composition, not OO inheritance** — appropriate
  when a structure builds on another by adding fields. See
  [FP-in-Lean: Structures and Inheritance](https://leanprover.github.io/functional_programming_in_lean/functor-applicative-monad/inheritance.html).
- **Sigma-type pattern for dependent fields.** When a structure
  has later fields that depend on earlier ones, define an
  independent struct first, then a dependent struct, then
  combine via sigma type (preferably with `extends`). Allows
  operations on independent components separately.
- **Typeclass-instance pattern.** Define the interface as a
  structure with the typeclass's fields; define the typeclass
  with a single field containing an interface instance; functions
  taking / returning the typeclass have an interface-version that
  the typeclass-version wraps. Separates interface (mathematical
  object) from typeclass resolution (isolating resolution errors).
- **Factor out structure components into separate definitions.**
  Makes type signatures explicit.
- **Universe-polymorphic.** Make universe levels as polymorphic
  as compiles.
- **Check for unused `universe` / `variable` declarations** after
  editing files that introduce or modify them; remove unused
  ones.
- **Non-negotiable interfaces for formalising pre-existing objects**:
  When formalising a specific mathematical object, the
  interface (objects, primitive constructors, generators) is
  fixed by the external mathematical source. Implementation
  strategies (proof techniques, auxiliary inductives, named
  composites) may change freely; weakening the interface of
  a standard mathematical concept to ease implementation is
  always wrong.
- **Compositional tests.** Where possible, calculate one value
  per test, assert it matches the expectation, return the value
  for reuse in other tests. Reduces duplication; chains tests
  together.
