# Instructions for Claude Code

This document contains guidance for AI assistants working on this Lean 4
project.  When beginning a session, please read this entire file and
adhere to its guidelines throughout the session.

## Project Notes

- All modules under `GebLean/` should open `namespace GebLean … end GebLean`;
  tests may need `open GebLean` rather than un-qualified names.
- `GebLean/Utilities.lean` acts as an index module. Add new utility files
  under `GebLean/Utilities/` and import them from the index.
- Root entry module: `GebLean.lean` re-exports the library's public API.
- When you add a new public module, list it in `GebLean.lean` so downstream
  users keep a single entry point.
- Library namespace: `GebLean` (see `[[lean_lib]] name = "GebLean"` in
  `lakefile.toml`).
- Source files live under `GebLean/` and should use the `GebLean` namespace.
- External deps: mathlib and related tools are pinned in
  `lake-manifest.json`; see `lean-toolchain` for the toolchain.

## Workflow

When making changes to Lean code:

1. **Build first**: Always run `lake build` after making edits. If adding
   dependencies, update `lakefile.toml`, run `lake update`, and commit the
   updated `lake-manifest.json`.  Also always run `lake test`.
2. **Iterate on errors**: If the build fails, fix errors yourself and rebuild
   before proposing a change.
3. **No warnings or sorry**: Code must build **without any warnings**,
   including:
   - No `declaration uses 'sorry'` warnings (never use `sorry`)
   - No unused variable or parameter warnings
   - No other linter warnings
4. **Only show results once complete**: Don't ask for approval until you have
   a clean build with no warnings
5. **Exception - Ask for help if stuck**: If you can't figure out how to
   fill in an underscore (never use `sorry`), are making no progress, or
   don't understand what's wrong, pause and explain:
   - What you're trying to accomplish
   - What problems you're encountering
   - What you've tried so far
   - Why you're stuck on a particular underscore
6. **First errors first**: When there are multiple warnings or errors in a
    build, always fix the first error first.  Later errors may be caused by
    earlier ones, or their fixes may be affected by earlier fixes.
7. **Underscores**: When you want to see the type of a goal you're working on
   (you can do this with computational content as well as proof content),
   insert an underscore (`_`) as the implementation of the goal.  Building
   will then produce an "unsolved goals" error and will print the type
   of the goal.  Do this whenever you take a step in a definition or
   proof, so that you know exactly what it is that you're trying to
   define or prove next.  Use `_`, not `sorry` -- we _want_ the build to
   be broken when there's a hole we haven't filled in yet, and `_` also
   shows the type of the hole.
8. **#check**: Use `#check <expr>` to check the type of an expression

## Code Style

- There are standard Lean style guidelines at
  [Lean Library Style Guidelines](https://leanprover-community.github.io/contribute/style.html)
- **Line length**: Keep lines to 80 characters or less
  (the Lean standard only requires <=100, but we prefer a stricter one)
- Don't use emojis
- In transient (unrecorded) conversation, you may be informal and
  enthusiastic if you like, but in any persistent work (such as
  all source code (including comments), documentation, and project
  guidelines/instructions), stick to a dry, formal, unopinionated, mathematical
  style.  Never promote any aspect or passage of code as more significant
  than any other, such as by calling something "key", or an "insight",
  or "core", or "advanced".  Never refer to properties of code or
  constructions as "advantages" or "benefits"; if you want to document a
  property of some code or design because you don't think it's immediately
  obvious just from reading the code itself, then simply call it a "property"
  or similar detached word.  Never call code "important" (if we didn't
  think it were important, we wouldn't be writing it).  Never opine that
  something is "complex" or "complicated"; readers can decide what they
  consider complex.
- Do not use all-caps words unless they're acronyms.
- Don't write "TODO" comments or summaries of completed or future work in the
  code itself; track to-dos/future work below in `CLAUDE.md` if necessary
- Don't write comments which state in natural language what the
  code following them does.  We can assume that readers of our code
  are coders and can understand the code itself.  Comments can sometimes
  be appropriate for explaining relationships with _concepts_ or with _other_
  areas of code, which may not be obvious from the nearby code.
- Do not give up on a task we've agreed to try just because it seems like
  a lot of work, or you think it's unimportant or unsuitable in some cases,
  or anything like that.  If you do think there's a good reason not to do
  it, first pause and discuss it with me -- don't just abandon it or call
  it "done" or "good enough".
- Comments should never refer to the historical process of the code's
  development, and we should never do anything related to "backwards
  compatibility" (including making comments about it).  We're writing
  completely new code here; as far as users are concerned, there is no
  history yet.
- Make our tests as compositional as possible.  In general, this will mean
  calculating only one value per test, asserting that it matches what we
  expect, and then returning it as a value.  That will allow us to reuse that
  test, and its return value, in other tests, minimize code duplication, and
  chain tests together.
- When making changes, especially long-running large changes, be strict
  about the following procedures:
  - After each individual code change, re-run `lake build` and `lake test`,
    and immediately fix any problems before moving on to the next code change.
  - Make sure we're not removing any existing tests, unless removing tests
    is a specific goal of the change we're making.
- Preseve the options in `lakefile.toml`, such as:
  - `autoImplicit = false` and `relaxedAutoImplicit = false`: write binders
    explicitly; don't rely on implicit inference.
  - `pp.unicode.fun = true`: prefer `fun x ↦ ...` formatting.
  - `weak.linter.mathlibStandardSet = true`: follow mathlib's standard
    linters.
  - `maxSynthPendingDepth = 3`: avoid tactics requiring deep typeclass search;
    structure instances explicitly when possible.
- Namespaces: put code under `namespace GebLean` (matching file path).
- Imports: centralize in `GebLean.lean` for library public surface; modules
  should import only what they use.
- LSP: Lean files are typechecked on save via the Lean server; keep files
  compilable.
- Keep the development constructive: never import or `open` `Classical`,
  and never use `classical` attribute in proofs.  Similarly, never use
  `noncomputable`.  Similarly, never use `axiom` -- our results should depend
  only on Lean's native type theory.
- Explain module placement and imports.
- Keep Lean options consistent (don't override project-level options without
  discussion).
- Any style guidelines which aren't specific to Lean apply to documentation
  and style guidelines and such as well -- in particular, they apply to this
  file itself (`CLAUDE.md`).

## Markdown Linting

All markdown files in this repository should be free of lint warnings. Use
`markdownlint-cli2` to check for and fix any issues, for example:

```bash
markdownlint-cli2 README.md CLAUDE.md .github/copilot-instructions.md
```

Always fix all warnings/errors before proposing a Markdown-file change
(as with any other source file).

## Lean 4 Library and Categorical Theory Resources

Links to mathematical concepts available in Lean 4 libraries (particularly
`mathlib`).  In our code, we should only use standard libraries, but we
might want to examine external libraries for ideas.

### Searchable

- [Loogle](https://loogle.lean-lang.org/)
  - A searchable reference to the Lean standard libraries -- we should
    use this to try to find standard implementations of concepts that
    we don't already know about.
- [Reservoir](https://reservoir.lean-lang.org/)

### Lean language

- [The Lean 4 Theorem Prover and Programming Language (conference paper)](https://link.springer.com/content/pdf/10.1007/978-3-030-79876-5_37.pdf?pdf=inline%20link)
- [Functional Programming in Lean: Structures and Inheritance](https://leanprover.github.io/functional_programming_in_lean/functor-applicative-monad/inheritance.html)
- [Lean Language Reference: Type Classes](https://lean-lang.org/doc/reference/latest/Type-Classes/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Theorem Proving in Lean 4: Type Classes](https://lean-lang.org/theorem_proving_in_lean4/Type-Classes/)
- [Functional Programming in Lean: Type Classes and Polymorphism](https://leanprover.github.io/functional_programming_in_lean/type-classes/polymorphism.html)
- [Tabled Typeclass Resolution](https://arxiv.org/pdf/2001.04301)
- [Use and abuse of instance parameters in the Lean mathematical library](https://arxiv.org/pdf/2202.01629.pdf)

### General mathematics

- [Lean's "mathlib" page](https://leanprover-community.github.io/mathlib-overview.html)

### General category theory

- [Lean's "category theory" page](https://leanprover-community.github.io/theories/category_theory.html)

### Polynomial functors

- [mathlib4's univariate polynomial functors](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/PFunctor/Univariate/Basic.html)
- [mathlib4's multivariate polynomial functors](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/PFunctor/Multivariate/Basic.html)
- [mathlib4's W-types](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/PFunctor/Multivariate/W.html)
- [mathlib4's M-types](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/PFunctor/Multivariate/M.html)

### Profunctors

- [Mathlib.CategoryTheory.Limits.Shapes.End (ends and coends)](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/End.html)

### Computability

- [Mathlib.Computability.Primrec](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/Primrec.html)
- [Mathlib.Computability.TMComputable](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/TMComputable.html)
- [Mathlib.Computability.TuringMachine](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/TuringMachine.html)

### Monad algebra

- [mathlib4's Monad.Algebra](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Monad/Algebra.html)

### Kan extensions

- [mathlib4's KanExtension](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/KanExtension/Basic.html)

### Grothendieck Construction

- [Mathlib.CategoryTheory.Grothendieck](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Grothendieck.html)
  - Provides Lean formalization of the Grothendieck construction for functors
    valued in categories (\(C \to Cat\)), including morphisms and universal
    properties.

- [Mathlib.CategoryTheory.Bicategory.Grothendieck](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Bicategory/Grothendieck.html)
  - Bicategorical generalization of the Grothendieck construction.

### Simplicial Sets and Nerves

- [Mathlib.AlgebraicTopology.SimplicialSet.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialSet/Basic.html)
- [Mathlib.AlgebraicTopology.SimplicialSet.Nerve](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialSet/Nerve.html)
- [Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction](https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialSet/NerveAdjunction.html)

### Quotients

- [Init.Prelude.Quot](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot)
  - Other operations on `Quot` follow
- [Init.Core.Quot.recOn](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#Quot.recOn)
  - Other operations on `Quot` precede and follow
- [Init.Core.Quotient](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#Quotient)
- [Mathlib.Data.Fintype.Quotient](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Quotient.html)

### Topos Theory

- [Mathlib.CategoryTheory.Topos.Classifier](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Topos/Classifier.html)
- [b-mehta/topos: Topos theory in Lean](https://github.com/b-mehta/topos)
  - Independent repository formalizing foundational aspects of topos theory,
    including subobject classifiers, Lawvere-Tierney topologies, and
    categorical theorems.

### Presheaf/Copresheaf Universal Properties

- [Mathlib.CategoryTheory.Limits.Presheaf](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Presheaf.html)
  - Formalizes limits and colimits within presheaf categories, including the
    colimit-of-representables theorem.

- [Mathlib.CategoryTheory.Comma.Presheaf.Colimit](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Comma/Presheaf/Colimit.html)
  - Addresses colimit structures in comma categories related to presheaf
    categories.

- [Mathlib.Topology.Sheaves.Sheaf](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Sheaves/Sheaf.html)
  - Implementation of sheaf theory, with presheaves and categorical structures
    detailed for topological spaces.

- [Mathlib.Topology.Sheaves.Presheaf](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Sheaves/Presheaf.html)
  - Documents presheaf categories for sheaf-theoretic constructions.

### Subobject Classifiers and Related

- [Mathlib.CategoryTheory.Topos.Classifier](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Topos/Classifier.html)
  - Detailed formalization of subobject classifiers in category theory,
    including construction for presheaf categories.

- [Mathlib.CategoryTheory.Subpresheaf.Subobject](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Subpresheaf/Subobject.html)
  - Focuses on subobjects and subpresheaf categories, relevant to classifier
    theory and morphism structure.

- [Mathlib/CategoryTheory/Sites/Closed.lean](https://plmlab.math.cnrs.fr/nuccio/octonions/-/blob/add-vector-api-alt/Mathlib/CategoryTheory/Sites/Closed.lean)
  - Code and theory for closed sites, relevant for power objects and
    classifier constructions.

## Testing

This project uses Lean 4's built-in testing capabilities along with
property-based testing via Plausible.

### Running Tests

```bash
lake test
```

The test driver is configured as a library, so tests run during the build
process. Any `#guard` assertion failures will cause the build to fail.

### Writing Tests

Tests live in the `test/` directory. See [test/README.md](test/README.md) for
detailed information.

#### Quick Reference

**Unit tests with `#guard`**:

```lean
import GebLean

#guard some_function arg == expected_result
```

**Property-based testing with Plausible**:

```lean
import Plausible

-- Test that associativity holds
example (a b c : MyType) : (a ∘ b) ∘ c = a ∘ (b ∘ c) := by
  plausible  -- Finds counterexamples if property doesn't hold
```

**Note**: The `linter.hashCommand` linter is disabled for all test files via
the lakefile configuration, so you don't need `set_option` in test files.

### Plausible

Plausible is already available as a transitive dependency through mathlib.
It provides QuickCheck-style property testing integrated with Lean's tactic
framework.

**References**:

- <https://github.com/leanprover-community/plausible/>
- <https://brandonrozek.com/blog/writing-unit-tests-lean-4/>

## Development Processes

- See [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
  for tips on many aspects of theorem-proving.  If you're struggling to
  prove something, or even just about to embark on a
  potentially-challenging proof, check the table of contents and find
  and read sections that appear likely to be relevant.
- Consider using `grind`, an SMT-based solver
  (<https://lean-lang.org/doc/reference/latest/The--grind--tactic/>)
- Consider using `aesop`, a general-purpose automation using best-first search;
  it can be configured with custom rule sets
- Always add the `@[ext]` attribute to structure definitions (when it compiles)
to automatically generate extensionality lemmas
- When defining a structure, always derive whatever standard instances are
applicable to that structure, such as `Inhabited`, `DecidableEq`, and
`Repr`
- In Lean, `extends` is implemented using composition, not classical
  object-oriented inheritance. This makes it appropriate for situations
  where a structure builds upon another structure by adding fields.
  See [Functional Programming in Lean: Structures and Inheritance](https://leanprover.github.io/functional_programming_in_lean/functor-applicative-monad/inheritance.html).

- When defining a structure with later fields that depend on earlier
  ones, first define one with independent earlier fields, then define
  a dependent one comprising independent fields which individual depend
  on fields of the earlier one, then define the combined structure as
  an (optionally named) sigma type.  This allows operations to be defined
  on components of the structure separately, with some different dependent
  operations potentially depending on the same earlier operation.  (In
  particular, build the sigma type using `extends` when that compiles.)
- When using or defining a typeclass instance:

  - Define a structure comprising the fields of the interface of the typeclass
  - Define the typeclass itself as a having a single field containing
    an instance of the interface structure
  - A function that takes the typeclass as a parameter and/or returns a
    typeclass instance should have a version that takes and/or returns the
    interface structure, which should be wrapped in the version that takes
    and/or returns the typeclass as a parameter, which does nothing but call
    the interface-structure version

  This separates the definition of the interface of the typeclass, which
  can then be operated on as a mathematical object itself, from typeclass
  resolution, which in particular isolates typeclass resolution errors to
  the resolution itself rather than other compiler errors which prevent
  finding a valid instance.
- When working with object equalities in categories, use `eqToHom` and `eqToIso`
  when possible.  See the mathlib4 docs for `Mathlib/CategoryTheory/EqToHom`.
  Use explicit transport functions.
- Factor out definitions of structure components into separate definitions
  to make their type signatures explicit.
- Make universe levels as polymorphic as possible (that is, as polymorphic
  as will compile!).
