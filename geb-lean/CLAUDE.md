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

### Build Before Proposing Changes

When making changes to Lean code:

1. **Build first**: Always run `lake build` after making edits. If adding
   dependencies, update `lakefile.toml`, run `lake update`, and commit the
   updated `lake-manifest.json`.  Also always run `lake test`.
2. **Iterate on errors**: If the build fails, fix errors yourself and rebuild
   (potentially multiple cycles)
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

This approach attempts to minimize back-and-forth and keeps the conversation
focused on design decisions rather than syntax errors or incomplete proofs.

## Code Style

- There are standard Lean style guidelines at
  [Lean Library Style Guidelines](https://leanprover-community.github.io/contribute/style.html)
- **Line length**: Keep lines to 80 characters or less
  (the Lean standard only requires <=100, but we prefer a stricter one)
- Keep responses concise - match verbosity to task complexity
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
  something is "complex" or "complicated".
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
- Using mathlib:
  - Import selective modules, e.g. `import Mathlib.Data.Nat.Basic`. Avoid
    blanket imports; keep dependency surface small.
- Proving lemmas:
  - Prefer `by` proof blocks with readable tactic scripts; keep simp sets
    local via `[simp]` only when justified.
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

Common issues to watch for:

- Line length: Keep lines to 80 characters or less (MD013)
- Fenced code blocks: Surround with blank lines (MD031)
- Lists: Surround with blank lines (MD032)
- URLs: Use angle brackets for bare URLs (MD034)

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

- [Mathlib.Data.Fintype.Quotient](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Quotient.html)

### Topos Theory

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

## Development Tips

### Working with Dependent Types and Equivalences

When proving equivalences (`Equiv`) between structures with dependent types:

1. **Destructuring**: Use `rcases` to destructure nested sigma types and
  subtypes
   - Example: `rcases wit with ⟨⟨o', m', w⟩, h⟩`
   - Be explicit with type annotations to help Lean: `ha : a = o`

2. **Substitution**: Use `subst` to substitute equalities
   - Order matters with dependent types - substitute simpler equalities first
   - Example: `subst ha hb ho'` (substitute `a = o`, `b = o` before `o' = ...`)

3. **Heterogeneous Equality**: When substitution produces `≍` (HEq):
   - Use `eq_of_heq` to convert to regular equality when types are
     definitionally equal
   - Then use `Sigma.mk.injEq` or similar to extract component equalities

4. **Simplification hierarchy**:
   - `simp only [...]` - most controlled, only unfolds specified definitions
   - `simp [...]` - more aggressive, may unfold additional things
   - `dsimp only [...]` - definitional simplification; reduces `id`,
     performs beta-reduction
   - Use `simp only [depToFunctorData] at ha` to simplify hypotheses in-place

5. **Breaking down equality goals**:
   - `congr n` - apply congruence `n` levels deep to decompose structured
     equalities
   - Often useful before using `split` to reduce match expressions
   - Example: `congr 2` to get through nested sigma types to the core
     equality

6. **Reducing match expressions**:
   - `split` - case splits on match/if expressions in the goal
   - Use parentheses for sequencing: `(split; split; rfl)`
   - Combine with `dsimp only [id]` first to expose matches hidden in function
     applications

7. **Subtype projections without classical choice**:
   - Destructure subtypes and sigma terms with `rcases`, then `cases` the
     stored domain/codomain equalities instead of relying on `simp` +
     `classical` to resolve transports
   - This keeps proofs fully constructive while still collapsing the round-trip
     transports introduced by equivalences
   - When the final goal is a sigma equality, prefer `cases` on the stored
     equalities to obtain definitional `rfl`s rather than running `simp` and
     `subst` on the whole expression
   - Chain simple `cases` eliminations with semicolons
     (`cases hfa; cases hfb; …`) after a targeted `simp` to reduce the amount
     of boilerplate while keeping lines under 80 characters

8. **Handling Sigma types**:
   - Use `change` to rewrite goal with explicit type annotations for nested
     sigmas
   - `Sigma.mk.injEq` to convert sigma equality to component equalities
   - Extract components: `have ⟨ho', hsig⟩ := h` after
     `rw [Sigma.mk.injEq] at h`

### Isomorphisms

Proofs of isomorphisms look like this:

```lean
def roundtrip_equiv (data : A) : B_of_A data ≃ original_type where
  toFun := ...      -- Convert forward
  invFun := ...     -- Convert backward
  left_inv := by    -- Show toFun ∘ invFun = id
    rcases ...
    subst ...
    simp [...]
  right_inv := by   -- Show invFun ∘ toFun = id
    rcases ...
    subst ...
    simp [...]
```

### Proving Equivalences with Pattern Matching and Dependent Types

See also "Working with Dependent Types and Equivalences" above for general
techniques. This section focuses specifically on the challenges introduced
by pattern matching.

When proving `left_inv` and `right_inv` for equivalences involving dependent
types with pattern matching, pattern matching in tactic mode often creates
eliminator applications (`Subtype.rec`, `Sigma.rec`, `Eq.rec`) that don't
reduce symbolically. These appear as complex nested expressions with `match`
statements that block definitional equality.

Given a categorical isomorphism, you can derive an equivalence
(which is strictly weaker) using `Cat.equivOfIso`.

#### Potentially-useful techniques

1. **Pattern match early** in term mode using `match` to destructure all
   inputs
2. **Simplify definitions** with `simp only` to unfold and normalize
3. **Remove casts** with `simp only [cast_eq]` after substitutions make all
   equalities reflexive
4. **Beta-reduce** with `dsimp only [id]` to eliminate `id` wrappers
5. **Split matches** with `split; split; ...` to reduce all pattern match
   expressions
6. **Close with reflexivity** using `rfl`

Example structure:

```lean
left_inv := fun ⟨⟨components...⟩, proofs...⟩ => by
  match inputs with
  | ⟨patterns...⟩ =>
    simp only [definitions...] at *
    -- Extract equalities from hypotheses
    rw [Sigma.mk.injEq] at hyps
    -- Substitute to make all indices equal
    subst equalities...
    -- Now everything should be definitionally equal
    simp only [cast_eq]
    dsimp only [id]
    split; split; split; ... -- one split per match
    rfl
```

#### Tips

- Component-by-component equality with `Sigma.ext` works well when the
  structure is exposed, but fails when hidden behind pattern match eliminators
- Proof irrelevance is automatic for `Prop` components after the data
  components match
- Don't use `subst` prematurely - it can prevent later tactics from
  working. Apply it only after extracting all needed equalities
- The `split` tactic reduces pattern match expressions that appear in
  goal types
- Consider using `grind`, an SMT-based solver
  (<https://lean-lang.org/doc/reference/latest/The--grind--tactic/>), which:
  - Automatically builds equivalence classes and applies congruence rules
  - Works well with `Equiv.left_inv` and `Equiv.right_inv` lemmas
  - One possible pattern is to simplify with `simp`, add hypotheses with
    `have`, then call `grind`
- Consider using `aesop`, a general-purpose automation using best-first search;
  it can be configured with custom rule sets

#### Pattern: Handling Complex Dependencies with `rcases` + `grind`

When `grind` times out on complex goals with dependent parameters,
or you have nested sigma types with dependent components, or
multiple equivalences need to compose correctly, you can try this pattern:

1. **Destructure early with `rcases`**: Extract all equalities from sigma
   types before substituting
2. **Apply equivalence lemmas before substituting**: Get `left_inv`/
   `right_inv` results while variables are still in scope
3. **Substitute all equalities at once**: Use `subst` to align all indices
4. **Apply `congr 1` then `grind`**: Let `grind` handle the remaining
   dependent congruence

Example:

```lean
hom_inv_id := by
  funext ⟨a, b, c, f, g, h, comp_wit⟩
  simp only [CategoryStruct.comp, CategoryStruct.id,
    Function.comp_apply, id_eq, cast_eq]
  -- Destructure to extract equalities
  rcases f with ⟨⟨a_f, b_f, f'⟩, ha_f : a_f = a, hb_f : b_f = b⟩
  rcases g with ⟨⟨a_g, b_g, g'⟩, ha_g : a_g = b, hb_g : b_g = c⟩
  rcases h with ⟨⟨a_h, b_h, h'⟩, ha_h : a_h = a, hb_h : b_h = c⟩
  -- Get left_inv results before substituting (while a, b, c in scope)
  have hf := (equiv_f data a b).left_inv ⟨⟨a_f, b_f, f'⟩, ha_f, hb_f⟩
  have hg := (equiv_g data b c).left_inv ⟨⟨a_g, b_g, g'⟩, ha_g, hb_g⟩
  have hh := (equiv_h data a c).left_inv ⟨⟨a_h, b_h, h'⟩, ha_h, hb_h⟩
  have hcomp := (equiv_comp data a b c ...).left_inv comp_wit
  -- Now substitute - this aligns all indices
  subst ha_f hb_f ha_g hb_g ha_h hb_h
  -- After substitution, use congr + grind
  congr 1
  grind
```

That pattern sometimes works because:

- Destructuring early gives you explicit equality hypotheses
- Applying lemmas before `subst` keeps the original variables in scope
- `subst` then replaces all the index variables at once
- After substitution, the problem is simple enough for `grind` to handle

### Extensionality Lemmas

Always add the `@[ext]` attribute to structure definitions (when it compiles)
to automatically generate extensionality lemmas:

```lean
@[ext]
structure MyStruct where
  field1 : Type
  field2 : field1 → Type
  proof_field : SomeProp field1 field2
```

**Properties**:

- Lean automatically generates the appropriate ext theorem
- Handles proof irrelevance automatically (fields in `Prop` are ignored)
- Works correctly with dependent types and heterogeneous equality
- Follows the mathlib pattern (see `NatTrans` in
  `Mathlib.CategoryTheory.NatTrans`)
- Avoids manual ext theorems that need `cases`, `congr`, etc.

### Derived instances

When defining a structure, derive whatever standard instances are
applicable to that structure, such as `Inhabited`, `DecidableEq`, and
`Repr`.

### Type Classes

#### Factoring Common Typeclass Fields

When multiple typeclasses share the same data fields (like finiteness
witnesses), factor them out using a `Type`-valued structure:

```lean
/-- A proof of finiteness of a quiver. -/
structure FinQuiverWitness (V : Type u) [Quiver.{v + 1} V] where
  fintypeVertex : Fintype V
  fintypeEdge : ∀ a b : V, Fintype (a ⟶ b)

attribute [instance] FinQuiverWitness.fintypeVertex
  FinQuiverWitness.fintypeEdge

class FiniteQuiver (V : Type u) [Quiver.{v + 1} V] where
  toFiniteness : FinQuiverWitness V := by infer_instance

instance {V : Type u} [Quiver.{v + 1} V] [h : FiniteQuiver V] :
    FinQuiverWitness V := h.toFiniteness
```

**Typeclass declaration format**:

- Use a `Type`-valued structure (`Prop` if it compiles -- i.e., when
  the data/interface is pure proof content) to hold the actual data/interface
- Mark the structure's fields as `[instance]` to make them available
- Each typeclass contains a single field of the witness structure type
- Provide an instance to extract the witness from the typeclass

That process, in short, is to treat the data/interface required by a typeclass
as a first-class structure in and of itself, and constrain the operation
of the language's `typeclass` mechanism to operations on those structures.
We can use extension and dependent typing on the structures themselves to
generate the interfaces of "derived" classes, then use `typeclass` solely
on the resulting structures, then declare instances that extract components
of the structure to ensure that instances of "derived" classes also guarantee
instances of "inherited" classes.

Bundled category structures (like `SemicategoryCat`, `AcyclicQuiverCat`)
should store witness/struct data directly (which will often take the
form of nested dependently-typed structures) rather than typeclass instances
in brackets. Then derive typeclasses via instances.

We should do this for interactions with Lean standard-library typeclasses.
For our own new code, just don't create typeclasses; use interface structures.

#### Converting Between Structures and Typeclasses

When creating bidirectional conversions between structure-based
implementations and typeclass-based interfaces, follow this pattern:

**Structure → Typeclass (use `instance`)**:

- Take structure parameters explicitly (e.g., `HomSet`, `CategoryOps`,
  `CategoryData`)
- Make the type parameter implicit: `{U : Type u}`
- Explicitly provide typeclass fields that define the interface
  (e.g., `Hom := hs`)
- The typeclass instance is the output, not an input parameter

```lean
instance {U : Type u} (hs : HomSet.{v + 1, u} U)
    (ops : CategoryOps hs) : CategoryStruct.{v, u} U where
  Hom := hs
  id := ops.id
  comp := ops.comp
```

**Typeclass → Structure (use `abbrev`)**:

- Take typeclass instances as implicit parameters: `[Category U]`
- Extract structure data from the typeclass
- Use `abbrev` for definitional equality

```lean
abbrev categoryOpsOfCategoryStruct (U : Type u) [CategoryStruct.{v, u} U] :
    CategoryOps (homSetOfQuiver U) where
  comp := CategoryStruct.comp
  id := CategoryStruct.id
```

**Rationale**:

This pattern avoids circular typeclass search. When converting structure
to typeclass, all input data comes from explicit structure parameters,
not from typeclass synthesis. This prevents Lean from entering infinite
loops trying to synthesize a typeclass to construct that same typeclass.

**Example hierarchy in the codebase**:

- `HomSet` ↔ `Quiver`: `instance` / `abbrev homSetOfQuiver`
- `IdentityStruct` ↔ `ReflQuiver`: `instance` /
  `abbrev identityStructOfReflQuiver`
- `CategoryOps` ↔ `CategoryStruct`: `instance` /
  `abbrev categoryOpsOfCategoryStruct`
- `CategoryData` ↔ `Category`: `instance` /
  `abbrev categoryDataOfCategory`

This creates a clean separation where structures are the source of truth,
and typeclasses are derived interfaces for interoperability with mathlib.

#### Type Class Troubleshooting

If you struggle with instance resolution or other aspects of type class
use, do the following:

- Check the Lean documentation references about type classes in this document
- Write a version of the definition you're trying to implement which
  factors out all usage of type classes into usage of the underlying
  structures that we have defined, get that implemented, and then
  implement the type class version by wrapping its inputs and outputs
  with the structure/typeclass conversion functions we have defined
  along with the underlying-structure definitions

### Structure Composition with `extends`

In Lean, `extends` is implemented using composition, not classical
object-oriented inheritance. This makes it appropriate for situations where
a structure logically builds upon another structure by adding fields.

**When to use `extends`**:

Use `extends` when structure B contains all of structure A's data plus
additional fields. For example:

```lean
structure FintypeData (α : Type u) extends Finset α where
  complete : FinsetComplete toFinset
```

This expresses that `FintypeData` is a `Finset` with an additional
completeness property.

**Properties**:

- `extends` creates a `toX` field automatically (e.g., `toFinset`)
- The extending structure inherits all fields from the base structure
- This is composition, not inheritance in the OO sense
- Moving up the hierarchy is not upcasting

**Reference**:

See [Functional Programming in Lean: Structures and
Inheritance](https://leanprover.github.io/functional_programming_in_lean/functor-applicative-monad/inheritance.html)
for details on how `extends` works in Lean.

### Equality in Categories: Use `eqToHom` and `eqToIso`

When working with object equalities in categories, use `eqToHom` and `eqToIso`
when applicable.  See the mathlib4 docs for `Mathlib/CategoryTheory/EqToHom`.
Use explicit transport functions.  When you have equality of indices
in dependent types (e.g., morphism equalities `f = g` where types depend on
objects), prefer explicit transport functions or casts over rewrite tactics.

### Pattern Matching in Functor Definitions

When defining functors with pattern matching on morphisms that include
composition:

1. **Avoid composition in match discriminants**: Pattern matching on `f ≫ g`
   directly in the discriminant prevents definitional reduction, blocking
   proofs of `map_comp`.

2. **Use helper functions**: When morphisms have inductive structure (like
   `AdjoinedIdHom`), create a separate helper function for the non-trivial
   cases:

   ```lean
   def mapHelper : SemiHom X Y → (obj X ⟶ obj Y)
     | .case1 => ...
     | .case2 => ...

   def map : Hom X Y → (obj X ⟶ obj Y)
     | .id _ => 𝟙 _
     | .hom f => mapHelper f
   ```

3. **Proving map_comp**: Use `cases` to split on constructors, then use
   `change` to explicitly state the expected goal form:

   ```lean
   map_comp f g := by
     cases f with
     | id =>
       cases g with
       | id => change 𝟙 _ = 𝟙 _ ≫ 𝟙 _; simp
       | hom g' => change mapHelper g' = 𝟙 _ ≫ mapHelper g'; simp
     | hom f' =>
       cases g with
       | id => change mapHelper f' = mapHelper f' ≫ 𝟙 _; simp
       | hom g' =>
         change mapHelper (comp f' g') = mapHelper f' ≫ mapHelper g'
         cases f' <;> cases g' <;> simp [mapHelper, comp, ...]
   ```

4. **Properties**: This approach keeps composition reduction in the proof
   where it can be handled explicitly, rather than requiring it to reduce
   definitionally in the pattern match.

### Proving Functor Equality

When proving that two functors are equal (e.g., `F ⋙ G = 𝟭 C`):

1. **Use `Functor.hext`** for heterogeneous equality:
   - First goal: object equality `∀ x, F.obj x = G.obj x`
   - Second goal: morphism equality using `≍` (heterogeneous equality)
   - The morphism goal has form: `∀ x y f, F.map f ≍ G.map f`

2. **Pattern matching strategy**:
   - Case on the morphism constructor first: `cases f with`
   - Handle each constructor separately
   - For dependent pattern matching, remember which combinations are possible
   - Use `nomatch` or just omit cases that are impossible

3. **Working with dependent pattern matches**:
   - When casing creates subcases, check which are actually inhabited
   - Use `cases` on the actual morphism value to handle all constructors

4. **Avoid computational definitions in proofs**:
   - Don't use tactics (such as `cases`) to generate computational content;
     for any computational content, construct terms explicitly
   - Separate proof-irrelevant proof content, which may use tactics, from
     computational content

Example pattern:

```lean
theorem functor_comp_id : F ⋙ G = 𝟭 C := by
  apply Functor.hext
  · intro x; cases x <;> rfl  -- object equality
  · intro x y f
    cases f with
    | constructor1 => ...  -- handle each constructor
    | constructor2 x' => cases x' <;> rfl  -- nested case if needed
```

When proving functor equality with `Functor.hext`, the heterogeneous
equality `≍` won't reduce unless you properly case on all the variables
involved. If `rfl` fails, you likely haven't cased enough to expose
the definitional equality.

### Finset-based Fintype Instances

When defining `Fintype` instances for types with recursive structure (such as
bounded-length paths in a quiver), follow mathlib's pattern of separating
computational content (`Finset`) from typeclass (`Fintype`).

Reference: `Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting`

**The pattern**:

1. Define a recursive `Finset` function that constructs the set directly
2. Prove completeness (membership theorem)
3. Derive the `Fintype` instance via `Fintype.ofFinset` or direct construction

**Rationale**: Lean's typeclass synthesis does not work well with `letI`
bindings in recursive function contexts. Mathlib instances like `Sigma.
instFintype` and `Quiver.Path.instDecidableEq` exist but cannot be used
directly in recursive definitions due to these synthesis limitations.

The Finset-based approach avoids typeclass synthesis entirely by working
directly with concrete `Finset` values.

**Example** (adapted from [AcyclicPresentation.lean:339-403](GebLean/
AcyclicPresentation.lean)):

```lean
def finsetPathsBounded {V : Type u} [Quiver.{v + 1} V] [Fintype V]
    [DecidableEq V] [∀ a b : V, DecidableEq (a ⟶ b)]
    [∀ a b : V, Fintype (a ⟶ b)] (a b : V) (n : ℕ) :
    Finset {p : Quiver.Path a b // pathLength p ≤ n} :=
  match n with
  | 0 =>
    if h : a = b then
      {⟨h ▸ Quiver.Path.nil, by subst h; simp [pathLength]⟩}
    else
      ∅
  | n + 1 =>
    let baseCase : Finset {p : Quiver.Path a b // pathLength p ≤ n + 1} :=
      if h : a = b then
        {⟨h ▸ Quiver.Path.nil, by subst h; simp [pathLength]⟩}
      else
        ∅
    let consCase : Finset {p : Quiver.Path a b // pathLength p ≤ n + 1} :=
      Finset.univ.biUnion fun (c : V) =>
        (finsetPathsBounded a c n).biUnion fun ⟨p, hp⟩ =>
          (Finset.univ : Finset (c ⟶ b)).map
            ⟨fun f => ⟨Quiver.Path.cons p f, by simp [pathLength]; omega⟩,
             fun f₁ f₂ h => by cases h; rfl⟩
    baseCase ∪ consCase

theorem mem_finsetPathsBounded_iff {V : Type u} [Quiver.{v + 1} V]
    [Fintype V] [DecidableEq V] [∀ a b : V, DecidableEq (a ⟶ b)]
    [∀ a b : V, Fintype (a ⟶ b)] {a b : V} {n : ℕ}
    (p : {p : Quiver.Path a b // pathLength p ≤ n}) :
    p ∈ finsetPathsBounded a b n := by
  -- Proof by induction on n, casing on path structure...

instance fintypePathsBounded {V : Type u} [Quiver.{v + 1} V] [Fintype V]
    [DecidableEq V] [∀ a b : V, DecidableEq (a ⟶ b)]
    [∀ a b : V, Fintype (a ⟶ b)] (a b : V) (n : ℕ) :
    Fintype {p : Quiver.Path a b // pathLength p ≤ n} :=
  ⟨finsetPathsBounded a b n, fun p => mem_finsetPathsBounded_iff p⟩
```

**Techniques**:

- Use `Finset.univ.biUnion` to enumerate over all vertices/edges
- Use `Finset.map` with explicit embeddings (`⟨fun ... , fun ... => ...⟩`)
  to transform elements
- Avoid products; use nested `biUnion` instead
- In completeness proofs, use `simp only` with specific lemmas to control
  unfolding
- Pattern match on path constructors to extract implicit intermediate vertices
