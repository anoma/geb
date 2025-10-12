# Instructions for Claude Code

This document contains guidance for AI assistants working on this Lean 4
project.

## Project Notes

- All modules under `GebLean/` should open `namespace GebLean … end GebLean`;
  tests may need `open GebLean` rather than un-qualified names.
- Use `Cat.equivOfIso` when turning category isomorphisms into equivalences.
- `GebLean/Utilities.lean` acts as an index module. Add new utility files
  under `GebLean/Utilities/` and import them from the index. For example,
  `sigmaTrivialSubtype` lives in `GebLean/Utilities/Sigma.lean`.
- Keep the development constructive: do not import or `open` `Classical`
  and avoid the `classical` attribute in proofs.

## Workflow

### Build Before Proposing Changes

When making changes to Lean code:

1. **Build first**: Always run `lake build` after making edits
2. **Iterate on errors**: If the build fails, fix errors yourself and rebuild
   (potentially multiple cycles)
3. **No warnings or sorry**: Code must build **without any warnings**,
   including:
   - No `declaration uses 'sorry'` warnings
   - No unused variable or parameter warnings
   - No other linter warnings
4. **Only show results once complete**: Don't ask for approval until you have
   a clean build with no warnings
5. **Exception - Ask for help if stuck**: If you can't figure out how to fill
   in a `sorry`, are making no progress, or don't understand what's wrong,
   pause and explain:
   - What you're trying to accomplish
   - What problems you're encountering
   - What you've tried so far
   - Why you're stuck on a particular `sorry`

This approach minimizes back-and-forth and keeps the conversation focused on
design decisions rather than syntax errors or incomplete proofs.

## Lean 4 Proof Techniques

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
   - `dsimp only [...]` - definitional simplification, good for reducing `id`,
     beta-reduction
   - Use `simp only [depToFunctorData] at ha` to simplify hypotheses in-place

5. **Breaking down equality goals**:
   - `congr n` - apply congruence `n` levels deep to decompose structured
     equalities
   - Helpful before using `split` to reduce match expressions
   - Example: `congr 2` to get through nested sigma types to the core
     equality
   - For repeated `cases` on equalities between the same object type, prefer
     the helper `elimSixEq` in `DepCategoryJudgments.lean` to keep proofs
     compact.

6. **Reducing match expressions**:
   - `split` - case splits on match/if expressions in the goal
   - Use parentheses for sequencing: `(split; split; rfl)`
   - Combine with `dsimp only [id]` first to expose matches hidden in function
     applications

7. **Subtype projections without classical choice**:
   - Destructure subtypes and sigma terms with `rcases`, then `cases` the
     stored domain/codomain equalities instead of relying on `simp` +
     `classical` to resolve transports
   - Follow the substitutions with `simp [depToFunctorData,
     functorDataToDep_depToFunctorData_morT, cast_eq]` so casts drop away
   - This keeps proofs fully constructive while still collapsing the round-trip
     transports introduced by equivalences
   - When the final goal is a sigma equality, prefer `cases` on the stored
     equalities to obtain definitional `rfl`s rather than running `simp` and
     `subst` on the whole expression
   - Chain simple `cases` eliminations with semicolons (`cases hfa; cases hfb; …`) after
     a targeted `simp` to reduce the amount of boilerplate while keeping lines
     under 80 characters

8. **Handling Sigma types**:
   - Use `change` to rewrite goal with explicit type annotations for nested
     sigmas
   - `Sigma.mk.injEq` to convert sigma equality to component equalities
   - Extract components: `have ⟨ho', hsig⟩ := h` after
     `rw [Sigma.mk.injEq] at h`

### Common Patterns

**Round-trip equivalence proofs** (A → B → A):

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

**Proof irrelevance**: Lean automatically handles proof irrelevance for
`Prop`-valued types. After using `subst` to substitute equalities, different
proofs of the same proposition are automatically considered equal.

### Proving Equivalences with Pattern Matching and Dependent Types

When proving `left_inv` and `right_inv` for equivalences involving dependent
types with pattern matching:

#### The Core Challenge

Pattern matching in tactic mode creates eliminator applications
(`Subtype.rec`, `Sigma.rec`, `Eq.rec`) that don't reduce symbolically. These
appear as complex nested expressions with `match` statements that block
definitional equality.

#### The Solution Pattern

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

#### Key Insights

- **Component-by-component equality** with `Sigma.ext` works well when the
  structure is exposed, but fails when hidden behind pattern match eliminators
- **Proof irrelevance** is automatic for `Prop` components after the data
  components match
- **Don't use `subst` prematurely** - it can prevent later tactics from
  working. Apply it only after extracting all needed equalities
- **The `split` tactic** is crucial for reducing pattern match expressions that
  appear in goal types

#### What Doesn't Work

- Trying to use `Sigma.ext` chains before reducing pattern matches
- Using `congr` on goals with unreduced eliminators
- Attempting to use `ext` on types without registered extensionality lemmas
- Relying on definitional equality when pattern match eliminators are present

#### Debugging Tactics

When working on proofs, **never use `all_goals sorry`** to hide unsolved goals.
This prevents you from seeing what remains to be proven. Instead:

- Let the build fail to see the actual unsolved goals
- Use `all_goals (try <tactic>)` to apply tactics conditionally
- Add targeted `sorry` only after understanding what's needed

#### Automation Tactics to Try

When facing complex goals, it's worth trying powerful automation tactics
before manual proof:

- **`grind`** - SMT-based solver
  (<https://lean-lang.org/doc/reference/latest/The--grind--tactic/>)
  - **EXCELLENT for dependent congruence** - This is the standard idiomatic
    way to handle dependent type equality in Lean!
  - Automatically builds equivalence classes and applies congruence rules
  - Works well with `Equiv.left_inv` and `Equiv.right_inv` lemmas
  - Success rate depends on complexity:
    - ✅ Works great for 1-2 dependent parameters
    - ⚠️ May timeout with 3+ dependent parameters
  - Use `set_option maxHeartbeats <n>` to increase timeout if needed
  - **Usage pattern**: After simplifying with `simp`, add hypotheses with
    `have`, then just call `grind`

- **`aesop`** - General-purpose automation using best-first search
  - Effective for structural goals and standard library lemmas
  - May timeout on goals with heavy pattern matching or dependent types
  - Can be configured with custom rule sets

**Key Discovery**: `grind` is THE solution for dependent congruence problems
that would otherwise require complex manual application of `Eq.recOn`,
heterogeneous equality, or dependent rewriting. Always try `grind` first when
you have equalities involving dependent types!

#### Advanced Pattern: Handling Complex Dependencies with `rcases` + `grind`

When `grind` times out on complex goals with 3+ dependent parameters, use
this pattern:

1. **Destructure early with `rcases`**: Extract all equalities from sigma
   types before substituting
2. **Apply equivalence lemmas BEFORE substituting**: Get `left_inv`/
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
  -- Get left_inv results BEFORE substituting (while a, b, c in scope)
  have hf := (equiv_f data a b).left_inv ⟨⟨a_f, b_f, f'⟩, ha_f, hb_f⟩
  have hg := (equiv_g data b c).left_inv ⟨⟨a_g, b_g, g'⟩, ha_g, hb_g⟩
  have hh := (equiv_h data a c).left_inv ⟨⟨a_h, b_h, h'⟩, ha_h, hb_h⟩
  have hcomp := (equiv_comp data a b c ...).left_inv comp_wit
  -- NOW substitute - this aligns all indices
  subst ha_f hb_f ha_g hb_g ha_h hb_h
  -- After substitution, use congr + grind
  congr 1
  grind
```

**Why this works**:

- Destructuring early gives you explicit equality hypotheses
- Applying lemmas before `subst` keeps the original variables in scope
- `subst` then replaces all the index variables at once
- After substitution, the problem is simple enough for `grind` to handle
- This breaks down a complex 3+ dependency problem into manageable pieces

**When to use**:

- `grind` alone times out (too many dependencies)
- You have nested sigma types with dependent components
- Multiple equivalences need to compose correctly

### Project-Specific Context

- **CategoryJudgments**: Finite category with 4 objects (Obj, Mor, Id, Comp)
  and 11 morphisms
- **FunctorData**: Category structure represented as morphisms in target
  category
- **DepCategoryData**: Same structure using dependent types
- **CopresheafData**: Alias for `FunctorData (Type u)` - functors to Type
- These representations should be equivalent (ongoing work to prove full
  correspondence)

## Code Style

- **Line length**: Keep lines to 80 characters or less
- Prefer editing existing files over creating new ones
- Don't create documentation files unless explicitly requested
- Keep responses concise - match verbosity to task complexity
- Avoid emojis unless explicitly requested by the user
- Don't write "TODO" comments or summaries of completed or future work in the
  code itself; track to-dos/future work below in `CLAUDE.md` if necessary

### Extensionality Lemmas

Always add the `@[ext]` attribute to structure definitions to automatically
generate extensionality lemmas:

```lean
@[ext]
structure MyStruct where
  field1 : Type
  field2 : field1 → Type
  proof_field : SomeProp field1 field2
```

**Benefits**:

- Lean automatically generates the appropriate ext theorem
- Handles proof irrelevance automatically (fields in `Prop` are ignored)
- Works correctly with dependent types and heterogeneous equality
- Follows the mathlib pattern (see `NatTrans` in
  `Mathlib.CategoryTheory.NatTrans`)
- Avoids manual ext theorems that need `cases`, `congr`, etc.

**When NOT to use**: Don't use `@[ext]` on `inductive` types - they use case
analysis rather than field-based extensionality.

### Factoring Common Typeclass Fields

When multiple typeclasses share the same data fields (like finiteness
witnesses), you can factor them out using a `Type`-valued structure:

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

**Key points**:

- Use a `Type`-valued structure (not `Prop`) to hold the actual data
- Mark the structure's fields as `[instance]` to make them available
- Each typeclass contains a single field of the witness structure type
- Provide an instance to extract the witness from the typeclass
- This avoids duplicating field definitions across multiple classes
- **Cannot use `Prop`**: Prop-valued structures can only contain proofs,
  not data like `Fintype` instances

### Bundled Structures: Store Data, Not Typeclass Instances

**Key Principle**: Bundled category structures (like `SemicategoryCat`,
`AcyclicQuiverCat`) should store witness/struct data directly rather than
typeclass instances in brackets. Then derive typeclasses via instances.

**Don't do this** (redundant and hides dependencies):

```lean
structure AcyclicCategoryCat : Type (u + 1) where
  carrier : Type u
  [acyclic : AcyclicQuiver carrier]  -- Redundant!
  [acat : AcyclicCategory carrier]   -- Requires acyclic but it's hidden
```

**Do this instead** (explicit and clean):

```lean
structure AcyclicCategoryCat : Type (u + 1) where
  toAcyclicQuiverCat : AcyclicQuiverCat
  semicat : @SemicategoryStruct toAcyclicQuiverCat.carrier
    toAcyclicQuiverCat.quiver

instance (V : AcyclicCategoryCat) : AcyclicQuiver
    V.toAcyclicQuiverCat.carrier where
  edgesIncrease := V.toAcyclicQuiverCat.edgesIncrease

instance (V : AcyclicCategoryCat) : AcyclicCategory
    V.toAcyclicQuiverCat.carrier where
  toSemicategoryStruct := V.semicat
```

**Benefits**:

- **No redundancy**: Each piece of data stored exactly once
- **Explicit dependencies**: Clear what data is needed and how it relates
- **Avoids diamonds**: No duplicate typeclass instances
- **Enables factoring**: Can compose structures via fields (e.g.,
  `AcyclicCategoryCat` extends `AcyclicQuiverCat`)
- **Better semantics**: Structure fields are data; instances are derived
  properties

**Extension vs Parameters**:

- **`extends`**: `class A extends B` means `[A]` automatically provides `[B]`
  - Example: `AcyclicQuiver extends Quiver` → `[AcyclicQuiver V]` gives
    `[Quiver V]`
- **Parameters**: `class A (V) [B V]` means `[A V]` requires but doesn't
  provide `[B V]`
  - Example: `AcyclicCategory (V) [AcyclicQuiver V]` → need both
    `[AcyclicQuiver V]` and `[AcyclicCategory V]`
  - Used to add properties/structure to existing types without creating
    diamonds

**Pattern for abbreviations**: When creating convenient access functions,
use `abbrev` for conciseness:

```lean
/-- Every edge in an acyclic quiver goes from a smaller vertex to a
    larger vertex. -/
abbrev edge_increases := @AcyclicQuiver.edgesIncrease
```

This is cleaner than spelling out the full type signature when the function
just wraps a typeclass field.

### Equality in Categories: Use `eqToHom` and `eqToIso`

**Reference**: See the mathlib4 docs for `Mathlib/CategoryTheory/EqToHom`
(`EqToHom` search).

When working with object equalities in categories, **avoid rewriting by
equalities**. Instead, use `eqToHom` and `eqToIso`:

```lean
-- Given h : X = Y in a category C

-- Don't do this:
rw [h]  -- Can lead to dependent type theory problems

-- Do this instead:
eqToHom h     -- Creates a morphism X ⟶ Y
eqToIso h     -- Creates an isomorphism X ≅ Y
```

**Why this matters**:

- Rewriting by object equalities can create complex dependent type issues
- `eqToHom` and `eqToIso` provide clean morphisms/isomorphisms
- Mathlib provides many simplification lemmas for these functions
- This pattern extends to dependent types: use explicit transport functions
  instead of raw rewrites

**Similar principle for dependent types**: When you have equality of indices
in dependent types (e.g., morphism equalities `f = g` where types depend on
objects), prefer explicit casts or equivalences over direct rewrites.

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
   - Example: In a semicategory with only `zero → one` morphisms:
     - `ofSemi` only exists when `x = zero` and `y = one`
     - Other combinations (`zero → zero`, `one → one`, `one → zero`)
       have no `ofSemi` morphisms
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

**Key insight**: When proving functor equality with `Functor.hext`, the
heterogeneous equality `≍` won't reduce unless you properly case on all the
variables involved. If `rfl` fails, you likely haven't cased enough to expose
the definitional equality.

### Comment Style

Comments should explain **what the code does and why**, not the historical
process of how we arrived at it:

- **Good**: Comments that clarify intent, explain non-obvious behavior, or
  document important constraints
- **Avoid**: Process-oriented comments like "key insight", "we discovered",
  "after trying X we found Y"
- **Rationale**: What feels like a "key insight" during development might be
  obvious to another reader, or they might find a different aspect insightful.
  Focus on the code itself, not the journey to write it.

Example:

```lean
-- Bad: "The key insight is that after hm, both equivalences are the same"
-- Good: Remove the comment - the code is clear enough

-- Bad: "We need to destructure early before substituting"
-- Good: Remove or replace with "Destructure to extract equality hypotheses"
```

## Problem-Solving Strategy

When struggling with a definition or proof that's becoming excessively long or
complicated:

1. **Factor out helper lemmas**: Break down the problem into smaller, provable
   steps
2. **Make incremental progress**: Prove useful intermediate results that build
   toward your goal
3. **Take smaller steps**: If stuck, step back and prove something simpler
   first
4. **Create helper functions**: Extract complex expressions into named
   definitions

This approach helps you:

- Make firm progress even when the full goal seems difficult
- Create reusable building blocks for later proofs
- Keep individual proofs manageable and understandable
- Debug issues more easily by isolating problems

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

### Testing Strategy

- **Algebraic laws** (associativity, identity, etc.): Use `plausible` to test
  properties
- **Concrete examples**: Use `#guard` with specific values
- **Edge cases**: Test boundary conditions explicitly
- **Functors and morphisms**: Verify composition and identity laws

### Why Plausible is Available

Plausible is already available as a transitive dependency through mathlib.
It provides QuickCheck-style property testing integrated with Lean's tactic
framework.

**References**:

- <https://github.com/leanprover-community/plausible/>
- <https://brandonrozek.com/blog/writing-unit-tests-lean-4/>

## Markdown Linting

All markdown files in this repository should be free of lint warnings. Use
`markdownlint-cli2` to check for and fix any issues:

```bash
markdownlint-cli2 README.md CLAUDE.md .github/copilot-instructions.md
```

Common issues to watch for:

- Line length: Keep lines to 80 characters or less (MD013)
- Fenced code blocks: Surround with blank lines (MD031)
- Lists: Surround with blank lines (MD032)
- URLs: Use angle brackets for bare URLs (MD034)

## Future Work

This section tracks planned improvements and extensions to the codebase.

### Acyclic Quiver Infrastructure

**Automatic decidability for finite quivers**:

- Implement decidability instance for `Relation.ReflTransGen` on finite types
- This would enable `AcyclicQuiver.ofFiniteAcyclic` to work with `by decide`
- Requires: bounded path enumeration up to n vertices
- File: `GebLean/AcyclicQuiver.lean` (currently has `sorry`)

### Test Coverage

**WalkingParallelPairSemi completion**:

- Add semicategory structure (composition is trivial - these are maximal paths)
- Define identity adjoining to construct a full category
- Prove isomorphism between the completed category and mathlib's
  `WalkingParallelPair`
- Show this is a `FiniteAcyclicCategory`
- File: `test/AcyclicCat.lean`
