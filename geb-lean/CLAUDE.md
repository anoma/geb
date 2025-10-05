# Instructions for Claude Code

This document contains guidance for AI assistants working on this Lean 4 project.

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

1. **Destructuring**: Use `rcases` to destructure nested sigma types and subtypes
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

6. **Reducing match expressions**:
   - `split` - case splits on match/if expressions in the goal
   - Use parentheses for sequencing: `(split; split; rfl)`
   - Combine with `dsimp only [id]` first to expose matches hidden in function
     applications

7. **Handling Sigma types**:
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
