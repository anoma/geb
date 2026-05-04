# Geb Idris Development Guidelines

## Current Work

- **MLDirichF Generalization**: Extending MLDirichF to support type checking
on generic S-expressions and arbitrary finite two-level DAGs. See
[docs/mldirichf-generalization.md](docs/mldirichf-generalization.md) for
details.

## Build Commands

- Full build: `idris2 --build geb.ipkg`
- Remove build files: `idris2 --clean geb.ipkg`
- Run all tests: `./build/exec/geb`
- Prefer compile-time tests (using `Assert`/`Assertion`) over run-time tests

## Code Style Guidelines

- **Types**: Use total functions (`%default total`)
- **Naming**: Use camelCase for functions, PascalCase for types, all-caps for
  constants
- **Exports**: Mark functions as `public export`, `export`, or private
  appropriately
- **Documentation**: Use `--` for single-line comments, `{- -}` for multi-line
  comments
- **Error handling**: Use `Either` for recoverable errors, `Maybe` for
  optional values
- **Line length**: Keep lines under 80 characters
- **Imports**: Group imports by library/module category
- **Whitespace**: Use 2-space indentation, no trailing whitespace
- **Pattern matching**:
  - Prefer explicitly exhaustive pattern matching
  - No spaces around `=` in pattern matches: `{src=(a ** x)}` not
    `{src = (a ** x)}`
- **Line breaking**: Break long type signatures across multiple lines to
  stay under 80 characters
- **Section headers**: Format with matching dash lines above and below:
  - End section name with one space and four dashes: `---- Section Name ----`
  - Use equal-length dash lines above and below the header

## Testing

Tests are organized in parallel structure to source files and use `Assert`
for assertions.

## Development Practices

- Capitalize data constructors and constants to avoid implicit variable
  binding issues
- Capitalize function names to avoid shadowing warnings when they appear as
  implicit parameters in their own type signatures
- Proactively suggest documentation updates when learning something important,
  finishing major components, or discovering patterns that help write correct
  Idris code

## Proof Techniques

### Functional Extensionality

- Add a `FunExt` parameter to functions that need it: `(fext : FunExt)`
- Use `funExt $ \x => ...` to prove function equality
- Only use when necessary - many proofs work without it

### Unicity of Identity Proofs (UIP)

- Use `uip` from `IdrisUtils` when comparing two proofs of the same equality
- All proofs of the same equality are themselves equal
- Useful for proving category laws involving rewrite rules

### Working with Implicit Parameters

- Consider making implicit parameters explicit when they appear in proof goals
- Idris doesn't support implicit lambda abstractions like `\{x} => ...`
- Explicit parameters work better with `funExt`

### Pattern Matching vs Accessors

- **Avoid pattern matching on function results**: Idris cannot pattern match on
  the result of function calls, which can prevent it from seeing type
  equivalences
- **Use accessor functions instead**: Replace pattern matches like
  `(x ** y)` with `fst`/`snd` calls when:
  - The value comes from a function application
  - You need to pass the value to another function
  - Type equivalences need to be visible to the type checker
- **Keep arguments abstract**: Instead of pattern matching function parameters,
  keep them as variables and use accessors when needed
- **Example patterns to avoid**:

  ```idris
  -- Bad: pattern matching prevents type checking
  f (g x ** h x) = ...

  -- Good: use accessors
  f result = ... where z = fst result ...
  ```

- This technique is crucial for:
  - Converting between similar types (e.g., finite vs general copresheaves)
  - Working with dependent pairs from function results
  - Situations where Idris needs to see that types are definitionally equal

### Working with Dependent Pairs

- **Object mapping**: For dependent types, map to `DPair BaseType DepType`
  rather than just the dependent type itself
- **Morphism mapping**: For `DepToBase` morphisms on dependent pairs, use `fst`
  to extract the base element rather than pattern matching on specific
  constructors

### Dependent Pair Equality

- Use `dpEq12` to break dependent pair equality into two component proofs
- Syntax: `dpEq12 firstProof secondProof`
- Helpful for proving equality of morphisms in categories

## Module Management Checklist

When **renaming** a module or **creating** a new module, follow these steps:

### Renaming a Module

1. Use `git mv` to rename files (preserves history):
   - `git mv src/Path/OldModule.idr src/Path/NewModule.idr`
   - `git mv src/Path/Test/OldModuleTest.idr src/Path/Test/NewModuleTest.idr`
2. Update module declarations at the top of both files
3. Update imports in any files that reference the module
4. Update test function names (e.g., `oldModuleTest` → `newModuleTest`)
5. Update `geb.ipkg` to reference the new module names
6. Update `src/Executable/Test/Main.idr` if it imports the test module
7. Run `make` to verify everything compiles

### Creating a New Module

1. Create the module file: `src/Path/NewModule.idr`
2. Create the test file: `src/Path/Test/NewModuleTest.idr`
3. Add proper module declarations at the top of both files
4. Add the module to `geb.ipkg` in the appropriate section
5. If creating a test module, add it to `src/Executable/Test/Main.idr`:
   - Add the import statement
   - Add the test function call to the test list
6. Run `make` to verify everything compiles

## Pre-submission Checklist

Before proposing any code changes, ALWAYS check:

1. **Trailing whitespace**: Run `git diff --check`
2. **Line length**: Ensure all lines are ≤80 characters
3. **Compilation** (for Idris files): Run `make` to check the entire project
   - Important: Check the whole project, not just the current file, as changes
     may affect symbols used elsewhere
4. **Markdown linting** (for .md files): Run `markdownlint-cli2 <filename>`

Only propose changes after ALL checks pass.

## Category Theory Patterns

- Use `ExtEq` from `IdrisCategories.idr` for expressing extensional equality
  and naturality conditions
- When working with opposite categories, use explicit morphism representations
  rather than implicit ones via dependent types
- Define categorical structures (functors, natural transformations) with their
  laws as explicit proof obligations in the type:
  - Use dependent pairs to bundle mappings with their coherence conditions
  - Create accessor functions for each component
  - This ensures laws are proven at construction time, not assumed
- Whenever defining something with categorical structure, always define:
  - Identity morphism/functor/transformation
  - Composition operation
  - Proofs that the category laws hold (left/right identity, associativity)
- When proving functor law preservation (e.g., composition), handle all
  possible morphism combinations. Use `impossible` for cases that can't occur
  by the type structure

### Finite Two-Level Forest Categories

For implementation details on copresheaves over `Fin2Forest` and MLDirichF
generalization, see
[docs/mldirichf-generalization.md](docs/mldirichf-generalization.md).
This includes patterns for object/morphism mappings, functor law proofs, and
PRA functor implementation.

## Proof Development Techniques

### Incremental Hole-Driven Development

When writing complex proofs, use Idris's hole mechanism to develop proofs
incrementally:

1. Start a proof with a hole: `?proofName`
2. Enter the Idris REPL: `idris2 --find-ipkg src/Path/To/File.idr`
3. Check the hole type: `:t proofName` (note: no `?` in REPL)
4. For full details with implicit parameters: `:ti proofName`
5. Make partial progress, leaving new holes for remaining steps
6. Compile to verify your partial proof is correct
7. Repeat until complete

Example workflow:

```idris
-- Start with a hole
myProof : SomeComplexType
myProof = ?myProof_hole

-- Make partial progress
myProof = rewrite someEquality in ?myProof_step1

-- Check what remains
-- In REPL: :t myProof_step1
-- Continue building incrementally
```

This technique is essential for complex proofs where determining the entire
proof structure in advance is difficult.

### Understanding Proof Obligations

When developing proofs, use `let` bindings to understand what lemmas are
available and how they relate to the goal:

1. Put potentially useful conditions/lemmas in `let` bindings
2. Check the hole type to see the types of these bindings alongside the goal
3. Identify which lemmas match the required proof obligations
4. Once identified, inline the proof for cleaner code

This technique helps bridge the gap between what you have and what you need to
prove.

### Implementing Complex Pattern Matching

When implementing complex pattern matching:

- Start with type signatures and holes to ensure types are correct
- Pattern match one parameter at a time, creating smaller holes
- Use the type checker to understand what's needed in each case
- If implementation seems impossible (e.g., needing to produce `Fin 0`),
  reconsider the design - it may indicate a fundamental issue

### Working with Initial Algebras and Free Monads

When pattern matching on types defined as `Mu` or `FreeMonad`:

- **Cannot match on smart constructors**: Constructors like `inFC` and `inFV`
  work for building values but not for pattern matching
- **Must use full constructors**: Pattern match on `InFree (TFC ...)` and
  `InFree (TFV ...)` directly
- **Handle variable cases**: For `Mu` types, the `TFV` case represents
  variables which shouldn't occur in closed terms - handle with `void`

Example:

```idris
-- Building values - smart constructors work
fsNat n = inFC (FSANat n, Lin)

-- Pattern matching - need full constructors
finSetSExprValidDec (InFree (TFC (FSANat n, Lin))) = Yes (ValidNat n)
finSetSExprValidDec (InFree (TFV x)) = void x
```

### Mutual Recursion and Decidability

When implementing decidability for mutually recursive data types:

- **Mirror the recursion structure**: Create mutually recursive decidability
  functions that match your data types
- **Avoid indirect recursion**: Don't use conversions like `asList` in
  recursive calls - Idris can't see through them for totality checking
- **Create custom predicates**: Instead of using generic predicates with
  conversions, create specific ones for your use case

Example: Instead of using `All` with `asList` for `SnocList`, create a custom
predicate:

```idris
mutual
  data MyValid : MyType -> Type where ...
  data MyValidList : SnocList MyType -> Type where
    ValidNil : MyValidList Lin
    ValidSnoc : MyValidList xs -> MyValid x -> MyValidList (xs :< x)
```

### Function Design Patterns

#### Breaking Up Dependent Pair Functions

When defining functions that return dependent pairs, break them into three
functions for clarity and better type inference:

```idris
-- Instead of one complex function:
complexFunc : Input -> DPair Data ProofAboutData
complexFunc input = (computeData input ** computeProof input)

-- Use three functions:
-- 1. Compute the data
funcData : Input -> Data
funcData input = computeData input

-- 2. Compute the proof (dependent on the data function)
funcProof : (input : Input) -> ProofAboutData (funcData input)
funcProof input = computeProof input

-- 3. Combine them
complexFunc : Input -> DPair Data ProofAboutData
complexFunc input = (funcData input ** funcProof input)
```

Benefits:

- Each function has a simpler type
- Easier to test and reason about individually
- Better type inference
- Can reuse the data computation in the proof

#### Avoiding Let Bindings

Idris sometimes struggles with recognizing that `let` bindings are equal to
their definitions. Prefer inline function calls:

```idris
-- Avoid:
f x = let y = g x
          z = h y
      in k z

-- Prefer:
f x = k (h (g x))
```

This is especially important in proofs where type equality matters.

### Contravariant Functor Tips

When working with contravariant functors (like `el(T1)^op`), remember that
morphisms go in the opposite direction:

- A morphism `f : a → b` in the base category
- Becomes a morphism from `F(b) → F(a)` in the contravariant image
- Pay careful attention to argument order when calling morphism mappings

## Session Continuity

For long-running or complex work that may span multiple sessions, use the
`.session` directory to preserve context:

### When to Use Session Documentation

- Working on multi-phase implementations
- Complex mathematical analysis requiring deep thought
- Design work that needs to be preserved across compactions
- Any task where losing context would require significant re-exploration

### How to Use

1. Create documentation in `.session/<topic-name>.md`
2. Include:
   - Overview of the problem/task
   - Analysis and conclusions reached
   - Implementation plan with phases
   - Status checkboxes for tracking progress
   - Key lemmas or code patterns identified

### File Format

```markdown
# Topic Name

## Overview
Brief description of the work.

## Analysis
Detailed analysis, including any "ultrathink" reasoning.

## Implementation Plan
### Phase 1: ...
### Phase 2: ...

## Key Insights
- Important discoveries
- Code patterns to use

## Status
- [x] Completed items
- [ ] Pending items
```

### Benefits

- Survives context window compactions
- Can be resumed in new sessions
- Provides documentation for future reference
- Enables incremental progress on complex tasks
