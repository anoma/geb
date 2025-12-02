# NPN End Analysis: Second Component Constraints

## Overview

This document analyzes the constraints on the second component of the end of
`NegPosNatRecPF`, a profunctor derived from the polynomial representation of
a dual-variance data structure inspired by Edward Kmett's "PHOAS for Free".

## Background

### The NegPosNatRecPF Profunctor

The profunctor `NegPosNatRecPF : Type -> Type -> Type` is defined as:

```idris
NegPosNatRecPF x y = InterpPolyFuncFreeM (NegPosMaybePP x) y
```

This is a parameterized free monad where:

- The parameter `x` appears in **negative** (contravariant) positions
- The parameter `y` appears in **positive** (covariant) positions

A term of `NegPosNatRecPF x y` is a dependent pair:

```idris
(i : NegPosNatEndFst x ** NegPosNatEndSnd x i y)
```

Where:

- `NegPosNatEndFst x = PolyFuncFreeMPos (NegPosMaybePP x)` - positions of the
  free monad (the "shape" of a term)
- `NegPosNatEndSnd x i y = NegPosNatEndDir x i -> y` - assignment of values to
  variable leaves

### The End

The end is defined as:

```idris
NegPosNatEnd = EndBase NegPosNatRecPF = (x : Type) -> NegPosNatRecPF x x
```

The end consists of polymorphic terms that use the same type for both negative
and positive occurrences.

### The Wedge Condition

For a term `el : NegPosNatEnd` to be a valid element of the end, it must
satisfy the **wedge condition**: for any morphism `mab : a -> b`:

```text
lmap mab (el b) = rmap mab (el a)
```

This decomposes into two component conditions:

1. **First component** (`NPNWedgeCondFst`): positions must agree
2. **Second component** (`NPNWedgeCondSnd`): direction functions must agree

## First Component (Already Established)

The first component constraint has been established in `npnWedgeCondFstEq`:

> The first component at any type `a` is entirely determined by its value at
> `Unit`. Specifically:
>
> ```idris
> fst (el a) = npnePosFromUnitFst (fst $ el ()) a
> ```

This allows "pulling out" the first component from the polymorphic structure.

## Second Component Constraint (This Analysis)

### Main Result

**The second component constraint is that it must form a natural transformation
from the polynomial functor `NegPosNatEndDirUnit i` to the identity functor.**

Given `i : NegPosNatEndFst Unit` (the first component at Unit), the second
component must be:

```idris
eta : NaturalTransformation (NegPosNatEndDirUnit i) (id {a=Type})
```

This means for each type `x`, we have `eta x : NegPosNatEndDirUnit i x -> x`,
and for any `f : a -> b`:

```text
f . eta a = eta b . npneduMap i a b f
```

### Why Naturality Equals the Wedge Condition

The wedge condition on the second component (`NPNWedgeCondSnd`) states:

```idris
(i : NegPosNatEndDir a (npnWedgeRightFst el a b mab)) ->
  npnWedgeRightSnd el a b mab i = npnWedgeLeftSnd el a b mab (rewrite ...)
```

Tracing through the definitions:

- `npnWedgeRightSnd` = `mab . snd (el a)` (rmap just post-composes)
- `npnWedgeLeftSnd` = `snd (el b) . <direction_transformation>` (lmap
  transforms directions)

The direction transformation under `lmap` is exactly `npneduMap`, so the
condition becomes:

```text
mab . snd (el a) = snd (el b) . npneduMap i a b mab
```

This is precisely the naturality condition for `snd (el _)`.

### Characterizing Natural Transformations

For a polynomial functor `P x = (j : J ** D j -> x)`, natural transformations
`eta : P -> id` are characterized by:

```text
NaturalTransformation P id  ~=  (j : J) -> D j
```

Each natural transformation picks a direction for each position.

### The Structure of NegPosNatEndDirUnitPF

The polynomial functor is defined recursively on the tree structure:

```idris
NegPosNatEndDirUnitPF : NegPosNatEndFst Unit -> PolyFunc
NegPosNatEndDirUnitPF (InPFM (PFVar ()) dm) =
  PFTerminalArena                           -- Variable leaf: one direction
NegPosNatEndDirUnitPF (InPFM (PFCom FZ) dm) =
  PFInitialArena                            -- Zero/leaf: no directions
NegPosNatEndDirUnitPF (InPFM (PFCom (FS FZ)) dm) =
  pfCoproductArena                          -- Node: combines children
    (pfProductArena PFIdentityArena rec_left)
    rec_right
```

Interpreting this:

- **Variable leaf** (`PFVar`): `InterpPolyFunc PFTerminalArena x = x`
  (the identity functor)
- **FZ node**: `InterpPolyFunc PFInitialArena x = Void`
  (no directions, constant Void)
- **FS FZ node**: `Either (x, P_left x) (P_right x)`
  (coproduct of product with left child and right child)

### Natural Transformations as Paths

A natural transformation from `NegPosNatEndDirUnit i` to `id` corresponds to
a **path through the term** to a variable occurrence:

1. **At a variable leaf**: The only choice is identity - we extract the value
   directly.

2. **At an FZ node** (the "zero" constructor): There are no directions, hence
   no possible natural transformations. This makes sense - a closed leaf has
   no variable occurrences to select.

3. **At an FS FZ node** (the "successor" constructor): The functor is
   `Either (x, P_left x) (P_right x)`. A natural transformation must handle
   both cases:
   - **Left case** `(x, p_left)`: We can either:
     - Return `x` directly (stop here - select the negative occurrence)
     - Use a nat trans from `P_left` to continue into the left subtree
   - **Right case** `p_right`: We must use a nat trans from `P_right`

This yields a recursive characterization:

```text
NatTrans (Either (id x P_left) P_right) id
  ~=  (Unit + NatTrans P_left id) x NatTrans P_right id
```

### Interpretation in PHOAS Terms

In the context of PHOAS (Parametric Higher-Order Abstract Syntax):

- A **position** `i : NegPosNatEndFst Unit` represents the **structure** of a
  term - its AST shape
- A **natural transformation** `eta : NegPosNatEndDirNT i` represents a
  **selection of one specific occurrence** of the bound variable in that term

For example, in a term like `\x. f (g x) x`:

- The position encodes the tree structure with two occurrences of `x`
- One natural transformation selects the first occurrence (in `g x`)
- Another natural transformation selects the second occurrence (the standalone
  `x`)

The end elements are therefore characterized by:

```idris
NegPosNatEnd ~= (i : NegPosNatEndFst Unit ** NegPosNatEndDirPath i)
```

Where `NegPosNatEndDirPath i` is equivalent to `NegPosNatEndDirNT i`.

## Implementation Plan

### Phase 1: Define Path Type

Define an inductive type representing valid paths:

```idris
data NegPosNatEndDirPath : NegPosNatEndFst Unit -> Type where
  PathVar : NegPosNatEndDirPath (InPFM (PFVar ()) dm)
  PathNodeLeft : NegPosNatEndDirPath (InPFM (PFCom (FS FZ)) dm)
  PathNodeLeftRec : NegPosNatEndDirPath (dm (Left () ** const ())) ->
    NegPosNatEndDirPath (InPFM (PFCom (FS FZ)) dm)
  PathNodeRightRec : NegPosNatEndDirPath (dm (Right () ** voidF Unit)) ->
    NegPosNatEndDirPath (InPFM (PFCom (FS FZ)) dm)
```

Note: The FZ case has no constructor - there are no valid paths through a
closed leaf.

### Phase 2: Path-to-NatTrans Conversion

Define the conversion from paths to natural transformations:

```idris
pathToNatTrans : (i : NegPosNatEndFst Unit) ->
  NegPosNatEndDirPath i -> NegPosNatEndDirNT i
```

### Phase 3: NatTrans-to-Path Conversion

Define the inverse conversion:

```idris
natTransToPath : (i : NegPosNatEndFst Unit) ->
  NegPosNatEndDirNT i -> NegPosNatEndDirPath i
```

### Phase 4: Isomorphism Proof

Prove the round-trip properties to establish:

```idris
NegPosNatEndDirPath i ~= NegPosNatEndDirNT i
```

### Phase 5: Full End Characterization

Combine with the first component result to get:

```idris
NegPosNatEnd ~= (i : NegPosNatEndFst Unit ** NegPosNatEndDirPath i)
```

## Key Lemmas Needed

1. **Direction functor preservation**: Show that the direction polynomial
   functor at arbitrary types is related to the one at Unit via the contramap.

2. **Naturality sufficiency**: Show that any family of functions satisfying
   naturality can be derived from a path.

3. **Path uniqueness**: Show that different paths yield different natural
   transformations.

## Connection to "PHOAS for Free"

This analysis connects to Kmett's article as follows:

- The profunctor `NegPosMaybeP` corresponds to the base functor of a
  dual-variance recursive type
- The end of the parameterized free monad gives closed terms of this type
- The characterization as (position, path) pairs shows that closed terms are
  essentially trees where we've selected one specific variable occurrence

This provides a constructive characterization of PHOAS terms that could be
useful for:

- Implementing normalization-by-evaluation
- Proving properties about term transformations
- Understanding the structure of binding in dependent type theory

## Status

- [x] Analyzed first component constraints
- [x] Identified that second component must be natural transformation
- [x] Characterized natural transformations as paths
- [x] Implement `NegPosNatEndDirPath` type
- [x] Implement path-to-natTrans conversion
- [x] Implement natTrans-to-path conversion
- [x] Prove isomorphism (strict, with refined GADT)
- [x] Prove full end characterization

### Isomorphism Status

The path/natTrans correspondence has been established with a **strict**
isomorphism (no quotient needed):

```text
NegPosNatEndDirNT i ≅ NegPosNatEndDirPath i
```

This was achieved by refining the `NpnpLeftChoice` type to a GADT that tracks
whether choices are meaningful:

- `LeftForced`: When left subtree has no positions, the choice is forced
- `LeftDirect hasPos`: When positions exist, chose direct value
- `LeftRecurse hasPos path`: When positions exist, chose to recurse

The position witness ensures that `LeftDirect` and `LeftRecurse` can only be
constructed when there are actual positions in the left subtree, eliminating
the redundant representations that previously required a quotient.

**Computational Technique - `with` Clause Forcing**: We discovered that using
nested `with` clauses to force polynomial functor destructuring allows the
pattern matching in eliminators to fire. For example:

```idris
elimIntroNpnppNodeLeftBeta dm x r leftCase rightCase recLeftPos getX recurseLeft
  with (pfProductArena PFIdentityArena (NpnppRecLeftPF dm)) proof prodPFEq
    elimIntroNpnppNodeLeftBeta ... | (leftPFPos ** leftPFDir)
      with (NpnppRecLeftPF dm) proof recLeftPFEq
        elimIntroNpnppNodeLeftBeta ... | ... | (recLeftPFPos ** recLeftPFDir)
          with (NpnppRecRightPF dm) proof recRightPFEq
            elimIntroNpnppNodeLeftBeta ... | ... | ... | (...) = Refl
```

This technique forces Idris to destructure the polynomial functors before
applying the eliminator, allowing the beta-reduction to happen definitionally.

**Remaining `believe_me` usages**: ~12 remain, primarily for:
- `closedPathToNatTransLeftBeta`: case expressions don't reduce automatically
- `closedPathConstFalse` node case: uses `elimNpnppNodeDependent` (believe_me
  bridges gap between decomposed components and original `allFalse` proof)
- `probePathAtLeftRecurse`: simplified to direct `believe_me` with documented
  reasoning chain (was previously using `with` clauses that still needed
  `believe_me`)
- `elimNpnppNodeDependent`: bridges gap between `P elem` and `P (introNpnppNode...)`
- `pathToNatTransToPath` node case
- `natTransToPathToNatTrans`
- `npneDirIsoFwd/npneDirIsoBwd`: direction isomorphisms (2)
- End characterization lemmas (5): `endPosIsClosed`, `endDirFromClosedPath`,
  `endToClosedPathToEnd`, `closedPathToEndToClosedPath`, plus wedge proof

**Refactoring Summary** (December 2024):

The `with` clause pattern was analyzed across all usages:

1. **Functions that now avoid `with` clauses**:
   - `closedPathConstFalse`: Refactored to use `elimNpnppNodeDependent` with
     `believe_me` for bridging decomposed components to original proof context
   - `probePathAtLeftRecurse`: Simplified to direct `believe_me` with documented
     reasoning chain (4-step reduction via beta lemmas)

2. **Functions that MUST keep `with` clauses** (they enable `Refl`):
   - `npnppNodePosIsEither`: Proves position type equals explicit Either
   - `elimIntroNpnppNodeLeftBeta`: Beta rule for left intro
   - `elimIntroNpnppNodeRightBeta`: Beta rule for right intro
   - `closedPathToNatTransRightBeta`: Beta rule for nat trans on right elements
   - `probePathAtLeftDirect`: Proof that probing at direct choice returns True

These beta lemmas are **foundational** - they provide the computational reductions
that other proofs build upon. The `with` clauses force polynomial functor types
to compute, enabling `Refl` to work where it otherwise wouldn't.

**Fundamental Limitation - `with` Clause Type Abstraction**: A core issue blocks
many `believe_me` eliminations. When using `with` clauses to force polynomial
functor evaluation:

```idris
with (NpnppRecRightPF dm) proof recRightPFEq
  ... | (recRightPFPos ** recRightPFDir) = ...
```

The types are abstracted to fresh variables (`recRightPFPos`, `recRightPFDir`)
that are only **propositionally** equal to the originals (via `recRightPFEq`),
not **definitionally** equal. When we try to make a recursive call:

- The goal uses abstracted types: `rightPos : recRightPFPos`
- The recursive function expects original types:
  `pos : pfPos (NpnppRecRightPF dm)`

Even though `recRightPFEq` proves these are equal, Idris can't use this
propositional equality to unify the types. The `rewrite` tactic doesn't help
because the goal type itself is expressed in terms of the abstracted types.

**Potential Solutions** (not yet implemented):
1. Restructure functions to take polynomial functor shapes as explicit type
   parameters, threading them through recursion
2. Use well-founded recursion instead of structural recursion
3. Create auxiliary lemmas that bridge the type gap explicitly
4. **API-based approach** (PREFERRED - see detailed section below)

## API-Based Approach to Polynomial Functor Proofs

### The Core Problem

The `with` clause type abstraction problem arises because we're **breaking
abstraction** - we pattern match on the internal structure of polynomial
functor interpretations (`InterpPolyFunc`), which causes Idris to introduce
fresh type variables that are only propositionally (not definitionally) equal
to the original types.

### The Solution: Universal Properties

Instead of interacting with structures via pattern matching on their details,
we should define **complete introduction and elimination APIs** in the style
of:
- Type system rules (intro/elim rules for each type former)
- Category theory (universal morphisms, adjunctions)

Users should **never pattern match** on `InterpPolyFunc` directly. Instead,
they interact with structures only through:
1. **Introduction forms** - ways to construct elements
2. **Elimination forms** - ways to consume elements
3. **Beta rules** - how eliminators compute on introducers
4. **Eta rules** - uniqueness of morphisms (when applicable)

### Architecture for NPN Node Polynomial Functor

For `NpnppNodePF dm = pfCoproductArena (NpnppNodeLeftPF dm) (NpnppRecRightPF dm)`:

#### Introduction Forms (Already Exist)
```idris
introNpnppNodeLeft : (dm : ...) -> (x : Type) ->
  (recLeftPos : pfPos (NpnppRecLeftPF dm)) ->
  (getX : x) ->
  (recurseLeft : pfDir {p=NpnppRecLeftPF dm} recLeftPos -> x) ->
  InterpPolyFunc (NpnppNodePF dm) x

introNpnppNodeRight : (dm : ...) -> (x : Type) ->
  (recRightPos : pfPos (NpnppRecRightPF dm)) ->
  (recurseRight : pfDir {p=NpnppRecRightPF dm} recRightPos -> x) ->
  InterpPolyFunc (NpnppNodePF dm) x
```

#### Elimination Form (Already Exists)
```idris
elimNpnppNodeInterp : (dm : ...) -> (x : Type) -> (r : Type) ->
  (leftCase : (recLeftPos : ...) -> (getX : x) ->
              (recurseLeft : ... -> x) -> r) ->
  (rightCase : (recRightPos : ...) ->
               (recurseRight : ... -> x) -> r) ->
  InterpPolyFunc (NpnppNodePF dm) x -> r
```

#### Beta Rules (Already Exist)
```idris
elimIntroNpnppNodeLeftBeta :
  elimNpnppNodeInterp dm x r leftCase rightCase
    (introNpnppNodeLeft dm x recLeftPos getX recurseLeft)
  = leftCase recLeftPos getX recurseLeft

elimIntroNpnppNodeRightBeta :
  elimNpnppNodeInterp dm x r leftCase rightCase
    (introNpnppNodeRight dm x recRightPos recurseRight)
  = rightCase recRightPos recurseRight
```

#### What's Missing: Eta Rule / Case Analysis Principle

We need a lemma that says: **every element is either a left or right intro**.
This allows us to do case analysis without pattern matching:

```idris
npnppNodeCases : (dm : ...) -> (x : Type) ->
  (elem : InterpPolyFunc (NpnppNodePF dm) x) ->
  Either
    (recLeftPos : pfPos (NpnppRecLeftPF dm) **
     getX : x **
     recurseLeft : (pfDir {p=NpnppRecLeftPF dm} recLeftPos -> x) **
     elem = introNpnppNodeLeft dm x recLeftPos getX recurseLeft)
    (recRightPos : pfPos (NpnppRecRightPF dm) **
     recurseRight : (pfDir {p=NpnppRecRightPF dm} recRightPos -> x) **
     elem = introNpnppNodeRight dm x recRightPos recurseRight)
```

With this, we can prove things about arbitrary elements by:
1. Use `npnppNodeCases` to get either a left or right decomposition
2. In each case, we have `elem = intro...`, so we can substitute
3. Then the beta rules apply, giving us computational content

### Refactoring `closedPathConstFalse`

Currently uses `with` clauses to force pattern matching:
```idris
closedPathConstFalse ... pos dirFn allFalse
  with (pfProductArena ...) proof eq
    ... | (leftPFPos ** leftPFDir) = ... believe_me ...
```

Should instead be:
```idris
closedPathConstFalse ... elem allFalse =
  case npnppNodeCases dm Bool elem of
    Left (recLeftPos ** getX ** recurseLeft ** elemEq) =>
      -- elem = introNpnppNodeLeft dm Bool recLeftPos getX recurseLeft
      -- Use this equality to rewrite the goal, then apply beta rules
      rewrite elemEq in
        ... use closedPathToNatTransLeftBeta ... recurse ...
    Right (recRightPos ** recurseRight ** elemEq) =>
      rewrite elemEq in
        ... use closedPathToNatTransRightBeta ... recurse ...
```

### Benefits of This Approach

1. **No type abstraction problem**: We never use `with` clauses on polynomial
   functor structures, so no fresh type variables are introduced.

2. **Composable proofs**: Beta rules compose naturally. If `f` and `g` both
   satisfy beta rules, then `f ∘ g` does too.

3. **Cleaner architecture**: The API clearly separates:
   - Structure definition (intro/elim forms)
   - Computational content (beta rules)
   - Proof obligations (eta/uniqueness)

4. **Reusable across different polynomial functors**: The same pattern applies
   to any polynomial functor combinator (coproduct, product, etc.).

### Implementation Plan

1. **Define `npnppNodeCases`**: The eta/case-analysis principle for node PF
   - ✅ COMPLETED (with `believe_me` internally)
2. **Define similar case principles** for other PF combinators as needed
3. **Refactor `closedPathConstFalse`** to use case principles instead of `with`
   - ✅ COMPLETED - Uses `elimNpnppNodeDependent` instead of `with` clauses
4. **Refactor `probePathAtLeftRecurse`** similarly
   - ✅ COMPLETED - Removed nested `with` clauses, simplified to direct
     `believe_me` with documented reasoning chain
5. **Refactor other functions** that use `with` clause pattern matching
   - ✅ COMPLETED - Analyzed remaining `with` uses; they are fundamental beta
     lemmas (`elimIntroNpnppNodeLeftBeta`, `elimIntroNpnppNodeRightBeta`,
     `closedPathToNatTransRightBeta`, `probePathAtLeftDirect`) that DO need
     `with` clauses to enable `Refl`
6. **Remove `believe_me`** calls as the API-based proofs go through
   - ONGOING - Some `believe_me` are fundamental (see analysis below)

### Implementation Status: `npnppNodeCases`

We implemented `npnppNodeCases` using a **dependent eliminator** approach:

```idris
-- Dependent eliminator that gives P elem by case analysis
elimNpnppNodeDependent :
  (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
  (x : Type) ->
  (P : InterpPolyFunc (NpnppNodePF dm) x -> Type) ->
  (leftCase : ... -> P (introNpnppNodeLeft dm x ...)) ->
  (rightCase : ... -> P (introNpnppNodeRight dm x ...)) ->
  (elem : InterpPolyFunc (NpnppNodePF dm) x) ->
  P elem

-- Case analysis returning Either with equality proofs
npnppNodeCases :
  (fext : FunExt) -> (dm : ...) -> (x : Type) ->
  (elem : InterpPolyFunc (NpnppNodePF dm) x) ->
  Either (NpnppNodeLeftCase dm x elem) (NpnppNodeRightCase dm x elem)
```

**Key Finding**: The dependent eliminator uses `believe_me` internally because:
- `elimNpnppNodeInterp` decomposes `elem` into components
- These components, when passed to `introNpnppNodeLeft/Right`, reconstruct `elem`
- However, Idris doesn't see this as *definitional* equality due to:
  1. Polynomial functor types being computed through multiple layers
  2. Direction function eta-expansion (case expressions don't reduce)
- The propositional equality holds, but bridging it requires `believe_me`

**Why Direct Pattern Matching Fails**: We tried multiple approaches:
1. Pattern match on `fst elem` as `Left ((), recLeftPos)` → "Can't match on ()"
2. Use `with` clauses to force PF computation → Type abstraction problem
3. Separate position argument with explicit Either type → Type mismatch between
   `pfCoproductPos ...` and `Either ...`

The fundamental issue is that Idris doesn't automatically compute polynomial
functor types through their combinators (`pfCoproductArena`, `pfProductArena`).

### Key Insight

The fundamental insight is: **don't expose internal structure**. Polynomial
functors are abstract data types. Their internals (dependent pairs, Either,
etc.) are implementation details. The correct interface is through universal
properties (intro/elim/beta/eta), not through pattern matching.

This is the same principle as:
- Church encodings (data = its eliminator)
- Categorical universal properties (objects defined by morphisms, not elements)
- Abstract algebra (groups defined by operations and laws, not by representation)

**New Beta Lemmas for `closedPathToNatTrans`**: We created lemmas showing how
`closedPathToNatTrans` reduces on specific element forms:

- `closedPathToNatTransRightBeta`: Shows reduction on `introNpnppNodeRight`
  elements. Compiles with `Refl` using nested `with` clauses.
- `closedPathToNatTransLeftBeta`: Shows reduction on `introNpnppNodeLeft`
  elements. Uses `believe_me` because the direction function constructed by
  `introNpnppNodeLeft` involves case expressions that Idris doesn't reduce.

The right beta lemma enabled eliminating `believe_me` from
`closedPathConstFalseRight` by composing `trans betaStep inductionHypothesis`.

**Case Expression Reduction Issue**: When `introNpnppNodeLeft` constructs:
```idris
\d => case d of Left () => getX; Right rd => recurseLeft rd
```
The case expression `case Left () of { Left () => a; Right _ => b }` doesn't
reduce to `a` automatically. This blocks the left beta lemma from compiling
with `Refl`.

### Full End Characterization

The full end characterization has been established:

```text
NegPosNatEnd ≅ NegPosNatEndClosedPath
            = (i : NegPosNatEndFst Unit **
               (NpnpIsClosed i, NegPosNatEndDirPath i))
```

This characterizes closed PHOAS terms as:

1. A term shape (position `i` at Unit)
2. A proof that all leaves are closed (`NpnpIsClosed i`)
3. A path through the term structure (`NegPosNatEndDirPath i`)

Key components:

- `closedPathToEnd`: Converts a closed path to an end element
- `endToClosedPath`: Converts an end element (with wedge condition) to a
  closed path
- `npneDirIsoFwd/npneDirIsoBwd`: Direction isomorphism between
  `NegPosNatEndDir a (npnePosFromUnitFst i a)` and `NegPosNatEndDirUnit i a`

The forward direction (`endToClosedPath`) requires the wedge condition, which
is implicit in the definition of the end. The backward direction
(`closedPathToEnd`) produces elements that automatically satisfy the wedge
condition.

## Implementation Notes

### Pattern Matching Challenges (Resolved)

The implementation of `pathToNatTrans` for the FS FZ (node) case encountered
significant challenges with Idris's pattern matching on dependent types.

The issue was that the polynomial functor interpretation type:

```idris
InterpPolyFunc (NpnppNodePF dm) x
  = (i : pfCoproductPos P Q ** pfCoproductDir P Q i -> x)
```

does not reduce at the type level in a way that allows pattern matching on
the `Either` structure. Specifically:

1. `pfCoproductPos P Q` computes to `Either (fst P) (fst Q)`, but Idris
   doesn't see this as a literal `Either` for pattern matching purposes.

2. Pattern matching on `Left` or `Right` in the dependent pair's first
   component doesn't refine the type of the second component appropriately.

### Solution: Combinator-Style Programming

The solution was to avoid pattern matching entirely and instead use a
**combinator-style** (point-free) approach. Key components:

1. **Eliminators**: Functions that encapsulate case analysis on complex types.
   - `elimNpnppNodeInterp`: Dispatches on Left/Right cases of node elements
   - Pattern matching happens at the definition site where types are concrete

2. **Introduction forms**: Functions that construct elements of complex types.
   - `introNpnppNodeLeft`, `introNpnppNodeRight`: Construct node elements
   - Handle type-level computations internally

3. **API-based position handling**: Instead of relying on type reduction,
   use existing APIs from PolyCat.idr:
   - `polyInjLOnPos`, `polyInjROnPos`: Map positions into coproduct positions
   - These APIs pattern match at the definition site where types are concrete

### natTransToPath Implementation

The inverse direction (`natTransToPath`) uses probing to determine which path
the natural transformation takes:

1. **Probing**: Apply the nat trans at type `Bool` with test values to
   determine if it uses the direct value or recurses.

2. **Position extraction**: `anyPositionNPNE` finds a position to use for
   probing, returning `Nothing` if the position type is `Void` (in which case
   the only option is to use the direct value).

3. **Mutual recursion**: `determineLeftChoice` and `natTransToPath` are
   mutually recursive.

### Special Cases

- **PFVar case**: Represents open terms (just a variable). A nat trans from
  `const Unit` to `id` is impossible to implement. This case is excluded
  by requiring an `NpnpIsClosed` proof, which has no constructor for PFVar.
  The case is marked `impossible` in `closedPathToNatTrans`.

- **FZ case**: Represents leaves with no variable occurrences. The direction
  type is `Void`, so `void` handles this case trivially.

### Closed Terms Constraint

The `NpnpIsClosed` predicate ensures a position has no PFVar nodes anywhere:

```idris
data NpnpIsClosed : NegPosNatEndFst Unit -> Type where
  IsClosedLeaf :
    (dm : NPNPPdirFZ -> NegPosNatEndFst Unit) ->
    NpnpIsClosed (InPFM (PFCom FZ) dm)
  IsClosedNode :
    (dm : NPNPPdirFSFZ -> NegPosNatEndFst Unit) ->
    (leftClosed : NpnpIsClosed (dm NpnppDirLeft)) ->
    (rightClosed : NpnpIsClosed (dm NpnppDirRight)) ->
    NpnpIsClosed (InPFM (PFCom (FS FZ)) dm)
```

This allows `closedPathToNatTrans` to mark the PFVar case as `impossible`,
avoiding the need for `believe_me`.
