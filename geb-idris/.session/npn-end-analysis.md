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
- [ ] Prove isomorphism
- [ ] Prove full end characterization

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
