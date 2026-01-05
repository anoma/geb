# Dialgebra and Hexagon Category Equivalences

## Status: Active

## Overview

This workstream establishes equivalences between:

1. `DiagElem (DialgebraProf F G)` and the `Dialgebra F G` category
2. `HexagonCat` for functor-derived profunctors and `DiagElem (DialgebraProf F G)`
3. Composition giving `HexagonCat` equivalent to `Dialgebra F G`

## Background

### Mathlib Status (verified 2026-01-05)

Mathlib has:

- `Endofunctor.Algebra F` for endofunctors F : C -> C
- `Endofunctor.Coalgebra F` for endofunctors F : C -> C

Mathlib does NOT have:

- `Dialgebra F G` for pairs of functors F, G : C -> D

### Existing Infrastructure

In `ParanatAlg.lean`:

- `DialgebraProf F G : Cop x C -> Type v` - the dialgebra profunctor
- `AlgProf F` and `CoalgProf F` with equivalences to mathlib categories
- Pattern for proving `DiagElem` equivalences

In `HexagonCat.lean`:

- `HexagonObj P Q` - objects of the hexagon category for profunctors P, Q
- `HexagonHom` - morphisms satisfying the hexagon condition
- `Category` instance on `HexagonObj P Q`
- `ProfDialgebraProf P Q` - the profunctor-dialgebra profunctor
- Equivalence `HexagonObj P Q` equivalent to `DiagElem (ProfDialgebraProf P Q)`

## Tasks

### 1. Define Dialgebra Category

Define `Dialgebra F G` for functors `F, G : C -> D`:

- Objects: pairs `(A, phi : F.obj A -> G.obj A)`
- Morphisms: `m : A -> B` such that `G.map m . phi = psi . F.map m`

This generalizes both:

- `Algebra F` (when G = identity)
- `Coalgebra F` (when F = identity)

### 2. Prove DiagElem(DialgebraProf) equivalent to Dialgebra

Follow the pattern from `diagElemAlgEquiv` and `diagElemCoalgEquiv`:

- Define conversion functions both directions
- Define functor both directions
- Construct unit and counit isomorphisms
- Build the equivalence

### 3. Name HexagonCat Instance

Give the `Category (HexagonObj P Q)` instance a name `HexagonCat` for clarity.

### 4. Covariant Projection Profunctor

For functors `F, G : C -> D`, there are two approaches to derive profunctors:

#### Approach A: Forget contravariant argument

```text
F' : Cop x C -> Type v
F'(a, b) = F.obj b
```

This is precomposition with the second projection `Cop x C -> C`.

#### Approach B: Representable endo-profunctor

```text
F' : Cop x C -> Type v
F'(a, b) = Hom_D(F.obj a, F.obj b)
```

Note: The nlab definition of representable profunctor for `f : C -> D` is
`D(1,f)(d, c) = Hom_D(d, f(c))`, where `d` is in D and `c` is in C. This is
a profunctor `Dop x C -> Set` (not `Cop x C`). The hom-set `Hom_D(d, f(c))`
lives in Type (the enriching category), making this a valid profunctor.
For endo-profunctors on C derived from `F : C -> D`, the natural analogues
are either Approach A (ignoring the contravariant argument, requiring
`F : C -> Type v`) or the hom-functor construction above (applying F to
both arguments, valid for any `F : C -> D`).

#### Analysis

**Approach A is correct for dialgebras**: With `P(a,b) = F.obj b` and
`Q(a,b) = G.obj b`:

- `Prof.map1 P m` = identity (contravariant action is trivial)
- `Prof.map2 P m` = `F.map m` (covariant action)

The hexagon condition `P(m,1) . f . Q(1,m) = P(1,m) . g . Q(m,1)` becomes:
`id . f . G.map m = F.map m . g . id`, which simplifies to
`f . G.map m = F.map m . g` -- the dialgebra morphism condition.

**Approach B gives a different structure**: The diagonal
`P(c,c) = Hom_D(F.obj c, F.obj c)` is a hom-set, not a single object.
A diagonal transformation `P(c,c) -> Q(c,c)` would be a function
`Hom_D(F c, F c) -> Hom_D(G c, G c)`, which is not a dialgebra structure.

**Conclusion**: Approach A is the correct one for the dialgebra equivalence.

Next step: Check if mathlib has the second projection functor
`Cop x C -> C`. If not, define it in `Utilities/Category.lean`.

### 5. HexagonCat equivalent to DiagElem(DialgebraProf)

For profunctors `P = F'` and `Q = G'` derived from functors F, G:

- Show `HexagonObj F' G'` is equivalent to `DiagElem (DialgebraProf F G)`
- The hexagon condition should simplify when P, Q ignore contravariant args

### 6. Compose Equivalences

Chain the equivalences:

```text
HexagonCat F' G' ---(step 5)---> DiagElem(DialgebraProf F G)
                 ---(step 2)---> Dialgebra F G
```

## Implementation Notes

### Dialgebra Morphism Condition

For `Dialgebra F G`, a morphism `m : (A, phi) -> (B, psi)` satisfies:

```text
      F.obj A ---phi---> G.obj A
         |                  |
      F.map m            G.map m
         |                  |
         v                  v
      F.obj B ---psi---> G.obj B
```

Commutes: `G.map m . phi = psi . F.map m`

### Hexagon Condition Simplification

When P and Q ignore the contravariant argument:

- `Prof.map1 P m` = identity (contravariant action is trivial)
- `Prof.map2 P m` = `F.map m` (covariant action)

The hexagon condition `P(m,1) . f . Q(1,m) = P(1,m) . g . Q(m,1)` becomes:

```text
id . f . G.map m = F.map m . g . id
```

Which is exactly `f . G.map m = F.map m . g`, the dialgebra morphism condition.

## Context Files

- `GebLean/ParanatAlg.lean` - add Dialgebra section
- `GebLean/HexagonCat.lean` - add HexagonCat name and functor section
- `GebLean/Utilities/Category.lean` - possibly add projection functor
