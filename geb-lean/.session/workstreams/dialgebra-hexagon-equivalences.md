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

### 4. Profunctors Derived from Functors

For a functor `F : C -> D`, there are two approaches to derive profunctors on
`Dop x C`:

#### Approach A: Forgetful profunctor (projection)

```text
F' : Dop x C -> Type v
F'(d, c) = F.obj c
```

This ignores the contravariant argument entirely. It is precomposition of F
with the second projection `Dop x C -> C`.

For endo-profunctors on C (i.e., when D = C), this requires `F : C -> Type v`
(so that `F.obj c` lives in Type).

#### Approach B: Representable profunctor

```text
D(1,F) : Dop x C -> Type v
D(1,F)(d, c) = Hom_D(d, F.obj c)
```

This is the standard nlab definition of representable profunctor for
`F : C -> D`. The contravariant argument `d` comes from D, not from C.
The hom-set `Hom_D(d, F.obj c)` lives in Type (the enriching category),
making this a valid profunctor.

For endo-profunctors on C (when D = C), this becomes `C(1,F)(a, c) = Hom(a, F c)`.

#### Analysis for Dialgebra Equivalence

For `HexagonCat`, we need endo-profunctors `P, Q : Cop x C -> Type v`.

**Approach A with `F : C -> Type v`**: Setting `P(a,c) = F.obj c` and
`Q(a,c) = G.obj c`:

- `Prof.map1 P m` = identity (contravariant action is trivial)
- `Prof.map2 P m` = `F.map m` (covariant action)

The hexagon condition `P(m,1) . f . Q(1,m) = P(1,m) . g . Q(m,1)` becomes:
`id . f . G.map m = F.map m . g . id`, which simplifies to
`f . G.map m = F.map m . g` -- the dialgebra morphism condition.

**Approach B with `F : C -> C`**: Setting `P(a,c) = Hom(a, F.obj c)`:

The diagonal `P(c,c) = Hom(c, F.obj c)` is a hom-set, not a single element.
A diagonal element would pick out a morphism `c -> F.obj c` for each `c`,
which is a *coalgebra* structure, not an algebra. The hexagon condition
for morphisms would relate to coalgebra morphisms, not dialgebras.

**Conclusion**: Approach A (forgetful/projection profunctor) with functors
`F, G : C -> Type v` is correct for the dialgebra equivalence.

The `ProjProf` utility in `Profunctors.lean` implements Approach A.

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

When `P = ProjProf F` and `Q = ProjProf G` for `F, G : C -> Type v`:

- `P(a, c) = F.obj c` (ignores contravariant argument)
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
