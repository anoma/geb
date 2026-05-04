# Comprehensive Factorization System

## References

- Street, R. and Walters, R. (1973). "The comprehensive
  factorization of a functor." *Bull. Amer. Math. Soc.*, 79(5),
  pp. 936-941.
- nLab: [comprehensive factorization system](
  https://ncatlab.org/nlab/show/comprehensive+factorization+system)

## Mathematical Description

Every functor `F : C -> D` admits two canonical factorizations:

### Version 1: (Final, Discrete Fibration)

```text
F = m . e
```

where:

- `e : C -> K.Elements` is a **final** functor
- `m : K.Elements -> D` is a **discrete fibration**
- `K : D^op -> Type` is the presheaf defined by
  `K(d) = pi_0(StructuredArrow d F) = pi_0(d / F)`

The presheaf `K` is obtained as the left Kan extension:
`K = Lan_{F^op}(!)` where `! : C^op -> Type` is the terminal
presheaf (constant at `PUnit`).

The factorization goes through the category of elements
`K.Elements`:

- Objects: pairs `(d, [sigma])` where `d : D` and
  `[sigma]` is a connected component of `StructuredArrow d F`
  (i.e., an element of `K(d)`)
- Morphisms from `(d, [sigma])` to `(d', [sigma'])`:
  morphisms `f : d -> d'` in `D` such that `K(f)([sigma']) = [sigma]`
  (i.e., the presheaf action maps `[sigma']` to `[sigma]`)

The functors:

- `e(c) = (F(c), [id_{F(c)}])` where `[id_{F(c)}]` is the
  connected component of the identity in
  `StructuredArrow (F(c)) F`
- `m(d, [sigma]) = d` (the forgetful functor from elements)

### Version 2: (Initial, Discrete Opfibration)

```text
F = m' . e'
```

where:

- `e' : C -> K'.Elements` is an **initial** functor
- `m' : K'.Elements -> D` is a **discrete opfibration**
- `K' : D -> Type` is the copresheaf defined by
  `K'(d) = pi_0(CostructuredArrow F d) = pi_0(F / d)`

The copresheaf `K'` is obtained as the right Kan extension:
`K' = Ran_F(!)` where `! : C -> Type` is the terminal
copresheaf.

## Mathlib Availability

### Available in mathlib

- `ConnectedComponents J` -- `ConnectedComponents.lean`
- `IsConnected` -- `IsConnected.lean`
- `Zigzag`, `Zag` -- `IsConnected.lean`
- `Functor.Final` -- `Limits/Final.lean`
- `Functor.Initial` -- `Limits/Final.lean`
- `leftKanExtension L F` -- `KanExtension/Basic.lean`
- `rightKanExtension L F` -- `KanExtension/Basic.lean`
- `pointwiseLeftKanExtension` -- `KanExtension/Pointwise.lean`
- `pointwiseRightKanExtension` -- `KanExtension/Pointwise.lean`
- `Functor.lan`, `Functor.ran` -- `KanExtension/Adjunction.lean`
- `StructuredArrow d F` -- `StructuredArrow/Basic.lean`
- `CostructuredArrow F d` -- `StructuredArrow/Basic.lean`
- `F.Elements` -- `Elements.lean`
- `structuredArrowEquivalence` -- `Elements.lean`
- `Grothendieck F` -- `Grothendieck.lean`
- `Functor.mapConnectedComponents` -- `ConnectedComponents.lean`
- `ConnectedComponents.typeToCatHomEquiv` -- same

### Requires our own definitions

- Discrete fibration: unique Cartesian lifts
- Discrete opfibration: unique cocartesian lifts
- Comprehensive factorization: the `(e, m)` construction

## Discrete Fibration Definition

A functor `p : E -> B` is a **discrete fibration** if for every
object `e : E` and morphism `f : b -> p(e)` in `B`, there
exists a unique morphism `f' : e' -> e` in `E` with
`p(f') = f`.

Equivalently: for each `b : B`, the fiber `p^{-1}(b)` is a
discrete category, and morphisms in `B` induce functions
between fibers.

Discrete fibrations over `B` are equivalent to presheaves
`B^op -> Type` via the Grothendieck construction. The
category of elements of a presheaf `F` is the total category
of the corresponding discrete fibration, and the projection
functor `F.Elements -> B` is the fibration.

Standard properties to verify:

1. The forgetful functor from `F.Elements` to `B` (for any
   presheaf `F`) is a discrete fibration.
2. Every discrete fibration is a Grothendieck fibration
   (in the sense of `IsFibered`).
3. Discrete fibrations are closed under composition.
4. A discrete fibration is faithful.

## Application to Weighted Cones

The comprehensive factorization connects to weighted cones
via:

```text
StrongRestrictedWedge G H
  ~= Wedge(diagElemProf G H)
  ~= Cone(TwArr(forget_H) >> profOnTwArr G)
  ~= WeightedCone(Lan_{TwArr(forget_H)}(!))(profOnTwArr G)
```

The weight `Lan_{TwArr(forget_H)}(!)` is the presheaf of
connected components arising from the comprehensive
factorization of `TwArr(forget_H)`.

The WeightedWedge construction uses `profOnTwArr H` as its
weight, which differs from this Kan-extension weight.
The Q2 counterexample (StrongRestricted vs Weighted on
`WalkingParallelPair`) reflects this difference.
