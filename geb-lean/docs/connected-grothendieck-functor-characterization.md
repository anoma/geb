<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Functor Characterization for Connected Grothendieck Constructions](#functor-characterization-for-connected-grothendieck-constructions)
  - [Background](#background)
  - [The Diagonal Construction](#the-diagonal-construction)
  - [FunctorToConnGrothendieckData](#functortoconngrothendieckdata)
    - [Components](#components)
    - [Construction](#construction)
    - [Extraction](#extraction)
    - [Round-trip Theorems](#round-trip-theorems)
  - [FunctorFromConnGrothendieckData](#functorfromconngrothendieckdata)
    - [Structure](#structure)
    - [Alternative Formulation](#alternative-formulation)
  - [FunctorBetweenConnGrothendieckData](#functorbetweenconngrothendieckdata)
    - [Same Base Category (C = C)](#same-base-category-c--c)
    - [Different Base Categories](#different-base-categories)
  - [Implementation Notes](#implementation-notes)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Functor Characterization for Connected Grothendieck Constructions

This document describes the introduction and elimination rules for functors
to, from, and between connected Grothendieck constructions.

## Background

For the standard Grothendieck construction `Grothendieck F` where `F : C ⥤ Cat`,
we have:

- **FunctorToData**: Characterizes functors `D ⥤ Grothendieck F` via a base
  functor `D ⥤ C`, fiber objects, fiber morphisms, and coherence conditions.

- **FunctorFromData**: Characterizes functors `Grothendieck F ⥤ E` via fiber
  functors `F.obj c ⥤ E` for each `c`, natural transformations, and coherence.

- **FunctorBetweenData**: Characterizes functors
  `Grothendieck G ⥤ Grothendieck F` via a base functor, fiber-to-fiber
  functors, and cross-fiber morphisms.

The connected Grothendieck construction is built from two nested Grothendieck
constructions:

```text
ConnectedGrothendieckAlt C F = GrothendieckContra' (domainFiberFunctor C F)
```

where `domainFiberFunctor C F : C^op ⥤ Cat` sends `a` to
`Grothendieck (restrictToDomainFiber C F a)`.

This construction projects to `Arrow C` via `connGrothendieckAltProjection`.

## The Diagonal Construction

A morphism in `ConnectedGrothendieckAlt C F` from `(arr, e)` to `(arr', e')`
where `arr, arr' : Arrow C` and `e, e'` are fiber elements consists of:

1. An Arrow morphism `(alpha, beta) : arr -> arr'` forming a commutative square:

   ```text
   arr.left ---arr.hom--> arr.right
      |                      |
    alpha                  beta
      v                      v
   arr'.left --arr'.hom-> arr'.right
   ```

2. A fiber morphism via the **diagonal construction**:
   - The diagonal `w = arr.hom >> beta = alpha >> arr'.hom` is another arrow
   - There are canonical TwistedArrow morphisms:
     - `tw_arr : TwistedArrow.mk' arr.hom -> TwistedArrow.mk' w` via
       `(id, beta)`
     - `tw_arr' : TwistedArrow.mk' arr'.hom -> TwistedArrow.mk' w` via
       `(alpha, id)`
   - Since `F : TwistedArrow' C ⥤ Cat` is covariant, both fibers transport into
     `F.obj (TwistedArrow.mk' w)`:
     - `(F.map tw_arr).obj e` in `F.obj (TwistedArrow.mk' w)`
     - `(F.map tw_arr').obj e'` in `F.obj (TwistedArrow.mk' w)`
   - The fiber morphism is: `(F.map tw_arr).obj e -> (F.map tw_arr').obj e'`

## FunctorToConnGrothendieckData

Data specifying a functor `D ⥤ ConnectedGrothendieckAlt C F`:

### Components

1. **Arrow functor** `arrFun : D ⥤ Arrow C`
   - Assigns to each `d : D` an arrow `arrFun.obj d : Arrow C`
   - Maps morphisms to Arrow morphisms (commutative squares)

2. **Fiber objects**
   `fiberObj : (d : D) -> F.obj (arrowToTwistedArrow' (arrFun.obj d))`
   - For each `d`, a fiber element over the corresponding twisted arrow

3. **Fiber morphisms** via the diagonal:
   - For each `g : d -> d'`, let `(alpha, beta) = arrFun.map g`
   - Let `w` be the diagonal arrow, with `tw_d`, `tw_d'` the canonical morphisms
   - `fiberMap g : (F.map tw_d).obj (fiberObj d) ->`
     `(F.map tw_d').obj (fiberObj d')`

4. **Identity coherence**: `fiberMap (id d)` equals identity (up to transport)

5. **Composition coherence**: `fiberMap (g >> h)` decomposes correctly

### Construction

Given `FunctorToConnGrothendieckData`, construct `functorToConnGrothendieck`:

- **Objects**: `d |-> (arrFun.obj d, fiberObj d)` (viewed in connected Grothendieck)
- **Morphisms**: `g |-> (arrFun.map g, fiberMap g)` (with appropriate transport)

### Extraction

Given `G : D ⥤ ConnectedGrothendieckAlt C F`, extract `ofFunctorToConnGrothendieck`:

- `arrFun := G >> connGrothendieckAltProjection`
- `fiberObj d := (G.obj d).fiber.fiber`
- `fiberMap g` extracted from `(G.map g).fiber`

### Round-trip Theorems

- `functorToConnGrothendieck (ofFunctorToConnGrothendieck G) = G`
- `ofFunctorToConnGrothendieck (functorToConnGrothendieck data) = data`

## FunctorFromConnGrothendieckData

Data specifying a functor `ConnectedGrothendieckAlt C F ⥤ E`.

Since `ConnectedGrothendieckAlt C F = GrothendieckContra'`
`(domainFiberFunctor C F)`, this specializes
`GrothendieckContra'.FunctorFromData`.

### Structure

1. **Fiber functors**: For each `a : C`, a functor
   `innerFiberAlt C F a ⥤ E`
   where `innerFiberAlt C F a = Grothendieck (restrictToDomainFiber C F a)`

2. **Natural transformations**: For each `f : a' -> a` in C, a natural
   transformation relating the fiber functors via domain transport

3. **Coherence**: Identity and composition conditions

### Alternative Formulation

Equivalently, using the Arrow projection:

1. **Arrow-indexed fibers**: For each `arr : Arrow C`, a functor
   `F.obj (arrowToTwistedArrow' arr) ⥤ E`

2. **Diagonal compatibility**: For each Arrow morphism, compatible
   transformations via the diagonal construction

3. **Coherence conditions**

## FunctorBetweenConnGrothendieckData

### Same Base Category (C = C)

For `ConnectedGrothendieckAlt C F ⥤ ConnectedGrothendieckAlt C G`:

**Complete characterization**: Natural transformations `alpha : F -> G`

The functor is `connGrothendieckAltMap C alpha`, which:

- Preserves the Arrow projection (identity on Arrow C)
- Acts by `alpha` on fibers

This is already implemented:

- `connGrothendieckAltMap` takes `(F -> G)` and produces
  `ConnectedGrothendieckAlt C F ⥤ ConnectedGrothendieckAlt C G`
- `connGrothendieckAltFunctor` is the full functor
  `(TwistedArrow' C ⥤ Cat) ⥤ Over (Cat.of (Arrow C))`

**Equivalence theorem**: `(F -> G) ≃ FunctorBetweenData C F G` where functors
preserve the projection to Arrow C.

### Different Base Categories

For `ConnectedGrothendieckAlt C F ⥤ ConnectedGrothendieckAlt C' G`:

Components:

1. **Arrow functor** `Arrow C ⥤ Arrow C'`
2. **Fiber transformation** compatible with the arrow functor
3. **Diagonal compatibility**

This requires `GrothendieckContra'.FunctorBetweenData`
specialized to the domain fiber functors.

## Implementation Notes

The implementation builds on existing infrastructure:

1. `arrowToTwistedArrow' : Arrow C ⥤ TwistedArrow' C` - converts arrows to
   twisted arrows

2. `connGrothendieckAltProjection : ConnectedGrothendieckAlt C F ⥤ Arrow C` -
   the projection functor

3. `GrothendieckContra'.FunctorFromData` - existing characterization for
   contravariant Grothendieck

4. `connGrothendieckAltFunctor` - existing functoriality for natural
   transformations

The diagonal construction helpers need to be defined:

- `arrowDiagonal : Arrow.Hom arr arr' -> Arrow C` - the diagonal arrow
- `arrowToDiagonalLeft`, `arrowToDiagonalRight` - canonical TwistedArrow
  morphisms
