# Weighted Wedges via Diagonal Elements

## Problem Statement

We have defined `WeightedWedge` and `WeightedCowedge` as weighted cones and
weighted cocones over specific functors derived from profunctors (via the
twisted arrow category). There is a known result that weighted cones/cocones
can be defined as ordinary cones/cocones using the category of elements of
the weight functor.

The question: can we find a category K with an endoprofunctor Q such that
ordinary wedges/cowedges over Q are equivalent to weighted wedges/cowedges?
If so, this would validate our definitions by showing that two different
approaches (via weighted cones and via ordinary wedges) yield equivalent
categories.

## Current Definitions

From `GebLean/Weighted.lean`:

```lean
abbrev WeightedWedge (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) :=
  WeightedCone (C := D) (J := TwistedArrow C)
    (profunctorOnTwistedArrow C W) (profunctorOnTwistedArrow C P)

abbrev WeightedCowedge (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) :=
  WeightedCocone (C := D) (J := CoTwistedArrow C)
    (profunctorOnOpCoTwistedArrow C W)
    (profunctorOnCoTwistedArrow C P)
```

So:

- `WeightedWedge W P` is a weighted cone over `TwistedArrow C` with weight
  `profunctorOnTwistedArrow C W` and diagram `profunctorOnTwistedArrow C P`
- `WeightedCocone W D` has weight `W : Jᵒᵖ ⥤ Type v` (a presheaf) and consists
  of a natural transformation `W ⟶ homToFunctor D pt`

## Background: Reductions

### Weighted Cones to Ordinary Cones

For a weight `W : J ⥤ Type v` and diagram `D : J ⥤ C`:

```text
WeightedCone W D ≅ Cone (D ∘ π)
```

where `π : El(W) → J` is the projection from the category of elements.

### Wedges to Cones

For a profunctor `P : Cᵒᵖ ⥤ C ⥤ D`:

```text
Wedge P ≅ Cone (profunctorOnTwistedArrow C P)
```

where `Tw(C) = El(Hom_C)` is the twisted arrow category (the category of
elements of the hom profunctor).

## Four Candidates

The question suggests four possibilities for the base category K:

1. `El(W)` - Category of elements of the weight profunctor
2. `El(W)` for wedges, `El(W)ᵒᵖ` for cowedges
3. `DiagElem W` - Category of diagonal elements of the weight profunctor
4. `DiagElem W` for wedges, `(DiagElem W)ᵒᵖ` for cowedges

## Analysis

### Structure of WeightedWedge

A `WeightedWedge W P` consists of:

- An apex `pt : D`
- For each `tw ∈ TwistedArrow C` and `w ∈ W(twDom, twCod)`, a morphism
  `leg(tw, w) : pt ⟶ P(twDom, twCod)`
- Naturality along morphisms in `TwistedArrow C`

The indexing is by `El(profunctorOnTwistedArrow C W)`, which has:

- Objects: pairs `(f : c → d, w)` where `w ∈ W(c, d)`
- Morphisms: `(u, v) : (f, w) → (g, w')` where `(u, v)` is a morphism in
  `Tw(C)` and the weight is preserved

### Structure of Ordinary Wedges

An ordinary wedge for `Q : Kᵒᵖ ⥤ K ⥤ D` consists of:

- An apex `pt : D`
- For each `k : K`, a morphism `π_k : pt ⟶ Q(k, k)`
- Wedge condition: for `f : k₁ ⟶ k₂`, the covariant and contravariant
  actions agree

The indexing is by objects of K (at the diagonal).

### Why DiagElem W is the Natural Choice

For a wedge over `K = DiagElem W`:

- Objects of `DiagElem W` are pairs `(c, w)` where `w ∈ W(c, c)`
- This matches the "diagonal" components of a weighted wedge

If we define `Q = P ∘ (forget × forget)` where `forget : DiagElem W → C`:

- `Q((c, w), (c, w)) = P(c, c)`
- Components would be `π_{(c,w)} : pt ⟶ P(c, c)` for each diagonal element

The wedge condition for a morphism `f : (c₁, w₁) ⟶ (c₂, w₂)` in `DiagElem W`:

```text
P(id, f.base) ∘ π_{(c₁,w₁)} = P(f.base, id) ∘ π_{(c₂,w₂)}
```

This is the dinaturality/wedge condition restricted to morphisms that are
compatible with the weight profunctor.

### The Indexing Mismatch

There is a fundamental mismatch:

- `WeightedWedge W P` has components at ALL twisted arrows with weight data
- Ordinary wedges on `DiagElem W` only have components at DIAGONAL elements

However, the naturality condition of weighted wedges
might determine the non-diagonal components from the diagonal ones.

For a weighted cone, the leg at `(f : c → d, w)` can be computed from legs
at simpler twisted arrows via naturality.

### Proposed Approach

Define:

- `WeightedWedge' W P := Wedge (pullbackProfunctor (DiagElem.forget W) P)`

where `pullbackProfunctor F P` is the profunctor on `DiagElem W` defined by:

```text
(pullbackProfunctor F P).obj (op x) :=
  fun y => P.obj (op (F.obj x)) |>.obj (F.obj y)
```

The equivalence would need to show:

1. Every weighted wedge restricts to a wedge on `DiagElem W`
2. Every wedge on `DiagElem W` extends uniquely to a weighted wedge
3. These operations are inverse functors

## Tasks

### 1. Define the Pullback Profunctor

Define `pullbackProfunctor : (K ⥤ C) → (Cᵒᵖ ⥤ C ⥤ D) → (Kᵒᵖ ⥤ K ⥤ D)`
that pulls back a profunctor along a functor.

### 2. Define WeightedWedge' and WeightedCowedge'

```lean
abbrev WeightedWedge' (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) :=
  Wedge (pullbackProfunctor (DiagElem.forget W) P)

abbrev WeightedCowedge' (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) :=
  Cowedge (pullbackProfunctor (DiagElem.forget W) P)
```

### 3. Construct Restriction Functor

`restrict : WeightedWedge W P ⥤ WeightedWedge' W P`

Takes a weighted wedge and restricts to diagonal components.

### 4. Construct Extension Functor

`extend : WeightedWedge' W P ⥤ WeightedWedge W P`

Takes a wedge on `DiagElem W` and extends to all twisted arrows using the
naturality data.

### 5. Prove Equivalence

Show that `restrict` and `extend` form an equivalence of categories.

## Status

- [ ] Task 1: Define pullback profunctor
- [ ] Task 2: Define WeightedWedge' and WeightedCowedge'
- [ ] Task 3: Construct restriction functor
- [ ] Task 4: Construct extension functor
- [ ] Task 5: Prove equivalence
