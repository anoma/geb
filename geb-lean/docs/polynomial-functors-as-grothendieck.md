# Polynomial Functors as Double Grothendieck Constructions

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Overview](#overview)
- [Polynomial Functors as Spans](#polynomial-functors-as-spans)
- [The Double Grothendieck Structure](#the-double-grothendieck-structure)
  - [First Layer: Position Grothendieck (p : E -> I)](#first-layer-position-grothendieck-p--e---i)
  - [Second Layer: Direction Grothendieck (d : E -> X)](#second-layer-direction-grothendieck-d--e---x)
- [Universal Properties: functorFrom and functorTo](#universal-properties-functorfrom-and-functorto)
  - [Introduction Rules (functorTo)](#introduction-rules-functorto)
  - [Elimination Rules (functorFrom)](#elimination-rules-functorfrom)
- [Polynomial Functors: Double Universal Property](#polynomial-functors-double-universal-property)
  - [Generic functorFrom for Polynomials](#generic-functorfrom-for-polynomials)
  - [Generic functorTo for Polynomials](#generic-functorto-for-polynomials)
  - [Generic functorBetween for Polynomials](#generic-functorbetween-for-polynomials)
- [The Evaluation Functor as Composition](#the-evaluation-functor-as-composition)
- [Implications for Our Formalization](#implications-for-our-formalization)
  - [Eliminate Low-Level Proofs](#eliminate-low-level-proofs)
  - [Universal Interface for Polynomial Operations](#universal-interface-for-polynomial-operations)
  - [Automatic Naturality](#automatic-naturality)
  - [Composition and Reuse](#composition-and-reuse)
- [The Free Monad Monad Example](#the-free-monad-monad-example)
- [Relationship to Existing Work](#relationship-to-existing-work)
  - [Grothendieck.lean](#grothendiecklean)
  - [PolyAdjunctions.lean](#polyadjunctionslean)
- [Summary](#summary)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## Overview

Polynomial functors have a deep relationship with Grothendieck constructions
that allows us to work with them at a high categorical level, avoiding manual
dependent type manipulations. This document explains the theory and its
practical implications for our formalization.

## Polynomial Functors as Spans

A polynomial functor `P : I ← E → X` is given by:

- A position functor `p : E → I`
- A direction functor `d : E → X`

This span induces a functor `P* : Type/I → Type/X` (the evaluation functor).

## The Double Grothendieck Structure

The evaluation can be understood as a composition of two Grothendieck
constructions:

### First Layer: Position Grothendieck (p : E -> I)

The position functor `p : E → I` gives a Grothendieck construction:

- Objects: `∫ᵖ E = Σ(i : I) × p⁻¹(i)` - pairs of positions and directions
- Morphisms: Fiber-preserving maps
- Projection: `π : ∫ᵖ E → I` forgetting the direction

This creates the slice category structure over `I`.

### Second Layer: Direction Grothendieck (d : E -> X)

The direction functor `d : E → X` gives another Grothendieck construction:

- Takes families over `I` (from first layer) to families over `X`
- Objects: `∫ᵈ(...) → X` - dependent sums over direction fibers
- The evaluation `P*(A)(x) = Σ(e : E with d(e) = x) × A(p(e))`

## Universal Properties: functorFrom and functorTo

Grothendieck constructions come with universal functors (see
`GebLean/Utilities/Grothendieck.lean`):

```lean
functorFrom : (F : C ⥤ Cat) → (C₀ : C) → (∫F C₀) ⥤ F.obj C₀
functorTo   : (F : C ⥤ Cat) → (C₀ : C) → F.obj C₀ ⥤ (∫F C₀)
```

These satisfy universal properties making them initial/terminal in appropriate
categories of functors.

### Introduction Rules (functorTo)

To define a functor **into** a Grothendieck construction, it suffices to:

1. Specify the base component (map to base category)
2. Specify the fiber components (maps to fibers)
3. Prove compatibility

The universal property of `functorTo` packages this data into a single functor.

### Elimination Rules (functorFrom)

To define a functor **from** a Grothendieck construction, it suffices to:

1. Define it on total space
2. Prove it respects the projection

The universal property of `functorFrom` guarantees the result is functorial.

## Polynomial Functors: Double Universal Property

Since polynomial functors are **double** Grothendieck constructions, we get
double universal properties:

### Generic functorFrom for Polynomials

To define `Poly(I,X) ⟹ G`:

1. Apply functorFrom for direction Grothendieck
2. This reduces to defining a map from the intermediate category
3. Apply functorFrom for position Grothendieck
4. This reduces to defining a map from `E` with compatibility conditions

**All naturality and functoriality is automatic from the universal properties.**

### Generic functorTo for Polynomials

To define `F ⟹ Poly(I,X)`:

1. Apply functorTo for position Grothendieck
2. This packages position and fiber data
3. Apply functorTo for direction Grothendieck
4. This completes the polynomial structure

**Again, all categorical properties are automatic.**

### Generic functorBetween for Polynomials

To define `Poly(I,X) ⟹ Poly(J,Y)`:

- Use functorFrom on source
- Use functorTo on target
- Compose through intermediate categories

This factors polynomial-to-polynomial maps through the universal properties of
both sides.

## The Evaluation Functor as Composition

Our current `polyBetweenEvalFunctor : PolyBetween I X ⥤ (Type/I ⥤ Type/X)`
should be factored as:

```text
Type/I
  → [functorFrom for position p]
  → (intermediate: families indexed by E)
  → [base change along p∘projection]
  → Type
  → [functorTo for direction d]
  → Type/X
```

The intermediate category is the slice over the position space, and transitions
are handled by the Grothendieck universal properties.

**Currently we define evaluation as a monolithic functor. This should be
refactored as a composition of functorFrom and functorTo.**

## Implications for Our Formalization

### Eliminate Low-Level Proofs

With generic functorFrom/To/Between for polynomials:

- **Never** manually manipulate dependent type transports
- **Never** prove naturality by hand
- **Never** match on internal representations

All such proofs are factored into the generic Grothendieck machinery and proven
once.

### Universal Interface for Polynomial Operations

Every operation involving polynomial functors should use:

- `functorFrom` when extracting information FROM polynomials
- `functorTo` when constructing polynomials FROM other data
- `functorBetween` when transforming between polynomial categories

Examples:

- Free monad representation: use functorFrom
- Free monad unit: use functorTo
- Free monad multiplication: use functorBetween

### Automatic Naturality

When operations are defined through functorFrom/To/Between:

- Naturality follows from composition of natural transformations
- Functoriality follows from functoriality of components
- Coherence follows from universal properties

We prove categorical properties at the abstract level, not concrete level.

### Composition and Reuse

Operations defined at the functorFrom/To/Between level:

- Compose naturally with other such operations
- Abstract over the specific polynomial
- Work uniformly across different polynomial constructions

This creates a library of reusable categorical constructions.

## The Free Monad Monad Example

The multiplication `Free(Free(P)) → Free(P)` is currently stuck on low-level
transport proofs. With the Grothendieck approach:

1. **Both sides are polynomial functors**, so use functorBetween
2. **Factor through intermediate categories** (families over tree positions)
3. **The join operation** is composition of functorFrom and functorTo
4. **Naturality** is automatic from functoriality of the constituent functors

No transport proofs needed - just categorical composition.

## Relationship to Existing Work

### Grothendieck.lean

Our `GebLean/Utilities/Grothendieck.lean` already has:

- Basic Grothendieck construction
- `functorFrom` and `functorTo`
- Universal properties

We need to extend this to:

- Double Grothendieck constructions
- Generic functorFrom/To/Between for polynomial functors
- Composition rules

### PolyAdjunctions.lean

Our `GebLean/PolyAdjunctions.lean` has various adjunctions between polynomial
categories. These should be:

- Refactored using functorFrom/To/Between
- Proven to satisfy universal properties
- Composed to build higher-level constructions

The existing `polyToType` and `polyToOver` should factor through the
Grothendieck functors.

## Summary

**Thesis**: Polynomial functors are double Grothendieck constructions, giving
them universal properties via functorFrom/To/Between.

**Implication**: Every operation on polynomial functors should be defined
through these universal functors, not by manual dependent type manipulation.

**Benefit**: Eliminates all low-level transport proofs, makes naturality
automatic, creates a reusable categorical API.

**Next Steps**: Implement generic functorFrom/To/Between for polynomial
functors in `PolyAdjunctions.lean`, then refactor all existing operations to
use them.
