# Strict Double Categories in GebLean

This document describes the design and implementation of strict double
categories in `GebLean/Utilities/DoubleCategory.lean`.

## Overview

A strict double category is a category internal to Cat, consisting of:

- A set of objects
- A category of vertical morphisms between objects
- A category of horizontal morphisms between objects
- Squares (2-cells) filling boundaries of four morphisms
- Two compositions for squares (vertical and horizontal)
- Two kinds of identity squares

The strictness means all composition laws hold as equalities (not just up
to isomorphism).

## Structure Hierarchy

The implementation follows the pattern established in `Category.lean`,
building up from type definitions to operation bundles to law bundles:

### Type Families

- `VertHomSet Obj` - Vertical morphism types
- `HorHomSet Obj` - Horizontal morphism types
- `SquareSet vhs hhs` - Square types indexed by boundary morphisms

### Operations

- `CompositionalStruct` (reused from Category.lean)
- `IdentityStruct` (reused from Category.lean)
- `SquareVCompStruct` - Vertical composition of squares
- `SquareHCompStruct` - Horizontal composition of squares
- `SquareVertIdStruct` - Vertical identity squares
- `SquareHorIdStruct` - Horizontal identity squares
- `DoubleCategoryOps` - All operations bundled

### Laws

- `SquareVAssocLaw`, `SquareHAssocLaw` - Associativity
- `SquareVIdCompLaw`, `SquareVCompIdLaw` - Vertical identity laws
- `SquareHIdCompLaw`, `SquareHCompIdLaw` - Horizontal identity laws
- `InterchangeLaw` - Coherence between compositions
- `VertIdVCompLaw`, `HorIdHCompLaw` - Identity squares compose
- `IdOnIdLaw` - Identity on identity
- `SquareLaws` - All square laws bundled
- `DoubleCategoryLaws` - All laws (morphisms + squares)

### Data

- `DoubleCategoryData` - Operations and laws bundled
- `vertCategoryData`, `horCategoryData` - Extract category data
- `VertCategoryOfDoubleCategoryData` - Mathlib Category instance
- `HorCategoryOfDoubleCategoryData` - Mathlib Category instance

## Universe Polymorphism

The implementation uses four universe variables:

- `u` - Objects
- `vMor` - Vertical morphisms
- `hMor` - Horizontal morphisms
- `sq` - Squares

This allows maximum flexibility in how the types are instantiated.

## The Interchange Law

The interchange law is the coherence condition for double categories.
For a 2x2 grid of squares:

```text
  α  | α'
  ───┼────
  β  | β'
```

The two ways to compose must be equal:

```text
(α ⬝ₕ α') ⬝ᵥ (β ⬝ₕ β') = (α ⬝ᵥ β) ⬝ₕ (α' ⬝ᵥ β')
```

## Future Extensions

The following extensions are planned for future development:

### Companions and Conjoints

A companion pair relates horizontal and vertical morphisms. Given a
vertical morphism `v : A →ᵥ B`, a companion is a horizontal morphism
`v* : A →ₕ B` with squares witnessing a specific relationship.

Conjoints are the dual notion.

### Double Functors

A double functor `F : D → E` between double categories consists of:

- Object map
- Vertical functor
- Horizontal functor
- Square map preserving all structure

### Horizontal and Vertical Transformations

Natural transformations adapted to the double category setting.

### Modifications

2-cells between double natural transformations.

### Tabulators

Universal constructions in double categories analogous to limits.

### Weak Double Categories

Relaxing strictness to allow composition laws up to coherent isomorphism.

## References

- nLab: <https://ncatlab.org/nlab/show/double+category>
- Robert Paré's tutorial slides (docs/double-categories-dalhousie.pdf)
- UniMath StrictDoubleCats formalization
