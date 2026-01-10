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

## Double Functors

A strict double functor between double categories preserves all structure
strictly. The implementation follows the Ops/Laws/Data pattern:

- `DoubleFunctorOps` - Object map, vertical/horizontal morphism maps, square
  map
- `DoubleFunctorLaws` - All preservation laws bundled
- `DoubleFunctorData` - Operations and laws bundled

Preservation properties (with `DF` prefix for explicit parameter versions):

- `DFPreservesVId`, `DFPreservesHId` - Identity preservation
- `DFPreservesVComp`, `DFPreservesHComp` - Composition preservation
- `DFPreservesSqVertId`, `DFPreservesSqHorId` - Square identity preservation
- `DFPreservesSqVComp`, `DFPreservesSqHComp` - Square composition preservation

Helper functions:

- `vertFunctorData`, `horFunctorData` - Extract ordinary functor data

## Natural Transformations

Two kinds of natural transformations exist between double functors, differing
in whether the components are vertical or horizontal morphisms.

### Vertical Transformations

A vertical transformation `τ : F ⟹ᵥ G` assigns to each object `A` a vertical
morphism `τ_A : F(A) →ᵥ G(A)` with naturality squares for horizontal
morphisms.

- `VertTransOps` - Components and naturality squares
- `VertTransLaws` - Naturality and coherence with identities and composition
- `VertTransData` - Operations and laws bundled

### Horizontal Transformations

A horizontal transformation `σ : F ⟹ₕ G` assigns to each object `A` a
horizontal morphism `σ_A : F(A) →ₕ G(A)` with naturality squares for
vertical morphisms.

- `HorTransOps` - Components and naturality squares
- `HorTransLaws` - Naturality and coherence with identities and composition
- `HorTransData` - Operations and laws bundled

### Composition of Transformations

Identity and composition operations for transformations:

- `VertTransOps.id` - Identity vertical transformation on a functor
- `HorTransOps.id` - Identity horizontal transformation on a functor
- `VertTransOps.vComp` - Vertical composition of vertical transformations
  (composing τ : F ⟹ᵥ G with σ : G ⟹ᵥ H)
- `HorTransOps.hComp` - Horizontal composition of horizontal transformations
  (composing τ : F ⟹ₕ G with σ : G ⟹ₕ H)
- `VertTransOps.hComp` - Godement product of vertical transformations
  (composing τ : F ⟹ᵥ G with σ : H ⟹ᵥ K to get (H∘F) ⟹ᵥ (K∘G))
- `HorTransOps.vComp` - Godement product of horizontal transformations
  (composing τ : F ⟹ₕ G with σ : H ⟹ₕ K to get (H∘F) ⟹ₕ (K∘G))

### Category Axioms for Transformation Composition

The category axioms (identity and associativity) for vComp and hComp hold
as heterogeneous equalities (HEq) rather than propositional equality (Eq).
This is because the transformation structures contain dependent types:
the natSquare field depends on the app field, so when two transformations
have equal app components but different expressions for them, their types
technically differ.

Helper lemmas:

- `VertTransOps.heq_mk`, `HorTransOps.heq_mk` - Construct HEq from
  component-wise equality/HEq
- `sqVIdComp_heq`, `sqVCompId_heq`, `sqVAssoc_heq` - Square law wrappers
- `sqHIdComp_heq`, `sqHCompId_heq`, `sqHAssoc_heq` - Square law wrappers

Category axioms:

- `VertTransOps.vComp_id_left_heq` - id ⬝ᵥ τ ≅ τ
- `VertTransOps.vComp_id_right_heq` - τ ⬝ᵥ id ≅ τ
- `VertTransOps.vComp_assoc_heq` - (τ ⬝ᵥ σ) ⬝ᵥ ρ ≅ τ ⬝ᵥ (σ ⬝ᵥ ρ)
- `HorTransOps.hComp_id_left_heq` - id ⬝ₕ τ ≅ τ
- `HorTransOps.hComp_id_right_heq` - τ ⬝ₕ id ≅ τ
- `HorTransOps.hComp_assoc_heq` - (τ ⬝ₕ σ) ⬝ₕ ρ ≅ τ ⬝ₕ (σ ⬝ₕ ρ)

## Double Functor Composition

Operations:

- `DoubleFunctorOps.comp` - Composition of double functor operations
- `DoubleFunctorOps.id` - Identity double functor operations
- `DoubleFunctorData.comp` - Composition of double functor data
- `DoubleFunctorData.id` - Identity double functor data

Category axioms (all proved by `rfl`):

- `DoubleFunctorOps.comp_id_right` - F ∘ id = F
- `DoubleFunctorOps.comp_id_left` - id ∘ F = F
- `DoubleFunctorOps.comp_assoc` - (F ∘ G) ∘ H = F ∘ (G ∘ H)
- `DoubleFunctorData.comp_id_right`, `comp_id_left`, `comp_assoc` - analogous

Laws:

- `DoubleFunctorLaws.id` - Identity functor satisfies DoubleFunctorLaws
- `DoubleFunctorLaws.comp` - Composition of functors satisfying laws also
  satisfies laws

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

### Modifications

2-cells between double natural transformations (vertical or horizontal).

### Tabulators

Universal constructions in double categories analogous to limits.

### Weak Double Categories

Relaxing strictness to allow composition laws up to coherent isomorphism.

## References

- nLab: <https://ncatlab.org/nlab/show/double+category>
- Robert Paré's tutorial slides (docs/double-categories-dalhousie.pdf)
- UniMath StrictDoubleCats formalization
