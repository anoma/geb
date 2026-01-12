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

Godement product (cross-direction composition) category axioms:

- `VertTransOps.hComp_id_left_heq` - hComp (id Id) σ ≅ σ
- `VertTransOps.hComp_id_right_heq` - hComp τ (id Id) ≅ τ
- `VertTransOps.hComp_assoc_heq` - hComp (hComp τ σ) ρ ≅ hComp τ (hComp σ ρ)
- `HorTransOps.vComp_id_left_heq` - vComp (id Id) σ ≅ σ
- `HorTransOps.vComp_id_right_heq` - vComp τ (id Id) ≅ τ
- `HorTransOps.vComp_assoc_heq` - vComp (vComp τ σ) ρ ≅ vComp τ (vComp σ ρ)

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

## Companions and Conjoints

Companions and conjoints relate vertical and horizontal morphisms in a
double category. They provide a way to "translate" between the two kinds
of morphisms while preserving structure.

### Companions

A companion for a vertical morphism `v : A →ᵥ B` is a horizontal morphism
`v* : A →ₕ B` going in the same direction, together with two binding
squares satisfying an identity condition.

```text
        hId A             hor
     A ───────→ A      A ───────→ B
     |         |       |         |
vId A│    φ    │v    v │    ψ    │ vId B
     ↓         ↓       ↓         ↓
     A ───────→ B      B ───────→ B
        hor              hId B
```

The binding squares φ and ψ compose vertically:

```text
        hId A
     A ───────→ A
     |         |
vId A│    φ    │v
     ↓         ↓
     A ───────→ B
     |   hor   |
   v │    ψ    │ vId B
     ↓         ↓
     B ───────→ B
        hId B
```

The identity condition states: `φ ⬝ᵥ ψ ≅ sqHorId v`.

This uses heterogeneous equality (HEq) because the boundaries differ:
`φ ⬝ᵥ ψ` has vertical boundaries `(vComp (vId A) v, vComp v (vId B))`
while `sqHorId v` has boundaries `(v, v)`. These are propositionally
equal by the identity laws but not definitionally equal.

Implementation:

- `Companion` - Structure with `hor`, `phi`, `psi`, and `identity` fields
- `HasCompanions` - Class for double categories where every vertical
  morphism has a companion
- `Companion.ofVId` - The companion of a vertical identity is the
  horizontal identity

### Conjoints

A conjoint for a vertical morphism `v : A →ᵥ B` is a horizontal morphism
`v_* : B →ₕ A` going in the opposite direction, together with two binding
squares satisfying an identity condition.

```text
        hor             hId A
     B ───────→ A      A ───────→ A
     |         |       |         |
vId B│    ε    │v    v │    η    │ vId A
     ↓         ↓       ↓         ↓
     B ───────→ B      B ───────→ A
        hId B             hor
```

The binding squares ε and η compose horizontally:

```text
           hor             hId A
        B ───────→ A ───────→ A
        |         |         |
   vId B│    ε    │v   η    │ vId A
        ↓         ↓         ↓
        B ───────→ B ───────→ A
           hId B       hor
```

The identity condition states: `ε ⬝ₕ η ≅ sqVertId hor`.

This again uses HEq because `ε ⬝ₕ η` has horizontal boundaries
`(hComp hor (hId A), hComp (hId B) hor)` while `sqVertId hor` has
boundaries `(hor, hor)`.

Implementation:

- `Conjoint` - Structure with `hor`, `epsilon`, `eta`, and `identity`
  fields
- `HasConjoints` - Class for double categories where every vertical
  morphism has a conjoint
- `Conjoint.ofVId` - The conjoint of a vertical identity is the
  horizontal identity

### Companion vs Conjoint

The distinction between companions and conjoints lies in:

1. Direction: Companions go the same direction as the vertical morphism
   (A →ₕ B), conjoints go the opposite direction (B →ₕ A)

2. Composition: Companion binding squares compose vertically, conjoint
   binding squares compose horizontally

3. Duality: In a double category with duality, conjoints in one
   direction correspond to companions in the opposite direction

### Example: Identity Morphisms

For any vertical identity `vId A`, both the companion and conjoint are
the horizontal identity `hId A`:

- `Companion.ofVId A` gives companion `hId A` with binding squares
  `sqVertId (hId A)` for both φ and ψ
- `Conjoint.ofVId A` gives conjoint `hId A` with binding squares
  `sqVertId (hId A)` for both ε and η

The identity conditions use the `sqVIdComp` law (for companions) and
`horIdHComp` law (for conjoints) to verify that composing identity
squares yields the appropriate identity square.

### Composition of Companions and Conjoints

Companions and conjoints are preserved by vertical composition:

- `Companion.comp`: Given `v : A →ᵥ B` with companion `v* : A →ₕ B` and
  `w : B →ᵥ C` with companion `w* : B →ₕ C`, the composite `vComp v w`
  has companion `hComp v* w* : A →ₕ C`. The binding squares are
  constructed by pasting the individual binding squares.

- `Conjoint.comp`: Given `v : A →ᵥ B` with conjoint `v_* : B →ₕ A` and
  `w : B →ᵥ C` with conjoint `w_* : C →ₕ B`, the composite `vComp v w`
  has conjoint `hComp w_* v_* : C →ₕ A` (note the reversed order). The
  binding squares are constructed by pasting.

The proofs of the identity conditions for composed companions/conjoints
require the interchange law and several HEq congruence lemmas including
`sqVComp_heq_both`, `sqHComp_heq_both`, and `sqHComp_heq_all`.

### Companion-Conjoint Adjunction

When a vertical morphism `v : A →ᵥ B` has both a companion `v* : A →ₕ B`
and a conjoint `v_* : B →ₕ A`, their binding squares compose to form
unit and counit squares that establish an adjunction `v* ⊣ v_*` in the
horizontal bicategory.

The binding squares are:

- φ : sqs (vId A) v (hId A) v* (companion)
- ψ : sqs v (vId B) v* (hId B) (companion)
- ε : sqs (vId B) v v_* (hId B) (conjoint)
- η : sqs v (vId A) (hId A) v_* (conjoint)

The compositions that form the adjunction:

- `adjunctionUnit`: φ ⬝ₕ η gives a square from `hId A` to `v* ⬝ v_*`
- `adjunctionCounit`: ε ⬝ₕ ψ gives a square from `v_* ⬝ v*` to `hId B`

Additional compositions:

- `psiHCompEpsilon`: ψ ⬝ₕ ε gives a square from `v* ⬝ v_*` to `hId B`
  with vertical boundary `v` on both sides
- `etaHCompPhi`: η ⬝ₕ φ gives a square from `hId A` to `v_* ⬝ v*`
  with vertical boundary `v` on both sides

Primed versions (`adjunctionUnit'`, etc.) apply identity laws to simplify
the types.

#### Triangle Identities

The triangle identities express that whiskering unit/counit by the companion
or conjoint and composing vertically yields identity squares. These are the
coherence conditions that make `v* ⊣ v_*` a proper adjunction.

**Right triangle (for v*):**

```text
     sqVComp (unitWhiskerRight'' ⬝ᵥ counitWhiskerLeft') = sqVertId v*
```

The constructions:

- `unitWhiskerRight`: adjunctionUnit' ⬝ₕ sqVertId `v*` (raw)
- `unitWhiskerRight'`: applies identity law to get top boundary `v*`
- `unitWhiskerRight''`: applies associativity for bottom boundary
- `counitWhiskerLeft`: sqVertId `v*` ⬝ₕ adjunctionCounit' (raw)
- `counitWhiskerLeft'`: applies identity law to get bottom boundary `v*`
- `rightTriangleComposite`: the vertical composite of whiskered unit and counit

**Left triangle (for v_*):**

```text
     sqVComp (unitWhiskerLeftConj' ⬝ᵥ counitWhiskerRightConj'') = sqVertId v_*
```

The constructions mirror the right triangle with `v_*` in place of `v*`.

## Modifications

Modifications are 2-cells between natural transformations in a double
category, providing structure for a 3-categorical view of double
categories, functors, transformations, and modifications.

### Vertical Modifications

A modification Γ : τ ⟹ σ between vertical transformations τ, σ : F ⟹ᵥ G
assigns to each object A a square relating τ_A and σ_A:

```text
       hId F(A)
    F(A) ─────→ F(A)
     |           |
τ_A  │    Γ_A    │ σ_A
     ↓           ↓
    G(A) ─────→ G(A)
       hId G(A)
```

Implementation:

- `VertModOps` - Component squares for each object
- `VertModLaws` - Naturality: τ.natSquare(f) ⬝ₕ Γ_B ≅ Γ_A ⬝ₕ σ.natSquare(f)
- `VertModData` - Operations and laws bundled
- `VertModOps.id` - Identity modification on a transformation
- `VertModOps.hComp` - Horizontal composition of modifications

### Horizontal Modifications

A modification Γ : τ ⟹ σ between horizontal transformations τ, σ : F ⟹ₕ G
assigns to each object A a square relating τ_A and σ_A:

```text
        τ_A
    F(A) ─────→ G(A)
     |           |
vId  │    Γ_A    │ vId
     ↓           ↓
    F(A) ─────→ G(A)
        σ_A
```

Implementation:

- `HorModOps` - Component squares for each object
- `HorModLaws` - Naturality: τ.natSquare(v) ⬝ᵥ Γ_B ≅ Γ_A ⬝ᵥ σ.natSquare(v)
- `HorModData` - Operations and laws bundled
- `HorModOps.id` - Identity modification on a transformation
- `HorModOps.vComp` - Vertical composition of modifications

## Future Extensions

The following extensions are planned for future development:

### Tabulators

Universal constructions in double categories analogous to limits.

### Weak Double Categories

Relaxing strictness to allow composition laws up to coherent isomorphism.

## References

- nLab: <https://ncatlab.org/nlab/show/double+category>
- Robert Paré's tutorial slides (docs/double-categories-dalhousie.pdf)
- UniMath StrictDoubleCats formalization
