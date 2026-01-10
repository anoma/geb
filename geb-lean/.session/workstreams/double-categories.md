# Double Categories Workstream

Implementation of strict double categories and related structures.

## Completed

- [x] Basic type definitions (VertHomSet, HorHomSet, SquareSet)
- [x] Square operation types (VComp, HComp, VertId, HorId)
- [x] DoubleCategoryOps structure
- [x] Square law definitions (associativity, identity, interchange)
- [x] DoubleCategoryLaws and DoubleCategoryData structures
- [x] Category extraction functions (vertCategoryData, horCategoryData)
- [x] Mathlib Category instances (VertCategoryOfDoubleCategoryData,
      HorCategoryOfDoubleCategoryData)
- [x] Design document (docs/DoubleCategory.md)
- [x] DoubleFunctorOps structure
- [x] DoubleFunctorLaws structure (with DFPreserves* abbrevs)
- [x] DoubleFunctorData structure (with vertFunctorData, horFunctorData)
- [x] Vertical natural transformations (VertTransOps, VertTransLaws,
      VertTransData)
- [x] Horizontal natural transformations (HorTransOps, HorTransLaws,
      HorTransData)
- [x] DoubleFunctorOps.comp and DoubleFunctorOps.id
- [x] VertTransOps.id and HorTransOps.id (identity transformations)
- [x] VertTransOps.vComp (vertical composition of vertical transformations)
- [x] HorTransOps.hComp (horizontal composition of horizontal transformations)
- [x] VertTransOps.hComp (Godement product of vertical transformations)
- [x] HorTransOps.vComp (Godement product of horizontal transformations)
- [x] Category axioms for VertTransOps.vComp (identity, associativity - HEq)
- [x] Category axioms for HorTransOps.hComp (identity, associativity - HEq)
- [x] Helper lemmas (VertTransOps.heq_mk, HorTransOps.heq_mk,
      sqVIdComp_heq, sqVCompId_heq, sqVAssoc_heq, sqHIdComp_heq, etc.)
- [x] VertTransOps.interchange (interchange law for vertical transformations)
- [x] HorTransOps.interchange (interchange law for horizontal transformations)
- [x] HorTransSquareNaturality definition
- [x] sqVComp_heq_left, sqVComp_heq_right (HEq congruence for sqVComp)
- [x] sqHComp_heq_left, sqHComp_heq_right (HEq congruence for sqHComp)

## In Progress

None currently.

## Planned Extensions

### Companions and Conjoints

- [ ] Define companion structure
- [ ] Define conjoint structure
- [ ] Prove relationship between companions and conjoints
- [ ] Connection to adjunctions

### Double Functors (Laws for Composition)

- [ ] DoubleFunctorLaws for composed functors
- [ ] Identity and associativity laws for functor composition
- [ ] DoubleFunctorData for composed functors

### Transformation Composition Laws

- [ ] VertTransLaws for vComp and hComp
- [ ] HorTransLaws for hComp and vComp
- [ ] Identity and associativity laws for Godement products (hComp/vComp)

### Interchange Law for Transformations (Completed)

The interchange law for transformations relates the Godement product
to vertical/horizontal composition. The law:
`(τ ⬝ᵥ τ') ⬝ₕ (σ ⬝ᵥ σ') = (τ ⬝ₕ σ) ⬝ᵥ (τ' ⬝ₕ σ')`
holds when σ satisfies `VertTransLaws` (or `HorTransLaws` for horizontal).
These laws include the naturality conditions (`naturality` and
`squareNaturality`) that ensure intermediate components can be reordered.
See `VertTransOps.interchange` and `HorTransOps.interchange`.

### Modifications

- [ ] Modification between horizontal transformations
- [ ] Modification between vertical transformations

### Examples

- [ ] Rel (relations as horizontal, functions as vertical)
- [ ] Span (spans as horizontal, functions as vertical)
- [ ] Commutative squares in a category
- [ ] Quintets in a 2-category

### Advanced

- [ ] Tabulators
- [ ] Weak double categories (pseudo double categories)
- [ ] Double limits and colimits
- [ ] Connection to 2-categories and bicategories
