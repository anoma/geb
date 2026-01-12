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
- [x] sqVComp_heq_both, sqHComp_heq_both (HEq for both square arguments)
- [x] VertTransOps.id_laws (VertTransLaws for identity vertical transformation)
- [x] VertTransOps.vComp_laws (VertTransLaws for vertical composition)
- [x] VertTransOps.hComp_laws (VertTransLaws for Godement product)
- [x] HorTransOps.id_laws (HorTransLaws for identity horizontal transformation)
- [x] HorTransOps.hComp_laws (HorTransLaws for horizontal composition)
- [x] HorTransOps.vComp_laws (HorTransLaws for Godement product)
- [x] DoubleFunctorOps category axioms (comp_id_right, comp_id_left, comp_assoc)
- [x] DoubleFunctorLaws.id (identity functor satisfies laws)
- [x] DoubleFunctorLaws.comp (composition preserves laws)
- [x] DoubleFunctorData.id and DoubleFunctorData.comp
- [x] DoubleFunctorData category axioms (comp_id_right, comp_id_left, comp_assoc)

## In Progress

None currently.

## Planned Extensions

### Companions and Conjoints

- [x] Define Companion structure
- [x] Define Conjoint structure
- [x] HasCompanions class
- [x] HasConjoints class
- [x] Companion.ofVId (companion of vertical identity)
- [x] Conjoint.ofVId (conjoint of vertical identity)
- [x] Documentation with diagrams
- [x] Companion.comp (companion of composite is composite of companions)
- [x] Conjoint.comp (conjoint of composite is composite of conjoints in reverse)
- [x] sqHComp_heq_all (HEq congruence when all boundaries change)
- [ ] Prove relationship between companions and conjoints
- [ ] Connection to adjunctions

### Transformation Composition Laws (Completed)

All transformation composition operations now have laws proving they preserve
the transformation structure:

- [x] VertTransLaws for id, vComp, and hComp
- [x] HorTransLaws for id, hComp, and vComp
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
