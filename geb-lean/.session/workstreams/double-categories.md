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

## In Progress

None currently.

## Planned Extensions

### Companions and Conjoints

- [ ] Define companion structure
- [ ] Define conjoint structure
- [ ] Prove relationship between companions and conjoints
- [ ] Connection to adjunctions

### Double Functors (Extended)

- [ ] Composition of double functors
- [ ] Identity double functor
- [ ] Category of double categories

### Natural Transformations (Extended)

- [ ] Vertical composition of vertical transformations
- [ ] Horizontal composition of vertical transformations
- [ ] Vertical composition of horizontal transformations
- [ ] Horizontal composition of horizontal transformations

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
