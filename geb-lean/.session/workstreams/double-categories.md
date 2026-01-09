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

## In Progress

None currently.

## Planned Extensions

### Companions and Conjoints

- [ ] Define companion structure
- [ ] Define conjoint structure
- [ ] Prove relationship between companions and conjoints
- [ ] Connection to adjunctions

### Double Functors

- [ ] DoubleFunctorOps structure
- [ ] DoubleFunctorLaws structure
- [ ] DoubleFunctorData structure
- [ ] Composition of double functors
- [ ] Identity double functor

### Natural Transformations

- [ ] Horizontal natural transformation
- [ ] Vertical natural transformation
- [ ] Relationship between them

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
