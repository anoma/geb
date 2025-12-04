# Workstream: Generalized Polynomial Functors

## Status

Completed (Phase 1-3). Phase 4 is an optional extension.

## Context

The current `Polynomial.lean` defines polynomial functors with domain `Over X`
for `X : Type u`. However, the domain category can be generalized to an
arbitrary category `D`, with composition requiring constraints only on the
second functor.

This workstream generalizes the polynomial functor definitions to work with
arbitrary domain categories while preserving the existing W-type equivalence
as a specialization.

## Analysis Summary

### What Can Be Generalized

1. **Polynomial functors `D -> Type`**: The existing `CoprodCovarRepCat D`
   already works for any category `D`. No changes needed.

2. **Polynomial functors `D -> Over Y`**: Can be defined as
   `FamilyCat (CoprodCovarRepCat D) Y` for any category `D` and type `Y`.
   Evaluation works without constraints on `D`.

3. **Composition**: For `f ≫ g`:
   - `f : PolyFunctorBetween D Y` - arbitrary domain `D`
   - `g : PolyFunctorBetween (Over Y) Z` - domain MUST be `Over Y`
   - Result: `f ≫ g : PolyFunctorBetween D Z`

   Constraints:
   - `g`'s representables must be in `Over Y` (to index into `f` via `.hom`)
   - `D` must have "sigma-type structure" to construct the composed family.
     Specifically, we need to form `Σ eg, fiber(f, y, pf(eg))` which requires
     `D` objects to have total spaces (like `.left` in `Over X`). This is
     satisfied when `D = Over X`.

4. **W-type equivalence**: Specific to `Over X` for `X : Type u`. This
   stays specialized.

### Constraints Actually Used

- **For evaluation**: No special structure on `D` needed
- **For composition**:
  - Second functor (`g`) representables must be `Over Y` objects (for indexing)
  - First functor (`f`) domain `D` must be `Over X` (for sigma-type construction)
  - In practice, this means composition stays specialized to `Over X -> Over Y`
- **For W-types**: Full `Type` structure required

## Design

### New Type Aliases

```lean
-- Polynomial functor from D to Type (already exists as CoprodCovarRepCat)
abbrev PolyFunctorToTypeCat (D : Type u) [Category.{v} D] : Cat :=
  CoprodCovarRepCat D

-- Polynomial functor from D to Over Y
abbrev PolyFunctorToOverCat (D : Type u) [Category.{v} D] (Y : Type u) : Cat :=
  FamilyCat (CoprodCovarRepCat D) Y
```

### Generalized Evaluation

```lean
-- Evaluation for any domain D
def polyToTypeCatEval {D : Type u} [Category.{v} D]
    (P : PolyFunctorToTypeCat D) (A : D) : Type (max u v) :=
  Sigma (i : ccrIndex P), (ccrFamily P i --> A)

-- Evaluation producing Over Y
def polyToOverCatEval {D : Type u} [Category.{v} D] (Y : Type u)
    (P : PolyFunctorToOverCat D Y) (A : D) : Over Y :=
  (familySliceForward Y).obj (fun y => polyToTypeCatEval (P y) A)
```

### Generalized Composition

```lean
-- Composition with general first argument
-- Note: Lean convention uses ≫ (diagrammatic order), so f comes before g
def polyToOverComp {D : Type u} [Category.{v} D] {Y Z : Type u}
    (f : PolyFunctorToOverCat D Y)
    (g : PolyFunctorToOverCat (Over Y) Z) :
    PolyFunctorToOverCat D Z := ...
```

The key insight is that `g`'s representables are in `Over Y`, so
`(ccrFamily (g z) ig).hom eg : Y` provides the index into `f`.

### Specialized Definitions

The current `PolyFunctorCat X` and `PolyFunctorBetweenCat X Y` become
specializations:

```lean
abbrev PolyFunctorCat (X : Type u) : Cat :=
  PolyFunctorToTypeCat (Over X)

abbrev PolyFunctorBetweenCat (X Y : Type u) : Cat :=
  PolyFunctorToOverCat (Over X) Y
```

### Equivalence with FamilyCat Type X

Since `FamilyCat Type X ≌ Over X`, we should have:

```lean
def polyFunctorCatFamilyEquiv (X : Type u) :
    PolyFunctorToTypeCat (FamilyCat Type X) ≌ PolyFunctorToTypeCat (Over X)
```

## Implementation Plan

### Phase 1: Add General Type Aliases and Evaluation

1. Add `PolyFunctorToTypeCat D` as alias for `CoprodCovarRepCat D`
2. Add `PolyFunctorToOverCat D Y` as alias for `FamilyCat (CoprodCovarRepCat D) Y`
3. Define `polyToTypeCatEval` for general `D`
4. Define `polyToOverCatEval` for general `D` and `Y`
5. Add helper functions analogous to existing ones

### Phase 2: Generalize Composition

1. Define `polyToOverCompIndex` for general first argument
2. Define `polyToOverCompFamily` for general first argument
3. Define `polyToOverComp` combining these
4. Prove composition properties (associativity with identity)

### Phase 3: Refactor Existing Code

1. Redefine `PolyFunctorCat X` as `PolyFunctorToTypeCat (Over X)`
2. Redefine `PolyFunctorBetweenCat X Y` as `PolyFunctorToOverCat (Over X) Y`
3. Redefine `polyBetweenComp` in terms of `polyToOverComp`
4. Verify all existing lemmas still compile

### Phase 4: Equivalences

1. Prove `PolyFunctorToTypeCat (FamilyCat Type X) ≌ PolyFunctorToTypeCat (Over X)`
2. Prove `PolyFunctorToOverCat (FamilyCat Type X) Y` is equivalent to
   `PolyFunctorToOverCat (Over X) Y`

### Phase 5: Verify W-Type Equivalence

1. Ensure `WTypeDiagramCat X Y ≌ PolyFunctorBetweenCat X Y` still works
2. This should require no changes since it uses the specialized definitions

## Tasks

### Phase 1 (COMPLETED)

- [x] Add `ccrEval` for general domain evaluation
- [x] Add `PolyToOverCat` alias for `FamilyCat (CoprodCovarRepCat D) Y`
- [x] Define `polyToOverEvalFamily` and `polyToOverEval` for general domain
- [x] Add helper functions (`ptoefIndex`, `ptoefMor`, `ptoefMk`, `ptoeLeft*`)
- [x] Build and verify no regressions

### Phase 2 (SKIPPED - see constraints)

Composition cannot be fully generalized due to sigma-type construction
requirements. The existing `polyBetweenComp` stays specialized to `Over X`.

- [x] Document constraints in this file

### Phase 3 (COMPLETED)

Specialized definitions have been refactored as explicit specializations of the
generalized forms.

- [x] Refactor `PolyFunctorBetweenCat` as `PolyToOverCat (D := Over X) Y`
- [x] Refactor `polyBetweenEvalFamily` and `polyBetweenEval` to use
  `polyToOverEvalFamily` and `polyToOverEval`
- [x] Refactor `pbefIndex`, `pbefMor`, `pbefMk` to use `ptoefIndex`, `ptoefMor`,
  `ptoefMk`
- [x] Refactor `pbeLeftY`, `pbeLeftFiber`, `pbeLeftMk` to use `ptoeLeftY`,
  `ptoeLeftFiber`, `ptoeLeftMk`
- [x] Refactor `mor_to_pbe_*` functions to use `mor_to_ptoe_*` generalizations
- [x] Build and test

### Phase 4 (OPTIONAL)

- [ ] Define functor `FamilyCat Type X ≌ Over X` on CoprodCovarRep
- [ ] Prove equivalence of polynomial functor categories
- [ ] Build and verify

### Phase 5

- [x] Verify W-type equivalence still works (build passes)

## File Organization

The implementation will modify `GebLean/Polynomial.lean` with a new section
structure:

1. **Family-Slice Equivalence** (existing)
2. **General Polynomial Functors to Type** (new)
3. **General Polynomial Functors to Over Y** (new)
4. **Specialized Polynomial Functors** (refactored existing)
5. **Polynomial Functor Composition** (generalized)
6. **Identity and Composition Properties** (existing, updated)
7. **W-Type Diagrams** (existing)
8. **W-Type/Polynomial Equivalence** (existing)

## Notes

### Universe Levels

The implementation uses `universe u u'` where:

- `u` is the morphism universe level (required by `familySliceForward Y`)
- `u'` is the object universe level for the domain category `D`

The generalized definitions use `{D : Type u'} [Category.{u} D]` allowing `D`
to live at any universe level while constraining morphisms to level `u`. This
is required because `familySliceForward Y` needs `Y : Type u` and the family
to produce `Type u` values.

### Naming Convention

- `PolyFunctorToTypeCat` - general polynomial functor to Type
- `PolyFunctorToOverCat` - general polynomial functor to Over Y
- `PolyFunctorCat` - specialized to domain Over X (existing name)
- `PolyFunctorBetweenCat` - specialized to domain Over X (existing name)

### Backward Compatibility

All existing definitions and lemmas should continue to work after refactoring.
The specializations ensure that code using `PolyFunctorCat X` or
`PolyFunctorBetweenCat X Y` does not need modification.
