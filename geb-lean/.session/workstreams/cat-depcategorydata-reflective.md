# Cat to DepCategoryData Reflective Inclusion

## Status: In Progress

Building a fully faithful reflective inclusion from `Cat` (mathlib's category of
categories) into `DepCategoryData`.

## Current Progress

### Completed

1. `DepCategoryCat.lean`: Refactored to use stacked subcategory chain:
   - `DepCompleteCL` = FullSubcategory of `DepCompleteObj` with `CategoryLaws`
   - `DepCompleteUCL` = FullSubcategory of `DepCompleteCL` with `Unique`
   - `DepCategoryCat` = FullSubcategory of `DepCompleteUCL` with `WitnessSubsingleton`
   - Built equivalence `DepCategoryCat ≃ Cat`
   - Inclusion functors come automatically from mathlib's `ObjectProperty.ι`

2. `DepCategoryAdjunction.lean`: Updated for the stacked structure:
   - `truncateWitnessesFunctor` truncates witness types via `Quotient trueSetoid`
   - `truncateUCLAdjunction` is the adjunction `truncateUCLFunctor ⊣ DepCategoryCat.ι`
   - `depCategoryCatι_reflective` is the `Reflective` instance

### In Progress

Building the next reflective inclusion: `DepCompleteUCL ⊆ DepCompleteCL`.

## Architecture

The stacked subcategory structure:

```text
DepCompleteObj  (has Exists)
    |
    | HasCategoryLaws.ι (fully faithful)
    v
DepCompleteCL   (has Exists + CategoryLaws)
    |
    | DepCompleteCL.HasUnique.ι (fully faithful)
    v
DepCompleteUCL  (has Exists + CategoryLaws + Unique)
    |
    | DepCompleteUCL.HasWitnessSubsingleton.ι (fully faithful, reflective)
    v
DepCategoryCat  (has Exists + CategoryLaws + Unique + WitnessSubsingleton ≃ Cat)
```

The first reflective inclusion (`DepCategoryCat ⊆ DepCompleteUCL`) is complete.
The reflection works by truncating witness types to subsingletons via quotients.

## Remaining Reflective Inclusions

1. **`DepCompleteUCL ⊆ DepCompleteCL`**: Need to reflect Unique property by
   quotienting morphism types to make composites unique.

2. **`DepCompleteCL ⊆ DepCompleteObj`**: Need to reflect CategoryLaws - this may
   require a different approach since it involves ensuring the category laws hold.

3. **`DepCompleteObj ⊆ DepCategoryData`**: Need to reflect Exists - this adds
   identity and composition witnesses where they don't exist.

## Files

- `GebLean/DepCategoryCat.lean` - Stacked subcategory chain and Cat equivalence
- `GebLean/DepCategoryAdjunction.lean` - Reflective adjunctions
- `GebLean/DepCategoryJudgments.lean` - Property definitions
- `GebLean/Utilities/SetoidCat.lean` - Contains `Quotient.trueSetoid_subsingleton`
