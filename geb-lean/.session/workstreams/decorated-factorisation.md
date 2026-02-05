# Decorated Factorisation Category

## Status: COMPLETE

The `decFactCategory` Category instance in `GebLean/Factorization.lean` is fully
implemented with no errors, warnings, sorries, or underscores.

## Completed Components

1. **Object type**: `DecFactObj F tw` - decorated objects over a factorisation
2. **Morphism type**: `DecFactHom F tw` - decorated morphisms with fiber maps
3. **Composition**: `decFactComp` - composition of decorated morphisms
4. **Identity**: `decFactId` - identity decorated morphism
5. **Category laws**:
   - `decFact_id_comp`: identity is left unit
   - `decFact_comp_id`: identity is right unit
   - `decFact_comp_assoc`: composition is associative

## Proof Technique Summary

The associativity proof required the factoring-out-lemmas technique:

1. **Transform lemmas**: `assoc_fM_transform`, `assoc_gM_transform`,
   `assoc_hM_transform` establish how each fiber component transforms under
   associativity using `eqToHom` and `Cat.eqToHom_map_heq`.

2. **Object HEq lemmas**: `assoc_obj_heq_extendCod`, `assoc_obj_heq_interchange`,
   `assoc_obj_heq_extendDom` establish object-level HEq for the functor images
   using `eqToHom_obj_heq`.

3. **Core combiner**: `decFact_assoc_core` combines category equality, object
   HEqs, and morphism HEqs into the full 6-composition HEq using `heq_comp`.

4. **Explicit version**: `decFact_comp_assoc_fiber_explicit` orchestrates all
   the pieces, stripping eqToHom terms and applying the core lemma.

5. **Main proof**: `decFact_comp_assoc` uses `decFactHom_ext` to combine
   factorisation associativity with fiber associativity.
