# Decorated Factorisation Category

## Status: COMPLETE

The `decFactCategory` Category instance and `decFactFunctor` in
`GebLean/Factorization.lean` are fully implemented with no errors,
warnings, sorries, or underscores.

## Completed Components

1. **Object type**: `DecFactObj F tw` - decorated objects over a factorisation
2. **Morphism type**: `DecFactHom F tw` - decorated morphisms with fiber maps
3. **Composition**: `decFactComp` - composition of decorated morphisms
4. **Identity**: `decFactId` - identity decorated morphism
5. **Category laws**:
   - `decFact_id_comp`: identity is left unit
   - `decFact_comp_id`: identity is right unit
   - `decFact_comp_assoc`: composition is associative
6. **Functor components**:
   - `decFactMapObj`: object map (fiber unchanged since midpoint preserved)
   - `decFactMapHom`: morphism map (fiberMorph unchanged since h preserved)
   - `decFactMap`: functor between decorated factorisation categories
7. **Cat-valued functor**: `decFactFunctor : TwistedArrow C ⥤ Cat`
   generalizing `factorisationFunctor` with fiber data from `F`
8. **Fiber accessors** (Phase 1):
   - `DecFactObj.fiberAtι`: fiber transported to `F(twObjMk ι)`
   - `DecFactObj.fiberAtπ`: fiber transported to `F(twObjMk π)`
   - `DecFactObj.fiberToArrMorph`: twisted arrow morphism from
     `twObjMk (𝟙 mid)` to `tw` via ι-path
   - `DecFactObj.fiberToArrMorphViaπ`: same via π-path
   - `DecFactObj.fiberAtArr`: fiber transported to `F(tw)`
   - `DecFactObj.fiberToArrMorph_eq_viaπ`: two paths agree
9. **Morphism accessors** (Phase 2):
   - `DecFactHom.fiberMorphAtι`: fiberMorph transported via
     `twExtendDom x.ι h`
   - `DecFactHom.fiberMorphAtπ`: fiberMorph transported via
     `twExtendCod h y.π`
   - `DecFactHom.fiberMorphToArrMorph`: twisted arrow morphism
     from `twObjMk h` to `tw`
   - `DecFactHom.fiberMorphAtArr`: fiberMorph transported to
     `F(tw)`
10. **Total decorated factorisation category** (Phase 3):
    - `TotalDecFactObj C F`: extends `TotalFactObj` with fiber
    - `TotalDecFactHom C F`: extends `TotalFactHom` with
      fiberMorph
    - `totalDecFactCategory`: Category instance
11. **Grothendieck equivalence** (Phase 4):
    - `TotalDecFactGrothendieck C F`: abbreviation for
      `TwGrothendieckObj C (decFactFunctor F)`
    - `totalDecFactGrothendieckEquivObj`: type equivalence
    - `totalDecFactToGrothendieck`,
      `grothendieckToTotalDecFact`: functors
    - `totalDecFactEquivGrothendieck`: `Equivalence`
      (category equivalence, not just Cat isomorphism)
    - `grothendieckHomToTotalDecFactHom`,
      `totalDecFactHomToGrothendieckHom`: morphism
      translations
    - `decFact_hom_heq`: cross-type HEq for
      `DecFactHom` across different twisted arrows

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

### Functor proof technique

The `decFactFunctor` proofs (`map_id`, `map_comp`) use `Functor.ext` which
introduces `eqToHom` sandwich terms. The `decFact_eqToHom_sandwich_fiberMorph_heq`
lemma handles the fiberMorph HEq by `subst`-ing both equality proofs (which
collapses the `eqToHom` terms to `eqToHom rfl`), then using `Category.id_comp`
and `Category.comp_id` to eliminate them, and `rw` to close the HEq goal.
This works because `decFactMapHom` preserves fiberMorph definitionally.
