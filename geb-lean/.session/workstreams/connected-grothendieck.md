# Workstream: Connected Grothendieck Construction

## Status

Complete - nested Grothendieck approach implemented

## Context

The connected Grothendieck construction defines a functor
`E : Fun(Tw(C), Cat) -> Cat/Arr(C)` that assigns to each functor
`F : TwistedArrow C -> Cat` a category `E(F)` over the arrow category.

See `docs/connected-grothendieck-construction.md` for the mathematical
specification.

## Implementation

File: `GebLean/Utilities/ConnectedGrothendieck.lean`

### Approach: Nested Grothendieck Construction

The connected Grothendieck construction decomposes as two nested standard
Grothendieck constructions:

```text
E(F) = Grothendieck (fiberFunctor F)
where fiberFunctor F : C -> Cat is defined by
      fiberFunctor F b = Grothendieck (restrictToFiber F b)
```

This leverages mathlib's existing Grothendieck construction to get
associativity for free.

### Completed (Nested Approach)

1. Fiber inclusion functor `overOpToTwistedArrow b`
   - Type: `(Over b)^op -> TwistedArrow' C`
   - Maps `(f : a -> b)` to `f` as a twisted arrow
   - Maps morphisms `alpha : f -> g` in `(Over b)^op` to `(alpha, id b)`

2. Restriction functor `restrictToFiber F b = overOpToTwistedArrow b >> F`
   - Restricts `F : Tw(C) -> Cat` to the fiber over `b`

3. Fiber transport twisted arrow morphism `fiberTransportTwMorph beta ov`
   - Type: `twObjMk' ov.hom -> twObjMk' (ov.hom >> beta)`
   - The twisted arrow morphism `(id, beta)`
   - Used to transport fiber elements along base morphisms

4. Fiber transport functor `fiberTransport beta ov`
   - Transports elements from fiber over `b` to fiber over `d` for `beta : b -> d`

5. `fiberFunctorTransition beta : Grothendieck (restrictToFiber F b) ->
   Grothendieck (restrictToFiber F d)`
   - Complete functor with object and morphism maps
   - Preserves identity: `fiberFunctorTransitionHom_id`
   - Preserves composition: `fiberFunctorTransitionHom_comp`

6. Helper lemmas for identity and composition:
   - `twObjMk'_comp_id` - twisted arrow equality for identity
   - `fiberTransportTwMorph_id` - transport morphism is eqToHom for identity
   - `fiberTransport_id` - transport functor is eqToHom for identity
   - `fiberTransport_comp` - transport functor composition law
   - `fiberFunctorTransitionObj_id` - object-level identity law
   - `fiberFunctorTransitionObj_comp` - object-level composition law

7. `fiberFunctorTransition_id` - functor-level identity law
   - `fiberFunctorTransition C F (id b) = id (Grothendieck (restrictToFiber C F b))`

8. `fiberFunctorTransition_comp` - functor-level composition law
   - `fiberFunctorTransition C F (beta >> gamma) =
      fiberFunctorTransition C F beta >> fiberFunctorTransition C F gamma`

9. `fiberFunctor : C -> Cat` - the fiber functor
   - `fiberFunctor.obj b = Grothendieck (restrictToFiber C F b)`
   - `fiberFunctor.map beta = fiberFunctorTransition C F beta`

10. `ConnectedGrothendieck' F = Grothendieck (fiberFunctor C F)`
    - The connected Grothendieck construction as a category

### Key Helper Lemmas

- `eqToHom_obj_heq` - in Cat, `(eqToHom h).obj x =~ x` (uses `cases h; rfl`)
- `Grothendieck.eqToHom_base'` - `.base` of eqToHom is eqToHom
- `Cat.eqToHom_map_heq` - `(eqToHom h).map f =~ f`
- `Cat.functor_map_heq_of_eq_eqToHom` - when functor equals eqToHom
- `Cat.functor_map_heq_of_eq_comp_comp_eqToHom` - when functor equals composition
- `Functor.map_eqToHom_comp_heq` - `G.map (eqToHom h >> f) =~ G.map f`

### Direct Approach (preserved for reference)

1. Object type `ConnGrothendieckObj` - pairs (arrow, fiber element)
2. Morphism type `ConnGrothendieckHom` - arrow squares with fiber morphisms
3. Composition operation `connGrothendieckComp`
4. Identity operation `connGrothendieckId`
5. Left identity proof `connGrothendieckId_comp`
6. Right identity proof `connGrothendieckComp_id`
7. Coherence lemmas for associativity (partial)
8. Projection to Arrow category

### Remaining Work

1. Establish equivalence between `ConnectedGrothendieck'` and the direct
   construction (if needed)

2. Define the projection functor to the Arrow category

3. Prove universal properties

## References

- `docs/connected-grothendieck-construction.md` - Mathematical specification
- `GebLean/Utilities/Grothendieck.lean` - Standard Grothendieck construction
- `GebLean/Utilities/TwistedArrow.lean` - Twisted arrow category definitions
