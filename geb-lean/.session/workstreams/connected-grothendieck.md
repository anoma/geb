# Workstream: Connected Grothendieck Construction

## Status

In Progress - projection functor defined; universal properties remaining.

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

### Completed

1. Fiber inclusion functor `overOpToTwistedArrow b`
   - Type: `(Over b)^op -> TwistedArrow' C`
   - Maps `(f : a -> b)` to `f` as a twisted arrow
   - Maps morphisms `alpha : f -> g` in `(Over b)^op` to `(alpha, id b)`

2. Restriction functor `restrictToFiber F b = overOpToTwistedArrow b >> F`
   - Restricts `F : Tw(C) -> Cat` to the fiber over `b`

3. Fiber transport functor `fiberTransport beta ov`
   - Transports elements from fiber over `b` to fiber over `d` for `beta : b -> d`

4. `innerFiberContra` and `fiberFunctorContra`
   - Uses `GrothendieckContra'` for the inner fiber layer
   - `innerFiberContra C F b = GrothendieckContra' (restrictToFiber C F b)`
   - `innerFiberContraTransition` for morphism transport
   - Identity and composition laws proved

5. `ConnectedGrothendieckContra`
   - `ConnectedGrothendieckContra F = Grothendieck (fiberFunctorContra C F)`
   - All morphism directions correct (domArr, codArr, fiberMorph)

6. Object equivalence
   - `connGrothendieckContraObjEquiv :`
     `ConnectedGrothendieckContra C F ≃ ConnGrothendieckObj C F`

7. Morphism correspondence (both directions)
   - `connGrothendieckContraHomToHom` converts morphisms from
     `ConnectedGrothendieckContra` to `ConnGrothendieckHom`
   - `connGrothendieckHomToContraHom` converts morphisms from
     `ConnGrothendieckHom` to `ConnectedGrothendieckContra`
   - Key lemmas: `overOpToTwistedArrow_map_eq_twMorphDom_comp_eqToHom`,
     `twDom'_diagDom_eq_diagCod`, `twCod'_diagDom_eq_diagCod`,
     `connGrothendieckHomToContra_source_eq`, `overOpToTwArr_map_innerBase_eq`

8. Projection functor to Arrow category
   - `connGrothendieckContraProjection :`
     `ConnectedGrothendieckContra C F -> Arrow C`
   - Maps objects `(b, (ov, e))` to the arrow `ov.hom : ov.left -> b`
   - Maps morphisms `(domArr, codArr, fiberMorph)` to `(domArr, codArr)`
   - Helper lemmas: `grothendieckContra'_comp_base_left`,
     `fiberFunctorContra_map_base_left`, `grothendieckContra'_eqToHom_base_left`

### Helper Lemmas

- `Over.map_obj_left` - `Over.map` preserves the `left` component
- `eqToHom_obj_heq` - in Cat, `(eqToHom h).obj x =~ x`
- `Grothendieck.eqToHom_base'` - `.base` of eqToHom is eqToHom
- `Cat.eqToHom_map_heq` - `(eqToHom h).map f =~ f`
- `Functor.map_eqToHom_comp_heq` - `G.map (eqToHom h >> f) =~ G.map f`
- `Functor.map_comp_eqToHom_heq` - `G.map (f >> eqToHom h) =~ G.map f`
- `GrothendieckContra'.conj_eqToHom_fiber_heq` - conjugation by eqToHom

### Direct Approach (preserved for reference)

1. Object type `ConnGrothendieckObj` - pairs (arrow, fiber element)
2. Morphism type `ConnGrothendieckHom` - arrow squares with fiber morphisms
3. Composition and identity operations
4. Identity laws proved

### Remaining Work

1. Prove universal properties

## References

- `docs/connected-grothendieck-construction.md` - Mathematical specification
- `GebLean/Utilities/Grothendieck.lean` - Standard Grothendieck construction
- `GebLean/Utilities/TwistedArrow.lean` - Twisted arrow category definitions
