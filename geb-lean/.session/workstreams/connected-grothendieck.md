# Workstream: Connected Grothendieck Construction

## Status

Blocked - morphism correspondence between `ConnectedGrothendieckContra` and
`ConnGrothendieckHom` cannot be established with current definitions due to
fundamental type mismatch in fiber transport morphisms (see Morphism Direction
Analysis section)

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

3. Oppositized restriction `restrictToFiberOp F b = restrictToFiber ⋙ Cat.opFunctor'`
   - Post-composes oppositization to fiber categories

4. Fiber transport functor `fiberTransport beta ov`
   - Transports elements from fiber over `b` to fiber over `d` for `beta : b -> d`

5. Oppositized fiber transport `fiberTransportOp`
   - Uses `Cat.opFunctor'.map (fiberTransport ...)`

6. `fiberFunctorTransition` and `fiberFunctorTransitionOp`
   - Transition functors for both versions
   - Identity and composition laws proved

7. `fiberFunctor : C -> Cat` and `fiberFunctorOp : C -> Cat`
   - Both fiber functors with full functor laws

8. Two nested constructions:
   - `ConnectedGrothendieck' F = Grothendieck (fiberFunctor C F ⋙ Cat.opFunctor')`
   - `ConnectedGrothendieckOp F = Grothendieck (fiberFunctorOp C F)`

9. Object equivalence `connGrothendieckObjEquiv`
   - Establishes equivalence between nested and direct object types

10. `innerFiberContra` and `fiberFunctorContra` (NEW)
    - Uses `GrothendieckContra'` for the inner fiber layer
    - `innerFiberContra C F b = GrothendieckContra' (restrictToFiber C F b)`
    - `innerFiberContraTransition` for morphism transport
    - Identity and composition laws proved (`innerFiberContraTransition_id`,
      `innerFiberContraTransition_comp`)
    - `fiberFunctorContra : C ⥤ Cat` - fiber functor with correct morphism
      directions

11. `ConnectedGrothendieckContra` (NEW)
    - `ConnectedGrothendieckContra F = Grothendieck (fiberFunctorContra C F)`
    - domArr and codArr have correct directions
    - fiberMorph direction: BLOCKED - see analysis below

### Morphism Direction Analysis

Attempt to establish morphism correspondence between `ConnectedGrothendieckContra`
and `ConnGrothendieckHom` revealed a fundamental type mismatch in the domain
arrow components of the fiber transport morphisms.

**In `ConnGrothendieckHom.fiberMorph`:**

- Source: `(F.map (connGrothendieckTwMorphCod)).obj x.fiber` (transport via `(𝟙, codArr)`)
- Target: `(F.map (connGrothendieckTwMorphDom ≫ eqToHom)).obj y.fiber`
  (transport via `(domArr, 𝟙)` then `eqToHom` from DiagDom to DiagCod)

**In `ConnectedGrothendieckContra` morphism `f`:**

- Source: `(fiberTransportTwMorph).obj x.fiber.fiber` = `(F.map TwMorphCod).obj ...`
  (MATCHES the direct construction)
- Target: `(F.map (overOpToTwistedArrow.map f.fiber.base)).obj y.fiber.fiber`

**Root cause of the type mismatch:**

The two twisted arrow morphisms to DiagCod have different domain arrow types:

1. `overOpToTwistedArrow.map f.fiber.base`:
   - `twDomArr' = f.fiber.base.left : y.fiber.base.left ⟶ x.fiber.base.left`

2. `connGrothendieckTwMorphDom ≫ eqToHom`:
   - `twDomArr' = eqToHom (...) ≫ f.fiber.base.left : x.fiber.base.left ⟶ x.fiber.base.left`

These have fundamentally different source objects for the domain arrow:
`y.fiber.base.left` vs `x.fiber.base.left`. This is not an issue of morphism
direction within a fixed type; the types themselves differ.

**Why this happens:**

- `connGrothendieckTwMorphDom` transports through DiagDom first, then uses
  `eqToHom` to reach DiagCod
- `overOpToTwistedArrow.map` goes directly to DiagCod
- The `eqToHom` component introduces an additional type coercion on the domain
  arrow that changes its source object

**Consequence:**

The morphisms `overOpToTwistedArrow.map f.fiber.base` and
`connGrothendieckTwMorphDom ≫ eqToHom` cannot be proven equal because they have
different component types. Therefore, `f.fiber.fiber` from
`ConnectedGrothendieckContra` cannot be used to construct
`ConnGrothendieckHom.fiberMorph`.

**Possible resolutions:**

1. Modify `ConnGrothendieckHom.fiberMorph` to use `overOpToTwistedArrow.map`
   instead of `connGrothendieckTwMorphDom ≫ eqToHom`
2. Define the inner fiber of `ConnectedGrothendieckContra` using a different
   structure that produces the expected morphism transport
3. Accept that the two constructions define different (but possibly equivalent)
   category structures requiring a non-trivial equivalence functor

### Helper Lemmas

- `eqToHom_obj_heq` - in Cat, `(eqToHom h).obj x =~ x`
- `Grothendieck.eqToHom_base'` - `.base` of eqToHom is eqToHom
- `Cat.eqToHom_map_heq` - `(eqToHom h).map f =~ f`
- `Cat.functor_map_heq_of_eq_comp_comp_eqToHom` - when functor equals composition
- `Functor.map_eqToHom_comp_heq` - `G.map (eqToHom h >> f) =~ G.map f`
- `Functor.map_comp_eqToHom_heq` - `G.map (f >> eqToHom h) =~ G.map f` (NEW)
- `Cat.Functor.op'_eqToHom` - `Functor.op' (eqToHom h) = eqToHom ...`
- `GrothendieckContra'.conj_eqToHom_fiber_heq` - conjugation by eqToHom

### Direct Approach (preserved for reference)

1. Object type `ConnGrothendieckObj` - pairs (arrow, fiber element)
2. Morphism type `ConnGrothendieckHom` - arrow squares with fiber morphisms
3. Composition and identity operations
4. Identity laws proved

### Remaining Work

1. Establish equivalence between `ConnectedGrothendieckContra` and the direct
   construction (`ConnGrothendieckObj`, `ConnGrothendieckHom`)

2. Define the projection functor to the Arrow category

3. Prove universal properties

## References

- `docs/connected-grothendieck-construction.md` - Mathematical specification
- `GebLean/Utilities/Grothendieck.lean` - Standard Grothendieck construction
- `GebLean/Utilities/TwistedArrow.lean` - Twisted arrow category definitions
