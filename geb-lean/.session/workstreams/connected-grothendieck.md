# Workstream: Connected Grothendieck Construction

## Status

Copresheaf construction complete with projection functor to `Arrow C`.
Presheaf construction complete with category instance and projection functor to
`TwistedArrow' C` (not `Arrow C`).

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

9. Presheaf Connected Grothendieck Construction (direct definition)
   - `ConnGrothendieckPresheafObj C G` for `G : (TwistedArrow' C)^op' -> Cat`
   - `ConnGrothendieckPresheafHom C G X Y` with `twMorph` and `fiberMorph`
   - Category instance `connGrothendieckPresheafCategory`
   - Identity, composition, and all category laws proved
   - Uses `cat_disch` tactic for handling dependent type issues in proofs

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

5. Projection functor for presheaf construction
    - `connGrothendieckPresheafProjection`:
      `ConnectedGrothendieckPresheaf C G ⥤ TwistedArrow' C`
    - Maps objects to their underlying twisted arrow
    - Maps morphisms to their `twMorph` component

10. Alternative Connected Grothendieck Construction (domain-indexed)
    - `underToTwistedArrow : Under a ⥤ TwistedArrow' C` - inclusion functor
    - `restrictToDomainFiber C F a = underToTwistedArrow C a ⋙ F`
    - `innerFiberAlt C F a = Grothendieck (restrictToDomainFiber C F a)`
    - `domainFiberTransport C F α` - transport functor for `α : c ⟶ a`
    - `innerFiberAltTransition C F α` - transition functor
    - `innerFiberAltTransition_id` and `innerFiberAltTransition_comp`
    - `domainFiberFunctor C F : Cᵒᵖ' ⥤ Cat` - the domain fiber functor
    - `ConnectedGrothendieckAlt = GrothendieckContra' (domainFiberFunctor C F)`

### Remaining Work

1. Prove universal properties for copresheaf construction
2. Establish equivalence between `ConnectedGrothendieckContra` and
   `ConnectedGrothendieckAlt`

### Investigated and Resolved

- **Projection from presheaf construction to `Arrow C`**: Investigated thoroughly.
  The presheaf construction projects to `TwistedArrow' C`, not `Arrow C`, due to
  the diagonal construction asymmetry (see below).

### Projection Asymmetry: Copresheaf vs Presheaf

The copresheaf and presheaf constructions project to different categories:

- **Copresheaf** `F : Tw(C) → Cat` projects to `Arrow C`
- **Presheaf** `G : Tw(C)^op → Cat` projects to `TwistedArrow' C`

The asymmetry arises from how the diagonal construction interacts with functor
variance:

1. **Diagonal construction**: Given an Arrow morphism `(g, h)`, form a diagonal
   twisted arrow `w = h ∘ f = f' ∘ g` and TwistedArrow morphisms from the
   component arrows `f`, `f'` to this composite `w`.

2. **Covariant case**: `F.map (f → w) : F(f) → F(w)` transports fibers INTO
   `F(w)`. Both fiber elements end up in `F(w)` where they can be compared.

3. **Contravariant case**: `G.map (f → w) : G(w) → G(f)` transports OUT of
   `G(w)`. We cannot use this to get fibers into a common category.

The presheaf construction instead uses TwistedArrow morphisms directly as base
morphisms. For `twMorph : f → f'`:

- `G.map twMorph : G(f') → G(f)` transports `e'` into `G(f)`
- The fiber morphism `e → G(twMorph)(e')` lives in `G(f)`

This naturally projects to `TwistedArrow' C` rather than `Arrow C`.

See `docs/connected-grothendieck-construction.md` Section 11.9 and
`GebLean/Utilities/ConnectedGrothendieck.lean` lines 3329-3368 for details.

### Presheaf Construction Notes

The presheaf construction uses a direct definition approach rather than
the nested approach via `C^op`. This is because the morphism directions
in `TwistedArrowOp' C` and `(TwistedArrow' C)^op'` don't align in a way
that makes the nested approach simple.

Key insight for category laws:

- Use `@CategoryStruct.comp (TwistedArrow' C)` for explicit composition
- `G.map_comp g.twMorph f.twMorph` (reversed order for opposite category)
- `cat_disch` handles dependent type issues in fiber morphism proofs

## References

- `docs/connected-grothendieck-construction.md` - Mathematical specification
- `GebLean/Utilities/Grothendieck.lean` - Standard Grothendieck construction
- `GebLean/Utilities/TwistedArrow.lean` - Twisted arrow category definitions
