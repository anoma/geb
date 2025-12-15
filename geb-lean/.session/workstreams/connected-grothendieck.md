# Workstream: Connected Grothendieck Construction

## Status

Both Connected Grothendieck constructions (Contra and Alt) project to `Arrow C`.
Presheaf construction projects to `TwistedArrow' C`.

### Completed: Alt Projection Functor

Object equivalence between `ConnectedGrothendieckAlt` and `ConnGrothendieckObj`
is complete via `connGrothendieckAltObjEquiv`.

Full projection functor `connGrothendieckAltProjection : ConnectedGrothendieckAlt C F
 -> Arrow C` is now complete with all category laws proved.

### Corrected Analysis: Alt DOES Project to Arrow C

Previous analysis was incorrect. The Alt construction has morphisms that form
Arrow squares with both domain and codomain going forward in C:

**Alt morphism structure** (`f : x -> y` in `ConnectedGrothendieckAlt`):

- `f.base : x.base -> y.base` in `C^op'` (equivalent to `y.base -> x.base` in C)
  but is used as the domain arrow component going from x's domain to y's domain
- `f.fiber.base.right : x.fiber.base.right -> y.fiber.base.right` (forward in C)

The Under.w lemma provides the Arrow square commutativity directly:
`x.fiber.base.hom >> f.fiber.base.right = f.base >> y.fiber.base.hom`

This is exactly an Arrow morphism square.

**Why it works**: The `GrothendieckContra'` construction uses base morphisms
that go forward in the underlying category C (even though they're typed in
`C^op'`). The `innerFiberAltTransition` functor preserves the `.right`
component of Under morphisms via `Under.map_map_right`.

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
     `ConnectedGrothendieckContra C F = ConnGrothendieckObj C F`

7. Morphism correspondence (both directions)
   - `connGrothendieckContraHomToHom` converts morphisms from
     `ConnectedGrothendieckContra` to `ConnGrothendieckHom`
   - `connGrothendieckHomToContraHom` converts morphisms from
     `ConnGrothendieckHom` to `ConnectedGrothendieckContra`
   - Key lemmas: `overOpToTwistedArrow_map_eq_twMorphDom_comp_eqToHom`,
     `twDom'_diagDom_eq_diagCod`, `twCod'_diagDom_eq_diagCod`,
     `connGrothendieckHomToContra_source_eq`, `overOpToTwArr_map_innerBase_eq`

8. Projection functor to Arrow category (Contra)
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

10. Alternative Connected Grothendieck Construction (domain-indexed)
    - `underToTwistedArrow : Under a -> TwistedArrow' C` - inclusion functor
    - `restrictToDomainFiber C F a = underToTwistedArrow C a >> F`
    - `innerFiberAlt C F a = Grothendieck (restrictToDomainFiber C F a)`
    - `domainFiberTransport C F alpha` - transport functor for `alpha : c -> a`
    - `innerFiberAltTransition C F alpha` - transition functor
    - `innerFiberAltTransition_id` and `innerFiberAltTransition_comp`
    - `domainFiberFunctor C F : C^op' -> Cat` - the domain fiber functor
    - `ConnectedGrothendieckAlt = GrothendieckContra' (domainFiberFunctor C F)`

11. Object equivalence for Alt construction
    - `connGrothendieckAltObjToObj` - maps Alt objects to ConnGrothendieckObj
    - `connGrothendieckObjToAltObj` - maps ConnGrothendieckObj to Alt objects
    - `underToTwArr_mk_twArr_eq` - helper lemma for roundtrip proofs
    - `connGrothendieckAltObj_roundtrip` - roundtrip proof Alt -> Obj -> Alt
    - `connGrothendieckObj_altRoundtrip` - roundtrip proof Obj -> Alt -> Obj
    - `connGrothendieckAltObjEquiv : ConnectedGrothendieckAlt C F = ConnGrothendieckObj C F`

12. Projection functor to Arrow category (Alt)
    - `connGrothendieckAltProjection : ConnectedGrothendieckAlt C F -> Arrow C`
    - `connGrothendieckAltObjToArrow` - object map
    - `connGrothendieckAltHomDomArr` - extracts domain arrow component
    - `connGrothendieckAltHomCodArr` - extracts codomain arrow component
    - `connGrothendieckAltMorphSquareComm` - Arrow square commutativity via Under.w
    - Identity and composition laws proved via:
      - `domainFiberFunctor_map` - simp lemma for functor map
      - `innerFiberAltTransition_map` - simp lemma for transition functor map
      - `innerFiberAltTransitionHom_base` - base of transition is Under.map
      - `Under.map_map_right` - mathlib lemma preserving right component

13. Morphism equivalence between Alt and ConnGrothendieckHom
    - `connGrothendieckAltHomToHom` - converts Alt morphisms to ConnGrothendieckHom
    - `connGrothendieckHomToAltHom` - converts ConnGrothendieckHom to Alt morphisms
    - Helper functions for conversion:
      - `connGrothendieckAltHomDomArr`, `connGrothendieckAltHomCodArr` - extract arrow components
      - `connGrothendieckAltHomFiberMorph` - extracts fiber morphism with eqToHom transport
      - `connGrothendieckHomToAltFiberBase` - constructs Under morphism via `Under.homMk`
      - `connGrothendieckHomToAltFiberMorph` - constructs fiber morphism with eqToHom transport
    - Roundtrip theorems:
      - `connGrothendieckHom_altRoundtrip` - Hom -> Alt -> Hom = Hom
      - `connGrothendieckAltHom_roundtrip` - Alt -> Hom -> Alt = Alt (up to HEq)
    - Helper lemma: `connGrothendieckHom_altFiberMorphRoundtrip` for fiber morphism roundtrip

14. Functoriality for Alt construction
    - `restrictToDomainFiberNatTrans` - whiskered natural transformation
    - `restrictToDomainFiberNatTrans_id` and `restrictToDomainFiberNatTrans_comp`
    - `innerFiberAltMap` - induced functor on inner fibers via `Grothendieck.map`
    - `innerFiberAltMap_id` and `innerFiberAltMap_comp`
    - `innerFiberAltMap_obj_base` and `innerFiberAltMap_map_base` - base preservation
    - Naturality lemmas:
      - `alpha_domainFiberTransport_naturality`
      - `innerFiberAltMap_natural_obj`
      - `innerFiberAltMap_naturality_fiber`
    - `domainFiberFunctorNatTrans` - natural transformation between domain fiber functors
    - `domainFiberFunctorNatTrans_id` and `domainFiberFunctorNatTrans_comp`
    - `connGrothendieckAltMap` - induced functor via `GrothendieckContra'.map`
    - `connGrothendieckAltMap_id` and `connGrothendieckAltMap_comp`

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
      `ConnectedGrothendieckPresheaf C G -> TwistedArrow' C`
    - Maps objects to their underlying twisted arrow
    - Maps morphisms to their `twMorph` component

### Remaining Work

1. Prove universal properties for copresheaf construction
2. Establish full equivalence between `ConnectedGrothendieckContra` and
   `ConnectedGrothendieckAlt`:
   - Morphism correspondence for Alt construction is complete (item 13 above)
   - Compose equivalences to get Alt = Contra (remaining)

### Investigated and Resolved

- **Alt projection category**: Initially hypothesized that Alt projects to
  `TwistedArrow' C`, but investigation revealed that Alt actually projects
  to `Arrow C` just like Contra. The `Under.w` lemma provides the Arrow
  square commutativity, and `Under.map_map_right` ensures the codomain
  component is preserved through transitions.

- **Projection from presheaf construction to `Arrow C`**: Investigated thoroughly.
  The presheaf construction projects to `TwistedArrow' C`, not `Arrow C`, due to
  the diagonal construction asymmetry (see below).

### Projection Asymmetry: Copresheaf vs Presheaf

The copresheaf and presheaf constructions project to different categories:

- **Copresheaf** `F : Tw(C) -> Cat` projects to `Arrow C`
- **Presheaf** `G : Tw(C)^op -> Cat` projects to `TwistedArrow' C`

The asymmetry arises from how the diagonal construction interacts with functor
variance:

1. **Diagonal construction**: Given an Arrow morphism `(g, h)`, form a diagonal
   twisted arrow `w = h . f = f' . g` and TwistedArrow morphisms from the
   component arrows `f`, `f'` to this composite `w`.

2. **Covariant case**: `F.map (f -> w) : F(f) -> F(w)` transports fibers INTO
   `F(w)`. Both fiber elements end up in `F(w)` where they can be compared.

3. **Contravariant case**: `G.map (f -> w) : G(w) -> G(f)` transports OUT of
   `G(w)`. We cannot use this to get fibers into a common category.

The presheaf construction instead uses TwistedArrow morphisms directly as base
morphisms. For `twMorph : f -> f'`:

- `G.map twMorph : G(f') -> G(f)` transports `e'` into `G(f)`
- The fiber morphism `e -> G(twMorph)(e')` lives in `G(f)`

This naturally projects to `TwistedArrow' C` rather than `Arrow C`.

See `docs/connected-grothendieck-construction.md` Section 11.9 and
`GebLean/Utilities/ConnectedGrothendieck.lean` for details.

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
