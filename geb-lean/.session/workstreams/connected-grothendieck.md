# Workstream: Connected Grothendieck Construction

## Status

In Progress - Category structure defined, associativity proof has a sorry

## Context

The connected Grothendieck construction defines a functor
`E : Fun(Tw(C), Cat) -> Cat/Arr(C)` that assigns to each functor
`F : TwistedArrow C -> Cat` a category `E(F)` over the arrow category.

See `docs/connected-grothendieck-construction.md` for the mathematical
specification.

## Implementation

File: `GebLean/Utilities/ConnectedGrothendieck.lean`

### Completed

1. Object type `ConnGrothendieckObj` - pairs (arrow, fiber element)
2. Morphism type `ConnGrothendieckHom` - arrow squares with fiber morphisms
3. Diagonal constructions `W1`, `W2`, `W3`, `W4` for composition
4. Transport morphisms `morphW1W3`, `morphW2W3` for fiber transport
5. Transport morphisms `morphW1W4`, `morphW2W4` for triple composition
6. Composition operation `connGrothendieckComp`
7. Identity operation `connGrothendieckId`
8. Extensionality lemma `connGrothendieckHom_ext`
9. Left identity proof `connGrothendieckId_comp`
10. Right identity proof `connGrothendieckComp_id`
11. Helper lemmas for identity laws using HEq peeling technique
12. Coherence lemmas for associativity:
    - `connGrothendieckMorphW1W3_comp_left` - LHS path for f.fiberMorph
    - `connGrothendieckMorphW1W3_comp_right` - RHS path for f.fiberMorph
    - `connGrothendieckMorphW2W3_comp_left` - LHS path for h.fiberMorph
    - `connGrothendieckMorphW2W3_comp_right` - RHS path for h.fiberMorph
    - `connGrothendieckMorphMiddle_coherence` - middle coherence for g.fiberMorph
13. Projection functor `connGrothendieckProjection : E(F) => Arrow C`
14. Object over Arrow C: `connGrothendieckOver : Over (Cat.of (Arrow C))`

### Remaining

1. Associativity proof (could be called `connGrothendieckComp_assoc`)
2. Use of associativity proof to provide `CategoryData`

## References

- `docs/connected-grothendieck-construction.md` - Mathematical specification
- `GebLean/Utilities/Grothendieck.lean` - Standard Grothendieck construction
- `GebLean/Utilities/TwistedArrow.lean` - Twisted arrow category definitions
