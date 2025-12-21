# Workstream: Polynomial Functor Adjunctions

## Status

Active

## Context

There are several adjunctions involving polynomial functors and `Type` that
arise from the categorical structure of polynomial functors. This workstream
tracks the implementation of these adjunctions in `GebLean/PolyAdjunctions.lean`.

The adjunctions relate categories of polynomial functors to simpler categories
(often `Type` or slice categories), capturing how polynomial functors arise
as free constructions or have forgetful functors with adjoints.

## File Structure

- `GebLean/PolyAdjunctions.lean` - Adjunctions involving polynomial functors
- Imports `GebLean/Polynomial.lean` (polynomial functor infrastructure)
- Imported by `GebLean/PolyAlg.lean` (to enable code factoring using adjunctions)

## Tasks

### Adjunctions to Implement

- [ ] Free/forgetful adjunction: polynomial functors over `Type` vs `Type`
- [ ] Slice-based adjunctions: relating `PolyFunctorBetweenCat X Y` to
      slice categories
- [ ] Cofree/forgetful adjunction (dual of free/forgetful)
- [ ] Identify which adjunctions arise from the family-slice equivalence

### Infrastructure

- [ ] Document each adjunction with categorical interpretation
- [ ] Provide examples showing how to use each adjunction
- [ ] Factor common code in `PolyAlg.lean` using adjunction properties

## Notes

This file should remain independent of `PolyAlg.lean` to allow the adjunctions
to be used for code factoring within `PolyAlg.lean`. The dependency direction
is: `Polynomial.lean` -> `PolyAdjunctions.lean` -> `PolyAlg.lean`.

## References

- nLab: polynomial functor (adjunctions section)
- Gambino, Kock. "Polynomial functors and polynomial monads"
