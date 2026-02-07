# Comprehensive Factorization

## Status

Phase 3 complete. Both cowedge and wedge weighted
equivalences proved.

## Context

Implementing the comprehensive factorization system
(Street-Walters 1973) in Lean 4, using mathlib definitions
wherever available.

## Research Findings

See `docs/comprehensive-factorization-research.md`.

Mathlib provides: `ConnectedComponents`, `IsConnected`,
`Functor.Final`, `Functor.Initial`, `StructuredArrow`,
`CostructuredArrow`, left/right Kan extensions (including
pointwise), `F.Elements`, Grothendieck construction.

Mathlib does NOT provide: discrete (op)fibration, the
comprehensive factorization itself.

## Implementation Plan

### Phase 1: Comprehensive Factorization (COMPLETE)

File: `GebLean/ComprehensiveFactorization.lean`

Completed definitions:

1. `IsDiscreteFibration p` -- for `p : E => B`
2. `IsDiscreteOpfibration p` -- dual
3. `elements_π_isDiscreteOpfibration` -- covariant
   elements forgetful functor is a discrete opfibration
4. `elementsPre_π_isDiscreteFibration` -- contravariant
   elements forgetful functor is a discrete fibration
5. `comprehensiveCopresheaf F` -- the copresheaf
   `K'(d) = ConnectedComponents (CostructuredArrow F d)`
6. `comprehensivePresheaf F` -- the presheaf
   `K(d) = ConnectedComponents (StructuredArrow d F)`
7. `comprehensiveE' F` -- initial functor
   `C => (comprehensiveCopresheaf F).Elements`
8. `comprehensiveM' F` -- discrete opfibration
   `(comprehensiveCopresheaf F).Elements => D`
9. `comprehensiveM'_isDiscreteOpfibration` -- proved
10. `comprehensiveFactorization'_comm` --
    `comprehensiveE' F >> comprehensiveM' F = F`
11. `comprehensiveE'_initial` --
    `Functor.Initial (comprehensiveE' F)`
12. `comprehensiveE F` -- final functor
    `C => (comprehensivePresheaf F).ElementsPre`
13. `comprehensiveM F` -- discrete fibration
    `(comprehensivePresheaf F).ElementsPre => D`
14. `comprehensiveM_isDiscreteFibration` -- proved
15. `comprehensiveFactorization_comm` --
    `comprehensiveE F >> comprehensiveM F = F`
16. `comprehensiveE_final` --
    `Functor.Final (comprehensiveE F)`
17. `comprehensiveCopresheafUnit` -- unit natural
    transformation `constPUnitFunctor C ⟶ F ⋙ K'`
18. `comprehensiveCopresheafLeftExt` -- left extension
    structure `(K', unit)` for `Lan_F(!)`
19. `comprehensiveCopresheaf_isPointwiseLan` -- proof
    that `K' = Lan_F(!)` is a pointwise left Kan
    extension
20. `comprehensivePresheafUnit` -- unit natural
    transformation `constPUnitFunctor Cᵒᵖ ⟶ F.op ⋙ K`
21. `comprehensivePresheafLeftExt` -- left extension
    structure `(K, unit)` for `Lan_{F.op}(!)`
22. `comprehensivePresheaf_isPointwiseLan` -- proof
    that `K = Lan_{F.op}(!)` is a pointwise left Kan
    extension

### Phase 2: Twisted Arrow Infrastructure (COMPLETE)

Files: `GebLean/Utilities/TwistedArrow.lean`,
`GebLean/Utilities/TwArrPresheaf.lean`

Completed definitions:

1. `coTwistedArrowMap F` -- induced functor on
   co-twisted arrows
2. `twistedArrowMap F` -- induced functor on
   twisted arrows
3. `profOnCoTwArr_profPullback` -- compatibility
4. `profOnTwArr_profPullback` -- dual compatibility

### Phase 3: Weighted Equivalences (COMPLETE)

File: `GebLean/ComprehensiveWeighted.lean`

Completed definitions:

1. `comprehensiveCoconeEquiv F G` --
   `Cocone (F ⋙ G) ≃ Cocone (comprehensiveM F ⋙ G)`
2. `comprehensiveConeEquiv F G` --
   `Cone (F ⋙ G) ≃ Cone (comprehensiveM' F ⋙ G)`
3. `cowedgeWeight H` --
   `comprehensivePresheaf (coTwistedArrowMap
   (DiagElem.forget H))`
4. `strongRestrictedCowedge_weightedCocone_equiv` --
   `StrongRestrictedCowedge G H ≃
   WeightedCocone (cowedgeWeight H)
   (profunctorOnCoTwistedArrow C G)`
5. `wedgeWeight H` --
   `comprehensiveCopresheaf (twistedArrowMap
   (DiagElem.forget H))`
6. `strongRestrictedWedge_weightedCone_equiv` --
   `StrongRestrictedWedge G H ≃
   WeightedCone (wedgeWeight H)
   (profunctorOnTwistedArrow C G)`

## Tasks

- [x] Create `GebLean/ComprehensiveFactorization.lean`
- [x] Define `IsDiscreteFibration` and `IsDiscreteOpfibration`
- [x] Prove standard properties of discrete (op)fibrations
- [x] Define `comprehensivePresheaf` and dual
- [x] Build the factorization functors `e` and `m`
- [x] Prove commutativity (`e >> m = F`)
- [x] Prove `e'` is initial
- [x] Prove `m'` is a discrete opfibration
- [x] Prove `e` is final
- [x] Prove `m` is a discrete fibration
- [x] Review checkpoint
- [x] Prove `comprehensiveCopresheaf` is `Lan_F(!)`
- [x] Prove `comprehensivePresheaf` is `Lan_{F.op}(!)`
- [x] Twisted arrow infrastructure
- [x] Review checkpoint
- [x] Corrected weighted wedges/cowedges

## Related Files

- `docs/comprehensive-factorization-research.md`
- `GebLean/ComprehensiveFactorization.lean`
- `GebLean/ComprehensiveWeighted.lean`
- `GebLean/Utilities/TwistedArrow.lean`
- `GebLean/Utilities/TwArrPresheaf.lean`
- `GebLean/Paranatural.lean`
- `GebLean/Weighted.lean`

## Related Workstreams

- `coend-universal-properties.md` (Q2, Q3)
- `weighted-vs-strong-restricted.md`
