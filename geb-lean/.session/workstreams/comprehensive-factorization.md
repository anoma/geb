# Comprehensive Factorization

## Status

Phase 5 complete. Paranatural transformations
characterized as ordinary natural transformations
via weighted limits:
`Paranat H G ≃
  (wedgeWeight H ⟶ profunctorOnTwistedArrow C G)`.

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

### Phase 4: Categorical Equivalences (COMPLETE)

File: `GebLean/ComprehensiveWeighted.lean`

Completed definitions:

1. `comprehensiveCoconeForwardFunctor F G` --
   `Cocone (F ⋙ G) ⥤ Cocone (comprehensiveM F ⋙ G)`
2. `comprehensiveCoconeBackwardFunctor F G` --
   `Cocone (comprehensiveM F ⋙ G) ⥤ Cocone (F ⋙ G)`
3. `comprehensiveCoconeEquivalence F G` --
   `Cocone (F ⋙ G) ≌ Cocone (comprehensiveM F ⋙ G)`
4. `comprehensiveConeForwardFunctor F G` --
   `Cone (F ⋙ G) ⥤ Cone (comprehensiveM' F ⋙ G)`
5. `comprehensiveConeBackwardFunctor F G` --
   `Cone (comprehensiveM' F ⋙ G) ⥤ Cone (F ⋙ G)`
6. `comprehensiveConeEquivalence F G` --
   `Cone (F ⋙ G) ≌ Cone (comprehensiveM' F ⋙ G)`
7. `strongRestrictedCowedge_weightedCocone_equivalence`
   -- `StrongRestrictedCowedge G H ≌
   WeightedCocone (cowedgeWeight H)
   (profunctorOnCoTwistedArrow C G)`
8. `strongRestrictedWedge_weightedCone_equivalence`
   -- `StrongRestrictedWedge G H ≌
   WeightedCone (wedgeWeight H)
   (profunctorOnTwistedArrow C G)`

### Phase 5: Paranat as Weighted Limit (COMPLETE)

File: `GebLean/ComprehensiveWeighted.lean`

Completed definitions:

1. `structureIntegralWeightedCone_isTerminal G H`
   -- terminality of the structure integral wedge
   transferred to weighted cones
2. `structureIntegralWeightedConeIso G H` -- iso
   in `WeightedCone` between structure integral
   image and natural transformation cone
3. `structureIntegralNatTransIso G H` -- iso in
   `Type v` between `StructureIntegral H G` and
   `(wedgeWeight H ⟶ profunctorOnTwistedArrow C G)`
4. `paranatWeightedLimitEquiv G H` --
   `Paranat H G ≃
   (wedgeWeight H ⟶ profunctorOnTwistedArrow C G)`

### Phase 6: Op Duality (PLANNED)

Three interconnected parts establishing duality relationships
via opposite categories and functors.

#### Phase 6A: Weighted Cone/Cocone Op Duality

File: `GebLean/Weighted.lean`

A `WeightedCocone (W : Jᵒᵖ ⥤ Type v) (D : J ⥤ C)` with
point `c` provides morphisms `D.obj j ⟶ c` for each `j`
and `w : W.obj (op j)`. A `WeightedCone W D.op` with
point `op c` provides morphisms `op c ⟶ D.op.obj (op j)`
in `Cᵒᵖ`, which is `D.obj j ⟶ c` in `C` -- the same
data. Morphisms between cones/cocones reverse direction.

Definitions:

1. `weightedCoconeOpCone` -- object-level map
   `WeightedCocone W D → WeightedCone W D.op`
2. `weightedConeOpCocone` -- inverse map
   `WeightedCone W D.op → WeightedCocone W D`
3. `weightedCoconeOpConeFunctor` -- functorial lifting
   (with direction reversal)
4. `weightedCoconeOpConeEquivalence` --
   `WeightedCocone W D ≌ (WeightedCone W D.op)ᵒᵖ`

Analogous to mathlib's `coconeEquivalenceOpConeOp`.

#### Phase 6B: Connected Components Op Equivalence

File: `GebLean/Utilities/Category.lean`

Connected components depend only on the zig-zag relation,
which is invariant under op (since `f : a ⟶ b` in `C`
gives `f.op : op b ⟶ op a` in `Cᵒᵖ`, and zig-zags go
both ways).

Definitions:

1. `connectedComponentsOpEquiv` --
   `ConnectedComponents Cᵒᵖ ≃ ConnectedComponents C`
2. `connectedComponentsEquivOfEquiv` --
   given `C ≌ D`, `ConnectedComponents C ≃
     ConnectedComponents D`

Mathlib has `isConnected_op_iff_isConnected` but no
direct equivalence on the `ConnectedComponents` type.

#### Phase 6C: Comprehensive Presheaf/Copresheaf Duality

File: `GebLean/ComprehensiveFactorization.lean`

The presheaf form uses
`ConnectedComponents (StructuredArrow d F)`, while
the copresheaf form uses
`ConnectedComponents (CostructuredArrow F d)`.

Mathlib provides:

```text
structuredArrowOpEquivalence :
  (StructuredArrow d F)ᵒᵖ ≌
    CostructuredArrow F.op (op d)
```

Composing with Phase 6B gives:

```text
ConnectedComponents (StructuredArrow d F)
  ≃ ConnectedComponents ((StructuredArrow d F)ᵒᵖ)
  ≃ ConnectedComponents
      (CostructuredArrow F.op (op d))
```

Definitions:

1. `comprehensivePresheafCopresheafIso` --
   `comprehensivePresheaf F ≅
     comprehensiveCopresheaf (F.op)`
   as functors `Dᵒᵖ ⥤ Type _`
2. `comprehensiveE_op_E'` -- relationship between
   `comprehensiveE F` and `comprehensiveE' (F.op)`
3. `comprehensiveM_op_M'` -- relationship between
   `comprehensiveM F` and `comprehensiveM' (F.op)`

Items 2-3 extend the presheaf/copresheaf iso to the
factorization functors. The precise statements depend on
the relationship between `P.ElementsPre` and
`(P.Elements)ᵒᵖ` for `P : Dᵒᵖ ⥤ Type v`, which needs
investigation during implementation.

#### Phase 6D: CostructureIntegral Elimination Rule

`CostructureIntegral H G ≃ Paranat H G` cannot hold
with the same `H, G` since
`StructureIntegral H G ≃ Paranat H G` already holds and
`CostructureIntegral` (a quotient) is structurally
different from `StructureIntegral` (a subtype).

Instead, we characterize `CostructureIntegral H G`
via its elimination rule (maps out of it), using the
weighted colimit elimination infrastructure
(`WeightedColimitElimination` in `Weighted.lean`).

The chain of equivalences:

1. `CostructureIntegral H G` is the `.pt` of the
   initial `StrongRestrictedCowedge G H`
   (`costructureIntegralCowedge_isInitial`)
2. Transfer via
   `strongRestrictedCowedge_weightedCocone_equivalence`
   to an initial weighted cocone (weighted colimit)
   with weight `cowedgeWeight H` and diagram
   `profunctorOnCoTwistedArrow C G`
3. Apply `homIsoWeightedLimitApex`: for any `Y`,
   `(CostructureIntegral H G → Y) ≅ d.pt` where
   `d` is the weighted limit of
   `homToFunctor (profOnCoTwArr C G) Y` by
   `cowedgeWeight H`
4. In `Type v`, that weighted limit is
   `NatTrans (cowedgeWeight H)
     (homToFunctor (profOnCoTwArr C G) Y)`

File: `GebLean/ComprehensiveWeighted.lean`

Definitions:

1. `costructureIntegralWeightedCocone_isInitial` --
   transfer initiality to weighted cocones
2. `costructureIntegralElimEquiv` --
   `(CostructureIntegral H G → Y) ≃
     (cowedgeWeight H ⟶
       homToFunctor (profOnCoTwArr C G) Y)`

This states: any hom-set with domain
`CostructureIntegral H G` is a natural transformation
type (a weighted limit). Combined with Phase 5
(`Paranat H G ≃ (wedgeWeight H ⟶ profOnTwArr C G)`),
this gives a complete picture: the structure integral
(end) characterizes paranaturality, while the
costructure integral (coend) is characterized by its
elimination into weighted limits.

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
- [x] Categorical equivalences for weighted (co)wedges
- [x] Paranat as weighted limit characterization
- [x] Weighted cone/cocone op duality (Phase 6A)
- [x] Connected components op equivalence (Phase 6B)
- [ ] Comprehensive presheaf/copresheaf duality (Phase 6C)
- [ ] CostructureIntegral duality research (Phase 6D)

## Related Files

- `docs/comprehensive-factorization-research.md`
- `GebLean/ComprehensiveFactorization.lean`
- `GebLean/ComprehensiveWeighted.lean`
- `GebLean/Utilities/TwistedArrow.lean`
- `GebLean/Utilities/TwArrPresheaf.lean`
- `GebLean/Paranatural.lean`
- `GebLean/Weighted.lean`
- `GebLean/Utilities/Category.lean`
- `GebLean/Utilities/ConnectedComponents.lean`

## Related Workstreams

- `coend-universal-properties.md` (Q2, Q3)
- `weighted-vs-strong-restricted.md`
