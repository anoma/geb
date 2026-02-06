# Comprehensive Factorization

## Status

Active

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

### Phase 1: Comprehensive Factorization

File: `GebLean/ComprehensiveFactorization.lean`

Definitions to add (one at a time, building incrementally):

1. `IsDiscreteFibration p` -- for `p : E => B`
2. `IsDiscreteOpfibration p` -- dual
3. Standard property: `F.Elements` forgetful functor is a
   discrete fibration (for any presheaf `F : B^op => Type v`)
4. Standard property: discrete fibrations are faithful
5. `comprehensivePresheaf F` -- the presheaf
   `K(d) = ConnectedComponents (StructuredArrow d F)`
   for `F : C => D`
6. `comprehensiveCopresheaf F` -- the copresheaf
   `K'(d) = ConnectedComponents (CostructuredArrow F d)`
7. `comprehensiveFactorizationE F` -- the functor `e : C => K.Elements`
   sending `c` to `(F(c), [id_{F(c)}])`
8. `comprehensiveFactorizationM F` -- the forgetful functor
   `m : K.Elements => D`
9. `comprehensiveFactorization_comm` --
   `comprehensiveFactorizationE F >> comprehensiveFactorizationM F = F`
10. `comprehensiveFactorizationE_final` --
    `Functor.Final (comprehensiveFactorizationE F)`
11. `comprehensiveFactorizationM_discreteFibration` --
    `IsDiscreteFibration (comprehensiveFactorizationM F)`
12. Dual versions (6-11 for the initial/opfibration case)

### Phase 2: Twisted Arrow Infrastructure

Files: `GebLean/Utilities/TwArrPresheaf.lean` and/or
`GebLean/Paranatural.lean`

Apply the comprehensive factorization to the twisted arrow
functor `TwArr(forget_H)`, producing general infrastructure
not specific to (co)wedges.

### Phase 3: Corrected Weighted Wedges

File: `GebLean/Weighted.lean`

Define weighted wedges/cowedges using the
comprehensive-factorization weight, and prove categorical
equivalences with `StrongRestrictedWedge` /
`StrongRestrictedCowedge`.

## Tasks

- [ ] Create `GebLean/ComprehensiveFactorization.lean`
- [ ] Define `IsDiscreteFibration` and `IsDiscreteOpfibration`
- [ ] Prove standard properties of discrete (op)fibrations
- [ ] Define `comprehensivePresheaf` and dual
- [ ] Build the factorization functors `e` and `m`
- [ ] Prove commutativity (`e >> m = F`)
- [ ] Prove `e` is final
- [ ] Prove `m` is a discrete fibration
- [ ] Dual versions
- [ ] Review checkpoint
- [ ] Twisted arrow infrastructure
- [ ] Review checkpoint
- [ ] Corrected weighted wedges/cowedges

## Related Files

- `docs/comprehensive-factorization-research.md`
- `GebLean/ComprehensiveFactorization.lean` (to be created)
- `GebLean/Utilities/TwArrPresheaf.lean`
- `GebLean/Paranatural.lean`
- `GebLean/Weighted.lean`

## Related Workstreams

- `coend-universal-properties.md` (Q2, Q3)
- `weighted-vs-strong-restricted.md`
