# Workstream: Restricted Coend as Ordinary Coend

## Status

Complete

## Context

We have established that Vene's restricted coend `Sigma(H, G)` should equal the
ordinary coend `integral^A H(A,A) . G(A,A)` where `.` denotes copowers. This
workstream formalizes this connection and relates it to standard categorical
machinery (weighted colimits, Kan extensions).

The central result: for `H : C^op x C -> Type` and `G : C^op x C -> D`:

```text
Sigma(H, G) = integral^A H(A,A) . G(A,A)
```

This connects Vene's Mendler-Lambek correspondence to standard category theory.

## Tasks

- [x] Define WeightedLimit as terminal object in WeightedCones category
- [x] Define WeightedColimit as initial object in WeightedCocones category
- [x] Check if mathlib has ends and coends (they exist as Dinat/Paranat transforms)
- [x] Define WeightedEnd and WeightedCoend (as terminal/initial weighted wedges)
- [x] Prove ends/coends as limits/colimits over twisted arrow category
- [x] Prove restricted coend equals ordinary coend with copowers:
      `Sigma(H, G) = integral^A H(A,A) . G(A,A)` (via `restrictedCoend_is_copowerCoend`)
- [x] Investigate connection to left Kan extensions (co-Yoneda lemma formalized)
- [x] Characterize coends as natural transformations via co-Yoneda
      (`CoendAsNatTransformations` section with `CowedgeFamily`, `coendToNatTrans`,
      `natTransToCoend`)

## Notes

### Implementation Summary

The connection between restricted coends and copower coends is established in
`GebLean/RestrictedCoendAsColimit.lean` via the following definitions:

1. `HasCopowers C` - Type class for categories with copowers (type-indexed
   coproducts), characterized by the adjunction `Hom(S . X, Y) ~ (S -> Hom(X, Y))`

2. `IsCopowerCowedgeDinatural` - The dinaturality condition for a family
   `omega : forall A, H(A,A) . G(A,A) -> pt` to form a cowedge of the copower
   profunctor.

3. `restrictedCowedgeToCopowerFamily` - Converts a restricted cowedge to a
   family of copower morphisms using `HasCopowers.desc`.

4. `copowerFamilyToRestrictedFamily` - Converts a copower family to a restricted
   cowedge family using `HasCopowers.inj`.

5. `restrictedCoend_is_copowerCoend` - The theorem stating that for a dinatural
   copower cowedge family, there exists a unique morphism from the restricted
   coend satisfying the factorization property.

### Kan Extension Connection

The connection to left Kan extensions is established in the `KanExtensionConnection`
section of `RestrictedCoendAsColimit.lean`:

1. `constFirstArgProfCowedge` - For a covariant functor `F : C ⥤ C`, builds a
   restricted cowedge from any morphism `F(pt) → apex`.

2. `constFirstArgProfUniversalCowedge` - The identity on `F(pt)` gives the
   universal restricted cowedge.

3. `constFirstArgProfUniversalCowedge_isInitial` - The co-Yoneda lemma:
   `Σ(HomToProf pt, constFirstArgProf F) ≅ F(pt)`.

This shows that when a profunctor arises from a covariant functor constant in
its first argument, the restricted coend equals the functor's value. This
recovers the Kan extension formula `(Lan_id F)(pt) = F(pt)` via the colimit
formula over the slice category.

### Coends as Natural Transformations (Co-Yoneda Characterization)

The `CoendAsNatTransformations` section in `RestrictedCoendAsColimit.lean`
implements the co-Yoneda characterization of coends for profunctors on Type:

1. `CowedgeFamily P Y` - Cowedge families `(π_A : P(A,A) → Y)` satisfying the
   cowedge condition. This is equivalent to `Cowedge P` with apex `Y` but
   stays in `Type w` rather than `Type (w+1)`.

2. `cowedgeFamilyFunctor P : Type w ⥤ Type w` - The functor sending `Y` to
   `CowedgeFamily P Y`. By the coend elimination rule, this is isomorphic to
   `Hom(∫^A P(A,A), -)`.

3. `CowedgeNatTrans P` - Natural transformations `cowedgeFamilyFunctor P ⟶ Id`.
   By co-Yoneda, these correspond to elements of the coend `∫^A P(A,A)`.

4. `coendToNatTrans` - Given an element `x` of a coend, constructs the
   corresponding natural transformation where `τ_x.app Y cw = desc cw x`.

5. `natTransToCoend` - Given a natural transformation, extracts the
   corresponding coend element by applying it to the injection cowedge.

This formalizes the co-Yoneda formula:
`∫^A P(A,A) ≅ Nat(Y ↦ Cowedge_Y P, Id)`

### Universal Property Equivalence (Analysis)

A cowedge from `P(A, B) = H(A, B) . G(A, B)` to apex `X` consists of:

- Family `omega_A : H(A,A) . G(A,A) -> X`
- Dinaturality condition

By the universal property of copowers, this is equivalent to:

- Family `Phi_A : H(A,A) -> (G(A,A) -> X)`
- Dinaturality condition

This is exactly an H-restricted G-cowedge! The dinaturality conditions match:

- Cowedge: `omega_{A, beta.g} . G(g, id) = omega_{B, beta} . G(id, g)`
- Restricted cowedge: `Phi_A(beta.g) . G(g, id) = Phi_B(beta) . G(id, g)`

### Multiple Perspectives on G^e(pt)

1. Vene's restricted coend: `Sigma(HomToProf pt, G)`
2. Ordinary coend: `integral^A (A -> pt) . G(A, A)`
3. Category of elements: `colim_{(A,f) in El(yoneda.obj pt)} G(A,A)`
4. Slice category: "colimit" over `Over pt` (but not functorial for profunctors)

### Profunctor Weight Extension (Simplified Approach)

The equivalences between weighted cowedges/wedges and ordinary cowedges/wedges
over copower/power profunctors are established via simple instantiation.

Since `WeightedCowedge W P` is defined as `WeightedCocone` over
`CoTwistedArrow C`, and
`weightedCoconeCowedgeEquiv : WeightedCocone W F ≌`
  `Cowedge (copowerProfunctor W F)` already exists, the
equivalence for profunctor weights follows by instantiation:

```lean
abbrev copowerWeightedProfunctor :
    (CoTwistedArrow C)ᵒᵖ ⥤ CoTwistedArrow C ⥤ D :=
  copowerProfunctor
    (profunctorOnOpCoTwistedArrow C W) (profunctorOnCoTwistedArrow C P)

abbrev weightedCowedgeCowedgeEquiv :
    WeightedCowedge W P ≌ Cowedge (copowerWeightedProfunctor W P) :=
  @weightedCoconeCowedgeEquiv (CoTwistedArrow C) _ D _ _
    (profunctorOnOpCoTwistedArrow C W)
    (profunctorOnCoTwistedArrow C P)
```

Similarly for wedges using `powerWeightedProfunctor` and `weightedWedgeWedgeEquiv`.

The universe constraints in `WeightedCoconeCoconeEquiv` and `WeightedConeConeEquiv`
were generalized (2026-01-27) to allow the index and target categories to be in
different universes, which in turn allows `ProfunctorWeights` to use fully
polymorphic universes for `D : Type w`.

### Mathlib Resources to Check

- `Mathlib.CategoryTheory.Limits.Shapes.End` - ends and coends
- `Mathlib.CategoryTheory.Functor.KanExtension` - Kan extensions
- Kelly's weighted limit formula: `{W, F} = lim(F . pi : El(W) -> C)`

## Related Files

- `GebLean/Weighted.lean` - WeightedCone, WeightedCocone definitions
- `GebLean/WeightedAlg.lean` - RestrictedCowedge, HasRestrictedCoend
- `GebLean/RestrictedCoendAsColimit.lean` - Initial analysis
- `GebLean/ParanatAlg.lean` - IsInitial/IsTerminal style examples
- `docs/weighted-cones-cocones-limits-colimits-ends-coends.md` - Background
