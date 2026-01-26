# Workstream: Coend-End Correspondence

## Status

In Progress

## Context

The Mendler algebra code uses coends and their relationship to ends. We need to
properly formalize:

1. The coend elimination rule: `Hom(∫^A P(A,A), Y) ≅ ∫_A Hom(P(A,A), Y)`
2. The co-Yoneda characterization of coends in terms of natural transformations
3. The connection between our weighted ends/coends and mathlib's ends/coends

The current `CoendAsNatTransformations` section in `RestrictedCoendAsColimit.lean`
has partial definitions but doesn't complete the proofs or make the end structure
explicit.

## Tasks

- [x] Search mathlib for existing coend elimination formula
  - Result: Mathlib does NOT have `Hom(∫^A P(A,A), Y) ≅ ∫_A Hom(P(A,A), Y)`
  - Mathlib only provides: `coend.desc` (universal property), `coend.ι_desc` (factorization)
  - We need to prove this formula ourselves
- [x] Add explicit equivalences between mathlib's ends/coends and our weighted
      ends/coends (with unit/terminal weight profunctor)
  - We already have equivalences for Wedge/Cowedge
  - Mathlib defines ends as terminal wedges, coends as initial cowedges
  - Transfer initiality/terminality across the categorical equivalences
  - Result: Added `Prop`-level transfers via `hasTerminalWeightedWedgeIffHasEnd`,
    `hasInitialWeightedCowedgeIffHasCoend` using `Equivalence.hasTerminal_iff`
    and `hasLimit_iff_hasTerminal_cone`
  - Added data-level transfers `isTerminalOfEquivFunctor`/`isInitialOfEquivFunctor`
    in `Utilities/Category.lean` (computable, no `choice`)
  - Added weighted end/coend to mathlib end/coend transfers:
    `isTerminalWedgeOfIsWeightedEnd`, `isWeightedEndOfIsTerminalWedge`,
    `isInitialCowedgeOfIsWeightedCoend`, `isWeightedCoendOfIsInitialCowedge`
- [ ] Show that `WeightedCowedgeOver unitProfunctor P Y` is the end
      `∫_A Hom(P(A,A), Y)`
- [ ] Formalize the coend elimination rule using the end structure
- [ ] Prove the co-Yoneda isomorphism:
      `∫^A P(A,A) ≅ Nat(Y ↦ ∫_A Hom(P(A,A), Y), Id)`
- [ ] Complete the proof that `coendToNatTrans` and `natTransToCoend` are
      mutually inverse
- [ ] Clean up `CoendAsNatTransformations` section to use proper
      initiality/terminality rather than assuming coend existence via parameters

## Notes

### Current State of CoendAsNatTransformations

The section defines:

- `cowedgeFamilyFunctor`: `Y ↦ WeightedCowedgeOver unitProfunctor P Y`
- `CowedgeNatTrans`: Natural transformations `cowedgeFamilyFunctor P ⟶ Id`
- `coendInjectionCowedge`: Injection maps form a cowedge
- `coendToNatTrans`: Coend element → natural transformation (assumes coend exists)
- `natTransToCoend`: Natural transformation → coend element

Missing:

- Proof that these maps are mutually inverse
- Explicit connection to ends
- Use of initiality (currently assumes `desc`, `fac`, `unique` as parameters)

### Dinaturality vs Paranaturality

When the target profunctor is constant (a fixed type), dinaturality and
paranaturality coincide. The cowedge condition `hι` in the current code is
exactly the dinaturality condition for the injection maps.

### Mathlib Resources

- `Mathlib.CategoryTheory.Limits.Shapes.End` - ends and coends

**What mathlib has:**

- `Wedge F` = `Multifork (multicospanIndexEnd F)` - cones for ends
- `Cowedge F` = `Multicofork (multispanIndexCoend F)` - cocones for coends
- `HasEnd F` = `HasMultiequalizer (multicospanIndexEnd F)`
- `HasCoend F` = `HasMulticoequalizer (multispanIndexCoend F)`
- `end_ F` = `multiequalizer (multicospanIndexEnd F)` - the end object
- `coend F` = `multicoequalizer (multispanIndexCoend F)` - the coend object
- `end_.π F j : end_ F ⟶ (F.obj (op j)).obj j` - projection from end
- `coend.ι F j : (F.obj (op j)).obj j ⟶ coend F` - injection into coend
- `end_.lift` / `coend.desc` - universal property constructors
- `endFunctor J C` / `coendFunctor J C` - functorial construction

**What mathlib does NOT have:**

- The coend elimination rule: `Hom(∫^A P(A,A), Y) ≅ ∫_A Hom(P(A,A), Y)`
- Any connection between ends and coends via Hom functors
- The co-Yoneda characterization of coends

## Related Files

- `GebLean/RestrictedCoendAsColimit.lean` - CoendAsNatTransformations section
- `GebLean/WeightedAlg.lean` - WeightedWedge, WeightedCowedge definitions
- `GebLean/Weighted.lean` - HasWeightedEnd, HasWeightedCoend
