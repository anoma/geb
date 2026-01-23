# Workstream: Restricted Coend as Ordinary Coend

## Status

Active

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

- [ ] Define WeightedLimit as terminal object in WeightedCones category
- [ ] Define WeightedColimit as initial object in WeightedCocones category
- [ ] Check if mathlib has ends and coends
- [ ] If mathlib has ends/coends, confirm they are weighted (co)limits with
      hom-functor weight
- [ ] Define WeightedEnd as terminal object in WeightedWedges category
- [ ] Define WeightedCoend as initial object in WeightedCowedges category
- [ ] Check if mathlib proves ends/coends as (co)limits over twisted arrow
      category; if not, prove it ourselves
- [ ] Prove restricted coend equals ordinary coend with copowers:
      `Sigma(H, G) = integral^A H(A,A) . G(A,A)`
- [ ] Investigate whether the ordinary coend can be expressed as a left Kan
      extension

## Notes

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
