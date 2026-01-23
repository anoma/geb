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

- [x] Define WeightedLimit as terminal object in WeightedCones category
- [x] Define WeightedColimit as initial object in WeightedCocones category
- [x] Check if mathlib has ends and coends (they exist as Dinat/Paranat transforms)
- [x] Define WeightedEnd and WeightedCoend (as terminal/initial weighted wedges)
- [x] Prove ends/coends as limits/colimits over twisted arrow category
- [x] Prove restricted coend equals ordinary coend with copowers:
      `Sigma(H, G) = integral^A H(A,A) . G(A,A)` (via `restrictedCoend_is_copowerCoend`)
- [ ] Investigate whether the ordinary coend can be expressed as a left Kan
      extension

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
