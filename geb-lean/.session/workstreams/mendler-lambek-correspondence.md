# Workstream: Mendler-Lambek Correspondence via Restricted/Weighted Coends

## Status

Complete

## Context

This workstream implements the correspondence between Mendler-style algebras
and conventional (Lambek) algebras for difunctors, following Vene's thesis
"Categorical Programming with Inductive and Coinductive Types" (sections
5.3-5.7).

The correspondence uses restricted coends (initial objects in the category
of restricted cowedges). We also investigate whether our `WeightedCowedge`
concept can accomplish the same thing as Vene's `RestrictedCowedge`.

### Mathematical Background

For an endodifunctor G : C^op x C -> C:

- **Mendler-style G-algebra**: A pair (C, Phi) where C is an object and
  Phi : Id^i/C -> G/C is a dinatural transformation. Equivalently, for
  each A, a function Phi_A : (A -> C) -> (G(A,A) -> C) satisfying the
  dinaturality condition.

- **Conventional G^e-algebra**: A pair (C, phi) where phi : G^e(C) -> C
  is a morphism, and G^e is the functor defined via restricted coends:
  G^e(C) = Sigma(Id^i/C, G) (the Id^i/C-restricted G-coend).

The correspondence (Theorem 5.19 in Vene) states that Alg(G^e) and Alg(G)^m
are isomorphic categories.

### Our Codebase Structures

- `RestrictedCowedge G H`: H-restricted G-cowedge (matches Vene's Def 5.9)
- `WeightedCowedge W P`: Weighted cowedge with data at ALL co-twisted arrows
- `restrictionFunctor`: WeightedCowedge H G -> RestrictedCowedge G H
  (faithful but not full)

### Naming Convention

We use our codebase convention:

- G : C^op x C -> C (the C-valued endodifunctor)
- H : C^op x C -> Type (the Type-valued restriction profunctor)

For the main correspondence, H = HomToProf pt (the hom-to-pt profunctor).

## Tasks

- [x] Create workstream document
- [x] Create markdown documentation of Vene sections 5.3-5.7
- [x] Verify RestrictedCowedge matches Vene's definition
- [x] Define MendlerAlgebra for difunctors (Vene's Definition 5.6)
- [x] Investigate whether WeightedCowedge can replace RestrictedCowedge
- [x] Define restricted coend functor G^e (Vene's Section 5.5)
- [x] Implement translation floor(-) : MendlerAlg -> ConventionalAlg
- [x] Implement translation ceil(-) : ConventionalAlg -> MendlerAlg
- [x] Prove floor(ceil(phi)) = phi
- [x] Prove ceil(floor(Phi)) = Phi
- [x] Establish the category isomorphism Alg(G^e) ~ Alg(G)^m

## Notes

### Definitions from Vene

**Definition 5.6 (Mendler-style algebra for difunctor)**:
For G : C^op x C -> C, a G-malgebra is (C, Phi) where Phi : Id^i/C -> G/C
is dinatural. The dinaturality condition (equation 5.6):

```text
Phi_A(beta . g) . G(g, id_A) = Phi_B(beta) . G(id_B, g)
```

**Definition 5.9 (Restricted cowedge)**:
An H-restricted G-cowedge is (C, Phi) where Phi is a dinatural transformation
from H to G/C (the slice profunctor).

**Definition 5.11 (Restricted coend)**:
An H-restricted G-coend Sigma(H, G) is the initial H-restricted G-cowedge.

**Definition 5.12-5.13 (Translations)**:

- floor(Phi) = [Phi]_G^{Id^i/C} (universal cowedge morphism)
- ceil(phi) = lambda A, gamma : A -> C. phi . inj_G^{Id^i/C}_A(gamma)

### Relationship to Our WeightedCowedge

WeightedCowedge has data at ALL co-twisted arrows (not just diagonals).
The restrictionFunctor extracts diagonal data. The question is whether
the weighted coend (initial WeightedCowedge) can serve the same role as
the restricted coend in the Mendler-Lambek correspondence.

**Findings (implemented in WeightedAlg.lean)**:

The restriction functor `WeightedCowedge H G ⥤ RestrictedCowedge G H` is:

- **Faithful**: Distinct weighted cowedge morphisms give distinct restricted
  cowedge morphisms (injective on hom-sets)
- **Not full**: Some restricted cowedge morphisms don't lift to weighted
  cowedge morphisms (there are fewer morphisms in WeightedCowedge)
- **Not essentially surjective** (generally): Not every restricted cowedge
  arises as the restriction of a weighted cowedge

Consequences:

1. The category of weighted Mendler cowedges embeds faithfully into the
   category of Mendler algebras, but this embedding is not an equivalence.

2. **Fewer morphisms**: Given weighted cowedges W₁, W₂ restricting to Mendler
   algebras M₁, M₂, a Mendler algebra morphism M₁ → M₂ might not lift to a
   weighted cowedge morphism W₁ → W₂.

3. **Not all algebras arise**: Not every Mendler algebra is the restriction
   of some weighted cowedge. WeightedCowedge requires data at ALL co-twisted
   arrows (off-diagonal as well as diagonal), while Mendler algebras only
   specify diagonal data.

4. **Conclusion**: `WeightedCowedge` cannot substitute for `RestrictedCowedge`
   in the Mendler-Lambek correspondence.

5. **Open question**: When both exist, do the initial objects (weighted coend
   vs restricted coend) coincide? The universal property might force them to
   agree even though the general categories differ.

### Implementation Summary (WeightedAlg.lean)

The implementation follows Vene's thesis structure:

1. **HomToProf profunctor**: `(A, B) ↦ (A ⟶ pt)` - Vene's "Id^i/C"
2. **MendlerAlgebra**: Structure with carrier, family, and dinaturality
3. **MendlerAlgebraCat**: Category of Mendler algebras
4. **HasAllHomToProfCoends**: Typeclass bundling existence of all coends
5. **GExtFunctor**: The functor `G^e : C ⥤ C` (G^e(pt) = restricted coend)
6. **ConventionalAlgebra**: F-algebra structure for any endofunctor
7. **floor/ceil**: The translations between algebra types
8. **floor_ceil/ceil_floor**: Roundtrip proofs (Propositions 5.15-5.16)
9. **floorFunctor/ceilFunctor**: Functorial versions
10. **mendlerLambekEquiv**: The category equivalence (Theorem 5.19)
