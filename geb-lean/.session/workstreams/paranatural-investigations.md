# Paranatural Category Theory Investigations

## Status: Active

## Questions to Investigate

### 1. Dialgebra Category in Mathlib

Does mathlib have a dialgebra category? If so:

- Show equivalence between that and the category of diagonal elements for
  the dialgebra profunctor (in ParanatAlg.lean)
- This parallels what we did for algebra and coalgebra profunctors
- Show that when input functors are endofunctors and one is identity, the
  dialgebra profunctor is naturally isomorphic to the algebra or coalgebra
  profunctor (depending on which endofunctor is identity)

### 2. Structure/Costructure Integrals as Ends/Coends

The current form of structure and costructure integrals (as equalizers and
coequalizers) looks like they may be Type-valued ends and coends.

- Work out if this is true
- If so, identify exactly which profunctors on which categories (probably
  categories of diagonal elements?) they are the ends and coends of

### 3. Wedges and Cowedges as Diagonal Elements

Can we express wedges and cowedges as categories of diagonal elements of
some profunctor? This would mean:

- Ends become terminal objects in some category of diagonal elements
- Coends become initial objects in some category of diagonal elements

### 4. Parametricity vs Paranaturality Divergence

Reference: docs/updates-on-paranatural-category-theory-*.pdf (abstract and
slideshow)

Page 10 slide "Divergence between strong dinaturality and parametricity"
shows a case where the "free theorem" from parametric polymorphism differs
from what we get from paranaturality.

**Terminology note**: We use "paranaturality" consistently to mean strong
dinaturality. Plain "dinaturality" refers to the weaker (non-compositional)
condition which is less useful for our purposes.

Questions:

- Given our work on paranaturality and categories of diagonal elements,
  can we understand what's wrong and what would be right?
- Paranaturality is not always correct, but works in important cases
  (Church numerals, initial algebras, terminal coalgebras)
- What is the right category-theoretic notion of parametricity?
- Can we identify possibilities and rank them by likelihood of correctness?

### 5. Slice-Presheaf Equivalence for Diagonal Elements

There is a well-known equivalence between slices over a presheaf and presheaves
over its category of elements (`slicePresheafEquiv`, `sliceCopresheafEquiv`).

Is there something similar for diagonal elements?

- Is there an equivalence between slices over a profunctor (in the category
  of paranatural transformations) and profunctors over the category of
  diagonal elements?
- If not, what IS equivalent to profunctors over DiagElem?

### 6. Costructure Integral via Opposite Categories

The costructure integral has "opposite directionality" from the standard coend.
Could we express it as a coend after all using an opposite category (like
(DiagElem Γ)ᵒᵖ or similar)?

### 7. Grothendieck Construction Approach to Parametricity

Alternative to Rel-enrichment: use two-sided or connected Grothendieck
construction to form something larger than DiagElem:

- Two-sided construction: sliced over C × C, giving two morphisms
- Connected construction: sliced over Arrow(C), with connecting morphism
  in the object ensuring relationship between contravariant/covariant positions
- Use category-of-elements specialization where base category is discrete
- Arrow(C) has good properties: inclusion C ↪ Arrow(C) has both left and
  right adjoints (domain/codomain projections), preserving all limits/colimits

## Context Files

- GebLean/Paranatural.lean - Core paranatural definitions
- GebLean/ParanatAlg.lean - Algebra/coalgebra/dialgebra profunctors
- GebLean/HexagonCat.lean - Hexagon category and profunctor-dialgebra
- GebLean/DinaturalNumbers.lean - Church numerals application
- docs/updates-on-paranatural-category-theory-*.pdf - Problem descriptions

## Progress

### Investigation Results (2024-12-31)

#### Question 1: Dialgebra in Mathlib

**Finding**: Mathlib does NOT have a Dialgebra category for pairs of functors
`F,G : C → D`.  Mathlib has:

- `Endofunctor.Algebra F` for F : C → C
- `Endofunctor.Coalgebra F` for F : C → C
- `Dialectica.Dial` (different concept - Gödel's Dialectica interpretation)

**Proposed work**:

- Define `Dialgebra F G` category where objects are (c, φ : F(c) → G(c))
- Prove `DiagElem (DialgebraProf F G) ≌ Dialgebra F G`
- Prove natural isomorphisms:
  - `DialgebraProf (Functor.id C) G ≅ CoalgProf G`
  - `DialgebraProf F (Functor.id D) ≅ AlgProf F`

#### Question 2: Ends/Coends

**Finding**: StructuralEnd IS the Type-valued end:

- `StructuralEnd Γ = ∫_I Γ(I,I)`
- **Category**: The end is taken over C (the base category of the profunctor)
- **Characterization**: The end is the limit over the twisted arrow category Tw(C),
  or equivalently defined via the wedge condition / equalizer:

  ```text
  ∫_c Γ(c,c) = { (x_c) ∈ ∏_c Γ(c,c) | ∀f:c→d, Γ(f,d)(x_d) = Γ(c,f)(x_c) }
  ```

  This matches our StructuralEnd definition exactly.

**Finding**: StructuralCoend is NOT the standard coend:

- Standard coend: identifies (I, Δ(I,f)(a)) ~ (J, Δ(f,J)(a)) for a ∈ Δ(I,J)
- StructuralCoend: identifies (I,x) ~ (J,y) when Δ(I,f)(x) = Δ(f,J)(y) ∈ Δ(I,J)
- These have opposite "directionality" - coend uses elements FROM off-diagonal,
  StructuralCoend uses elements mapping TO off-diagonal

#### Question 3: Wedges/Cowedges

**Finding**: Wedges are not naturally diagonal elements.

- Wedges for F are elements of the end ∫_X F(X,X)
- The end is terminal in the wedge category
- The wedge category structure differs from DiagElem category structure
- Ends/coends are universal objects, not terminal/initial diagonal elements

#### Question 4: Parametricity vs Paranaturality Divergence

**Root cause analysis**:
The divergence occurs because:

- Paranaturality tests condition for morphism graphs: (r∘f, f∘r) pairs
- Parametricity tests condition for ALL relations R with f∘h = k∘f

For type φ : ∀X.((X → X) → X) → X:

- f∘(r∘f) = (f∘r)∘f always holds for morphism-graph pairs
- But arbitrary (h,k) with f∘h = k∘f need not have form (r∘f, f∘r)

**Ranked solutions** (by likelihood of correctness):

1. **Rel-enriched profunctors (HIGH likelihood)**
   - Replace Set with Rel (category of sets with relations as morphisms)
   - Define profunctors F̂ : Relᵒᵖ × Rel → Rel
   - Relational diagonal elements: (A,a) → (B,b) are relations R with (a,b) ∈ F̂(R,R)
   - This IS parametricity - morphisms are logical relations

2. **Fibered categories (MEDIUM-HIGH likelihood)**
   - Hermida-Jacobs fibration approach
   - Parametricity as lifting property in fibration of relations

3. **Reflexive graphs (MEDIUM likelihood)**
   - Category RGraph with reflexive relations
   - May work for first-order types

4. **Syntactic restriction (LOW likelihood)**
   - Limit to "linear" types where paranaturality = parametricity
   - Works but doesn't solve the general case

**Why paranaturality works for Church numerals, μF, νF**:
These types have "linear" structure where the morphism-graph pairs suffice.
The problematic types like ((X → X) → X) → X have nested higher-order iteration
creating non-linear patterns.

#### Question 5: Slice-Presheaf Equivalence for Diagonal Elements

**Finding**: The standard equivalence does NOT directly generalize.

The standard result `Over P ≌ (P.Elements ⥤ Type)` for presheaves P : Cᵒᵖ → Type
does not immediately give `Over Γ (in Paranat) ≌ (DiagElem Γ ⥤ Type)` for
profunctors Γ : Cᵒᵖ × C → Type.

**Reasons**:

1. DiagElem Γ only captures diagonal elements (c, x ∈ Γ(c,c)), losing off-diagonal
   information from Γ(a,b) where a ≠ b
2. Paranatural transformations η : Δ → Γ have components η_{a,b} for ALL (a,b),
   not just diagonal positions
3. The paranaturality condition constrains how diagonal and off-diagonal relate

**Partial results**:

- `Over Γ` in ordinary Nat ≌ `(Γ.Elements ⥤ Type)` (standard result)
- DiagElem Γ is a pullback: `Γ.Elements ×_{Cᵒᵖ×C} C` along the diagonal
- For Hom profunctor: `Paranat(Δ, Hom) ≅ DiagElem(Δ)` (Yoneda-type result)

**Updated conjecture**:

`Over Γ (in Paranat)` ≌ `Prof(DiagElem Γ)` (profunctors on DiagElem Γ)

Reasoning:

- Paranatural transformations have MIXED variance (contravariant + covariant)
- Copresheaves `(DiagElem Γ → Type)` only capture covariant structure
- Profunctors `((DiagElem Γ)ᵒᵖ × DiagElem Γ → Type)` capture mixed variance
- The off-diagonal values of Δ naturally encode profunctor data via transport

This is MORE PLAUSIBLE than the copresheaf conjecture.

**Recommended investigation**:

1. Study whether the Yoneda-type result `Paranat(Δ, Hom) ≅ DiagElem(Δ)` holds
2. Define the functor `Over Γ → Prof(DiagElem Γ)` explicitly
3. Construct and verify the inverse

#### Question 6: Costructure Integral via Opposite Categories

**Finding**: YES, StructuralCoend can be expressed as a colimit using (DiagElem F)ᵒᵖ.

The reason for the oppositization is that:

- Standard coend ∫^c F(c,c) quotients diagonal elements by "coming from" off-diagonal
- StructuralCoend quotients diagonal elements by "mapping to" off-diagonal
- These are DUAL operations

**Precise statement**:

```text
StructuralCoend F ≅ colim_{(DiagElem F)ᵒᵖ} π
```

where π : DiagElem F → Type is the carrier projection (c, s) ↦ c.

**Why (DiagElem F)ᵒᵖ**: The StructuralCoend identifies (x, a) ~ (y, f(a)) for
f : x → y in DiagElem F. In the opposite category, f becomes a morphism y → x,
so the colimit quotients by "reversed" morphisms, which gives the right direction.

**Not a standard coend on C**: This is NOT of the form ∫^c Γ(c,c) for a profunctor
Γ : Cᵒᵖ × C → Type. The difference is that DiagElem F morphisms are more
restrictive than C morphisms (they must preserve F-structure).

#### Question 7: Grothendieck Construction Approach to Parametricity

**Finding**: Grothendieck constructions over Set DO NOT directly capture parametricity.

The fundamental issue:

- Set has functions as morphisms, not relations
- Two-sided Grothendieck tests pairs (f, g) of functions = morphism graphs
- Connected Grothendieck adds arrow structure but arrows are still functions
- Neither captures general relations R : A × B

**Using Rel as base category DOES work**:

- DiagElem over Rel-enriched profunctors Γ̂ : Relᵒᵖ × Rel → Rel captures parametricity
- Connected Grothendieck E(F) for F : Tw(Rel) → Cat gives "internalized" parametricity
  with relations as first-class objects

**Comparison with Rel-enriched DiagElem**:

| Approach | Parametricity? | Effort | Notes |
| -------- | -------------- | ------ | ----- |
| DiagElem/Set | No (morph. graphs) | Low | Existing infra |
| Two-sided/Set | No (func. pairs) | Medium | More structure |
| DiagElem/Rel | YES | Medium | Direct, clean |
| Connected/Rel | YES | Higher | Rel first-class |

**Conclusion**: The Grothendieck approach doesn't AVOID the need for Rel. It adds
value for:

- Making relations first-class objects in the category
- Compositional categorical structure via fibrations
- "Internalized" parametricity where relation witnesses are explicit

For basic parametricity, Rel-enriched DiagElem is simpler and more direct.

### Proposed Implementation Path

1. Implement Dialgebra category and prove equivalences (Question 1)
2. Document the end = StructuralEnd correspondence formally (Question 2)
3. Explore Rel-enriched diagonal elements for parametricity (Question 4)
4. Investigate `Paranat(Δ, Hom) ≅ DiagElem(Δ)` and implications for Question 5
5. Verify `Over Γ ≌ Prof(DiagElem Γ)` conjecture (Question 5 updated)
6. Formalize StructuralCoend as colimit over (DiagElem F)ᵒᵖ (Question 6)
