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
from what we get from paranaturality (strong dinaturality).

Questions:

- Given our work on paranaturality and categories of diagonal elements,
  can we understand what's wrong and what would be right?
- Paranaturality is not always correct, but works in important cases
  (Church numerals, initial algebras, terminal coalgebras)
- What is the right category-theoretic notion of parametricity?
- Can we identify possibilities and rank them by likelihood of correctness?

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

- Dinaturality tests condition for morphism graphs: (r∘f, f∘r) pairs
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
   - Limit to "linear" types where dinaturality = parametricity
   - Works but doesn't solve the general case

**Why paranaturality works for Church numerals, μF, νF**:
These types have "linear" structure where the morphism-graph pairs suffice.
The problematic types like ((X → X) → X) → X have nested higher-order iteration
creating non-linear patterns.

### Proposed Implementation Path

1. Implement Dialgebra category and prove equivalences (Question 1)
2. Document the end = StructuralEnd correspondence formally (Question 2)
3. Explore Rel-enriched diagonal elements for parametricity (Question 4)
