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

### 8. Extranatural Transformations and Paranaturality

Investigate the relationship between extranatural transformations
(Eilenberg-Kelly 1966) and paranatural/strong dinatural transformations:

- Does mathlib have extranatural transformations?
- What is the precise relationship to paranaturality?
- Is there a "strong extranatural" notion combining both generalizations?
- What are the connections to parametricity?

### 9. DiagElem as Connected Grothendieck Subcategory

**Conjecture**: The category of diagonal elements `DiagElem(Γ)` for a profunctor
`Γ : Cᵒᵖ × C → Type` is a subcategory of a specialization of the connected
Grothendieck construction. The construction proceeds as follows:

1. **Forgetful functor**: There is a forgetful functor `Tw(C) → Cᵒᵖ × C` that
   forgets the morphism in objects (sending `(f : a → b)` to `(a, b)`).

2. **Precomposition**: Given `Γ : Cᵒᵖ × C → Type`, precompose with the forgetful
   functor to obtain `Γ̃ : Tw(C) → Type`.

3. **Discrete inclusion**: Post-compose with the `Set → Cat` inclusion (treating
   sets as discrete categories) to obtain `Γ̂ : Tw(C) → Cat`.

4. **Connected Grothendieck**: Apply the connected Grothendieck construction to
   `Γ̂` to obtain a category over `Arrow(C)`.

5. **Diagonal restriction**: Take the full subcategory where objects have
   `domain = codomain` and the morphism is the identity. This forces the two
   components of Arrow(C) morphisms to coincide (since `m ∘ id = id ∘ m` means
   `m = m`).

6. **Discrete collapse**: Since the target categories are discrete, fiber
   morphisms reduce to equalities, which should give exactly the DiagElem
   compatibility condition.

**Questions**:

- Is this conjecture correct?
- If so, what is the precise equivalence or isomorphism?
- If not, what is the correct relationship between DiagElem and connected
  Grothendieck?
- Does this perspective suggest new properties of DiagElem?

### 10. Tw(C)-Copresheaves as Foundation for Parametricity

**Motivation**: DiagElem(Γ) is a restriction of the connected Grothendieck
construction to diagonal elements. This raises the question: are we losing
something by this restriction? Would we gain better categorical properties
by working with the full connected Grothendieck construction?

**Core proposal**: Instead of studying profunctors `Γ : Cᵒᵖ × C → Type` with
paranatural transformations, study copresheaves on twisted-arrow categories
`F : Tw(C) → Type` with natural transformations.

**Rationale**: For parametricity, we ultimately care about diagonal elements
(where the type variable is instantiated to the same type on both sides).
The twisted-arrow category Tw(C) naturally includes the "connecting morphism"
between contravariant and covariant positions. Objects of Tw(C) are arrows
`f : a → b`, which encode exactly this connection.

**Questions**:

1. Do natural transformations between Tw(C)-copresheaves correspond to
   paranatural transformations when restricted to the diagonal?

2. Would "connected transformations" (natural transformations between
   Tw(C)-copresheaves) have better compositional properties than paranatural
   transformations?

3. Is `[Tw(C), Set]` (copresheaves on twisted arrows) a better setting for
   parametricity than profunctors with paranatural transformations? Note that
   `[Tw(C), Set]` has good categorical properties (locally presentable,
   cocomplete) while profunctors with paranaturality do not form a topos.

4. What is the precise relationship between:
   - Profunctors `Cᵒᵖ × C → Type`
   - Tw(C)-copresheaves `Tw(C) → Type`
   - Arrow(C)-copresheaves `Arrow(C) → Type`

5. Could this approach resolve the parametricity/paranaturality divergence
   (Question 4)?

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

**Possible Yoneda-type result (UNVERIFIED)**:

The standard profunctor Yoneda lemma is `Nat(Hom, Γ) ≅ ∫_c Γ(c,c)` — transformations
**FROM** the Hom profunctor correspond to elements of the end. A paranatural
analogue might be:

```text
Paranat(Hom, Δ) ≅ StructuralEnd(Δ)
```

Note: This involves transformations FROM Hom, matching the direction of standard
Yoneda. Also note that StructuralEnd is a type (the end ∫_c Δ(c,c)), whereas
DiagElem is a category — these are related but distinct.

**Updated conjecture**:

`Over Γ (in Paranat)` ≌ `Prof(DiagElem Γ)` (profunctors on DiagElem Γ)

Reasoning:

- Paranatural transformations have MIXED variance (contravariant + covariant)
- Copresheaves `(DiagElem Γ → Type)` only capture covariant structure
- Profunctors `((DiagElem Γ)ᵒᵖ × DiagElem Γ → Type)` capture mixed variance
- The off-diagonal values of Δ naturally encode profunctor data via transport

This is MORE PLAUSIBLE than the copresheaf conjecture.

**Open sub-question**: What are the morphisms in `Prof(DiagElem Γ)`?

- Option A: Natural transformations (standard profunctor category)
- Option B: Paranatural transformations (recursive paranaturality)

The left side uses paranatural transformations explicitly. The right side could
use either. The standard slice-presheaf equivalence uses natural transformations
on both sides, but here paranaturality might propagate. This needs investigation.

**Recommended investigation**:

1. Verify whether `Paranat(Hom, Δ) ≅ StructuralEnd(Δ)` holds
2. Define the functor `Over Γ → Prof(DiagElem Γ)` explicitly
3. Determine which morphism structure (natural vs paranatural) makes this work
4. Construct and verify the inverse

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

#### Question 8: Extranatural Transformations and Paranaturality

**Research findings**:

Mathlib has `CategoryTheory.DinatTrans` (weak dinatural transformations) but does
NOT have strong dinatural transformations or extranatural transformations.

**Terminology clarification** (confirmed by literature):

- **Dinatural** (weak): Components α_c : F(c,c) → G(c,c) satisfying hexagon for
  morphisms f : c → c'. Condition only required for canonical span. Do NOT
  compose in general.
- **Strong dinatural** (Mulry 1992): Same components but hexagon must hold for
  ALL spans. These DO compose.
- **Paranatural** = Strong dinatural (confirmed by Neumann 2023, arXiv:2307.09289)
- **Extranatural** (Eilenberg-Kelly 1966): For functors with mixed variance where
  some variables appear only in one component. Compose under "no cycle" condition.

**Relationship diagram**:

```text
                    Natural
                       |
               Extranatural (special shape)
                       |
                   Dinatural (weak)
                       ^
        Strong Dinatural = Paranatural (stronger condition)
```

Extranatural and strong dinatural are ORTHOGONAL: extranatural concerns functor
shape, strong concerns condition strength. Both generalize natural transformations
but in different directions.

**Relationship to parametricity**:

Strong dinaturality captures graph-relation parametricity (Vene 2006, Eppendahl
1999). A family is strong dinatural iff it preserves pullback-defined relations
R_{F,f}. This matches our Question 4 analysis: paranaturality tests morphism
graphs, not all relations.

The CCC limitation: Strong dinatural transformations don't form a Cartesian
closed category, explaining why they can't model all polymorphic types including
nested function types.

**Open questions**:

1. Is there a "strong extranatural" notion combining both generalizations?
2. Precise characterization of types where paranaturality = parametricity
3. DiagElem analogue for extranatural transformations
4. Strong dinaturality in enriched settings (extranatural generalizes to enriched
   categories, but dinatural only works for Cartesian enrichment)
5. Connection between standard ends (weak extranaturality via wedges) and
   StructuralEnd

**References**:

- Mulry, "Strong Monads, Algebras and Fixed Points" (1992) - original definition
- Neumann, "Paranatural Category Theory" (2023, arXiv:2307.09289) - confirms
  paranaturality = strong dinaturality
- Eppendahl, "Parametricity and Mulry's Strong Dinaturality" (1999)
- Vene, "Parametricity and Strong Dinaturality" (2006)
- Eilenberg-Kelly, "A generalization of the functorial calculus" (1966) -
  extranatural transformations

#### Question 9: DiagElem as Connected Grothendieck Subcategory

Assessment: LIKELY CORRECT (90% confidence)

The conjecture that `DiagElem(Γ)` arises as a subcategory of the connected
Grothendieck construction appears to be correct. The precise statement is:

```text
DiagElem(Γ) ≅ ConnGroth(Γ̂) ×_{Arrow(C)} C
```

where:

- `Γ̂ : Tw(C) → Cat` is the discrete-category-valued functor induced from Γ
- `ConnGroth` is the connected Grothendieck construction
- The pullback is along the diagonal `Δ : C → Arrow(C)` sending `c ↦ id_c`

**Why it works**:

1. **Objects match**: On the connected Grothendieck side, objects over identity
   arrows are `(id_c, s ∈ Γ(c,c))`, which corresponds exactly to DiagElem
   objects `(c, s ∈ Γ(c,c))`.

2. **Arrow(C) morphisms between identities are single morphisms**: A morphism
   `id_a → id_b` in Arrow(C) consists of `(α,β)` with `β ∘ id = id ∘ α`, forcing
   `α = β`. So morphisms are just `m : a → b` in C.

3. **The two-sided fiber transport gives the DiagElem condition**: In the
   two-sided Grothendieck pattern for `Ψ : Aᵒᵖ × B → Cat`, a morphism involves
   comparing `b!(x)` with `a*(x')`. When applied to the diagonal of a profunctor
   `Γ`, this yields exactly:

   ```text
   Γ(id, m)(s) = Γ(m, id)(t)  in Γ(a, b)
   ```

   which is the DiagElem compatibility condition.

**Generalization**: Just as the ordinary Grothendieck construction
generalizes the category of elements (setting fibers = discrete categories),
the connected Grothendieck construction generalizes DiagElem. The "connected"
aspect naturally captures the two-directional transport that defines diagonal
element morphisms.

**Remaining verification needed**:

- Confirm the exact implementation of connected Grothendieck in the codebase
  matches this analysis
- Verify coherence conditions and universe level handling
- Determine whether the relationship is isomorphism or merely equivalence

#### Question 10: Tw(C)-Copresheaves as Foundation for Parametricity

**Findings (probability-ordered)**:

**(95%) [Tw(C)ᵒᵖ, Set] is a topos - CONFIRMED**

Presheaf categories are always topoi. This gives exponentials, subobject
classifiers, and internal logic. This is a structural advantage over
profunctors with paranatural transformations.

(80%) Neither Tw(C) nor Arrow(C) naturality equals paranaturality - LIKELY

Detailed analysis reveals:

- **Tw(C) morphisms between identities**: `(α,β) : id_a → id_b` requires
  `β ∘ α = id_b` (section-retraction pairs). This is MORE RESTRICTIVE than
  arbitrary morphisms `m : a → b`.

- **Arrow(C) morphisms between identities**: `(m,m) : id_a → id_b` for any
  `m : a → b`. The naturality condition becomes `η ∘ Γ(m,m) = Δ(m,m) ∘ η`,
  which tests the diagonal action, not the paranaturality hexagon.

- **Paranaturality** tests: `Δ(id,m) ∘ η ∘ Γ(m,id) = Δ(m,id) ∘ η ∘ Γ(id,m)`,
  comparing two different transport paths.

These are fundamentally different coherence conditions.

(60%) Tw(Rel) copresheaves may capture full parametricity - PLAUSIBLE

If we replace Set with Rel (relations as morphisms), then:

- Morphisms in C = Rel are relations R : A ↔ B
- Tw(Rel) objects are relations
- Natural transformations would test relational parametricity

This connects to Question 4's finding that Rel-enrichment is needed for full
parametricity.

**(40%) A "connected transformation" notion better than paranaturality exists -
UNCERTAIN**

We could define "connected transformations" as natural transformations between
genuine Tw(C)-copresheaves (not just profunctors viewed through the restriction
functor). These would:

- Have components `η_f : F(f) → G(f)` for ALL arrows f, not just identities
- Satisfy naturality for Tw(C) morphisms

But it's unclear whether this captures anything useful for parametricity that
paranaturality doesn't.

(30%) Pure Tw(Set) approach resolves parametricity divergence - UNLIKELY

The parametricity/paranaturality divergence (Question 4) stems from paranaturality
testing function graphs while parametricity tests all relations. Tw(Set) still
only has functions as morphisms, so it likely inherits the same limitation.

**What we lose by restricting to DiagElem**:

- Information about non-identity connecting morphisms
- The topos structure of the ambient category

**What we gain by staying with DiagElem**:

- Direct connection to existing paranatural transformation theory
- Simpler objects (diagonal elements vs full arrow-indexed families)
- The paranaturality condition itself (which Tw(C)/Arrow(C) naturality doesn't
  capture)

**Conclusions**:

1. Tw(C)-copresheaves provide better categorical structure (topos) but don't
   capture paranaturality

2. For parametricity, Tw(Rel) or Rel-enriched approaches remain the most
   promising direction

3. The connected Grothendieck perspective (Question 9) explains WHERE DiagElem
   comes from but doesn't suggest it should be REPLACED

4. A hybrid approach might work: use Tw(C)-copresheaves for the ambient category
   structure but impose paranaturality conditions separately

### Proposed Implementation Path

1. Implement Dialgebra category and prove equivalences (Question 1)
2. Document the end = StructuralEnd correspondence formally (Question 2)
3. Explore Rel-enriched diagonal elements for parametricity (Question 4)
4. Investigate `Paranat(Hom, Δ) ≅ StructuralEnd(Δ)` and implications (Question 5)
5. Verify `Over Γ ≌ Prof(DiagElem Γ)` conjecture (Question 5 updated)
6. Formalize StructuralCoend as colimit over (DiagElem F)ᵒᵖ (Question 6)
7. Prove DiagElem ≅ ConnGroth(Γ̂) ×_{Arrow(C)} C (Question 9)
8. Investigate Tw(Rel)-copresheaves for full parametricity (Question 10)
