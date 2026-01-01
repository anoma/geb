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

### 11. PHOAS, Mendler Algebras, and Dual-Variance Recursion

**References**:

- "PHOAS for Free" (Edward Kmett):
  <https://www.schoolofhaskell.com/user/edwardk/phoas>
- Uustalu, "Mendler-style Inductive Types, Categorically" (categorified Mendler)
- Idris-2 implementations in docs/PolyDifuncTest.idr and docs/InternalProfunctor.idr

**Background**:

Parametric Higher-Order Abstract Syntax (PHOAS) and Mendler algebras are
approaches to handling dual-variance (contravariant × covariant) in recursive
data structures. These may share limitations with paranatural transformations.

**PHOAS approach**:

The ExpF functor `ExpF a b = App b b | Lam (a → b)` is a profunctor:

- Contravariant in `a` (appears in negative position in Lam)
- Covariant in `b` (appears in positive positions)

The recursion scheme: `Rec p a b = Place b | Roll (p a (Rec p a b))`

Closed terms are obtained via the end: `∀x. Rec p x x`

**Mendler algebra formulas** (from Idris-2 implementations):

```text
MendlerAlg g c = ((x : Type) → (x → c) → g x x → c)
ProfMendlerExt g c = (x : Type ** (x → c, g x x))
ProfMendlerUniv g c = ((x : Type) → ((y : Type) → (y → c) → g y y → x) → x)
```

The existential form is the coend formula `∫ˣ (x → c) × g(x,x)`, and MendlerAlg
is a cowedge. The universal form is a CPS encoding of the same.

**Questions**:

1. Do PHOAS and Mendler algebras share limitations with paranaturality?

2. Does the "diagonal-first" nature of these approaches (immediately working
   with P(x,x)) lose information that Tw(C)-copresheaves preserve?

3. Can Mendler algebras be enriched over categories other than Set?

4. Is there a categorical analogue of parametric polymorphism beyond relational
   parametricity?

5. Is there a "free PHOAS monad" construction in the connected Grothendieck
   setting?

**OPEN QUESTION**: This is an active area of investigation. The implementations
in docs/ contain computational content but (as noted by the implementer) may be
missing explicit paranaturality/commutativity conditions. The relationship
between PHOAS/Mendler approaches and full categorical paranaturality needs
further study.

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

(60%) Tw(Rel) copresheaves may capture full parametricity - PLAUSIBLE BUT LIMITED

If we replace Set with Rel (relations as morphisms), then:

- Morphisms in C = Rel are relations R : A ↔ B
- Tw(Rel) objects are relations
- Natural transformations would test relational parametricity

This connects to Question 4's finding that Rel-enrichment is needed for full
parametricity.

However, there are structural concerns:

- **Rel is NOT a topos**: It lacks cartesian closure (no exponentials) and a
  standard subobject classifier. Rel is instead a dagger category / allegory /
  ∗-autonomous category (connected to linear logic).

- **[Tw(Rel)ᵒᵖ, Set] IS a topos**: Presheaves on any small category form a
  topos. So we could work in this presheaf topos while using Rel's relational
  structure.

- **But Rel is a FIXED category**: It doesn't parameterize over arbitrary C.
  This approach addresses Reynolds-style relational parametricity specifically,
  not "parametricity over an arbitrary category C."

These are fundamentally different concerns:

1. **Paranaturality over C**: Works for any category C (parametric in C)
2. **Relational parametricity**: Semantic notion specific to Set/Rel settings

For arbitrary C, one might consider Span(C) (where Span(Set) ≅ Rel) or internal
relations Rel(C) (if C has finite limits). A parameterized version might be
[Tw(Span(C))ᵒᵖ, Set] (at the cost of more work!).

Clarification - why both Span and Tw are needed:

These constructions serve different purposes and don't replace each other:

| Construction | Provides | Missing |
| ------------ | -------- | ------- |
| [Span(C)ᵒᵖ, Set] | Relational morphisms, topos | Profunctor structure |
| [Tw(C)ᵒᵖ, Set] | Connecting-morphism structure, topos | Relational morphisms |
| [Tw(Span(C))ᵒᵖ, Set] | Both | - |

- **[Span(C)ᵒᵖ, Set]** = presheaves on Span(C). For each object a: a set F(a).
  For each span a ← R → b: a function F(b) → F(a). This is NOT profunctors -
  it lacks the mixed variance (contravariant × covariant on pairs).

- **Profunctors on Span(C)** = Span(C)ᵒᵖ × Span(C) → Set. Proper profunctor
  structure with mixed variance. Paranaturality makes sense here. But this
  changes the BASE category to Span(C).

- **[Tw(Span(C))ᵒᵖ, Set]** = presheaves on Tw(Span(C)). Objects are spans in C.
  This connects to profunctors via diagonal-restriction (Question 9) while
  providing relational morphisms.

The Tw(-) part gives profunctor-like structure (objects are morphisms/spans,
encoding the connection between source and target). Span(C) upgrades the
morphisms from functions to relations/spans. The full [Tw(Span(C))ᵒᵖ, Set]
combines both.

(40%) A "connected transformation" notion better than paranaturality exists -
UNCERTAIN

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

2. Two distinct concerns must be separated:
   - **Paranaturality over arbitrary C**: A categorical notion that works for
     any category C
   - **Relational parametricity**: A semantic notion (Reynolds-style) specific
     to Set/Rel, testing polymorphism against all relations

3. [Tw(Rel)ᵒᵖ, Set] is a topos (even though Rel itself is not), providing
   logical structure while using relational morphisms. But this addresses only
   relational parametricity, not parametricity over arbitrary C.

4. For arbitrary C, Span(C) or Rel(C) might provide "relations in C," leading
   to [Tw(Span(C))ᵒᵖ, Set], but this requires further investigation.

5. The connected Grothendieck perspective (Question 9) explains WHERE DiagElem
   comes from but doesn't suggest it should be REPLACED

6. A hybrid approach might work: use Tw(C)-copresheaves for the ambient category
   structure but impose paranaturality conditions separately

#### Question 11: PHOAS, Mendler Algebras, and Dual-Variance Recursion

This is an open question under active investigation.

Findings (probability-ordered):

(95%) PHOAS and Mendler algebras are computational manifestations of ends/coends

- PHOAS "closed terms" = end `∫ₓ P(x,x)` = sections of the forgetful functor
- Mendler algebras = cowedges for coends
- Both rely on parametric polymorphism to get naturality/coherence for free
- The Idris implementations confirm: `MendlerAlg g c` is the cowedge formula,
  `ProfMendlerExt g c` is the coend formula `∫ˣ (x → c) × g(x,x)`

(90%) These approaches share the "diagonal collapse" limitation as DiagElem

- PHOAS immediately reduces to P(x,x)
- Mendler folds P(x,x) into c
- Neither directly captures the full profunctor P(a,b) for a ≠ b
- This mirrors our finding that DiagElem loses off-diagonal information

(85%) Tw(C)-copresheaves generalize PHOAS by preserving off-diagonal information

- Objects of Tw(C) are morphisms a → b (including a ≠ b cases)
- [Tw(C)ᵒᵖ, Set] captures the full profunctor structure
- The hexagon category lives naturally in this setting
- PHOAS is "diagonal-first"; Tw(C)-copresheaves are "profunctor-first"

(75%) A "categorical Mendler algebra" would be a cowedge in an enriched setting

- Requires coends to exist in the enriching category
- In Set-enriched case, reduces to standard Mendler algebra
- In general case, needs explicit coherence conditions
- This parallels DiagElem: in Set, parametricity gives wedge conditions for
  free; in general categories, we need explicit conditions

(70%) The connected Grothendieck construction provides the "right" bridge

- Takes a profunctor P : Cᵒᵖ × C → Cat
- Builds a fibration over Arr(C) capturing arrow dependence
- Unifies PHOAS diagonal structure with full profunctor variation
- May support a "free PHOAS monad" construction

**Analysis of Idris implementations**:

The user noted these implementations "don't include most of the
paranaturality/commutativity conditions, but they do have the computational
content." This is significant:

1. The computational content (recursion) works without explicit coherence
2. But coherence (paranaturality) is implicitly enforced by parametricity
3. When moving beyond Set to arbitrary C, coherence must be made explicit

This mirrors our DiagElem finding: in Set, parametric polymorphism gives wedge
conditions for free; in general categories, we need explicit conditions.

**Open questions**:

- Can Mendler algebras be enriched over categories other than Set?
- Does parametric polymorphism have a categorical analogue beyond relational
  parametricity?
- Is there a "free PHOAS monad" construction in the connected Grothendieck
  setting?

### 12. Extending Polynomial Functors to Dual Variances

**Motivation**: We have polynomial functors (coproducts of covariant representables)
for single-variance situations, but Neumann's counterexample type
`∀X.((X → X) → X) → X` appears "non-polynomial" due to the exponential structure.
Can we extend the polynomial framework to handle dual-variance profunctors?

**Proposed approaches**:

1. Profunctors as polynomial generalization: A polynomial P(X) = Σᵢ Xⁿⁱ generalizes
   to a profunctor P(A,B) = Σᵢ Aᵐⁱ × Bⁿⁱ
2. Tw(C)-copresheaves as the natural setting: Objects of Tw(C) are arrows,
   encoding the connection between contravariant and covariant positions
3. Dialgebras of polynomial functors as a test case

**Questions**:

1. How do we express "polynomial profunctor" precisely?
2. Does [Tw(C)ᵒᵖ, Type] provide the right completion for dual-variance polynomials?
3. How does this relate to the free coproduct completion (Dirichlet functors)?
4. Can we characterize which types are "polynomial" in the dual-variance sense?

**Investigation Results (2025-01-01)**:

(80%) Polynomial profunctors should be defined as coproducts of "birepresentables"

A birepresentable profunctor is `Hom(A, -) × Hom(-, B) : Cᵒᵖ × C → Set`, sending
(X, Y) to `Hom(A, Y) × Hom(X, B)`. Polynomial profunctors would then be:

```text
P(X, Y) = Σᵢ Hom(Aᵢ, Y)^mᵢ × Hom(X, Bᵢ)^nᵢ
```

This parallels how polynomial functors are coproducts of representables.

(75%) The Niu-Spivak framework (arXiv:2312.00990) provides a modern foundation

The 2024 monograph "Polynomial Functors: A Mathematical Theory of Interaction"
emphasizes that polynomial functors model "two-way communication" with positions
sending forward and directions sending backward. This bidirectional structure
is precisely the profunctor pattern (contravariant × covariant).

(70%) [Tw(C)ᵒᵖ, Set] is a natural completion but not automatically polynomial

Presheaf categories are always topoi, giving [Tw(C)ᵒᵖ, Set] all limits, colimits,
and exponentials. However, just as [Cᵒᵖ, Set] contains non-polynomial presheaves,
[Tw(C)ᵒᵖ, Set] contains non-polynomial copresheaves. We need additional structure
(e.g., a "polynomial subcategory") to characterize the polynomial ones.

(60%) The exponential in Neumann's counterexample may require passage to Dirichlet

Dirichlet functors (via free coproduct completion) include exponentials. If we
want to capture `(X → X) → X` as "polynomial," we may need the Dirichlet
extension of polynomial functors. For profunctors, this would be the free
coproduct completion of birepresentables.

**Codebase connection**:

Our `PolyAlg.lean` defines algebras of polynomial endofunctors on `Over X`.
Extending this to profunctor-valued situations would require:

1. Define `PolyProf X Y` as X-indexed families of polynomial profunctors
2. Define dialgebras for polynomial profunctors (connecting to ParanatAlg.lean)
3. Study the free completion to include exponentials

**References**:

- nLab polynomial functor
- Niu-Spivak "Polynomial Functors" (arXiv:2312.00990)
- Logical Methods in Computer Science 2024 paper on profunctors and species

### 13. Yoneda Embedding and CCC Requirement

**Observation**: Neumann's counterexample requires a Cartesian closed category
(for the exponential (X → X) → X). An arbitrary category C may not be CCC.

**Proposal**: Embed C into its presheaf category [Cᵒᵖ, Set], which IS a topos
(hence CCC). Then study paranaturality in this richer setting.

**Questions**:

1. Does the Yoneda embedding preserve/reflect paranaturality?
2. Can we characterize "representable paranaturals" (those coming from C)?
3. Does embedding in a CCC help or hurt the parametricity correspondence?
4. What is the relationship between profunctors on C and profunctors on [Cᵒᵖ,Set]?

**Investigation Results (2025-01-01)**:

(95%) [Cᵒᵖ, Set] is always a topos with all required structure - CONFIRMED

Presheaf categories have:

- All limits and colimits (computed objectwise)
- Exponential objects: Q^P(c) = Set^(C^op)(C(−, c) × P, Q)
- Subobject classifier via sieves
- Internal logic suitable for parametricity reasoning

(85%) The Yoneda embedding y : C → [Cᵒᵖ, Set] should preserve paranaturality

The Yoneda embedding is full and faithful. For paranatural transformations
η : Γ → Δ between profunctors on C, we can extend to profunctors on [Cᵒᵖ, Set]
by Kan extension. The key question is whether paranaturality conditions lift.

Conjecture: If η is paranatural for profunctors on C, then Lan_y(η) is
paranatural for the extended profunctors on [Cᵒᵖ, Set].

(80%) The CCC structure allows forming the problematic types

In [Cᵒᵖ, Set], we can form:

- Function spaces P → Q as exponential presheaves
- The problematic type `∀X.((X → X) → X) → X` as an end over presheaves
- Full parametricity reasoning via the internal logic

(70%) Profunctors on C embed into profunctors on [Cᵒᵖ, Set]

There should be a functor:

```text
Prof(C) → Prof([Cᵒᵖ, Set])
```

sending Γ : Cᵒᵖ × C → Set to the Kan extension along y × y^op.

(60%) This may not solve the parametricity divergence directly

The problem from Q4 is that paranaturality tests morphism graphs while
parametricity tests all relations. Embedding in a topos gives us more
structure (internal logic, subobject classifier), but the divergence
remains unless we use Rel-enrichment or a similar relational approach.

**Tentative conclusion**:

The Yoneda embedding approach is valuable for:

1. Ensuring exponentials exist for types like (X → X) → X
2. Providing internal logic for reasoning about parametricity
3. Studying representable vs non-representable paranaturals

But it does not automatically resolve the paranaturality/parametricity
divergence. That requires the Rel-enriched approach from Q4/Q10.

**References**:

- nLab category of presheaves
- John Baez "Topos Theory" series

### 14. Mathematical Model Behind Free Theorems

**Core question**: If we can STATE what the free theorem should be (as in Neumann's
slides: "for all h,k with f∘h = k∘f, we have..."), then what mathematical model
underlies that statement? And if we have that model, why not use it directly?

**Analysis needed**:

1. What is the precise categorical/type-theoretic formulation of "free theorem"?
2. Reynolds' relational parametricity uses logical relations - is there a
   category-theoretic analogue?
3. The divergence (Q4) shows paranaturality ≠ parametricity. What IS the
   right categorical notion?
4. Is there a universal property characterizing "parametric" polymorphism?

**Investigation Results (2025-01-01)**:

(95%) The model is REFLEXIVE GRAPH CATEGORIES - established by Dunphy-Reddy

The categorical semantics of parametricity uses reflexive graph categories.
Key sources:

- Dunphy's 2002 thesis "Parametricity as a Notion of Uniformity in Reflexive
  Graphs" (supervised by Reddy)
- Hermida-Reddy-Robinson "Reynolds Programme for Category Theory" (2014)

A reflexive graph category is a category with:

- Objects that carry reflexive graph structure (objects with "edge" relations)
- Morphisms that preserve this structure
- Parametric limits that give uniform polymorphic functions

(90%) Why we don't "just use" reflexive graph categories - COMPLEXITY

1. **Impredicativity problem**: Reynolds' original model requires an
   impredicative universe (like CIC). The theory becomes meta-theoretically
   demanding.

2. **Higher-order complications**: State and recursion complicate the models.
   Representation results require additional conditions (Sojakova-Johann 2018).

3. **Multiple valid models**: The framework admits different instantiations:
   - Reynolds' original model
   - PER model (Longo-Moggi)
   - Proof-relevant parametricity (Orsanigo)
   - Functorial parametricity

(85%) The "scone" construction provides categorical understanding

Mike Shulman's explanation (n-Category Cafe): The scone of a syntactic category
packages logical relations into categorical structure. For a type A, a "witness"
is a lifting to the scone category. This reveals WHY logical relations work -
they arise from universal properties.

(80%) Fibrations provide an alternative categorical formulation

Hermida-Jacobs approach: Parametricity as a lifting property in fibrations.
The 2014 paper combines:

- Reflexive-graph-category structure for relational parametricity
- Fibrational models of impredicative polymorphism
- Comprehension in the sense of Lawvere

(75%) Proof-relevant parametricity is emerging as better model

Recent work (ACM JACM 2021, Sojakova-Johann) develops proof-relevant
parametricity where witnesses of relatedness are themselves suitably related.
This generalizes Reynolds' proof-irrelevant relations to families with
non-trivial evidence.

(70%) Why paranaturality ≠ parametricity - MORPHISM GRAPHS vs RELATIONS

The fundamental divergence:

- Paranaturality tests: pairs (r∘f, f∘r) for morphisms r
- Parametricity tests: ALL pairs (h,k) with f∘h = k∘f

In reflexive graph categories:

- Morphisms ARE relations (reflexive graphs)
- Natural transformations in the graph category capture full parametricity
- Restriction to "morphism graphs" (diagonal relations) gives paranaturality

**Summary answer to Q14**:

The mathematical model IS reflexive graph categories (Dunphy-Reddy framework),
plus fibrations (Hermida-Jacobs), plus proof-relevance (recent work). We don't
"just use it" because:

1. The theory is technically demanding
2. Multiple models exist with different trade-offs
3. For many applications (initial algebras, Church numerals), paranaturality
   suffices, and is simpler
4. The full theory requires impredicativity in the meta-theory

**References**:

- Hermida-Reddy-Robinson (2014) - Reynolds Programme
- Dunphy thesis (2002) - Reflexive graphs
- Sojakova-Johann (2018) - General framework
- Shulman (2013) - Scones and logical relations

### 15. Relations-Based Approach from CategoryJudgments

**Observation**: CategoryJudgments.lean represents categorical structure as a
copresheaf on a finite category. The objects (Obj, Mor, Id, Comp) and morphisms
encode the typing constraints. This is a "freely generated then quotiented"
approach.

**Proposal for dual-variance**: Apply the same pattern:

1. Start with a category representing dual-variance structure
   (possibly Arrow(C) or Tw(C))
2. Consider copresheaves on this category - they freely represent dual-variance data
3. Add relations/equations that quotient to get functional operations
4. This gives a profunctor-like structure with explicit coherence

**Questions**:

1. What is the right "judgment category" for dual-variance data?
2. How do copresheaves on Tw(C) vs Arrow(C) differ for this purpose?
3. Can the quotienting step capture paranaturality or full parametricity?
4. How does this relate to the span/relation approach from Q10?

**Investigation Results (2025-01-01)**:

(90%) CategoryJudgments pattern is directly applicable

Our CategoryJudgments.lean defines:

- Objects: `Obj`, `Mor`, `Id`, `Comp` representing judgment types
- Morphisms: `dom`, `cod`, `idMor`, `left`, `right`, `composite`
- Coherence: equations like `idMor ≫ dom = idObj` enforced by the category

A copresheaf F : CategoryJudgments → Type assigns:

- F(Obj) = type of objects
- F(Mor) = type of morphisms
- F(Id) = type of identity witnesses
- etc.

This pattern extends to dual-variance by choosing the right indexing category.

(85%) Tw(C) is the right "judgment category" for dual-variance

For dual-variance data (profunctor-like), the indexing category should be Tw(C):

- Objects: arrows f : a → b (encoding both domain and codomain types)
- Morphisms: commuting squares (encoding transport in both directions)

A copresheaf F : Tw(C) → Type assigns:

- F(f : a → b) = "elements at connection f"
- Functoriality gives transport along commuting squares

This matches our connected Grothendieck construction from ConnectedGrothendieck.lean.

(80%) Span(C) gives the relational extension

For full parametricity (not just paranaturality), we need Span(C):

- Objects of Span(C) are objects of C
- Morphisms a → b are spans: a ← R → b (generalizing functions to relations)

The key fact: Span(Set) ≅ Rel (category of sets and relations).

For arbitrary C with pullbacks, Span(C) forms a bicategory with:

- 1-cells: spans a ← R → b
- 2-cells: morphisms of spans (pullback diagrams)

(75%) The combined approach: copresheaves on Tw(Span(C))

To capture both:

- Dual-variance structure (via Tw)
- Relational morphisms (via Span)

Consider: `[Tw(Span(C))ᵒᵖ, Set]`

Objects of Tw(Span(C)) are spans with direction (arrows in Span(C)).
This is the natural setting for profunctors with relational transport.

(70%) Quotienting can capture paranaturality, possibly full parametricity

In the freely-generated-then-quotiented pattern:

1. Freely generate: copresheaves on the indexing category
2. Quotient: add equivalence relations encoding coherence

For paranaturality: quotient by the hexagon condition
For parametricity: quotient by the full relational condition

The question is whether parametricity can be expressed as a quotient of freely
generated data, or whether it requires the relational structure intrinsically.

(65%) Connection to reflexive graphs

Reflexive graph categories (from Q14) can be viewed as:

- Objects: sets with a reflexive relation
- Morphisms: functions preserving the relation

This IS a special case of the span approach:

- A reflexive graph (X, R) where R ⊆ X × X is reflexive
- Morphisms preserve R, which generalizes preserving functions

**Proposed approach for dual-variance parametricity**:

1. Define `DualVarianceJudgments` as a category similar to CategoryJudgments
   but with objects encoding: `ContraPos`, `CovarPos`, `DiagElem`, `Transport`

2. Copresheaves on this give freely generated dual-variance data

3. Quotient by:
   - Paranaturality: for morphism-graph pairs
   - Or full parametricity: for arbitrary relational pairs

4. Compare: copresheaves on Tw(Span(C)) should be equivalent to the
   paranaturality-quotiented version restricted to graph relations

**Codebase connection**:

- CategoryJudgments.lean: pattern for judgment-based categorical generation
- ConnectedGrothendieck.lean: provides the Tw(C) infrastructure
- Future: define Span(C) and study copresheaves on Tw(Span(C))

**References**:

- Carboni-Kasangian-Street "Bicategories of spans and relations" (1984)
- nLab span
- 1Lab "The bicategory of spans"

### Proposed Implementation Path

1. Implement Dialgebra category and prove equivalences (Question 1)
2. Document the end = StructuralEnd correspondence formally (Question 2)
3. Explore Rel-enriched diagonal elements for parametricity (Question 4)
4. Investigate `Paranat(Hom, Δ) ≅ StructuralEnd(Δ)` and implications (Question 5)
5. Verify `Over Γ ≌ Prof(DiagElem Γ)` conjecture (Question 5 updated)
6. Formalize StructuralCoend as colimit over (DiagElem F)ᵒᵖ (Question 6)
7. Prove DiagElem ≅ ConnGroth(Γ̂) ×_{Arrow(C)} C (Question 9)
8. Investigate Tw(Rel)-copresheaves for full parametricity (Question 10)
9. Explore categorical Mendler algebras and PHOAS-Grothendieck connection
   (Question 11, OPEN)
