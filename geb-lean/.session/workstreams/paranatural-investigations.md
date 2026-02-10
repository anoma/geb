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
over its category of elements (`sliceEquivPresheaf`, `sliceEquivCopresheaf`).

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

**Finding**: Y, StructuralCoend can be expressed as a colimit using (DiagElem F)ᵒᵖ.

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
by Kan extension. The question is whether paranaturality conditions lift.

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
Sources:

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

Up to identification of equivalent induced relations,
Span(Set) ≅ Rel (category of sets and relations).

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

### 16. PER Model for Parametricity

**Question**: When referring to "PER" as a model of reflexive graph categories for
parametricity, does this mean "partial equivalence relations"? If so, what is that
model and what are the references?

(95%) Partial Equivalence Relations

A partial equivalence relation (PER) on a set X is a binary relation R ⊆ X × X
that is symmetric and transitive (but not necessarily reflexive). The domain of
the PER is {x ∈ X | xRx}, the set of elements related to themselves.

The PER model for parametricity works as follows:

1. **Basic setup**: Types are interpreted as PERs on a universal domain (often
   the natural numbers ω or an untyped lambda calculus model).

2. **Polymorphic types**: ∀α.F(α) is interpreted as:
   - Elements are those x such that for ALL PERs R, x is in the domain of F(R)
   - Two elements x, y are related iff for ALL PERs R, (x,y) ∈ F(R)

3. **Free theorems emerge**: Because polymorphic functions must work uniformly
   across ALL PERs, they must preserve the relational structure.

(90%) Connection to reflexive graphs

The category **PER** of partial equivalence relations can be viewed as:

- Objects: PERs on some base set
- Morphisms: functions that preserve the PER structure (i.e., if xRx' then
  f(x) R' f(x'))

This forms a reflexive graph category where:

- Each PER R induces a reflexive graph (dom(R), R|_{dom(R)})
- Morphisms are graph homomorphisms

The Dunphy-Reddy framework generalizes this: instead of working with PERs on a
fixed universal domain, they work with reflexive graph categories abstractly.

(85%) References

1. **Mitchell-Meyer 1985**: "Second-order logical relations" - establishes
   logical relations for System F

2. **Plotkin-Abadi 1993**: "A logic for parametric polymorphism" - develops
   the logical foundation

3. **Bainbridge et al. 1990**: "Functorial polymorphism" - categorical treatment

4. **Dunphy-Reddy 2004**: "Parametric limits" - reflexive graph category approach

5. **Atkey-Ghani-Johann 2014**: "A relationally parametric model" - fibrational
   approach

(80%) Why PERs capture parametricity

The intuition is:

- A PER R represents "observational equivalence at type R"
- A parametric function f : ∀α.F(α) must map R-related inputs to F(R)-related
  outputs for ANY choice of R
- This forces f to be "uniform" - it can't inspect the type parameter

The PER model is a "realizability model": each PER can be viewed as specifying
which programs are valid implementations of an abstract type.

### 17. Contravariant Yoneda Embedding and Continuations

**Question**: The covariant Yoneda embedding C ↪ [Cᵒᵖ, Type] embeds a category
into its presheaves. What about embedding Cᵒᵖ into [C, Type] (copresheaves)?
This should correspond to continuations. How does this relate to right Kan
extensions?

**Reference**: docs/Kan-extensions-program-optimization.pdf (Hinze 2012)

(95%) The contravariant representable embedding

The embedding Cᵒᵖ → [C, Type] sends:

- Object A ∈ Cᵒᵖ (i.e., A ∈ C) to the copresheaf Hom(A, −) : C → Type
- Morphism f : A → B in Cᵒᵖ (i.e., f : B → A in C) to the natural
  transformation Hom(f, −) : Hom(A, −) ⇒ Hom(B, −)

This is the *covariant* Yoneda embedding viewed contravariantly.

(95%) Right Kan extensions ARE generalized continuations

From Hinze's paper, the right Kan extension (G/J)(A) has the formula:

```text
(G/J)(A) = ∀Z. D(A, JZ) → GZ
```

When J : C → D and G : C → Type. This is the "end formula":

```text
(G/J)(A) = ∫_Z GZ^{D(A,JZ)}
```

**The continuation monad as codensity monad**:

When we take J = id : C → C, we get the codensity monad:

```text
(G/id)(A) = ∀Z. (A → Z) → GZ
```

Setting G = id (identity functor), we get:

```text
C(A) = ∀Z. (A → Z) → Z
```

This IS the continuation monad! More generally, for any monad M:

```text
C_M(A) = ∀Z. (A → M Z) → M Z
```

is the codensity monad for M's Kleisli inclusion, and every monad arises this way.

(90%) Application to dual-variance

For profunctors Γ : Cᵒᵖ × C → Type, we can view them via:

1. **Presheaf view**: Fix contravariant argument, get presheaf in covariant
2. **Copresheaf view**: Fix covariant argument, get copresheaf in contravariant

The copresheaf view corresponds to "continuation semantics":

- Γ(A, −) : C → Type is like "computations expecting A-shaped input"
- Transport along f : B → A (in Cᵒᵖ) is like "composing with continuation"

(85%) Yoneda lemma for copresheaves

For copresheaves F : C → Type, the Yoneda lemma gives:

```text
Nat(Hom(A, −), F) ≅ F(A)
```

This is the standard covariant Yoneda lemma.

The embedding Cᵒᵖ ↪ [C, Type] via Hom(−, −) is full and faithful, meaning C
embeds contravariantly as "continuation types" in the copresheaf category.

(80%) Connection to polynomial profunctors

In the polynomial profunctor setting (PolyDifunc.idr):

- `CovHomSlice a` = slice over Hom(a, −) = polynomial functor with projection
  to the covariant hom-functor
- `CovHomCoslice a` = coslice under Hom(a, −) = polynomial functor with
  injection from the covariant hom-functor

These are the basis for the hom-objects in the CCC structure: morphisms OUT
of polynomial profunctors use the continuation-like pattern of mapping into
a "continuation type" indexed by positions.

(75%) Potential application to parametricity

The continuation perspective suggests:

- Parametric functions can be viewed as "polymorphic continuations"
- The uniformity condition is: the continuation must work for ANY choice of
  "answer type"
- This connects to the ∀Z quantification in the Kan extension formula

Specifically, a paranatural transformation τ : Γ ⇒ Δ might be viewable as a
"relational continuation transformer" that works uniformly.

### 18. Polynomial Profunctors CCC Structure

**Question**: The polynomial profunctor implementation (PolyDifunc.idr) on Type
is Cartesian closed. Would this generalize to any cocomplete CCC C? And do the
hom-objects allow representing types like ((X → X) → X) → X?

**Reference**: docs/PolyDifunc.idr, especially `TypeProHomObj` and
`TypeParaRepHomObj`

(90%) Structure of the CCC on polynomial profunctors

From the implementation, the CCC structure works as follows:

1. **Objects** (`TypeProAr`): polynomial profunctors represented as:
   - `pos : Type` - positions
   - `contra : pos → Type` - contravariant directions
   - `covar : pos → Type` - covariant directions

2. **Terminal object**: Unit profunctor (single position, unit directions)

3. **Products** (`TypeParaProduct`): positional product with:
   - Positions: P × Q
   - Contravariant: disjoint union of contravariants
   - Covariant: disjoint union of covariants

4. **Hom-objects** (`TypeProHomObj`): For profunctors P, Q, the internal hom
   [P, Q] is:

```idris
TypeProHomObj p q =
  TypeParaSetProduct {a=(ipaPos p)}
    (\pi => TypeParaRepHomObj (ipaContra p pi) (ipaCovar p pi) q)
```

This says: a morphism P → Q is, for each position in P, a morphism from the
corresponding representable Hom(contra[p], −) × Hom(−, covar[p]) to Q.

(85%) The representable hom-object decomposition

The formula `TypeParaRepHomObj p p' q` computes hom-objects out of
birepresentables. Since polynomial profunctors are coproducts of
birepresentables, and coproducts are colimits, we use the adjunction:

```text
Hom(∐_i R_i, Q) ≅ ∏_i Hom(R_i, Q)
```

This is why hom-objects are products over positions.

(80%) Generalization to cocomplete CCCs

The construction should generalize, but with caveats:

1. **Cocompleteness needed**: For coproducts of representables (polynomial
   structure)

2. **CCC structure needed**: For the internal hom to exist and be well-behaved

3. **Size issues**: For large categories, we need locally small hom-sets or
   work in a larger universe

The possible theorem would be: if C is a locally small cocomplete CCC, then the
category of C-valued polynomial profunctors (= finitary birepresentable
functors Cᵒᵖ × C → Type) is also a CCC.

(75%) Representing ((X → X) → X) → X

This is a critical question. In the polynomial profunctor CCC:

- X is a type variable, so we need to interpret → as the internal hom
- (X → X) = [Hom(−,X) × Hom(X,−), Hom(−,X) × Hom(X,−)]

The challenge: the internal hom [P, Q] is polynomial only when P is
polynomial. But Hom(−,X) × Hom(X,−) is a representable profunctor, so
its internal hom should be polynomial.

However, there's a subtlety: the type variable X appears both covariantly and
contravariantly. In the polynomial profunctor setting:

- X as object: pick a type X
- X as profunctor: the representable Hom(−,X) × Hom(X,−)

For ((X → X) → X) → X, treating X as a profunctor:

1. (X → X) = internal hom of the representable with itself
2. ((X → X) → X) = hom from that to X
3. Final → X = hom to X

Each step produces a polynomial profunctor, so the indeed we CAN
represent such types, but they're profunctors, not single types.

(70%) Interpreting the result

The polynomial profunctor interpretation of ((X → X) → X) → X gives a
*family* indexed by (contravariant position, covariant position). To get a
single type, we'd need to:

1. Evaluate at specific arguments: P(A, B) for types A, B
2. Take diagonal elements: P(A, A)
3. Or take a (co)end: ∫_A P(A, A) or ∫^A P(A, A)

This connects back to parametricity: the "free theorem" for type
((X → X) → X) → X would come from examining the diagonal elements.

### 19. Hom-Profunctor as Parametric Right Adjoint

**Question**: Can we model polynomial profunctors as PRAs from Cᵒᵖ to the
category of PRAs from C to Type (curried view)? This would make the
hom-profunctor Hom(−, −) polynomial. See docs/SlicePolyDifunc.idr.

(85%) The curried PRA approach

The idea is to view a profunctor Γ : Cᵒᵖ × C → Type in curried form:

```text
Γ̃ : Cᵒᵖ → [C, Type]
```

where Γ̃(A) = Γ(A, −) is a copresheaf.

Now, if we restrict to:

- Copresheaves that are PRAs (polynomial functors) C → Type
- The functor Γ̃ itself being a PRA Cᵒᵖ → PRA(C, Type)

Then the hom-profunctor becomes:

```text
Hom̃ : Cᵒᵖ → [C, Type]
Hom̃(A) = Hom(A, −)
```

The covariant hom-functor Hom(A, −) is representable, hence a PRA (the "most
polynomial" functor - identity composed with a constant direction).

(80%) Is Hom̃ itself a PRA?

For Hom̃ to be a PRA from Cᵒᵖ to copresheaves, we need it to have a
polynomial presentation:

```text
Hom̃ = Lan_i ∘ i* for some i : I → Cᵒᵖ
```

The Yoneda embedding C → [Cᵒᵖ, Type] IS the left Kan extension along the
identity. Dually, Cᵒᵖ → [C, Type] via Hom(−, −) has similar properties.

The question is whether this is "polynomial" in the right sense.

(75%) Analysis of SlicePolyDifunc.idr

The implementation defines `PIP` (Polynomial functor In Poly), which is:

```idris
PIP = (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
```

This represents polynomial functors on the category Poly of polynomial
endofunctors on Type, with evaluation through multiple layers.

The structure captures:

1. A base polynomial functor (t1p, t1d)
2. Extensions for operating on polynomial functors (et1p, et1d, et2p, et2d)
3. Natural transformations (etonpos, etondir)

This is related to the slice category approach: polynomial functors on Poly
correspond to PRAs on slices.

(70%) The slice-polynomial correspondence

From the code, there's an isomorphism between:

- `PCECW b` = polynomial functor structures parameterized by base b
- `CoprCovHomSlice b` = coproducts of slices over covariant hom-functors

This suggests polynomial profunctors can be built from:

1. A base polynomial functor b
2. For each position of b, a slice over the covariant hom-functor of its
   direction

(65%) Making Hom polynomial via this approach

To make the hom-profunctor Hom(−, −) polynomial in the curried PRA sense:

1. View Hom(−, −) as Cᵒᵖ → [C, Type]
2. Represent this as a PRA using the Yoneda structure
3. The "positions" would be objects of C (for Cᵒᵖ)
4. The "directions" at position A would be the generators of Hom(A, −)

Since Hom(A, −) is representable (generated by id : A → A), this should work:

```text
Hom̃ : Cᵒᵖ → PRA(C, Type)
Hom̃(A) = "represented by A"
```

The challenge is making this precise categorically and verifying the PRA
structure.

(60%) Quotient types and coequalizers

The SlicePolyDifunc.idr implementation notes issues with impredicative
coequalizers. In Lean/mathlib:

- We have proper quotient types via `Quotient` and `Setoid`
- This would allow genuine coequalizers
- The construction would be more correct and convenient

A Lean port would:

1. Define polynomial functors on Poly using mathlib's PFunctor
2. Use Setoid/Quotient for coequalizers
3. Verify the PRA structure formally

(55%) Connection to multi-adjunctions

The implementation mentions multi-adjunctions between Poly and Type slices.
This relates to:

- Parametric right adjoints having left multi-adjoints
- The representability of copresheaves induced by polynomial structure

The connection to our parametricity investigation: if polynomial profunctors
arise from curried PRAs, then the PRA's left adjoint structure might encode
the uniformity condition that gives parametricity.

### 20. Twisted-Arrow Copresheaves and Arr(C) for Full Parametricity

**Question**: Should we be using twisted-arrow copresheaves Tw(C)ᵒᵖ → Type
instead of profunctors C^op × C → Type for parametricity? Should parametric
transformations be identity-on-morphisms functors over Arr(C) rather than
identity-on-objects functors over C?

**Motivation**: Neumann's counterexample where paranaturality and parametricity
diverge involves a condition "for all h, k with commutativity condition" — and
that commutativity condition is exactly the condition for (h, k) to be a
morphism in the arrow category Arr(C). This suggests paranaturality forgets
morphism structure that full parametricity requires.

(95%) The arrow category Arr(C) is richer than C

Arr(C) has:

- Objects: morphisms f : A → B in C
- Morphisms f → f': commutative squares (h, k) with k ∘ f = f' ∘ h

The inclusion C ↪ Arr(C) via c ↦ id_c is both reflective and coreflective:

- Left adjoint: dom (domain projection)
- Right adjoint: cod (codomain projection)

Because it has both adjoints, this inclusion preserves all limits AND colimits.
Furthermore:

- If C is cartesian closed, Arr(C) = [•→•, C] is cartesian closed
- If C is a topos, Arr(C) is a topos (with richer subobject classifier)

Objects of C embed as identity morphisms, so Arr(C) is a "morphism-centric"
view where we track not just objects but the morphisms between positions.

(90%) Paranaturality forgets morphism structure

Current approach for paranaturality:

- Profunctor Γ : C^op × C → Type
- Diagonal elements DiagElem(Γ) sliced over C
- Paranatural transformations = identity-on-C-objects functors in Cat/C

The diagonal isn't just "same object in both positions" — it's specifically
"identity morphism". By projecting to C, we forget that diagonal elements sit
over identity morphisms in Arr(C).

(85%) The proposed reframing

| Current (Paranaturality) | Proposed (Full Parametricity) |
| -------------------------- | ------------------------------- |
| Profunctor Γ : C^op × C → Type | Tw-copresheaf Φ : Tw(C)ᵒᵖ → Type |
| DiagElem(Γ) over C | TwCoprArrElem(Φ) over Arr(C) |
| Paranatural = id-on-obj in Cat/C | Parametric = id-on-mor in Cat/Arr(C) |

The connected Grothendieck construction for Tw(C)ᵒᵖ → Cat produces categories
over Arr(C). When the target is discrete (sets/types), we get TwCoprArrElem.

(80%) Why this captures full parametricity

An identity-on-underlying-morphisms functor between TwCoprArrElem categories
must respect:

1. The domain object (like paranaturality)
2. The codomain object (like paranaturality)
3. The morphism between them (which paranaturality forgets)

For Neumann's divergence case with "for all h, k with commutativity":

- (h, k) form a morphism in Arr(C)
- Working over Arr(C) makes this condition structural, not an extra quantifier

(75%) Diagonal elements as identity-morphism restriction

A twisted-arrow copresheaf Φ : Tw(C)ᵒᵖ → Type assigns Φ(f) to each morphism
f : A → B. The restriction to identity morphisms gives:

```text
Φ(id_A) = "diagonal data at A"
```

This should correspond to Γ(A, A) for the associated profunctor Γ. The full
Φ contains more information: how the diagonal data relates across morphisms.

(70%) Polynomial twisted-arrow copresheaves — naive approach

One possibility: coproducts of representables on Tw(C):

```text
Φ = ∐_{i ∈ I} Hom_{Tw(C)}(f_i, −)
```

The positions are morphisms f_i : A_i → B_i, not pairs of objects.

**Problem**: Tw(C) typically lacks coproducts and products even when C has them.
The naive "coproduct of representables" formula requires these to exist in the
indexing category, making this approach inadequate.

(68%) Dependent functors via currying — a richer approach

The connected Grothendieck construction and TwArrPresheaf.lean show that
twisted-arrow copresheaves can be "curried" into dependent functors. This
suggests a richer notion of "polynomial" that uses full dependency.

**Observation**: A twisted-arrow copresheaf Φ : Tw(C)ᵒᵖ → Type assigns
data to each morphism f : A → B. The curried view organizes this as:

- For each object c : C, data depending on morphisms out of c
- The dependency structure respects composition

This is analogous to how polynomial functors P(X) = Σ_{i:I} X^{B_i} use
dependent products over a base type I.

(65%) Dependent functors to Dirichlet functors on slices

**Proposal**: Instead of coproducts of representables, use dependent functors
from C to Dirichlet functors on slice categories:

1. Start with a polynomial endofunctor P : C → C with positions I and
   directions B_i (so P(c) = Σ_{i:I} Hom(B_i, c))

2. Form the category of elements ∫P with objects (c, i, f : B_i → c)

3. Define a dependent functor from ∫P to Dirichlet functors:
   - For each (c, i, f), produce a Dirichlet functor on C/c or C/B_i

A Dirichlet functor (covariant polynomial) on C/c has form:

```text
Dir(x) = Σ_{j : J} Hom_{C/c}(x, D_j)
```

This is dual to polynomial functors: sums of covariant representables.

(62%) Alternative via families and the slice equivalence

The slice/family equivalence (see `familySliceEquiv` in Polynomial.lean):

```text
Type/A ≃ Fam_A(Type) = (a : A) → Type
```

sends (B, f : B → A) to the fiber family a ↦ f⁻¹(a).

**Alternative proposal**: A polynomial twisted-arrow copresheaf could be:

```text
P : C → Dir(Fam(C))
```

where:

- P is a polynomial functor from C
- Dir(Fam(C)) is the category of Dirichlet functors on families over C
- The family structure provides the "slice over varying objects" capability

This avoids needing coproducts in Tw(C) by working with the dependent/family
structure directly.

(60%) Why this might capture parametricity better

The dependent-functor approach:

1. Uses the natural curried structure of twisted-arrow copresheaves
2. Connects directly to the connected Grothendieck construction
3. Allows the "slice object" to vary with input (full dependency)
4. Uses Dirichlet functors (covariant polynomial) which are the natural
   dual to polynomial functors

For the algebra profunctor Alg_F(A, B) = Hom(FA, B), the corresponding
dependent structure would have:

- Base polynomial: F itself
- For each (A, i, f : B_i → A), the Dirichlet part captures how algebra
  structures transport across morphisms

(65%) Dual-variance datatypes via Arr(C)

The proposal for dual-variance datatypes becomes:

1. Start with a polynomial twisted-arrow copresheaf Φ
2. Form TwCoprArrElem(Φ) over Arr(C)
3. The forgetful functor U : TwCoprArrElem(Φ) → Arr(C) may have adjoints
4. Initial/terminal objects in TwCoprArrElem(Φ) are dual-variance datatypes

Since C ↪ Arr(C) preserves limits/colimits, initial/terminal objects of C
map to initial/terminal in Arr(C), and adjoints to U would take these to
the corresponding initial/terminal twisted-arrow elements.

(60%) Connection to existing work

The in-progress equivalence TwCoprArrElem ↔ ConnGrothendieck (Question 9)
becomes central: it shows that twisted-arrow copresheaf elements over Arr(C)
are equivalent to a connected Grothendieck construction.

The existing DiagElem approach would be recovered by pulling back along the
inclusion C ↪ Arr(C), but this pullback loses the morphism information that
distinguishes paranaturality from full parametricity.

(55%) Open questions

1. Does the TwCoprArrElem approach give correct parametricity conditions for
   standard examples (folds, Church encodings, Neumann's counterexample)?

2. What is the relationship between:
   - Polynomial profunctors (coproducts of birepresentables)
   - Polynomial Tw-copresheaves (coproducts of Tw(C)-representables)

3. For the algebra profunctor Alg_F(A, B) = Hom(FA, B), what is the
   corresponding twisted-arrow copresheaf, and does TwCoprArrElem recover
   F-Alg with the correct parametricity structure?

4. How do the induced (co)monads from TwCoprArrElem adjoints relate to
   those from DiagElem adjoints?

### 21. Inner Endomorphisms, Arr(C) CCC, and E(Fact) Bridge

**Motivation**: Question 20 identified that parametric transformations should
respect arrow-category structure. This question refines the analysis by
characterizing the exact gap between paranaturality and parametricity, and
identifying the connected Grothendieck construction E(factorisationFunctor)
as the geometric bridge.

**The factorisation map.** For f : a → b in C, define:

```text
φ_f : Hom(b, a) → End_{Arr(C)}(f)
φ_f(g) = (g ∘ f, f ∘ g)
```

This lands in End_{Arr(C)}(f) = {(h, k) | k ∘ f = f ∘ h} because
(f ∘ g) ∘ f = f ∘ (g ∘ f). The image consists of "inner endomorphisms".

**Paranaturality tests im(φ_f).** The paranaturality condition at f involves
elements z ∈ P(b, a) and tests the pair (P.map₁(f)(z), P.map₂(f)(z)), which
for the Hom profunctor gives φ_f(z) = (z ∘ f, f ∘ z). The image of P(b, a)
under (P.map₁(f), P.map₂(f)) is the profunctorial analog of im(φ_f).

**Parametricity tests all of End_{Arr(C)}(f).** The free theorem for a type
expression T(X) tests ALL (h, k) ∈ End_{Arr(C)}(f). For Neumann's example
T(X) = ((X→X)→X)→X, the condition "for all h, k with f ∘ h = k ∘ f" is
exactly "for all (h, k) ∈ End_{Arr(C)}(f)".

**The gap.** im(φ_f) ⊆ End_{Arr(C)}(f), with equality iff φ_f is surjective.
Counterexample: a = {0,1}, b = {*}, f the unique map. Then End_{Arr}(f)
contains all (h, id) for h ∈ End(a), but im(φ_f) contains only constant
endomorphisms (since g : {*} → {0,1} picks one element). The swap on a is
in End_{Arr}(f) but not in im(φ_f).

**E(factorisationFunctor) sees full End_{Arr(C)}(f) at initial/terminal.**

An endomorphism of (f, d) in E(Fact) consists of (h, σ, k) where:

- h : a → a, k : b → b with f ≫ k = h ≫ f (arrow endomorphism)
- σ : d.mid → d.mid with d.ι ≫ σ = h ≫ d.ι and σ ≫ d.π = d.π ≫ k

At the initial factorisation d = (a, 𝟙, f): σ = h works, so every (h, k) ∈
End_{Arr}(f) lifts to (h, h, k). At the terminal factorisation d = (b, f, 𝟙):
σ = k works, so every (h, k) lifts to (h, k, k).

At interior factorisations, not all (h, k) may admit a compatible σ. The set
of liftable (h, k) depends on the midpoint structure.

**Arr(C) CCC characterizes full parametricity.** When C is CCC, Arr(C) =
[2, C] is also CCC. A type expression T(X) interprets as T^{Arr}(f) in
Arr(C) by induction on syntax:

- X ↦ f : A → B
- X → X ↦ [f, f] with source = End_{Arr}(f), target = End(B)
- (S → T) ↦ [S^{Arr}(f), T^{Arr}(f)] using the CCC internal hom
- S × T ↦ componentwise product

A parametric transformation γ : ∀X. T(X) → S(X) is γ that lifts to
Arr(C): for all f, there exists γ^{Arr}_f : T^{Arr}(f) → S^{Arr}(f)
consistent with evaluation at source and target.

**Parametricity is syntax-dependent.** The CCC interpretation T^{Arr}(f)
depends on the syntactic structure of T(X), not just the resulting
profunctor. Two syntactically different expressions with the same
profunctor could (in principle) have different parametricity conditions.
Paranaturality, by contrast, depends only on the profunctor.

**Polynomial profunctors: paranaturality = parametricity.** For polynomial
P(a,b) = Σ_i (a → c_i) × (d_i → b), the type expression decomposes into
purely covariant and contravariant pieces. At the → connective, the
relational lifting is generated by inner endomorphisms. So im(φ_f) generates
the full relational constraint, and paranaturality = parametricity. This
explains why the Idris presheaf correspondence works (not because
op(Type) ≅ Type, which is false, but because polynomial types lack genuine
mixed-variance interaction).

**The op(Type) ≠ Type clarification.** The Idris code works with presheaves
on Tw(op(Type)), where objects are (x, y, myx : y → x). This is NOT the
same as presheaves on Tw(Type) or on Arr(Type). The code's correctness for
polynomial profunctors comes from the algebraic decomposition of polynomials,
not from any categorical equivalence between Type and op(Type). For
non-polynomial profunctors, the Tw(op(Type)) approach adds off-diagonal
conditions beyond paranaturality but may not capture full parametricity.

**Open questions:**

1. Can a "polynomial decomposition" or "arena" representation for
   non-polynomial types provide enough syntactic structure for
   parametricity without full type syntax? The Idris IntProAr type gives
   such a decomposition for polynomial types.

2. Compute T^{Arr}(f) concretely for T(X) = ((X→X)→X)→X at f : {0,1} → {*}
   to exhibit the gap between im(φ_f) and End_{Arr}(f) at the profunctor
   level.

3. Define "E(Fact)-compatibility" as an intermediate condition: γ must be
   compatible with all connected Grothendieck morphisms (testing more
   pairs than paranaturality via arrow squares). Determine whether this is
   strictly between paranaturality and parametricity, and whether it has
   categorical value.

4. Investigate whether a Grothendieck topology on E(Fact) (rather than on
   Tw(C)) could characterize "parametrically determined" profunctors as
   sheaves.

5. The Span(C)/Rel approach (Question 10) makes relations first-class,
   while the Arr(C) CCC approach uses the functor-category structure of
   [2, C]. Determine the precise relationship: does interpreting in the
   CCC Arr(C) = [2, C] recover the relational lifting used in Reynolds'
   parametricity?

### 22. Non-CCC Parametricity via External Hom and E(Fact)

**Motivation**: Question 21 showed that full parametricity corresponds to
testing End_{Arr(C)}(f) rather than just inner endomorphisms im(φ_f). The CCC
structure of Arr(C) = [2, C] provides this via the internal hom. This question
investigates whether CCC is needed at all.

**External hom suffices for End_{Arr}(f).** For any category C and morphism
f : a → b, the set End_{Arr(C)}(f) = {(h, k) ∈ Hom(a,a) × Hom(b,b) | kf = fh}
is a Type (element of the universe). Computing it requires only the external
hom-sets Hom(a,a), Hom(b,b), and the composition operation. No internal hom
[f, f] in Arr(C) is needed. The internal hom [f, f] would give End_{Arr}(f) as
an OBJECT of Arr(C), but for universal quantification in the parametricity
condition, we only need it as a TYPE.

**Non-CCC relational interpretation.** Given a type expression T(X) with X
occurring both covariantly and contravariantly, define the relational fiber
T̃(f) ⊆ T(a) × T(b) for f : a → b by induction on T:

```text
X̃(f) = graph(f) = {(x, y) | f(x) = y}  [for C = Type]
(S→U)̃(f) = {(g₁, g₂) | ∀(x,y) ∈ S̃(f), (g₁(x), g₂(y)) ∈ Ũ(f)}
(S×U)̃(f) = S̃(f) × Ũ(f)
```

At the S→U connective, S̃(f) appears as a TYPE used for universal
quantification. When S(X) = X→X, S̃(f) = End_{Arr}(f), computed from
external homs. No internal hom or CCC structure is needed at any level.

For general C (not necessarily Type), the "graph" of f can be replaced by
the profunctor Hom(a,b) with f as a distinguished element. The relational
interpretation then uses profunctor actions P.map₁(h) and P.map₂(k) for
(h,k) ∈ End_{Arr}(f), all computed externally.

**Concrete verification for Neumann's example.** For T(X) = ((X→X)→X)→X:

```text
(X→X)̃(f) = End_{Arr}(f) = {(h,k) | kf = fh}
((X→X)→X)̃(f) = {(p,q) | ∀(h,k)∈End_{Arr}(f), f(p(h))=q(k)}
(((X→X)→X)→X)̃(f) = {(φ_a,φ_b) | ∀(p,q)∈((X→X)→X)̃(f), f(φ_a(p))=φ_b(q)}
```

End_{Arr}(f) is a Type at each step. The full free theorem emerges from this
inductive construction without any CCC requirement.

**E(Fact)-parametricity as an intermediate notion.** Define:

- Index category: E(Fact) = connected Grothendieck of factorisationFunctor
- Diagram: profOnEFact(G)(f, d) = G(dom(f), cod(f)), action by G.map₁(h) ≫ G.map₂(k)
- Weight: eFactWeight(H)(f, d) = H(d.mid, d.mid), action by H.map₁(σ) ≫ H.map₂(σ)
- EFact-Param(H, G) := NatTrans(eFactWeight(H), profOnEFact(G))

This is a syntax-free condition (depends only on profunctors H, G) that is
strictly between paranaturality and full parametricity:

- End_{E(Fact)}(f, d₀) ≅ End_{Arr}(f) at the initial factorisation d₀ = (a, id, f)
- So E(Fact)-parametricity tests all of End_{Arr}(f) at the top level
- But for nested types like ((X→X)→X)→X, the difference occurs at inner levels
  where the E(Fact) approach does not recursively strengthen

**Three levels of naturality (refined)**:

1. Paranaturality (syntax-free, Tw(C)-based): Tests im(φ_f) ⊆ End_{Arr}(f).
   Maximal syntax-free condition. Coincides with (2) and (3) for polynomial types.

2. E(Fact)-parametricity (syntax-free, E(Fact)-based): Tests all of End_{Arr}(f)
   at the top level. Coincides with (3) for types with at most one level of
   mixed-variance nesting.

3. Full parametricity (syntax-dependent): Tests End_{Arr}(f) recursively at
   every nesting level of →. Requires a type expression but NOT a CCC.
   External homs (landing in Type) suffice.

**Profunctor for Neumann's type.** In the standard enriched-profunctor
interpretation: for T(X) = ((X→X)→X)→X, the corresponding profunctor
P : C^op × C → Type (computed via ends/coends) satisfies P(a,a) ≅ T(a).
By the Yoneda lemma, (X→X) as a profunctor is isomorphic to Hom, so
P ≅ Hom as a profunctor. Two syntactically different type expressions can
yield isomorphic profunctors but different relational interpretations. This
is the source of the syntax-dependence.

**The profunctor-vs-syntax distinction** is the categorical content of
Neumann's counterexample: paranaturality is a condition on the profunctor
alone, while parametricity remembers the syntactic structure that produced it.

**Open questions:**

1. Can E(Fact)-parametricity be iterated (apply E(Fact) construction
   recursively to inner profunctors) to approximate full parametricity?

2. Is there a categorical structure (an operad, a multicategory, or a
   higher category) that encodes type expressions and their relational
   interpretations, providing a single framework for all three levels?

3. For a given profunctor P, the set of type expressions T with P_T ≅ P
   forms an equivalence class. The "parametricity closure" of P could
   be defined as the intersection of T̃(f) over all T with P_T ≅ P.
   Is this always paranaturality, or can it be strictly between?

4. The weighted limit formula for E(Fact)-parametricity:
   EFact-Param(H,G) = NatTrans(eFactWeight(H), profOnEFact(G)) over E(Fact).
   Can this be reduced to a weighted limit over Tw(C) with a LARGER weight?
   I.e., does the extra E(Fact) structure collapse to extra weight data?

### 23. Iterated Arrow Categories, Yoneda Parametricity, and Cubical Structure

**Sources**: Wadler, "Theorems for free!" (1989);
Maguire, "Review: Theorems for Free" (reasonablypolymorphic.com).

**Wadler's construction.** Types are read as relations:

```text
𝒜 × ℬ : (A × B) ⇔ (A' × B')  — products relate componentwise
𝒜* : A* ⇔ A'*                  — lists relate same-length pointwise
𝒜 → ℬ : (A → B) ⇔ (A' → B')  — functions map related inputs to related outputs
∀𝒳.ℱ(𝒳) : ∀F ⇔ ∀F'            — polymorphic: related under all type substitutions
```

Parametricity proposition: for t : T closed, (t, t) ∈ 𝒯.

**Relations specialized to functions.** (Blog post observation.)
When relations are restricted to graphs of functions, the type constructors
become bifunctors (×, List become bimap/map) and the function relation
becomes the naturality square: (f, f') ∈ (𝒜 → ℬ) reduces to
f' ∘ g = h ∘ f, which is exactly an Arrow(C) morphism condition. The ∀
construction becomes a natural transformation condition.

Blog post conjecture: "all laws in Haskell are just the category laws
disguised in different categories." This is essentially the Curry-Howard-Lambek
correspondence: the type system is the internal language of a CCC, and
every derivable equation is a categorical identity.

**Iterated arrow categories.** The arrow category Arr(C) = [2, C] where
2 = {0 → 1} is the walking arrow. By the exponential law in Cat:

```text
Arr⁰(C) = C
Arr¹(C) = [2, C]        (morphisms of C)
Arr²(C) = [2², C]       (commutative squares in C)
Arrⁿ(C) = [2ⁿ, C]      (n-dimensional commutative hypercubes)
```

The inclusion C ↪ Arr(C) sending c ↦ id_c is reflective (left adjoint = dom)
and coreflective (right adjoint = cod). Under the isomorphism, this is the
degeneracy map in the cubical structure.

The sequence Arr⁰(C), Arr¹(C), Arr²(C), ... with degeneracy inclusions IS
the cubical nerve of C. The n-cubes are the n-dimensional commutative
hypercubes. Face maps are the left/right adjoints of the inclusions.

**Connection to parametricity depth.** The mixed-variance nesting depth of a
type expression T(X) determines how many Arr-levels are needed:

```text
Depth 0: Constant or purely co/contravariant types (X, A, List X)
Depth 1: One level of → (X → X, (X → A) → X)
Depth 2: Nested → (((X→X)→X)→X — Neumann's example)
Depth n: n levels of mixed-variance nesting
```

Paranaturality = Arr¹-level testing (inner endomorphisms).
Full parametricity for depth-n types = Arrⁿ-level testing.
Full parametricity for all System F types = the entire cubical tower.

**Fixed point of iterated Arr.** Strict fixed point Arr(D) ≅ D in 1-Cat
exists only for trivial D (discrete categories). But in ∞-category theory,
the cubical nerve (the totality of all Arrⁿ data with face/degeneracy maps)
IS the ∞-categorical presentation of C. For ordinary 1-categories, all cubes
above dimension 1 are thin (uniquely determined). For ∞-categories, higher
cubes carry non-trivial homotopical information.

**Endofunctors extend along the tower.** An endofunctor F : C → C extends to
Arrⁿ(F) : Arrⁿ(C) → Arrⁿ(C) by applying F vertex-wise to each n-cube.
In Wadler's terms: the relational lifting of List(𝒜) along graph(f) equals
graph(map f). This is functoriality of List at each level. Endofunctors
are "depth 0" — they don't increase the mixed-variance nesting.

**Yoneda parametricity.** For any C (not necessarily CCC), the Yoneda
embedding y : C → PSh(C) = [Cᵒᵖ, Type] embeds C fully faithfully into
a topos. Since PSh(C) is CCC, ALL type expressions can be formed there.

Given T(X) a type expression and f : a → b in C:

- y(f) : y(a) → y(b) in PSh(C)
- T can be interpreted in PSh(C) using its CCC structure
- T^{Arr}(y(f)) computes the parametricity condition
- By the Yoneda lemma, conditions on representable elements reflect to C

This gives: **parametricity for any C = Wadler's construction in PSh(C),
restricted to representable objects**.

When C IS CCC: [y(a), y(b)] ≅ y([a, b]) (Yoneda preserves the CCC structure),
so the PSh(C) parametricity agrees with the C-internal computation. When C is
NOT CCC: [y(a), y(b)] exists in PSh(C) as a (generally non-representable)
presheaf, and the parametricity condition is the "canonical" one.

**Yoneda preserves relatedness.** The Yoneda embedding preserves limits,
monomorphisms, and (when they exist) products. A relation between a, b in C
(modeled as a subobject of a × b, or a span, or a morphism) maps to the
corresponding relation between y(a), y(b) in PSh(C). The presheaf topos
has MORE relations (non-representable subobjects of y(a) × y(b)), but
restricting to representable elements via the Yoneda lemma gives exactly
the C-level conditions.

"Pointwise parametricity": since y(a)(c) = Hom_C(c, a), conditions in
PSh(C) decompose into conditions at each "stage" c ∈ C. This is the
presheaf-topos analog of "testing at all types" in Wadler's framework.

**Connection to the iterated-Arr tower in PSh(C).**

```text
PSh(Arr⁰(C)) = [Cᵒᵖ, Type]
PSh(Arr¹(C)) = [(Arr C)ᵒᵖ, Type] ≅ [(C × 2)ᵒᵖ, Type]
PSh(Arrⁿ(C)) = [(C × 2ⁿ)ᵒᵖ, Type]
```

The Yoneda embedding into PSh(C) handles all depths simultaneously because
PSh(C) is CCC. The iterated-Arr approach handles one depth at a time.
The presheaf topos is the "universal" setting that subsumes all finite
depths.

**Open questions:**

1. Is the presheaf-topos parametricity equivalent to the Reynolds/Wadler
   parametricity for C = Type? If so, it would provide a categorical
   proof of the parametricity theorem.

2. For non-CCC C, does the Yoneda parametricity condition on representable
   elements coincide with E(Fact)-parametricity (Question 22) at depth 1?
   Does it coincide with paranaturality at depth 0?

3. The cubical presheaf topos [(C × □)ᵒᵖ, Type] (where □ is the cube
   category) should handle all depths. Is this related to cubical type
   theory's interpretation of parametricity?

4. Is there a notion of "parametric presheaf" (presheaf satisfying
   parametricity at all depths) that forms a reflective subcategory of
   PSh(C)?

5. The blog post's conjecture (all laws = category laws) is the
   Curry-Howard-Lambek correspondence. Can we make this precise for
   the paranatural/profunctor setting: every paranatural identity is
   a consequence of the categorical structure of the endoprofunctor
   category?

### 24. Mathlib Relation Infrastructure and Dialectica

**Mathlib's RelCat** (`CategoryTheory.Category.RelCat`):

- `RelCat := Type u` with `Hom X Y := SetRel X Y` (= `Set (X × Y)`)
- `graphFunctor : Type u ⥤ RelCat.{u}` embeds functions as graph
  relations (faithful, essentially surjective)
- `opEquivalence : RelCat ≌ RelCatᵒᵖ` — self-duality via
  argument-swapping. This is the categorical form of relation
  transposition.

The self-duality of RelCat corresponds to the mixed-variance nature
of Wadler's relational interpretation: a relation R ⊆ A × B is a
morphism A → B AND B → A simultaneously in RelCat, so mixed variance
is automatically handled.

**Dialectica category** (`CategoryTheory.Dialectica.Basic`):

- Objects: (U, X, α ⊆ U × X) — a pair of types with a relation
- Morphisms from (U, X, α) to (V, Y, β): pairs (f : U → V,
  F : U × Y → X) with α(u, F(u,y)) ≤ β(f(u), y)

The Dialectica morphism has covariant component f and contravariant
component F, with a logical-relation compatibility condition.
de Paiva (1989) showed the connection between Dialectica categories
and parametricity. Moss and von Glehn ("Dialectica models of type
theory", 2021) connect Dialectica categories to polynomial functors.

**Missing from mathlib:**

- No Yoneda/presheaf interpretation of relations
- No logical relations or relational parametricity formalization
- No profunctor interpretation of relations
- No functor from Cat to RelCat beyond graphFunctor

**Left Kan extension along Yoneda** (`Limits.Presheaf`):

For F : C ⥤ D, the cocontinuous extension is `F.op.lan`:

```text
        F
  C --------→ D
  |            |
  y            y
  ↓            ↓
PSh(C) ---→ PSh(D)
      F.op.lan
```

Properties:

- `compULiftYonedaIsoULiftYonedaCompLan`:
  `F ⋙ uliftYoneda ≅ uliftYoneda ⋙ F.op.lan` (extension property)
- `uniqueExtensionAlongULiftYoneda`: uniqueness among
  colimit-preserving extensions
- `preservesColimitsOfSize_leftKanExtension`: cocontinuity

For an endofunctor F : C → C, `F.op.lan : PSh(C) → PSh(C)` is
the canonical lift, given pointwise by the coend
∫^c P(c) × Hom(F(c), −).

**Connections to parametricity:**

| Concept | Mathlib | Parametricity role |
| ------- | ------- | ----------------- |
| RelCat | Exists | Target of relational interpretation |
| graphFunctor | Exists | Embeds terms (functions) as relations |
| RelCat self-duality | Exists | Handles mixed variance |
| Dial C | Exists | "Total category" of relational interpretation |
| F.op.lan | Exists | Lifts type constructors to PSh(C) |
| Relational interpretation | Missing | Functor from syntax to RelCat |
| Parametricity theorem | Missing | graphFunctor image ⊆ Dial morphisms |

**Dial(PSh(C)) as the universal parametricity framework:**

Dial C requires `[HasFiniteProducts C] [HasPullbacks C]` — the
cartesian monoidal structure, not just any tensor. For arbitrary C,
pass to PSh(C) = [C^op, Type], which is a topos and always
satisfies these requirements.

Objects of Dial(PSh(C)):

- (P, Q, α) where P, Q : C^op → Type are presheaves and
  α ⊆ P × Q is a sub-presheaf (natural family α(c) ⊆ P(c) × Q(c))

Morphisms from (P₁, Q₁, α₁) to (P₂, Q₂, α₂):

- f : P₁ →̇ P₂ (natural transformation, covariant)
- F : P₁ × Q₂ →̇ Q₁ (natural transformation, contravariant in Q)
- condition: α₁(p, F(p,q)) → α₂(f(p), q), naturally in c

Computability: mathlib's Dial uses `Subobject` (quotients), but for
PSh(C) = [C^op, Type], subobjects are natural predicates
`∀ c, P(c) → Q(c) → Prop`, which is constructive. A computable
`DialPSh` can be defined without depending on Subobject.

Comparison with EndoProf(C) + paranaturality:

| Aspect | Dial(PSh(C)) | EndoProf(C) |
| ------ | ----------- | ----------- |
| Objects | presheaves + relation | endoprofunctors |
| Morphisms | (f, F, condition) | paranatural transformations |
| Strength | full parametricity | paranaturality (weaker) |
| Requirements on C | none | none |

Connection: for an endoprofunctor P, define the diagonal presheaf
P̃(a) = P(a,a). The off-diagonal P(a,b) encodes "relating elements
at a to elements at b", which in Dial corresponds to the relation α.
Paranaturality uses only relations from morphisms in C, while Dial
uses all sub-presheaves — the gap is the non-representable relations.

**Embedding PSh(C) into Dial(PSh(C)):**

The embedding P ↦ (P, 1, ⊤) (terminal target, maximal relation) is
full and faithful: Hom_Dial((P,1,⊤),(Q,1,⊤)) ≅ Hom_PSh(P,Q).

This embedding does NOT preserve limits. Dial(PSh(C)) is a model of
linear logic, not cartesian logic. The product of (P, 1, ⊤) and
(Q, 1, ⊤) in Dial has target ≅ 1 + 1, not 1 — the extra component
tracks which factor is being "challenged" in the relational
interpretation. This non-preservation is mathematically correct: the
relational interpretation of A × B tests A-components and
B-components separately.

Similarly, the Chu construction Chu(PSh(C), Ω) has products with
target = coproduct of targets, not preserved by the (−, 1, ⊤)
embedding.

**Two approaches to mixing regular and parametric morphisms:**

Approach 1 (forgetful + section): The forgetful functor
U : Dial(PSh(C)) → PSh(C) sending (P, Q, α) ↦ P has a section
P ↦ (P, 1, ⊤). Compose by embedding regular morphisms then
composing in Dial. This is the linear-logic approach using the !
modality (non-polymorphic types = "of-course" types).

Approach 2 (parametricity as property): Stay in PSh(C) and define
parametricity as a predicate on morphisms:

```text
IsParametric(f) := for all relations α, T̃(α)-related
inputs map to S̃(α)-related outputs
```

The parametric morphisms form a wide subcategory of PSh(C)
inheriting all the topos structure. This matches how Haskell works:
the ambient category is Hask, the parametricity theorem says every
definable morphism satisfies the relational interpretation.

For Geb: Approach 2 is more natural. Work in PSh(C), extend type
constructors via F.op.lan, and prove the parametricity theorem once
("every morphism constructible from our combinators is parametric").
Dial(PSh(C)) serves as the proof framework, not the ambient
category.

### 25. Free Categories and Automatic Parametricity from Universal Properties

The parametricity relation is inductive — its definition follows the
structure of type syntax. For categories defined as free categories
generated by universal properties, the universal properties might
automatically yield equality (identity) relations.

**Observation:** A universal property states that a morphism is the
*unique* one satisfying some diagram condition. If every morphism in
C is forced by universal properties, then every endomorphism of an
arrow f : a → b (in the sense of End_{Arr(C)}(f)) is determined by
the universal properties. This means the parametricity condition
becomes trivially satisfied: there are no "junk" endomorphisms that
could violate it.

**Free categories generated by products, coproducts, and exponentials:**

- Free CCC on a set of generators: every morphism is a composition of
  projections, injections, evaluation, and currying. The endomorphisms
  of any morphism are exactly those forced by the CCC structure.
- Free category with finite limits: similar but with equalizers instead
  of exponentials.

**Conjecture:** For a free category C generated by a specified set of
universal properties (e.g., free CCC, free topos):

1. Every endoprofunctor on C is diagonally determined (in the
   surjectivity sense of IsDiagDeterminedProf)
2. Paranaturality = parametricity for C (the Neumann-style gap
   disappears because there are no "non-structural" endomorphisms)
3. The Yoneda parametricity in PSh(C) restricted to representables
   agrees with paranaturality on C

**Potential approach:** Show that for any morphism f : a → b in the
free CCC, the factorisation category E(Fact(f)) is connected (every
factorisation is connected to the trivial one via the CCC structure).
Connectedness of E(Fact(f)) would imply that E(Fact)-parametricity
reduces to paranaturality.

**Connection to initial algebras:** If C has an initial algebra for
an endofunctor T, the unique algebra morphism (catamorphism) from
the initial algebra to any other T-algebra is forced by the universal
property. This is the "free theorem" for catamorphisms: they commute
with all natural transformations. The universal property = the
parametricity condition here.

### 26. Parametric Polymorphism as an Internal Type

Rather than restricting to parametric polymorphism (living in
Dial(PSh(C))) or proving parametricity as an external meta-theorem,
the approach for Geb is to allow non-parametric polymorphism
(typecase, reflection on types) and make ParamPoly(T, S) an explicit
type in the language. This gives both ad-hoc dispatch and free
theorems, with free theorems available as internal lemmas.

**The polymorphic function type** (all, including non-parametric):

```text
Poly(T, S) = ∫_X [T(X), S(X)]    (end in PSh(C))
```

**The parametrically polymorphic function type** (subtype):

```text
ParamPoly(T, S) ↪ Poly(T, S)
ParamPoly(T, S) = { f : Poly(T, S) |
  ∀ (α : Sub(X × Y)),
    relInterp(T, α)-related inputs →
    relInterp(S, α)-related outputs }
```

This is a subobject of the polymorphic function type: a dependent
pair of a function and a proof of parametricity. Since PSh(C) is a
topos with subobject classifier Ω, this subobject exists as an
object of PSh(C).

**Reflective language structure:** In a dependently typed language
that can express its own type system internally:

- Type constructors are data (values of a type-of-types)
- `relInterp` is a computable function on type syntax
- `ParamPoly(T, S)` is a dependent subtype
- Free theorems are ordinary lemmas, proved by applying the
  parametricity witness to specific relations

The recursion for `relInterp` follows Wadler:

- `relInterp(A × B, α, β) = relInterp(A, α) × relInterp(B, β)`
- `relInterp(A → B, α, β) = { (f,g) | ∀ (x,y) ∈ relInterp(A, α).
  (f(x), g(y)) ∈ relInterp(B, β) }`
- `relInterp(∀X. T(X), _) = { (f,g) | ∀ α : Rel(X,Y).
  (f_X, g_Y) ∈ relInterp(T, α) }`
- `relInterp(μX. T(X), α)` = least relation closed under
  `relInterp(T, −)` (for initial algebras)

**Requirements on PSh(C):**

1. Internal type universe (object classifiers or subobject
   classifier Ω)
2. Internal relation type: Rel(X, Y) = Sub(X × Y)
3. Internal relational interpretation: computable recursion on type
   syntax
4. Dependent types: to form the subtype ParamPoly(T, S)

PSh(C) provides (1) and (2) as a topos. (3) requires reflecting the
type syntax as data, standard in a dependently typed language. (4)
is the dependent type structure of Geb itself.

**Comparison with Haskell:**

- Haskell forces all polymorphism to be parametric (no typecase),
  gets free theorems as an external meta-theorem (Wadler 1989)
- Geb allows non-parametric polymorphism (typecase, reflection),
  gets free theorems as internal lemmas via ParamPoly type
- Haskell restricts expressiveness for automatic parametricity;
  Geb increases expressiveness while making parametricity opt-in

**Analog:** Haskell's IO monad separates pure from effectful
computation. Here, ParamPoly separates parametric from non-parametric
polymorphism. Both are type-level distinctions that enable reasoning
about the restricted class while allowing the unrestricted class to
coexist.

### Completed Work

#### PolyTwCoprType Refactoring (2025-01-03)

The `PolyTwCoprType.lean` module has been refactored to use mathlib's category
of elements infrastructure. This supports Question 20's investigation of
TwCoprArrElem as a foundation for full parametricity.

**Stage 1** (completed): Replaced `outerPos` and `outerDir` fields in
`DepPolyFunctor` with a single `outerPoly : CoprodCovarRepCat Type` field.

**Stage 2** (completed): Added category of elements aliases in `Polynomial.lean`
using mathlib's `F.Elements` category. Defined `ccrProdIdType` operation for
polynomials (the `× id` operation).

**Stage 3** (completed): Replaced `ElemCatObj` and `ElemCatMor` structures with
abbreviations for `ccrElementsObj`/`ccrElementsMor` of `outerPolyProdId`. This
required:

- Creating accessor functions (`ElemCatObj.baseType`, `ElemCatObj.pos`,
  `ElemCatObj.dirMap`, `ElemCatObj.elem`, `ElemCatMor.func`, `ElemCatMor.posEq`)
- Proving compatibility lemmas (`ElemCatMor.dirCompat`, `ElemCatMor.elemCompat`)
  using sigma decomposition and heterogeneous equality handling
- Updating `Eval` structure to use explicit accessor function calls
- Updating `evalMap` proofs for the new accessor pattern

**Proof pattern for dependent type equalities in morphism compatibility**:

```lean
-- For ElemCatMor.dirCompat and elemCompat proofs:
-- 1. Destructure Y with `obtain ⟨Yt, Ysnd⟩ := Y; obtain ⟨Yfst, Ysnd⟩ := Ysnd`
-- 2. Use `Sigma.mk.injEq` to split sigma equality into components
-- 3. Use `subst hfst` to substitute the first component
-- 4. Use `heq_eq_eq` to convert heterogeneous to homogeneous equality
-- 5. Apply the remaining equality via simp or congrFun
```

This refactoring eliminates custom structure definitions in favor of mathlib's
categorical infrastructure, supporting the goal of using universal properties
rather than low-level transport proofs.

### 27. Copresheaf/Presheaf Reduction of Parametricity

**Question**: For profunctors that ignore one variance direction,
does parametric polymorphism reduce to naturality?

Specifically: if `P, Q : C^op ⥤ C ⥤ Type v` factor through the
projection (i.e., `P(a, b)` does not depend on `a`), then `P` is
effectively a copresheaf `C ⥤ Type v`. A diagonal family
`α_I : P(I,I) → Q(I,I)` becomes a family `α_I : P(I) → Q(I)`.
The claim is that `IsParamPoly` for such families reduces to
naturality as copresheaf transformations.

Dually, if `P(a, b)` does not depend on `b`, then `IsParamPoly`
should reduce to naturality as presheaf transformations.

This would confirm that profunctor parametricity correctly
specializes to the single-variance case.

**Formalization approach**: Define a "constant in first argument"
profunctor as `constProf Q := Functor.const C^op ⋙ Q` for
`Q : C ⥤ Type v`, and prove `IsParamPoly` for families between
such profunctors is equivalent to naturality of `Q ⟶ Q'`.

### 28. IsParamPoly Is Equivalent to IsParanatural

**Result**: `IsParamPoly ↔ IsParanatural` for ALL profunctors.
This means our `IsParamPoly` definition was wrong: it does
not capture parametric polymorphism, it just recaptures
paranaturality.

The `ProfRelLift` at a span `(R, π₁, π₂)` decomposes
definitionally as `∃ e, DiagCompat F R I₀ π₁ e d₀ ∧
DiagCompat F R I₁ π₂ e d₁`. Given a paranatural `α` and
witness `e`, applying paranaturality to each leg independently
with the same witness `α R e` gives the output conditions.

Proved in `ParamPoly.lean`:

- `isParanatural_implies_isParamPoly`
- `isParamPoly_iff_isParanatural`

Consequence: `ParamEndoProf` = `EndoProf`. The span-based
`ProfRelLift` definition operates on profunctors alone,
not on type expressions, and therefore cannot distinguish
paranaturality from parametricity.

### 29. Neumann's Counterexample and Parametric Correction

**Result**: `IsParamPoly` does NOT exclude Neumann's
counterexample, because `IsParamPoly ↔ IsParanatural` (Q28).
Our definition was wrong.

The Q14/Q20/Q21 analysis already identified that the
gap between paranaturality and full parametricity is
syntax-dependent: different type expressions can yield
isomorphic profunctors but different relational
interpretations. Our `ProfRelLift` operates on profunctors
alone and thus captures only paranaturality.

See Q34 for a detailed analysis of Neumann's counterexample,
spelling out the type, the two conditions, the gap between
them, and a concrete counterexample to the diYoneda lemma.

To achieve stronger-than-paranaturality parametricity,
the candidates from our earlier analysis are:

- Arr(C)-level testing (Q20)
- E(Fact)-parametricity (Q21)
- The iterated arrow category tower (Q22)

### 30. Universal Properties of ParamEndoProf

**Question**: What categorical structure does `ParamEndoProf`
have?

SUPERSEDED: since `IsParamPoly ↔ IsParanatural` (Q28),
`ParamEndoProf = EndoProf`, and this question reduces to
studying universal properties of `EndoProf` (Phase 2).

`EndoProf` (with paranatural morphisms) has terminal
objects and binary products but lacks equalizers.

### 32. Yoneda Embedding into ParamEndoProf

**Question**: The Yoneda embedding `y : C → Psh(C)` can be
viewed as a profunctor `y(c)(a, b) = Hom(a, c)` that ignores
its covariant argument. Does this give a fully faithful
embedding `C ↪ ParamEndoProf`?

**Expected answer**: Y. Since `y(c)` ignores the covariant
argument, `IsParamPoly` for transformations `y(c) → y(d)`
reduces to naturality of presheaf maps `Hom(-, c) → Hom(-, d)`,
which by Yoneda is `Hom(c, d)`. So:

`Hom_{ParamEndoProf}(y(c), y(d)) ≅ Hom_C(c, d)`

This embedding provides:

- Ground types from `C` inside the parametric type theory
- Full faithfulness means `C` is recovered exactly
- This is the profunctor version of "Yoneda is fully faithful"

**Formalization**: Define `yonedaProf : C ⥤ ParamEndoProf`
as the composition of the Yoneda embedding with the
"ignore covariant argument" functor `Psh(C) → EndoProf`.
Prove full faithfulness using Q27's reduction result.

### 31. Functoriality of ProfRelLift in Spans

**Question**: Is `ProfRelLift` functorial in the span? That is,
given composable spans `(R₁, π₁, π₂)` and `(R₂, ρ₁, ρ₂)` (with
a "composition" via pullback or similar), does the composed
relation lifting agree with composing the individual liftings?

This is needed to handle deeply nested type constructors (Q29)
and to understand the categorical structure of the relation
lifting operation itself.

### 33. Parametric (Co)Wedges for D-Valued Profunctors

**Question**: Can parametric polymorphism be generalized to
`D`-valued profunctors `P : Cᵒᵖ ⥤ C ⥤ D` via "parametric
(co)wedges", analogous to how `StrongRestrictedWedge` and
`StrongRestrictedCowedge` generalize paranaturality to the
`D`-valued setting?

The current `IsParamPoly` is defined for `Type v`-valued
profunctors. The weighted-limit formulation of paranatural
transformations (via `StrongRestrictedWedge`) already works
for arbitrary `D`. A parametric analogue would replace the
graph-span compatibility condition with full span-based
relation lifting in a `D`-enriched sense.

Sub-questions:

- What is the correct `D`-valued analogue of `ProfRelLift`?
  For `Type`-valued profunctors, the witness `e ∈ F(R,R)` is
  an element; for `D`-valued profunctors, it would be a
  morphism from a terminal object or a structured cone.
- Does the `D`-valued parametric condition collapse to
  paranaturality when `D` has enough structure (e.g., is a
  topos)?
- Can the relation-lifting be expressed as a (co)limit
  condition in `D`, making it compatible with the weighted
  (co)limit formulation of paranatural transformations?

This investigation should follow the universal-property
investigation (Q30), since the categorical structure of
`ParamEndoProf` informs what properties we need from `D`.

### 34. Neumann's Counterexample: Detailed Analysis

This section spells out, in detail, the divergence between
paranaturality (strong dinaturality) and Reynolds-style
parametricity, as presented in Neumann's TYPES 2024 talk
(slides 10-15).

#### The type

In Haskell-like syntax:

```haskell
phi :: forall x. ((x -> x) -> x) -> x
```

This is the type of a "recursion scheme" or "Church-style
iterator" that, given a way to produce an `x` from an
endomorphism `x -> x`, extracts a plain `x`. Inhabitants
include `\p -> p id` (apply the producer to the identity)
and `\p -> p (\x -> p (\_ -> x))` (apply twice with a
reset), among others.

#### The profunctor

The type expression `((X -> X) -> X) -> X` determines a
profunctor `T : C^op x C -> Set` by substituting `a` for
negative-variance occurrences of `X` and `b` for
positive-variance occurrences.

Tracking variance through the nesting:

```text
((X -> X) -> X) -> X
  -    +    -     +
```

Position 1 (`X -> ...`): negative (argument of `->`,
inside argument of `->`, inside argument of outer `->`)
Position 2 (`... -> X`): positive (result of `->`,
inside argument of `->`, inside argument of outer `->`)
Position 3 (`... -> X` in `(X->X)->X`): negative
(result of inner `->`, inside argument of outer `->`)
Position 4 (outermost `X`): positive (result of outer `->`)

So:

```text
T(a, b) = ((a -> b) -> a) -> b
```

A polymorphic function `phi : forall X. T(X,X)` is a family
`(phi_I : ((I -> I) -> I) -> I)` indexed by sets I, subject
to a coherence condition.

For the `ParanatSig` decomposition, the outer `->` becomes
the `ParanatSig` arrow, splitting `T` into:

- Source: `P(a, b) = (b -> a) -> b` (variance tracked
  within `(X -> X) -> X` alone; the outer `->`'s variance
  flip is NOT included)
- Target: `Q(a, b) = b` (the identity profunctor `IdProf`)

The relationship between `T` and `P, Q` is:
`T(a, b) = P(b, a) -> Q(a, b)`, where `P`'s variables
are swapped because P appears in negative position.
Formalized in `ParanaturalTopos.lean` as `divSource`
and `divTarget`.

#### Free theorem (Reynolds parametricity)

The Reynolds free theorem for this type says:

For all `f : I -> J`, `p : (I -> I) -> I`,
`q : (J -> J) -> J`:

If for all `h : I -> I` and `k : J -> J` such that
`f . h = k . f`:

```text
f(p(h)) = q(k)
```

then:

```text
f(phi_I(p)) = phi_J(q)
```

The hypothesis relates `p` and `q` via `f`: whenever
endomorphisms `h` on `I` and `k` on `J` form a commuting
square with `f` (i.e. `f . h = k . f`), then `p` and `q`
send them to `f`-related outputs. This quantifies over
**independent pairs** `(h, k)` satisfying the commutation
condition.

The conclusion says `phi` preserves this relatedness: if
the inputs `p, q` are `f`-related, the outputs
`phi_I(p), phi_J(q)` are also `f`-related.

#### Strong dinaturality (paranaturality)

The paranaturality condition for the same type says:

For all `f : I -> J`, `p : (I -> I) -> I`,
`q : (J -> J) -> J`:

If for all `r : J -> I`:

```text
f(p(r . f)) = q(f . r)
```

then:

```text
f(phi_I(p)) = phi_J(q)
```

Given `r : J -> I`, set `h := r . f : I -> I` and
`k := f . r : J -> J`. These automatically satisfy
`f . h = f . r . f = k . f`. So the paranaturality
hypothesis is a specialization of the parametricity
hypothesis to pairs of the form `(r . f, f . r)`.

#### The gap

The parametricity hypothesis quantifies over all pairs
`(h, k)` satisfying `f . h = k . f`.

The paranaturality hypothesis quantifies only over pairs
`(r . f, f . r)` for a single morphism `r : J -> I`.

Every pair `(r . f, f . r)` satisfies the commutation
condition, but not every commuting pair `(h, k)` has the
form `(r . f, f . r)` for some `r`. For `(h, k)` to have
this form, we would need a single `r` such that both
`h = r . f` and `k = f . r`. Given `h` and `k` with
`f . h = k . f`, we can try `r` such that `h = r . f`,
but then `k` must equal `f . r`, which may not hold:
from `f . r . f = k . f` we get `f . r = k` only if
`f` is an epimorphism (right-cancellable), which it need
not be.

Since the paranaturality hypothesis is weaker (fewer
pairs must satisfy the compatibility), it is easier for
a pair `(p, q)` to pass the paranaturality gate. So
paranaturality gives the conclusion for more `(p, q)`
pairs than parametricity does. This means paranaturality
is a **stronger condition on phi**: every paranatural
`phi` is parametric, but a parametric `phi` might fail
to be paranatural.

This is consistent with our Q28 proof: paranaturality
implies `IsParamPoly` (our span-based formulation).
The converse also holds because our `IsParamPoly` was
itself equivalent to paranaturality.

#### The counterexample to the diYoneda lemma

On slide 15, Neumann gives a concrete counterexample
showing that paranaturality does not determine a
transformation by its diagonal values. This refutes the
"diYoneda lemma," the profunctor analogue of the Yoneda
lemma.

The diYoneda lemma would claim: for `F : C^op x C -> Set`,

```text
F(I, I)  <-->  strong-end_K  C(I,K) x C(K,I) x F(K,K)
```

where the strong end is over `K` and the integrand is
a profunctor in `(I, J)` (Neumann's "diYoneda embedding"
`yy(I,J)(K,L) = C(I,L) x C(K,J)`).

The candidate maps are:

Forward (evaluate at identity):
`phi |-> phi_I(id, id)`

Backward (reconstruct from diagonal value):
`x |-> (K, a, b) |-> F(b, a)(x)`

The round-trip `x |-> x` works (forward-then-backward):

```text
x |-> phi where phi_K(a,b) = F(b,a)(x)
  |-> phi_I(id, id) = F(id, id)(x) = x
```

But the round-trip `phi |-> phi` fails
(backward-then-forward):

```text
phi |-> phi_I(id, id) = x
    |-> psi where psi_K(a,b) = F(b,a)(x)
```

This `psi` may differ from the original `phi`.

**Concrete counterexample**: Take `F = Hom_Set` (so
`F(K,K) = (K -> K)`) and `I` an arbitrary set. Define:

```text
phi_K(a : I -> K, b : K -> I) = (b . a)^2 = b.a.b.a
```

This is an element of the strong end
`strong-end_K Set(I,K) x Set(K,I) x Hom(K,K)`.
It is strongly dinatural (paranatural) in `K`.

Applying the round-trip:

```text
phi_I(id, id) = (id . id)^2 = id
```

Then the reconstructed transformation is:

```text
psi_K(a, b) = Hom(b, a)(id) = b . id . a = b . a
```

But `b . a /= (b . a)^2` in general (e.g., when
`b . a` is not idempotent). So `psi /= phi`:

```text
phi_K(a, b) = (b . a)^2
psi_K(a, b) = b . a
```

The function `(b . a)^2` is paranatural but is NOT
determined by its diagonal value `phi_I(id, id) = id`.
It "sees" off-diagonal information (the interaction
between `a` and `b` through a nontrivial `K`) that
cannot be recovered from the diagonal alone.

#### Why our span-based formulation failed

Our `ProfRelLift` definition in `ParamPoly.lean`
defines parametricity as: for every span
`(R, pi1 : R -> I0, pi2 : R -> I1)`, if
`ProfRelLift F pi1 pi2 d0 d1` then
`ProfRelLift G pi1 pi2 (alpha d0) (alpha d1)`.

The `ProfRelLift` condition decomposes as:

```text
exists e in F(R,R),
  F(id, pi1)(e) = F(pi1^op, id)(d0)   -- DiagCompat
  F(id, pi2)(e) = F(pi2^op, id)(d1)   -- DiagCompat
```

Each leg is an independent `DiagCompat` condition.
Paranaturality preserves each leg separately using the
same witness `alpha(R)(e)`, giving:

```text
exists (alpha(R)(e)) in G(R,R),
  G(id, pi1)(alpha(R)(e)) = G(pi1^op, id)(alpha(d0))
  G(id, pi2)(alpha(R)(e)) = G(pi2^op, id)(alpha(d1))
```

This works because the span's two projections are
handled independently. In contrast, Reynolds-style
parametricity for types like `((X -> X) -> X) -> X`
involves relations on function spaces, where the
hypothesis `f . h = k . f` correlates `h` and `k`
through `f` in a way that need not factor through
any single span witness. The profunctor-level span
decomposition loses this correlation.

In short: the span-based formulation tests whether
`alpha` respects the two-legged structure of profunctor
relations, but Reynolds parametricity for higher-order
types involves relational constraints within the type
expression's structure that the profunctor alone does
not encode.

#### Neumann's proposed responses

Neumann lists three possibilities (slide 11):

1. Give up.

2. Rule out types like `forall X. ((X -> X) -> X) -> X`.
   Hackett and Hutton [HH15] write: "parametricity of all
   System F types entails strong dinaturality. For the
   purposes of this paper, we assume all recursion operators
   of interest are strongly dinatural; in practice, we are
   not aware of any such operators in common use where this
   assumption fails."

3. Give difunctors a true exponential (the approach
   Neumann pursues in the rest of the talk, leading to the
   diYoneda embedding and the discovery that the diYoneda
   lemma is false).

#### Relationship to our formalization

What we have proved:

- `IsParamPoly ↔ IsParanatural` (Q28): our span-based
  `IsParamPoly` is not parametricity.
  It is equivalent to paranaturality.

- For types where paranaturality coincides with
  parametricity (linear types: Church numerals, initial
  algebras mu(F), terminal coalgebras nu(F)), our existing
  `EndoProf` category with paranatural morphisms is
  adequate.

- For types where paranaturality diverges from
  parametricity (types with nested higher-order iteration
  like `((X -> X) -> X) -> X`), a different formulation
  is needed. The candidates identified in Q20-Q22 remain:
  Arr(C)-level testing, E(Fact)-parametricity, and the
  iterated arrow category tower.

#### Formalization results (ParametricityDivergence section)

In `ParanaturalTopos.lean` section `ParametricityDivergence`:

- `divSource : Type^op ⥤ Type ⥤ Type` where
  `P(a,b) = (b -> a) -> b`
- `divTarget = IdProf : Type^op ⥤ Type ⥤ Type` where
  `Q(a,b) = b`
- `divParanatSig_eq : ParanatSig divSource divTarget =
  ((I : Type) -> ((I -> I) -> I) -> I)` (by rfl)
- `DivParanatural` and `DivParametric`: spelled-out Props
- `divParanatural_iff_isParanatural`: equivalence
- `divParanatural_implies_divParametric`: paranaturality
  implies parametricity
- `divApplyId = fun I p => p id`:
  - `divApplyId_parametric`: IS parametric
  - `divApplyId_not_paranatural`: NOT paranatural
  (Bool witness: f = const true, p = q = (. false))
- `divParametric_not_implies_divParanatural`: the
  converse of the implication fails
- `divIterOnce`, `divIterThree`: additional candidates,
  all parametric but not paranatural via the same Bool
  witness

The Bool witness works because: const-true makes the
LHS of the paranaturality hypothesis always `true`,
and `(. false)` applied to any parametrically-built
endomorphism yields `false`. So the hypothesis holds
trivially (true = true) but the conclusion requires
true = false.

#### Open questions from this analysis

1. ANSWERED (Q35). The gap goes the other direction:
   `divApplyId` is parametric but NOT paranatural.
   Paranaturality is the stronger condition.

2. Does the diYoneda counterexample `(b . a)^2`
   correspond to a specific `phi` of the above type that
   violates parametricity? Or is it a separate phenomenon
   (failure of the Yoneda principle for strong ends, which
   is related but distinct)?

3. Can the "linear type" condition (types where
   paranaturality = parametricity) be characterized
   precisely? This would tell us exactly when `EndoProf`
   suffices and when we need a stronger formulation.

4. Are there ANY paranatural elements of this type?
   Three tested candidates (divApplyId, divIterOnce,
   divIterThree) all fail paranaturality via the same
   Bool witness. In a parametric model, the conjecture
   is that the type has no paranatural inhabitants.

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
10. Verify PER model references and connection to reflexive graphs (Question 16)
11. Formalize continuation/Kan-extension connection for dual-variance (Question 17)
12. Port polynomial profunctor CCC to Lean and verify generalization (Question 18)
13. Define curried-PRA polynomial profunctors in Lean (Question 19)
14. Implement TwCoprArrElem approach for full parametricity (Question 20)
15. Verify inner-endomorphism characterization and E(Fact) bridge (Question 21)
16. Formalize non-CCC parametricity via external hom (Question 22)
17. Define E(Fact)-parametricity and compare with paranaturality (Question 22)
18. Investigate Yoneda parametricity for non-CCC categories (Question 23)
19. Formalize Arrⁿ(C) = [2ⁿ, C] cubical tower (Question 23)
20. Build relational-interpretation functor using RelCat and
    Dial (Question 24)
21. Use F.op.lan to lift type constructors to PSh(C) and verify
    compatibility with relational interpretation (Question 24)
22. Verify automatic parametricity for free CCC via
    connectedness of E(Fact) (Question 25)
23. Show catamorphism parametricity from initial-algebra
    universal property (Question 25)
24. Define internal relInterp recursion on type syntax in
    PSh(C) (Question 26)
25. Define ParamPoly(T, S) as subobject of Poly(T, S) in
    PSh(C) (Question 26)
26. Prove internal free theorems for ParamPoly inhabitants
    (Question 26)
27. DONE. Copresheaf/presheaf reduction: IsParamPoly for
    single-variance profunctors = naturality (Question 27).
    Both presheaf and copresheaf versions proved in
    ParamPoly.lean.
28. DONE. IsParamPoly ↔ IsParanatural for ALL profunctors.
    Our definition of parametricity was wrong: the span-based
    ProfRelLift decomposes as two DiagCompat conditions
    sharing a witness, which is what paranaturality preserves.
    ParamEndoProf = EndoProf as a consequence.
29. RESOLVED. IsParamPoly = IsParanatural (Q28), so
    ProfRelLift does NOT exclude Neumann's counterexample.
    See Q34 for detailed counterexample analysis. Stronger
    parametricity requires syntax-dependent notions
    (Arr-level, E(Fact), iterated tower).
30. SUPERSEDED. ParamEndoProf = EndoProf (Q28), so Q30
    reduces to studying universal properties of EndoProf
    (which is the existing Phase 2 investigation).
31. Prove functoriality of ProfRelLift in spans (Question 31)
32. DONE. yonedaEndoProf : C ⥤ EndoProf is fully faithful
    (yonedaEndoProf_fullyFaithful). Uses Q27 reduction and
    paranaturality=parametricity for presheaf-profunctors.
33. Generalize parametric polymorphism to D-valued
    profunctors via parametric (co)wedges (Question 33)
34. DONE. Neumann's counterexample analysis (Q34).
    Profunctors formalized as divSource/divTarget.
    DivParanatural/DivParametric Props defined and
    equivalence with IsParanatural proved.
35. DONE. Formal separation: paranaturality strictly
    stronger than parametricity for `((X->X)->X)->X`.
    `divApplyId` is parametric but not paranatural.
    Three candidates tested, all fail paranaturality via
    Bool witness (f=const true, p=q=(. false)).
36. DONE. DiagCompat decomposition of parametricity and
    paranaturality (Q36). Both conditions decompose as:
    "under a gate condition on (p,q), the pair
    (phi I₀ p, phi I₁ q) is DiagCompat for divTarget."
    The gate differs:
    - Paranaturality: DiagCompat divSource (= the source
      profunctor's own compatibility), which coincides
      with `Paranat divSource divTarget`.
    - Parametricity: "preserves DiagCompat from
      divHomProf to divTarget" (a higher-order condition
      using the hom-profunctor).
    Formalized as DivParametricBundled/DivParanaturalBundled
    with equivalences to subtype forms. Bundled paranaturality
    is definitionally Paranat divSource divTarget (rfl).
    `divHomProf_diagCompat_eq` shows DiagCompat for the
    hom-profunctor reduces to f . h = k . f (rfl).
