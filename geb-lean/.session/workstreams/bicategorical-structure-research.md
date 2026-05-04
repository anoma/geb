# Bicategorical Structure Under the Adjunction

## Status: Active Research - Currying Approach Under Investigation

## Context

Cat is not just a category but a 2-category (or bicategory): between any two
functors F, G : C → D, there's a category Nat(F, G) of natural transformations.
This workstream investigates what these natural transformations correspond to
under the L |- Phi adjunction.

## The Question

Under Phi : Cat → [J, Type], categories become copresheaves and functors become
natural transformations between copresheaves. But:

- Functors F, G : C → D form a category Fun(C, D)
- Natural transformations α : F ⇒ G are morphisms in Fun(C, D)
- What structure on copresheaves corresponds to Nat(F, G)?

## Analysis

### What Phi Does to Functors

For a functor F : C → D, the induced Phi(F) : Phi(C) → Phi(D) is a natural
transformation between copresheaves with components:

- (Phi(F))_Obj : Obj_C → Obj_D (the object function)
- (Phi(F))_Mor : Mor_C → Mor_D (the morphism function)
- (Phi(F))_Id : Id_C → Id_D (identity witness map = object function)
- (Phi(F))_Comp : Comp_C → Comp_D (composable pair map)

This is implemented in `OverFunctorData.toJudgmentNatTrans` at line 551 of
CatJudgmentAdjunction.lean.

### What Natural Transformations Become

A natural transformation α : F ⇒ G consists of:

- Components α_a : F(a) → G(a) for each object a ∈ C
- Naturality: G(f) ∘ α_a = α_b ∘ F(f) for each f : a → b

Under Phi, this would correspond to a "transformation between transformations":

- A 2-cell in the copresheaf category [J, Type]

### 1-categorical structure

The copresheaf category [J, Type] is a 1-category with:

- Objects: Copresheaves F : J → Type
- Morphisms: Natural transformations α : F → G

Natural transformations between functors F, G : C → D under Phi become:

- Elements of Hom_{[J,Type]}(Phi(C), Phi(D))

But there's no automatic 2-categorical structure in [J, Type] itself.

### The Correspondence

**Claim**: Natural transformations α : F ⇒ G between functors F, G : C → D
correspond to certain "extra structure" in [J, Type], not to morphisms.

Specifically, the functor category Fun(C, D) under Phi corresponds to:

- Objects: Natural transformations Phi(C) → Phi(D) satisfying functoriality
- Morphisms: ???

This "???" is where modifications would enter.

## Modifications and Higher Structure

### The 2-Category 2Cat

The 2-category of 2-categories has:

- 0-cells: 2-categories (like Cat)
- 1-cells: 2-functors
- 2-cells: 2-natural transformations (or pseudonatural transformations)
- 3-cells: Modifications

### Modifications Defined

A modification Γ : α ⇛ β between 2-natural transformations α, β : F ⇒ G
(themselves between 2-functors F, G : A → B) consists of:

- For each object a ∈ A, a 2-cell Γ_a : α_a ⇒ β_a in B
- Satisfying coherence conditions

### Application to Our Setting

For the L |- Phi adjunction, we have:

- Cat is a 2-category
- [J, Type] is a 1-category

The embedding Phi : Cat → [J, Type] "forgets" the 2-categorical structure.

To recover it, we would need to:

1. Enrich [J, Type] over Cat (making it a 2-category)
2. Make Phi a 2-functor
3. Natural transformations in Cat would correspond to 2-cells in enriched [J,Type]

### Enriched Copresheaf Categories

The category [J, Cat] of Cat-valued copresheaves IS a 2-category:

- Objects: Functors F : J → Cat
- 1-cells: Natural transformations α : F → G
- 2-cells: Modifications Γ : α ⇛ β

**Observation**: If we embed Cat into [J, Cat] instead of [J, Type], then:

- Functors become natural transformations (1-cells)
- Natural transformations become modifications (2-cells)

This is the "correct" 2-categorical embedding.

## Concrete Analysis

### What's Lost in [J, Type]

When we use Phi : Cat → [J, Type]:

- A category C maps to type-valued data
- Functors F : C → D map to natural transformations
- Natural transformations α : F ⇒ G... don't directly correspond to anything

The 2-cells are "collapsed" because Type has no internal 2-categorical structure.

### What Would Be Preserved in [J, Cat]

An embedding Phi' : Cat → [J, Cat] would send:

- Category C to a Cat-valued copresheaf
- Functor F : C → D to a natural transformation of Cat-valued copresheaves
- Natural transformation α : F ⇒ G to a modification between those

But this requires redefining the construction with Cat as the target instead
of Type.

## Transfors and Higher k-Cells

### The Transfor Hierarchy

- 0-transfor = functor
- 1-transfor = natural transformation
- 2-transfor = modification
- 3-transfor = perturbation
- k-transfor = (k-1)-cell between (k-2)-cells

### Connection to Our Adjunction

In the Type-valued setting:

- Phi sends functors to 1-transfors (natural transformations)
- There's no place for 2-transfors in [J, Type]

In a Cat-valued setting:

- Phi' would send functors to 1-transfors
- Natural transformations would become 2-transfors (modifications)

## Conclusions

1. **Under Phi : Cat → [J, Type]**: Natural transformations do not directly
   correspond to any morphism in [J, Type]. They're "lost" structure.

2. **Recovering structure**: To preserve 2-categorical structure, use Cat-valued
   copresheaves [J, Cat] instead of Type-valued copresheaves [J, Type].

3. **Modifications**: In [J, Cat], natural transformations between functors
   correspond to modifications between natural transformations of copresheaves.

4. **The embedding is 1-categorical**: The current L |- Phi adjunction views
   Cat as a 1-category. A 2-categorical version would require:
   - Target: [J, Cat] instead of [J, Type]
   - Phi as a 2-functor
   - L as a 2-functor (if it exists)

## Code References

- `GebLean/CatJudgmentAdjunction.lean:551-568` - toJudgmentNatTrans
- `GebLean/CategoryJudgments.lean:270-282` - NatTransData

## External References

- [nLab: modification](https://ncatlab.org/nlab/show/modification)
- [nLab: transfor](https://ncatlab.org/nlab/show/transfor)
- [nLab: 2-category](https://en.wikipedia.org/wiki/2-category)
- [nLab: bicategory](https://ncatlab.org/nlab/show/bicategory)
- Stephen Lack, "A 2-Categories Companion" (IMA notes)
- arXiv:2002.06055, "2-Dimensional Categories"

## Cat-Valued Copresheaves via Currying

### Pre/post-composing adjunction

Since we have the adjunction L ⊣ Φ : Cat ⇆ [J, Type], we can construct Cat-valued
copresheaves by composing with L:

1. A [J, Type]-valued copresheaf on C is: F : C → [J, Type]
2. Post-composing with L gives: L ∘ F : C → Cat (a Cat-valued copresheaf)

### The Currying Equivalence

By the exponential law in Cat:

```text
[C, [J, Type]] ≅ [C × J, Type]
```

A copresheaf on C valued in [J, Type] is equivalent to a copresheaf on C × J
valued in Type.

### Combined Construction

Cat-valued copresheaves on C can be obtained from Type-valued copresheaves on
C × J:

1. Start with G : C × J → Type (copresheaf on the product)
2. Curry to get G̃ : C → [J, Type]
3. Post-compose with L to get L ∘ G̃ : C → Cat

### Application to 2-Categorical Embedding

For the 2-categorical embedding Φ' : Cat → [J, Cat], we could construct:

1. Define Ψ : Cat → [J, [J, Type]] ≅ [J × J, Type]
2. Apply L pointwise: Φ' = L_* ∘ Ψ : Cat → [J, Cat]

where L_* denotes post-composition with L.

### What Ψ Should Be

The question becomes: what copresheaf on J × J captures the 2-categorical structure?

For a category C, we need Ψ(C) : J × J → Type such that:

- Ψ(C)(Obj, Obj), Ψ(C)(Obj, Mor), etc. encode the data
- After applying L pointwise, we get Φ'(C) : J → Cat with the right properties

One approach: Ψ(C)(j₁, j₂) could encode "morphisms in C from j₁-data to j₂-data"
in some sense.

### Why This Helps

The product J × J has 16 objects (pairs from {Obj, Mor, Id, Comp}²). This provides
enough room to encode:

- The basic category structure (diagonal entries)
- The "hom" structure needed for 2-cells (off-diagonal entries)

### Concrete Proposal

Define Ψ(C) : J × J → Type by:

- Ψ(C)(Obj, Obj) = Obj_C (objects)
- Ψ(C)(Mor, Mor) = Mor_C (morphisms)
- Ψ(C)(Obj, Mor) = Mor_C (morphisms viewed as "arrows from objects to morphisms")
- Other entries encode composition and identity structure

The exact definition must be proven to ensure L_* ∘ Ψ produces the
correct Cat-valued structure.

### Verification Needed

1. Does this construction give the right Φ'(C)(j) for each j ∈ J?
2. Do functors F : C → D induce natural transformations Φ'(C) → Φ'(D)?
3. Do natural transformations α : F ⇒ G induce modifications?
4. Is the construction compatible with the existing L ⊣ Φ adjunction?

## Future Work

1. Define Cat-valued copresheaves on CategoryJudgments
2. Extend the adjunction to a 2-adjunction L' |- Phi'
3. Verify that modifications correspond to natural transformations
4. Investigate whether the reflectivity extends to the 2-categorical level
5. Work out the explicit form of Ψ : Cat → [J × J, Type]
6. Verify the currying/L-composition construction produces the correct structure
7. Determine if [J × J, Type] is the natural home for understanding 2-cells
