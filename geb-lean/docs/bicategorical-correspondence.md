# Bicategorical Structure and the Adjunction

This document analyzes what happens to the 2-categorical structure of Cat
under the reflective adjunction L ⊣ Φ, particularly what natural
transformations between functors correspond to.

## The 2-Categorical Structure of Cat

Cat is not merely a category but a **2-category** (in fact, a strict
2-category):

- **0-cells**: Small categories
- **1-cells**: Functors F : C → D
- **2-cells**: Natural transformations α : F ⇒ G

For any two categories C and D, the hom-category Fun(C, D) has:

- Objects: Functors C → D
- Morphisms: Natural transformations

## What the Adjunction Preserves

### At the 1-Categorical Level

The adjunction L ⊣ Φ operates at the 1-categorical level:

- Φ : Cat → [J, Type] sends:
  - Categories → Copresheaves
  - Functors → Natural transformations of copresheaves

- L : [J, Type] → Cat sends:
  - Copresheaves → Categories (via quotient of free category)
  - Natural transformations → Functors

### The Missing Dimension

The copresheaf category [J, Type] is a **1-category**:

- Objects: Functors J → Type
- Morphisms: Natural transformations

There is no intrinsic 2-categorical structure in [J, Type]. Natural
transformations between functors in Cat have no direct correspondent.

## Analysis of the Correspondence

### Functors Under Φ

For F : C → D, the induced Φ(F) : Φ(C) → Φ(D) is a natural transformation
with components:

```text
Φ(F)_Obj : Obj_C → Obj_D
Φ(F)_Mor : Mor_C → Mor_D
Φ(F)_Id  : Id_C → Id_D    (= Φ(F)_Obj)
Φ(F)_Comp: Comp_C → Comp_D (induced on composable pairs)
```

### Natural Transformations Under Φ

For a natural transformation α : F ⇒ G between F, G : C → D, we have:

- Components α_c : F(c) → G(c) for each c ∈ C
- Naturality squares commuting

**Question**: What structure in [J, Type] corresponds to α?

### The Collapse

Under Φ, both F and G map to natural transformations Φ(F), Φ(G) : Φ(C) → Φ(D).
A natural transformation α : F ⇒ G does **not** correspond to a morphism in
[J, Type] because:

- Morphisms in [J, Type] are natural transformations between copresheaves
- Φ(F) and Φ(G) are **parallel** morphisms Φ(C) → Φ(D)
- There's no "morphism between parallel morphisms" in a 1-category

The 2-cells of Cat are **collapsed** (forgotten) by the embedding into the
1-category [J, Type].

## Recovering 2-Categorical Structure

### Option 1: Cat-Valued Copresheaves

Replace Type with Cat as the target:

**[J, Cat]** has 2-categorical structure:

- 0-cells: Functors J → Cat
- 1-cells: Natural transformations
- 2-cells: Modifications

An embedding Φ' : Cat → [J, Cat] would preserve 2-categorical structure:

|Cat|[J, Cat]|
|---|---|
|Category C|Cat-valued copresheaf Φ'(C)|
|Functor F : C → D|Natural transformation Φ'(F)|
|Nat. trans. α : F ⇒ G|Modification Γ_α|

### Option 2: Internal Hom Enrichment

The category [J, Type] can be enriched over Cat by considering:

- Hom_{[J,Type]}(F, G) as a category (not just a set)
- Natural transformations as objects
- Modifications as morphisms

This recovers some 2-categorical structure.

### Option 3: Spans or Profunctors

Natural transformations α : F ⇒ G can be viewed as spans:

```text
        α
    F ←--- G
     \   /
      ↘ ↙
       id_D
```

Under Φ, this might correspond to a span in [J, Type].

## Modifications Explained

### Definition

A **modification** Γ : α ⇛ β between natural transformations
α, β : F ⇒ G (where F, G : A → B are 2-functors) consists of:

- For each object a ∈ A, a 2-cell Γ_a : α_a ⇒ β_a in B
- Subject to coherence: for each f : a → b, a certain cylinder commutes

### Role in [J, Cat]

In [J, Cat], modifications are the natural 2-cells. If we embed Cat into
[J, Cat] via Φ':

- Natural transformation α : F ⇒ G in Cat
- Becomes a modification Φ'(α) : Φ'(F) ⇛ Φ'(G) in [J, Cat]

## The Transfor Hierarchy

Transfors generalize the notion of morphisms between categorical structures:

|k|k-transfor|Between|
|---|---|---|
|0|Functor|Categories|
|1|Natural transformation|Functors|
|2|Modification|Natural transformations|
|3|Perturbation|Modifications|

Under Φ : Cat → [J, Type]:

- 0-transfors (functors) → 1-transfors (nat. trans. in [J, Type])
- 1-transfors (nat. trans.) → (no correspondent)

Under Φ' : Cat → [J, Cat]:

- 0-transfors → 1-transfors
- 1-transfors → 2-transfors (modifications)

## Implications for the Adjunction

### Current State

The adjunction L ⊣ Φ views Cat as a 1-category. Natural transformations
between functors are not preserved as morphisms.

### Potential 2-Categorical Extension

A 2-adjunction L' ⊣ Φ' between 2-Cat and [J, Cat] would:

1. **Preserve 2-cells**: Natural transformations ↔ modifications
2. **Require 2-functoriality**: L' and Φ' must be 2-functors
3. **Triangle identities**: Become 2-categorical (involve modifications)

### Construction Sketch for Φ'

For a category C, define Φ'(C) : J → Cat:

- Φ'(C)(Obj) = discrete category on Obj_C
- Φ'(C)(Mor) = discrete category on Mor_C
- Φ'(C)(Id) = discrete category on Obj_C
- Φ'(C)(Comp) = discrete category on ComposablePairs_C

With functors between these induced by dom, cod, etc.

**Issue**: This makes all values discrete categories, losing information.

### Alternative: Non-Discrete Target

Another approach for Φ'(C):

- Φ'(C)(Obj) = category with one object per c ∈ C, with Aut(c) as morphisms
- Φ'(C)(Mor) = similarly enriched with automorphisms

This captures more structure but is more work to define.

## Constructing Cat-Valued Copresheaves via Currying

### `Cat`-valued copresheaves from reflector

Given the adjunction L ⊣ Φ : Cat ⇆ [J, Type], Cat-valued copresheaves can be
constructed by post-composing with L:

- A [J, Type]-valued copresheaf on C is: F : C → [J, Type]
- Post-composing with L gives: L ∘ F : C → Cat

### The Currying Equivalence

By the exponential law in Cat:

```text
[C, [J, Type]] ≅ [C × J, Type]
```

A copresheaf on C valued in [J, Type] is **equivalent** to a copresheaf on C × J
valued in Type. This is the standard currying/uncurrying isomorphism.

### Combined Construction

Cat-valued copresheaves on C arise from Type-valued copresheaves on C × J:

1. Start with G : C × J → Type (copresheaf on the product)
2. Curry to get G̃ : C → [J, Type]
3. Post-compose with L to get L ∘ G̃ : C → Cat

### Application to 2-Categorical Embedding

For Φ' : Cat → [J, Cat], construct as follows:

1. Define Ψ : Cat → [J, [J, Type]] ≅ [J × J, Type]
2. Apply L pointwise: Φ' = L_* ∘ Ψ : Cat → [J, Cat]

where L_* denotes post-composition with L.

### The Product Category J × J

The product J × J has 16 objects (pairs from {Obj, Mor, Id, Comp}²):

||Obj|Mor|Id|Comp|
|---|---|---|---|---|
|**Obj**|(Obj,Obj)|(Obj,Mor)|(Obj,Id)|(Obj,Comp)|
|**Mor**|(Mor,Obj)|(Mor,Mor)|(Mor,Id)|(Mor,Comp)|
|**Id**|(Id,Obj)|(Id,Mor)|(Id,Id)|(Id,Comp)|
|**Comp**|(Comp,Obj)|(Comp,Mor)|(Comp,Id)|(Comp,Comp)|

This 16-object category provides enough structure to encode:

- The basic category structure (diagonal entries)
- The "hom" structure needed for 2-cells (off-diagonal entries)

### Proposed Construction for Ψ

For a category C, define Ψ(C) : J × J → Type by:

- Ψ(C)(Obj, Obj) = Obj_C (objects of C)
- Ψ(C)(Mor, Mor) = Mor_C (morphisms of C)
- Ψ(C)(Obj, Mor) = Mor_C (morphisms as "hom-data")
- Ψ(C)(Mor, Obj) = Mor_C (morphisms with source information)
- Other entries encode identity, composition, and coherence structure

After applying L pointwise, this should yield Φ'(C) : J → Cat with:

- Φ'(C)(Obj) = L(Ψ(C)(Obj, -)) : a category
- Φ'(C)(Mor) = L(Ψ(C)(Mor, -)) : a category
- etc.

### Why This Might Work

The extra J-factor in J × J provides the "internal morphism" structure:

- The first J-coordinate indexes the "external" structure (objects, morphisms, etc.)
- The second J-coordinate provides internal category structure within each component

### Verification Questions

1. Does L_* ∘ Ψ give the correct Φ'(C)(j) for each j ∈ J?
2. Do functors F : C → D induce natural transformations Φ'(C) → Φ'(D)?
3. Do natural transformations α : F ⇒ G induce modifications?
4. Is the construction compatible with the existing L ⊣ Φ?
5. What is the explicit form of the morphisms in J × J?

## Conclusion

1. **Under Φ : Cat → [J, Type]**: Natural transformations do not correspond to
   any morphisms in [J, Type]. The 2-categorical structure is collapsed.

2. **Modifications as the answer**: In a Cat-valued embedding Φ' : Cat → [J, Cat],
   natural transformations correspond to modifications.

3. **Currying approach**: Cat-valued copresheaves can be constructed from
   copresheaves on J × J via currying and post-composition with L. This provides
   a concrete path to defining Φ' using the existing adjunction.

4. **The product J × J**: The 16-object category J × J is a natural candidate
   for encoding 2-categorical structure, with the second J-factor providing
   internal hom structure.

5. **For the current implementation**: The L ⊣ Φ adjunction captures the
   1-categorical essence of Cat. Extending to 2-categories may be achievable
   via the currying/product construction without fundamentally new machinery.

## References

- nLab: modification, transfor, 2-category, bicategory
- Lack, S. A 2-Categories Companion. IMA notes.
- Johnson, N., & Yau, D. (2020). 2-Dimensional Categories. arXiv:2002.06055.
- Kelly, G. M., & Street, R. (1974). Review of the elements of 2-categories.
  Springer LNM 420.
