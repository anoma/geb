# Retrofunctors and Potential Copresheaf Embeddings

This document analyzes whether the category Cof (categories with retrofunctors
as morphisms) admits a reflective or coreflective embedding into a copresheaf
category, analogous to the L ⊣ Φ adjunction for Cat.

## Background

### Retrofunctors Defined

A **retrofunctor** φ : A ↛ B between categories consists of:

1. An object function φ₀ : Obj(A) → Obj(B) (covariant in objects)
2. A morphism lift φ₁ : (a ∈ A, u : φ₀(a) → b) ↦ (f : a → a') (contravariant
   in morphisms, relative to the object map)

Subject to:

- Identity preservation: φ₁(a, id_{φ₀(a)}) = id_a
- Composition preservation: φ₁(a, v ∘ u) = φ₁(a', v) ∘ φ₁(a, u)

There is asymmetry in that that objects go "forward" while morphisms go
"backward" relative to the object assignment.

### The Category Cof

- Objects: Small categories
- Morphisms: Retrofunctors
- Composition: (γ ∘ φ)₁(a, u) = φ₁(a, γ₁(φ₀(a), u))

Alternative notation: Cat# (pronounced "Cat-sharp")

### Polynomial Characterization

A fundamental result of Ahman-Uustalu (2016) and Spivak-Niu (2021):

- Small categories ≅ comonoids in (Poly, y, ◁)
- Retrofunctors ≅ comonoid morphisms

This identifies Cof with comonoid morphisms in the monoidal category of
polynomial functors.

## Analysis: Can Cof Embed into Copresheaves?

### The Challenge

For Cat, the embedding Φ sends a category C to a copresheaf where:

- The object function Obj(C) is just a set
- The morphism function Mor(C) carries domain/codomain structure
- Identity and composition are additional structure

For Cof, we would need an embedding Ψ where retrofunctor structure is
naturally captured. The challenge is the **dependent lifting** in retrofunctors:

- The lift φ₁(a, u) depends on both an object a and a morphism u with
  source φ₀(a)
- This is not a simple function on morphisms but a **dependent** operation

### Approach 1: Dual (Presheaf) Direction

Consider presheaves on J^op instead of copresheaves on J:

- A presheaf F : J^op → Type has:
  - F(Obj) = a type
  - F(Mor) = a type
  - F(dom) : F(Obj) → F(Mor) (reversed direction!)
  - F(cod) : F(Obj) → F(Mor) (reversed direction!)

This reversal might capture the "backward" morphism direction of retrofunctors.

**Problem**: The domain/codomain maps in presheaves go from objects to
morphisms, not morphisms to objects. This doesn't directly model the
retrofunctor lifting structure.

### Approach 2: Extended Index Category

Define a category RetroJudgments with objects:

- Obj, Mor, Id, Comp (as in CategoryJudgments)
- Lift : Type of lifting judgments

With morphisms encoding:

- The usual category structure
- Lifting data: for each morphism u with source in the image, a lifted
  morphism in the source category

**Problem**: The lifting structure is inherently **dependent** on both an
object (in A) and a morphism (in B starting from the image of that object).
This dependency doesn't fit the form of a simple (co)presheaf.

### Approach 3: Two-Stage Construction

Retrofunctors factor as:

1. A bijective-on-objects functor (going backward: B → A)
2. A discrete opfibration (going forward: A → B)

Since discrete opfibrations over B ≅ copresheaves B → Set (via category of
elements), one might:

1. Encode the discrete opfibration part as a copresheaf
2. Encode the bijective-on-objects constraint separately

**Limitation**: This factorization is a structural theorem about retrofunctors,
not a direct embedding of Cof into a copresheaf category.

### Approach 4: Poly(1,1) as a Structured Index

Since Cof ≅ comonoid morphisms in Poly(1,1), consider:

- Poly(1,1) as a monoidal category
- Categories as comonoids
- An "embedding" into copresheaves on some category derived from Poly(1,1)

**Problem**: Poly(1,1) is a **large** category, losing the finiteness property
that makes CategoryJudgments attractive.

## Comparison Table

| Aspect | Cat embedding | Potential Cof embedding |
|--------|---------------|------------------------|
| Morphism direction | Covariant | Mixed (objects forward, morphisms backward) |
| Dependency structure | Independent types | Dependent lifting |
| Known characterization | Copresheaves on finite J | Comonoids in Poly |
| Adjunction type | Reflective | Unknown |
| Index category size | Finite (4 objects) | Likely infinite or dependent |

## Theoretical Obstacles

### The Dependent Type Problem

A retrofunctor's lift operation has signature:

```text
φ₁ : Π (a : Obj(A)), (u : φ₀(a) →_B b) → (Σ (a' : Obj(A)), a →_A a')
```

This is a **dependent function** where the domain depends on φ₀(a). Copresheaves
model **non-dependent** functors J → Type.

To capture this, one would need:

- Dependent copresheaves (functors into the category of families)
- Or a more sophisticated index encoding the dependency

### The Lack of "Walking Retrofunctor"

For functors, CategoryJudgments serves as a "walking category specification."
A similar "walking retrofunctor specification" would need to encode:

- Two quivers (source and target)
- The object map between them
- The dependent lifting structure
- Preservation laws

## Possible Directions

### 1. Internal Categories in Type

View retrofunctors as internal categories/functors in a category of types with
dependency. This shifts from copresheaves to internal category theory.

### 2. Twisted Arrow / Two-Sided Grothendieck

The two-sided Grothendieck construction relates functors C × D^op → Set to
spans of categories. A similar construction might relate mixed-variance
structures to retrofunctors.

### 3. Double Categories

Retrofunctors arise naturally in double category theory as "vertical morphisms"
dual to functors. The double category of lenses (Clarke, 2022) provides a
natural home for retrofunctors alongside functors.

### 4. Accept Non-Copresheaf Characterization

The Poly(1,1) comonoid characterization may be the "right" answer for
retrofunctors, even though it doesn't take the form of a copresheaf embedding.

## Applying the CategoryJudgments Methodology

### The Original Methodology

The CategoryJudgments construction followed a specific methodology:

1. **Components**: Identify the components of a category (Obj, Mor)
2. **Preservation**: Identify what functors preserve (identity, composition)
3. **Relations**: Track preserved structures as **relations** rather than functions
4. **Forcing**: The left adjoint L forces relations to be functional via completion
   (free category) and quotienting (by category laws)

### Application to Retrofunctors

If Cof is essentially algebraic (which it is), the same methodology applies.
The question becomes: what do retrofunctors "preserve" or have as structure?

A retrofunctor φ : A ↛ B has:

- **ObjMap**: φ₀(a) for each a ∈ A (forward on objects)
- **Lift**: φ₁(a, u) for (a, u) with dom(u) = φ₀(a) (backward lifting)
- **LiftId**: φ₁(a, id_{φ₀(a)}) = id_a
- **LiftComp**: φ₁(a, v ∘ u) = φ₁(a', v) ∘ φ₁(a, u)

### Proposed RetrofunctorJudgments

Tracking these as relations yields a category with approximately 11 objects:

| Object | Description |
|--------|-------------|
| Obj_S | Objects of source category |
| Obj_T | Objects of target category |
| Mor_S | Morphisms of source category |
| Mor_T | Morphisms of target category |
| Id_S | Identity witnesses in source |
| Id_T | Identity witnesses in target |
| Comp_S | Composable pairs in source |
| Comp_T | Composable pairs in target |
| ObjMap | Object correspondence witnesses |
| LiftablePair | Pairs (a, u) with dom(u) = φ₀(a) |
| Lift | Lifted morphism witnesses |

Morphisms would encode the structure maps and coherence conditions.

### What This Embeds

This construction would embed **retrofunctor diagrams** (source category,
target category, retrofunctor between them) into copresheaves, rather than
embedding Cof directly.

This parallels how one could define "FunctorJudgments" to embed functor diagrams.

### Cof as Essentially Algebraic

The lifting operation φ₁(a, u) has domain specified by an equation:
dom_B(u) = φ₀(a). This is exactly what essentially algebraic theories handle.

Essentially algebraic presentation of a retrofunctor:

- Sorts: A_obj, A_mor, B_obj, B_mor
- Total operations: dom_A, cod_A, comp_A, id_A, dom_B, cod_B, comp_B, id_B, φ₀
- Partial operation: φ₁ with domain {(a, u) | dom_B(u) = φ₀(a)}
- Equations: identity preservation, composition preservation

So Cof IS essentially algebraic, confirming the methodology should apply.

## Conclusion

A direct analogue of the L ⊣ Φ adjunction for Cof appears unlikely due to:

1. The inherently **dependent** nature of retrofunctor lifting
2. The **mixed variance** (covariant on objects, contravariant on morphisms)
3. The lack of a natural finite "walking retrofunctor" category

However, the CategoryJudgments methodology CAN be applied:

- Cof is essentially algebraic
- A ~11-object "RetrofunctorJudgments" category can encode the structure
- This embeds retrofunctor diagrams rather than Cof directly
- The Poly(1,1) comonoid characterization provides a complementary perspective

Further investigation might explore:

- Dependent copresheaves or fibered categories
- Double categorical frameworks
- Two-sided Grothendieck constructions
- Whether embedding retrofunctor diagrams leads to an embedding of Cof
- Simplification of the 11-object construction

## References

- Ahman, D., & Uustalu, T. (2016). Directed containers as categories. EPTCS 207.
- Clarke, B. (2020). Internal lenses as functors and cofunctors. EPTCS 323.
- Clarke, B. (2022). The Double Category of Lenses. PhD thesis, Macquarie.
- Spivak, D. I., & Niu, N. (2021). Polynomial Functors: A General Theory of
  Interaction.
- nLab: retrofunctor, discrete opfibration
- Topos Institute Blog: Retrotransformations (2023)
