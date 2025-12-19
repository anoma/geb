# Retrofunctors and Cof/Cat# Representation

## Status: Research Complete - Potential Directions Identified

## Context

This workstream investigates whether the category Cof (or Cat#) of small
categories with retrofunctors as morphisms can be represented via a reflective
or coreflective adjunction with a copresheaf (or presheaf) category, similar to
the L |- Phi adjunction for Cat.

## Key Concepts

### Retrofunctors (Cofunctors)

A retrofunctor φ : A ↛ B consists of:

- An object map φ₀ : Obj(A) → Obj(B) (forward direction)
- A morphism lift φ₁ : (a, u : φ₀(a) → b) ↦ (f : a → a') where φ₀(a') = b
  (backward direction relative to objects)

Properties:

- Preserve identities: φ₁(a, id_{φ₀(a)}) = id_a
- Preserve composition: φ₁(a, v ∘ u) = φ₁(a', v) ∘ φ₁(a, u) where a' = cod(φ₁(a,u))

### The Category Cof

- Objects: Small categories
- Morphisms: Retrofunctors
- Composition: (γ ∘ φ)₁(a, u) = φ₁(a, γ₁(φ₀(a), u))

### Key Results from Literature

1. **Polynomial Connection**: Cof ≅ comonoid morphisms in Poly(1,1)
   - Small categories are comonoids in (Poly, y, ◁)
   - Retrofunctors are the natural morphisms between comonoids
   - Reference: Ahman-Uustalu (2016), Spivak-Niu (2021)

2. **Factorization**: Every retrofunctor factors as
   (bijective-on-objects functor)^op followed by a discrete opfibration
   - Orthogonal factorization system (Bij^op, DOpf) on Cof

3. **Relationship to Lenses**: Delta lenses have underlying retrofunctors
   - Reference: Clarke (2020), "Internal lenses as functors and cofunctors"

## Research Directions

### Direction 1: Dual CategoryJudgments (Presheaves)

Consider presheaves on CategoryJudgments^op instead of copresheaves:

- Objects map to types, morphisms map to functions
- The domain/codomain maps go "the other way"
- This might naturally capture the "backward" nature of retrofunctors

**Hypothesis**: There may be an adjunction R |- Ψ where:

- Ψ : Cof → [J^op, Type] embeds Cof into presheaves
- R : [J^op, Type] → Cof reflects presheaves to retrofunctor categories

**Status**: Needs investigation - the composition lifting in retrofunctors
is more complex than simple functorial structure

### Direction 2: Extended Index Category

The lifting structure of retrofunctors might require additional judgment types:

- MorLift : Type of morphism lifting judgments
- With constraints encoding the lifting laws

**Observation**: The index category would need to encode:

- For each morphism u : φ₀(a) → b in target, a lift φ₁(a, u) in source
- This is a dependent structure not directly captured by a simple copresheaf

### Direction 3: Fibration/Opfibration Connection

Discrete opfibrations over C correspond to copresheaves C → Set via the
category of elements (Grothendieck construction).

**Potential approach**:

- Use the fact that retrofunctors factor through discrete opfibrations
- The DOpf part is a copresheaf; the Bij^op part is a functor constraint
- This suggests a two-stage construction rather than a single adjunction

### Direction 4: Poly(1,1) as Index

Since Cof ≅ comonoids in Poly(1,1), consider:

- The monoidal category Poly(1,1) itself as an "index"
- Categories as certain copresheaves on this structure
- Retrofunctors as natural transformations respecting comonoid structure

**Challenge**: Poly(1,1) is large and non-finite, losing the finiteness
property of CategoryJudgments

## Preliminary Assessment

A direct analogue of the L |- Phi adjunction for Cof appears unlikely because:

1. **Asymmetry**: Retrofunctors have fundamentally asymmetric structure
   (objects forward, morphisms backward) that doesn't fit the symmetric
   form of a copresheaf functor

2. **Dependent lifting**: The morphism lift depends on both source object
   and target morphism, requiring a more complex index structure

3. **Polynomial perspective**: The Poly(1,1) characterization suggests Cof
   is better understood through comonoid theory than copresheaf theory

However, there may be a *modified* construction using:

- A different (larger) index category encoding lifting structure
- A combination of presheaves and copresheaves
- A two-sided Grothendieck construction approach

## Code References

- `GebLean/CategoryJudgments.lean:44-72` - CategoryJudgments.Obj and SemiHom
- `GebLean/CatJudgmentAdjunction.lean:68-92` - toJudgmentFunctorData

## External References

- [nLab: retrofunctor](https://ncatlab.org/nlab/show/retrofunctor)
- [Topos Institute: Retrotransformations](https://topos.institute/blog/2023-10-20-retrotransformations/)
- [1Lab: Polynomial functors and lenses](https://1lab.dev/Cat.Instances.Poly.html)
- Clarke, "The Double Category of Lenses" (PhD thesis, 2022)
- Spivak, "A summary of categorical structures in Poly" (arXiv:2202.00534)

## Future Work

1. Investigate whether a "RetrofunctorJudgments" index category can be defined
2. Explore the two-sided Grothendieck construction for mixed variance
3. Consider whether the Poly(1,1) characterization admits a finite presentation
4. Study retrotransformations as the 2-cells if an embedding exists
