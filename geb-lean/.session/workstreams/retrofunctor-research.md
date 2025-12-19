# Retrofunctors and Cof/Cat# Representation

## Status: Active Research - Methodology Question Under Investigation

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

## New Question: Applying the CategoryJudgments Methodology

### The Methodology Revisited

The CategoryJudgments construction arose from a specific methodology:

1. Identify components of a category: Obj (objects), Mor (morphisms)
2. Identify what FUNCTORS preserve: identity, composition
3. Track preserved structures as RELATIONS (not functions)
4. The left adjoint L forces relations to be functional via:
   - Completion (free category on the underlying quiver)
   - Quotienting (by category laws, ensuring identity/composition behave correctly)

### Question: Can This Apply to Retrofunctors?

If Cof is essentially algebraic (which it likely is), the same methodology
might apply by asking: what do RETROFUNCTORS preserve/have as structure?

### What Retrofunctors "Preserve"

A retrofunctor φ : A ↛ B has:

- ObjMap: φ₀(a) for each a ∈ A (forward on objects, like functors)
- Lift: φ₁(a, u) for each a ∈ A and u : φ₀(a) → b in B (lifting morphisms)
- LiftId: φ₁(a, id_{φ₀(a)}) = id_a (lifted identities are identities)
- LiftComp: φ₁(a, v ∘ u) = φ₁(a', v) ∘ φ₁(a, u) (lifted compositions compose)

### Proposed "RetrofunctorJudgments" Construction

Following the methodology, track these as RELATIONS:

Objects (approximately 11):

1. Obj_S - objects of source category
2. Obj_T - objects of target category
3. Mor_S - morphisms of source category
4. Mor_T - morphisms of target category
5. Id_S - identity witnesses in source
6. Id_T - identity witnesses in target
7. Comp_S - composable pairs in source
8. Comp_T - composable pairs in target
9. ObjMap - witnesses for object correspondence
10. LiftablePair - pairs (a, u) where dom(u) = φ₀(a)
11. Lift - witnesses for lifted morphisms

Morphisms would encode:

- dom_S, cod_S : Mor_S → Obj_S (source category structure)
- dom_T, cod_T : Mor_T → Obj_T (target category structure)
- Standard category structure maps for both
- projections from LiftablePair to Obj_S and Mor_T
- The lifting map from LiftablePair to Mor_S
- Coherence maps for LiftId and LiftComp

### Analysis

This construction would embed the category of RETROFUNCTOR DIAGRAMS
(source category, target category, retrofunctor between them) into copresheaves,
rather than embedding Cof directly.

This is analogous to how one could define "FunctorJudgments" to embed functor
diagrams rather than single categories.

### The Essentially Algebraic Angle

Essentially algebraic theories allow operations with domains specified by equations.
The retrofunctor lift φ₁(a, u) has domain: pairs (a, u) where dom(u) = φ₀(a).

This IS expressible in essentially algebraic form:

- Sort A_obj, A_mor, B_obj, B_mor (basic types)
- Operations dom_A, cod_A, dom_B, cod_B, comp_A, comp_B, id_A, id_B
- Operation φ₀ : A_obj → B_obj
- Partial operation φ₁ with domain {(a, u) | dom_B(u) = φ₀(a)}
- Equations for preservation laws

So Cof IS essentially algebraic, and the methodology should apply in principle.

### Remaining Questions

1. Can the 11-object "RetrofunctorJudgments" be reduced to something smaller?

2. Since retrofunctor diagrams involve TWO categories, is there a way to
   embed Cof (single categories as objects) rather than retrofunctor diagrams?

3. The polynomial characterization Cof ≅ Comonoid(Poly) suggests another angle:
   can Poly(1,1) itself be given a finite essentially algebraic presentation?

4. What is the relationship between the 11-object approach and the Poly(1,1)
   comonoid approach?

## Future Work

1. Investigate whether a "RetrofunctorJudgments" index category can be defined
2. Explore the two-sided Grothendieck construction for mixed variance
3. Consider whether the Poly(1,1) characterization admits a finite presentation
4. Study retrotransformations as the 2-cells if an embedding exists
5. Determine if the 11-object construction can be simplified
6. Explore whether embedding retrofunctor diagrams leads to an embedding of Cof
