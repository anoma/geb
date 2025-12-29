# Novelty of Finite-Index Reflective Inclusion of Cat

## Status: Research Complete

## Context

This workstream investigates whether the reflective adjunction L |- Phi between
Cat and copresheaves on CategoryJudgments (a finite 4-object category) is a
novel construction or equivalent to something known.

## Related Files

- `GebLean/CategoryJudgments.lean` - The finite index category (4 objects: Obj,
  Mor, Id, Comp)
- `GebLean/CatJudgmentAdjunction.lean` - The adjunction construction
- `docs/categories-as-copresheaves.md` - Mathematical background

## Research Findings

### Comparison to Known Constructions

1. **Nerve-Realization Adjunction** (Δ, simplicial sets)
   - Index category: Simplex category Δ (infinite)
   - Right adjoint: Nerve N : Cat -> [Δ^op, Set] (presheaves)
   - Left adjoint: Realization τ₁ : [Δ^op, Set] -> Cat
   - Not reflective (nerve is not fully faithful)
   - Reference: Kan (1958), "Functors involving c.s.s."

2. **Essentially Algebraic Theory Presentation**
   - Cat is the category of models of a finite limit sketch
   - Gabriel-Ulmer duality relates theories to locally finitely presentable
     categories
   - This is the theoretical foundation but typically not presented as an
     explicit adjunction with a finite index category
   - Reference: Adamek-Rosicky, "Locally presentable and accessible categories"

3. **Walking Structures**
   - "Walking morphism" = interval category Δ¹
   - "Walking composable pair" = (2,1)-horn Λ₁²
   - These are finite but encode single operations, not full category structure
   - Reference: nLab "walking structure"

4. **Polynomial Comonoids**
   - Small categories ≅ comonoids in (Poly, ◁)
   - This is an isomorphism, not an adjunction
   - Retrofunctors are the corresponding morphisms
   - Reference: Spivak-Niu, "Polynomial Functors" (2021)

### Assessment of Novelty

The construction appears to be novel in the following sense:

- **Finite index category**: Most known embeddings of Cat use infinite index
  categories (Δ for nerve, 2-truncated Θ for weak 2-categories, etc.)

- **Explicit reflectivity**: While the essentially algebraic presentation of
  Cat is well-known, the explicit construction of a reflective adjunction
  L |- Phi with a 4-object index category does not appear in the literature

- **Copresheaf (covariant) direction**: The nerve uses presheaves
  (contravariant); this uses copresheaves (covariant)

### What Makes It Work

The CategoryJudgments category encodes exactly the minimal data needed:

- Objects and morphisms (the underlying quiver)
- Identity witnesses (which morphisms are identities)
- Composition witnesses (which triples compose)

This is similar to a "walking category specification" - the free category
containing exactly the structure needed to present any category.

### Related But Distinct

The construction is related to but distinct from:

1. **Grothendieck construction**: Gives equivalence between fibrations over B
   and pseudofunctors B^op -> Cat, but doesn't embed Cat itself

2. **Categories of elements**: Embeds copresheaves over C into Cat/C, not
   Cat into a copresheaf category

3. **Lawvere theories**: Encode algebraic theories via product-preserving
   functors from a finite-product category; Cat requires finite limits (not
   just products)

## Open Questions

1. Is there a published result that's equivalent under some transformation?

2. Can the construction be generalized to n-categories using a finite
   "n-CategoryJudgments" index category?

3. What is the relationship to Street's orientation for computads?

## References

- [nLab: nerve](https://ncatlab.org/nlab/show/nerve)
- [nLab: essentially algebraic theory](https://ncatlab.org/nlab/show/essentially+algebraic+theory)
- [nLab: walking structure](https://ncatlab.org/nlab/show/walking+structure)
- [nLab: presentation of a category by generators and relations](https://ncatlab.org/nlab/show/presentation+of+a+category+by+generators+and+relations)
- Adamek-Rosicky, "Locally presentable and accessible categories" (1994)
- Spivak-Niu, "Polynomial Functors: A General Theory of Interaction" (2021)
