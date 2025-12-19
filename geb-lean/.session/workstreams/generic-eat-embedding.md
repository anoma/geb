# Generic Essentially Algebraic Theory Embedding

## Status: Active Research

## The Question

Can the CategoryJudgments construction be generalized to embed ANY essentially
algebraic theory T into a copresheaf category [J_T, Type]?

## Proposed Architecture

1. **Judgment Category J_T**: Derived from T's signature
   - Objects for each sort
   - Objects for operation "witnesses"
   - Morphisms encoding dependencies

2. **Polynomial Endofunctor P_T**: On [J_T, Type]
   - Algebras = models of T (before equations)

3. **Two-Stage Left Adjoint**:
   - Completion: Free P_T-algebra (analogous to free category on quiver)
   - Quotient: By T's equations (analogous to category laws)

## Findings

### The Structure of J_T

J_T for an essentially algebraic theory T consists of:

- **Objects**: One per sort, plus "witness" objects for partial operation domains
- **Morphisms**: Encoding argument dependencies and domain constraints

Pattern: Purely algebraic theories (monoids, groups, rings) have trivial J_T
(just the sorts). Partial operations (like composition in Cat) create the
non-trivial structure requiring witness objects.

### Polynomial Endofunctor P_T

P_T on [J_T, Type] acts by:

```text
P_T(X)(j) = X(j) + Σ_{operations f targeting j} (domain data)
```

P_T-algebras are "pre-models" before equations.

### Decomposition Confirmed

L_T = Quotient ∘ Completion where:

- Completion: free P_T-algebra construction
- Quotient: by T's equations

### Relationship to Gabriel-Ulmer

Gabriel-Ulmer uses fp(Mod(T)) (all finitely presentable models); we use J_T
(finite generating set). Trade-off: computability vs universality.

### Relationship to Finite Limit Sketches

J_T is related to the underlying graph of the finite limit sketch S_T
corresponding to T. The polynomial structure encodes the limit cones.

## Code References

- `GebLean/CategoryJudgments.lean` - Example for Cat
- `GebLean/CatJudgmentAdjunction.lean` - The adjunction construction

## External References

- Gabriel-Ulmer duality
- Finite limit sketches
- Lawvere algebraic theories
