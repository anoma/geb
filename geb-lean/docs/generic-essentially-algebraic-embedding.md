# Generic Embedding of Essentially Algebraic Theories

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [The Question](#the-question)
- [Proposed Ingredients](#proposed-ingredients)
- [Analysis](#analysis)
  - [The Structure of J_T](#the-structure-of-j_t)
  - [The Polynomial Endofunctor P_T](#the-polynomial-endofunctor-p_t)
  - [Decomposition: L_T = Quotient ∘ Completion](#decomposition-l_t--quotient-%E2%88%98-completion)
  - [Relationship to Gabriel-Ulmer Duality](#relationship-to-gabriel-ulmer-duality)
  - [Relationship to Finite Limit Sketches](#relationship-to-finite-limit-sketches)
  - [Computability Property](#computability-property)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This document investigates whether the CategoryJudgments construction can be
generalized to embed ANY essentially algebraic theory into a copresheaf category.

## The Question

The L ⊣ Φ adjunction for Cat relies on the fact that Cat is the category of
models of an essentially algebraic theory. The construction used:

1. A finite acyclic category J (CategoryJudgments, 4 objects)
2. An embedding Φ : Cat → [J, Type]
3. A left adjoint L : [J, Type] → Cat via completion + quotienting

**Question**: Can we build a generic construction that works for ANY essentially
algebraic theory T, embedding Mod(T) into [J_T, Type] for some finite acyclic
category J_T derived from T?

## Proposed Ingredients

1. **Judgment Category J_T**: Sorts whose dependencies form a finite acyclic
   category (the copresheaves on J_T will be the target of the embedding)

2. **Polynomial Endofunctor P_T**: An endofunctor on [J_T, Type] whose algebras
   correspond to models of T

3. **Completion Functor**: The free-algebra construction for P_T

4. **Quotient Functor**: Quotienting by the equations of T

## Analysis

### The Structure of J_T

For an essentially algebraic theory T, the judgment category J_T is
constructed as follows:

**Objects of J_T:**

1. One object for each sort of T
2. Additional "witness" objects for the domains of partial operations

**Morphisms of J_T:**

1. For each operation f : S₁ × ... × Sₙ → S₀, morphisms encoding argument
   dependencies
2. For partial operations, morphisms from witness objects to the sorts involved
   in the domain constraint

**Example - Categories (T = Cat):**

- Sorts: Obj, Mor
- Partial operation: composition (defined when cod(f) = dom(g))
- J_Cat has 4 objects: Obj, Mor, Id (identity witness), Comp (composition witness)
- Morphisms: dom, cod : Mor → Obj, plus witness projections

**Example - Monoids (T = Mon):**

- Sorts: M (one sort)
- Total operations: unit : 1 → M, mult : M × M → M
- J_Mon has just 1 object: M
- No partial operations means no witness objects needed

This reveals a pattern: purely algebraic theories (no partial operations) have
trivial J_T consisting only of sorts. The interesting structure arises from
partial operations, which require witness types to encode their domains.

### The Polynomial Endofunctor P_T

For a copresheaf X : J_T → Type, the polynomial endofunctor P_T acts by:

```text
P_T(X)(j) = X(j) + Σ_{operations f targeting j} (domain data for f from X)
```

For each n-ary operation f : S₁ × ... × Sₙ → S₀:

- P_T contributes to the S₀ component
- The contribution is the product X(S₁) × ... × X(Sₙ)
- For partial operations, restricted to the appropriate domain

P_T-algebras (before equations) are "pre-models" of T with all operations but
without the equations enforced.

### Decomposition: L_T = Quotient ∘ Completion

The left adjoint L_T decomposes as:

1. **Completion**: Construct the free P_T-algebra on the copresheaf
   - For Cat: free category on the underlying quiver
   - Adds all formal compositions and identities

2. **Quotient**: Quotient by the equations of T
   - For Cat: associativity and unit laws
   - Forces the algebraic structure to satisfy T's axioms

This two-stage construction provides a computational recipe for building models
from arbitrary copresheaves.

### Relationship to Gabriel-Ulmer Duality

Gabriel-Ulmer duality states that for a locally finitely presentable category C:

```text
C ≃ Lex(fp(C)^op, Set)
```

where fp(C) is the category of finitely presentable objects and Lex denotes
finite-limit-preserving functors.

Our construction differs in that:

- Gabriel-Ulmer uses ALL finitely presentable models
- We use only the "judgment types" forming J_T
- J_T is a finite generating set, not the full fp category

The trade-off:

- Gabriel-Ulmer: universal but abstract
- J_T construction: computational but requires explicit judgment category

### Relationship to Finite Limit Sketches

An essentially algebraic theory T corresponds to a finite limit sketch S_T.
The relationship:

- Models of T = models of S_T = limit-preserving functors S_T → Set
- J_T is related to the underlying graph of S_T
- The polynomial structure encodes the cones that must be limits

### Computability Property

For finitely-presented essentially algebraic theories, J_T is finite. This means:

- [J_T, Type] is a functor category with finite domain
- The embedding Φ_T and left adjoint L_T are constructively definable
- The construction gives a computational handle on models of T

## References

- Gabriel, P., & Ulmer, F. (1971). Lokal präsentierbare Kategorien.
- Adámek, J., & Rosický, J. (1994). Locally presentable and accessible categories.
- Johnstone, P. T. (2002). Sketches of an Elephant, Vol. II.
