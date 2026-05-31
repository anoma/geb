# Novelty Analysis: Reflective Inclusion of Cat into Finite Copresheaves

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [The Construction](#the-construction)
- [Comparison to Known Constructions](#comparison-to-known-constructions)
  - [Nerve-Realization Adjunction](#nerve-realization-adjunction)
  - [Essentially Algebraic Theories](#essentially-algebraic-theories)
  - [Walking Structures](#walking-structures)
  - [Polynomial Functors](#polynomial-functors)
- [Novel Aspects](#novel-aspects)
  - [1. Finiteness of the Index Category](#1-finiteness-of-the-index-category)
  - [2. Explicit Reflectivity](#2-explicit-reflectivity)
  - [3. Copresheaf (Covariant) Direction](#3-copresheaf-covariant-direction)
  - [4. Direct Type-Theoretic Presentation](#4-direct-type-theoretic-presentation)
- [Mathematical Characterization](#mathematical-characterization)
  - [CategoryJudgments as a Sketch](#categoryjudgments-as-a-sketch)
  - [Relationship to 2-Monads](#relationship-to-2-monads)
- [Conclusion](#conclusion)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This document analyzes the mathematical novelty of the reflective adjunction
L ⊣ Φ between Cat and the copresheaf category [J, Type], where J is the
four-object category CategoryJudgments.

## The Construction

The adjunction consists of:

- **Embedding Φ : Cat → [J, Type]**: Sends a category C to a copresheaf
  encoding its objects, morphisms, identity witnesses, and composition
  witnesses
- **Reflection L : [J, Type] → Cat**: Constructs the free category on the
  underlying quiver, then quotients by identity and composition relations
- **Reflectivity**: The counit ε : L(Φ(C)) → C is an isomorphism for all
  categories C

The distinctive feature is that the index category J is **finite** (4 objects,
10 non-identity morphisms).

## Comparison to Known Constructions

### Nerve-Realization Adjunction

The nerve-realization adjunction τ₁ ⊣ N relates Cat to simplicial sets:

|Property|Nerve-Realization|Our Construction|
|---|---|---|
|Index category|Δ (infinite)|J (4 objects)|
|Direction|Presheaves (contravariant)|Copresheaves (covariant)|
|Reflective?|No (nerve not fully faithful)|Y|
|Left adjoint|τ₁ (1-truncation)|L (quotient of free cat)|

The nerve is not fully faithful because it fails to detect "extra"
degeneracies in simplicial sets. Our Φ is fully faithful because the counit
is an isomorphism.

### Essentially Algebraic Theories

Cat is well-known to be the category of models of an essentially algebraic
theory (equivalently, a finite limit sketch). Results include:

- Gabriel-Ulmer duality relates finitary essentially algebraic theories to
  locally finitely presentable categories
- Cat is locally finitely presentable

However, these results typically present Cat **theoretically** rather than
exhibiting an explicit finite index category and reflective adjunction. The
CategoryJudgments construction provides a **concrete computational**
presentation.

### Walking Structures

Walking structures (nLab terminology) provide "archetypal models" of
categorical data:

- Walking morphism: Δ¹ (2 objects, 1 non-identity morphism)
- Walking composable pair: Λ₁² (3 objects)
- Walking commutative triangle: Δ² (3 objects)

These are finite categories encoding **individual** categorical operations.
CategoryJudgments can be viewed as a "walking category specification"
encoding the **complete** data needed to present an arbitrary category.

### Polynomial Functors

The Poly(1,1) framework characterizes:

- Small categories ≅ comonoids in (Poly, ◁)
- Functors ≅ comonoid homomorphisms

This is an **isomorphism** rather than an adjunction, and doesn't directly
give an embedding into a (co)presheaf category.

## Novel Aspects

Based on the literature survey, the following aspects appear to be novel:

### 1. Finiteness of the Index Category

Known reflective embeddings of Cat use infinite index categories:

- Simplicial sets use Δ (infinitely many objects [n])
- Θ-sets and cellular sets use infinite skeletal categories
- Globular sets use the infinite globe category

CategoryJudgments achieves reflection with only **4 objects**.

### 2. Explicit Reflectivity

While the essentially algebraic nature of Cat implies it can be presented
via limits and colimits, the explicit construction of L and proof that
ε is an isomorphism is concrete and computational.

### 3. Copresheaf (Covariant) Direction

Most categorical embeddings into diagram categories use **presheaves**
(contravariant functors). The copresheaf direction is natural here because
the maps (dom, cod, etc.) point from more rich structure (morphisms) to
less (objects).

### 4. Direct Type-Theoretic Presentation

The construction directly reflects how categories are presented in type
theory and proof assistants:

- A type of objects
- A type of morphisms with source/target functions
- Identity and composition operations
- Equations ensuring category laws

This makes it suitable for implementation in systems like Lean.

## Mathematical Characterization

### CategoryJudgments as a Sketch

The category J = CategoryJudgments can be viewed as presenting a
**projective sketch** whose models in Set (equivalently, copresheaves
J → Set) are precisely the presentations of categories.

The reflection L computes the **syntactic category** from a presentation,
and Φ extracts the **canonical presentation** from a category.

### Relationship to 2-Monads

Categories can be characterized as algebras for a 2-monad on the 2-category
of graphs. The adjunction L ⊣ Φ provides a 1-categorical shadow of this,
with J encoding the "operations" of the 2-monad at the level of types.

## Conclusion

The reflective adjunction L ⊣ Φ using the finite category CategoryJudgments
appears to be a novel construction. While the underlying mathematical
principles (essentially algebraic theories, walking structures, category
presentations) are well-established, the specific combination of:

1. A finite 4-object index category
2. Copresheaves (covariant functors to Type)
3. Explicit reflective adjunction with computational content

has not been identified in the existing literature.

## References

- Adámek, J., & Rosický, J. (1994). Locally presentable and accessible
  categories. Cambridge University Press.
- Gabriel, P., & Ulmer, F. (1971). Lokal präsentierbare Kategorien.
  Springer LNM 221.
- Kan, D. M. (1958). Functors involving c.s.s cplxs. Trans. AMS, 87(2),
  330-346.
- Johnstone, P. T. (2002). Sketches of an Elephant, Vol. II. Oxford.
- nLab: walking structure, essentially algebraic theory, nerve
