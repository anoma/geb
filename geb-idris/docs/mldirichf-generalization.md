# MLDirichF Generalization Plan

## Overview

This document outlines the plan to generalize `MLDirichF` from the
`GenPolyFunc` module to support:

1. Type checking on generic S-expression terms for portability
to non-dependently-typed languages
2. Extension from single walking arrow to arbitrary finite two-level DAGs

## Current State

`MLDirichF` currently:

- Represents parametric right adjoint (PRA) functors on Dirichlet
  functor categories
- Works on copresheaves over the walking arrow category (one base type,
  one dependent type)
- Interprets only into Idris's dependent type system

## Planned Extensions

### 1. Generic Term Representation with Type Checking

We will develop a dual interpretation system:

**Generic Terms**: Use `SLSFmu`/`SLSFMnonSl` from `BinTree.idr` as the
generic term type

- S-expressions represented as atom + snoc-list structures
- Portable representation that doesn't require dependent types

**Type Checking**: Generate two parallel artifacts:

- A dependent type in Idris (for formal validation)
- A type-checker function operating on generic S-expression terms
- Establish formal correspondence: terms of dependent type ↔ generic
  terms passing checker

**Sliced Type Checking**: Support parameterized checking

- Not just "check against type X" but "check against type X with parameter Y"
- Example: checking against `Vect` with length parameter `n`
- Potential for fibration-based error reporting with different fiber types
  for different failure modes

### 2. Finite Two-Level DAG Categories

Generalize from walking arrow to arbitrary finite two-level DAGs:

**DAG Representation** (initial simple version):

```idris
TwoLevelDAG : Type
TwoLevelDAG = List Nat
```

- Length of list = number of base types
- Each element = number of dependent types on that base type
- Example: `[2, 0, 3]` represents 3 base types with 2, 0, and 3 dependent
  types respectively

**Index Structure**:

- Base types indexed by position in list
- Dependent types indexed by `(baseIndex, depIndex)` pairs
- Support morphisms between different DAG shapes (functors between copresheaf
  categories)

**Future Extension**: Consider richer DAGs with multiple dependencies
(dependent types depending on multiple base types)

### 3. S-Expression Encoding Conventions

Initial encoding patterns:

- **Product types**: `(atom: "prod", elements: [term1, term2, ...])`
- **Coproduct types**: `(atom: "coprod", elements: [index, term])`
- Additional conventions to be developed for:
  - Function types
  - Dependent types
  - Type constructors
  - Variable references

## Implementation Plan

1. **Define DAG representation**
   - Create `TwoLevelDAG` type and basic operations
   - Define morphisms between DAGs

2. **Generalize MLDirichF**
   - Extend current implementation to work over arbitrary two-level DAGs
   - Maintain compatibility with existing single-arrow case

3. **Build type checking machinery**
   - Implement S-expression type checker with extraction
   - Support sliced/parameterized type checking
   - Generate both checker and dependent type from same specification

4. **Establish correspondences**
   - Prove equivalence between dependent type inhabitants and checked
     S-expressions
   - Validate extraction produces correct dependent values

## Goals

This generalization must:

- Enable porting type systems to languages without dependent types
- Extend expressiveness to handle multiple base and dependent types
- Maintain formal connection to dependently-typed foundations

## Completed Work

### Core Infrastructure (in `FinDirich.idr`)

1. **Index Category**: `Fin2Forest` as `List Nat` with objects (`F2FObj`) and
   morphisms (`F2FMor`)
2. **Forest Functors**: `F2FFunctor` with functor laws as proof obligations
3. **Copresheaf Categories**: Both general (`F2FCopr`) and finite (`F2FFinCopr`)
   versions with explicit morphism mappings
4. **Category of Elements**: Complete structure for element categories with
   simplified morphism representation
5. **Natural Transformations**: Full categorical structure with identity,
   composition, and category laws (requiring `FunExt` and `uip` for some proofs)

### PRA Functor Implementation (in `FinCatPRA.idr`)

1. **General PRA Functors**: `F2FPRA` with object and morphism mappings
   following the dependent sum formula
2. **Finite PRA Functors**: `F2FFinPRA` for finite copresheaf categories
3. **Complete Functor Specifications**: Bundled functors with laws proven
4. **Conversion Functions**: Full suite of conversions between finite and
   general versions preserving all structure

### S-Expression Foundation (in `FinCatPRA.idr`)

1. **Atom type** (`FinSetAtom`): Products, coproducts, and natural numbers
2. **Type definition**: `FinSetSExpr = SLSFmu FinSetAtom`
3. **Validity predicates**: Mutually recursive validators with specific
   structural constraints
4. **Decidable type checker**: `finSetSExprValidDec` provides decidable
   validation

## Current Work: Finite Versions and S-Expression Integration

### Step 1: Extend S-Expression Representation

Now that we have the basic S-expression infrastructure, we need to:

1. **Define S-expression copresheaves**: Create types that represent
   copresheaves using S-expressions instead of `Nat`/`Fin`

2. **Implement S-expression natural transformations**: Represent morphisms
   between copresheaves as S-expressions

3. **Create conversion functions**: Bridge between `Nat`/`Fin` representations
   and S-expression representations

4. **Implement finite PRA functors**: Use S-expressions to handle the
   cardinality calculations for Hom-sets

### Step 2: Type Checking Infrastructure

Building on the decidable validator we created:

1. **Generate type checkers from PRA data**: Given a PRA functor, automatically
   generate S-expression validators for its initial algebra

2. **Establish formal correspondence**: Prove that valid S-expressions
   correspond exactly to inhabitants of the dependent types

3. **Support sliced type checking**: Enable parameterized validation for
   dependent types

### Next Steps

1. **Finite copresheaf constructors**: Build copresheaves from simple data
   (lists/S-expressions) with automatic naturality verification

2. **Natural transformations between PRA functors**: Define morphisms in the
   category of PRA functors

3. **Initial algebras**: Compute fixed points of PRA functors

4. **Type checker generation**: Automatically generate S-expression validators
   from PRA specifications with formal correspondence proofs

## Implementation Notes

- **Naming conventions**: Use `F2F` prefix for types, `f2f` prefix for functions
- **Proof techniques**: See CLAUDE.md for general patterns (functional
  extensionality, UIP, hole-driven development)
- **Finite representability**: Morphism mappings must be finitely representable (tables or
  constructive patterns) to maintain decidable type checking
