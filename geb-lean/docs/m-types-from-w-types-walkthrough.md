<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [M-types from W-types: A Walkthrough](#m-types-from-w-types-a-walkthrough)
  - [Overview](#overview)
  - [Part 1: Polynomial Functors via CCR](#part-1-polynomial-functors-via-ccr)
    - [Mathematical Background](#mathematical-background)
    - [Implementation in `Polynomial.lean`](#implementation-in-polynomiallean)
    - [Polynomial Endofunctors on `Over X`](#polynomial-endofunctors-on-over-x)
  - [Part 2: W-types as Initial Algebras](#part-2-w-types-as-initial-algebras)
    - [Algebras and Initial Algebras](#algebras-and-initial-algebras)
    - [Implementation in `PolyAlg.lean`](#implementation-in-polyalglean)
  - [Part 3: M-types as Terminal Coalgebras](#part-3-m-types-as-terminal-coalgebras)
    - [Coalgebras and Terminal Coalgebras](#coalgebras-and-terminal-coalgebras)
    - [The Approximation Approach](#the-approximation-approach)
    - [Relationship to the Free Monad](#relationship-to-the-free-monad)
    - [The Agreement Relation](#the-agreement-relation)
    - [The M-type as Consistent Sequences](#the-m-type-as-consistent-sequences)
    - [Meta-level: The Construction Uses W-types](#meta-level-the-construction-uses-w-types)
    - [The Anamorphism (Unfold)](#the-anamorphism-unfold)
    - [Anamorphism as Catamorphism on Nat](#anamorphism-as-catamorphism-on-nat)
  - [Part 4: Free Monad and Cofree Comonad](#part-4-free-monad-and-cofree-comonad)
    - [The Translate Polynomial (Coproduct)](#the-translate-polynomial-coproduct)
    - [The Scale Polynomial (Product)](#the-scale-polynomial-product)
    - [Free Monad](#free-monad)
    - [Cofree Comonad](#cofree-comonad)
  - [Part 5: The Connection](#part-5-the-connection)
    - [W-types are Free Monads on Empty](#w-types-are-free-monads-on-empty)
    - [M-types are Cofree Comonads on Terminal](#m-types-are-cofree-comonads-on-terminal)
    - [Free Monad and Cofree Comonad as Polynomials](#free-monad-and-cofree-comonad-as-polynomials)
    - [Directions (Families) for Free Monad and Cofree Comonad](#directions-families-for-free-monad-and-cofree-comonad)
    - [Higher-Order Monad and Comonad Structure](#higher-order-monad-and-comonad-structure)
    - [The Module Structure: Pattern Runs on Matter](#the-module-structure-pattern-runs-on-matter)
  - [Summary](#summary)
  - [Application: Interviews Run on People](#application-interviews-run-on-people)
  - [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# M-types from W-types: A Walkthrough

This document explains the implementation of polynomial functors, W-types
(initial algebras), and M-types (terminal coalgebras) in `GebLean/PolyAlg.lean`,
and how M-types can be understood in relation to W-types through the free
monad and cofree comonad constructions.

## Overview

The construction follows several steps:

1. **Polynomial functors** are represented as *coproducts of covariant
   representables* (CCR)
2. **W-types** are the initial algebras of polynomial endofunctors
3. **M-types** are the terminal coalgebras of polynomial endofunctors
4. **Free monad** on P is the initial algebra of `A + P(-)`
5. **Cofree comonad** on P is the terminal coalgebra of `A × P(-)`
6. W-types are free monads applied to the empty object
7. M-types are cofree comonads applied to the terminal object

## Part 1: Polynomial Functors via CCR

### Mathematical Background

A polynomial functor `P : Type → Type` has the form:

```text
P(X) = Σ_{i∈I} (B_i → X)
```

where:

- `I` is the "index type" (shapes/positions)
- `B_i` is the "fiber/arity type" at index `i` (directions/children)

This can be rewritten as a coproduct of representable functors:

```text
P(X) = Σ_{i∈I} Hom(B_i, X)
```

### Implementation in `Polynomial.lean`

The code defines `CoprodCovarRepCat` (CCR) as:

```lean
structure CoprodCovarRepCat (C : Type u) [Category C] where
  index : Type u
  family : index → C
```

For a polynomial functor on `Over X`, the evaluation at an object `Y : Over X`
is:

```lean
def ccrEval (ccr : CoprodCovarRepCat C) (Y : C) : Type u :=
  Σ i : ccr.index, (ccr.family i ⟶ Y)
```

This gives us `P(Y) = Σ_i (family(i) → Y)`.

### Polynomial Endofunctors on `Over X`

A polynomial endofunctor on `Over X` is defined as a family of CCR objects
indexed by the fibers of X:

```lean
def PolyEndo (X : Type u) : Type (u + 1) :=
  X → CoprodCovarRepCat (Over X)
```

At each fiber `x : X`, we have:

- `polyBetweenIndex X X P x` - the index type at fiber x
- `polyBetweenFamily X X P x i` - the family (an object of `Over X`)

`★ Family-slice equivalence ──────────────────`
The family-slice equivalence `FamilyCat Type Y ≃ Over Y` is used to move
between "families of types indexed by Y" and "types with maps to Y". This
lets us represent polynomials either as dependent types or as slice objects.
`─────────────────────────────────────────────────`

## Part 2: W-types as Initial Algebras

### Algebras and Initial Algebras

For a polynomial endofunctor `P`, a *P-algebra* consists of:

- A carrier object `A`
- A structure map `str : P(A) → A`

The *initial algebra* is a P-algebra `(W, str_W)` such that for any other
P-algebra `(A, str_A)`, there is a unique algebra homomorphism `fold : W → A`
making this diagram commute:

```text
P(W) --P(fold)--> P(A)
 |                 |
str_W             str_A
 |                 |
 v                 v
 W ----fold-----> A
```

**Lambek's Lemma**: The structure map of an initial algebra is an isomorphism.
This means `W ≅ P(W)`, so the initial algebra is a fixed point of the functor.

### Implementation in `PolyAlg.lean`

The W-type carrier is defined inductively:

```lean
inductive PolyFix (P : PolyEndo X) : X → Type u where
  | mk (x : X) (i : polyBetweenIndex X X P x)
      (children : ∀ (e : (polyBetweenFamily X X P x i).left),
        PolyFix P ((polyBetweenFamily X X P x i).hom e)) :
      PolyFix P x
```

Each element is a tree node with:

- A fiber `x : X`
- An index `i` (which shape)
- A function assigning child trees to each position in the family

The catamorphism (fold) is defined recursively:

```lean
def polyFixFold ... : ∀ x, PolyFix P x → ...
  | _, PolyFix.mk x i children =>
    polyAlgMkFamilyAt ... ⟨i, ...⟩
```

`★ Recursion is defined through folds ───────`
The fold is defined by recursion on the inductive structure of W-types.
At each node, we apply the algebra structure map to the result of folding
all children. This gives the unique algebra homomorphism from the initial
algebra to any other algebra.
`─────────────────────────────────────────────────`

## Part 3: M-types as Terminal Coalgebras

### Coalgebras and Terminal Coalgebras

For a polynomial endofunctor `P`, a *P-coalgebra* consists of:

- A carrier object `A`
- A structure map `str : A → P(A)`

The *terminal coalgebra* is a P-coalgebra `(M, dest)` such that for any other
P-coalgebra `(A, str_A)`, there is a unique coalgebra homomorphism
`unfold : A → M` making this diagram commute:

```text
     A ----unfold----> M
     |                 |
   str_A             dest
     |                 |
     v                 v
   P(A) --P(unfold)--> P(M)
```

**Lambek's Lemma (dual)**: The structure map of a terminal coalgebra is an
isomorphism. This means `M ≅ P(M)`, so the terminal coalgebra is also a
fixed point.

### The Approximation Approach

Unlike W-types (which are inductive), M-types cannot be defined inductively
because they may contain infinite data. In the terminology of Gambino and Kock,
W-type elements are *well-founded trees* (finite height for finitary
polynomials), while M-type elements are generally *non-well-founded* - they
may have infinite height even when the polynomial is finitary.

Instead, we use *approximations*:

```lean
inductive PolyCofixApprox (P : PolyEndo X) : Nat → X → Type u where
  | continue : (x : X) → PolyCofixApprox P 0 x
  | intro {n : Nat} (x : X) (i : polyBetweenIndex X X P x)
      (children : ∀ (e : (polyBetweenFamily X X P x i).left),
        PolyCofixApprox P n ((polyBetweenFamily X X P x i).hom e)) :
      PolyCofixApprox P (n + 1) x
```

The structure is depth-indexed:

- **At depth 0**: Only `continue` is available - a placeholder meaning
  "we stopped observing here"
- **At depth n+1**: Only `intro` is available - an observed node with shape
  `i` and children at depth n

### Relationship to the Free Monad

`PolyCofixApprox P n x` is closely related to the free monad `PolyFreeM 1 P x`
(trees with unit-labeled leaves and P-shaped internal nodes). The distinction:

- **Free monad on 1**: Two ways to terminate a path - (1) an explicit
  unit-leaf at any depth, or (2) a nullary P-node (a shape with no children)
- **PolyCofixApprox n**: Two ways to terminate - (1) `continue` ONLY at
  depth exactly 0, or (2) a nullary P-node at any depth

When a shape `i` has zero positions (empty arity), `intro x i children` is
valid where `children` is the empty function - no actual child approximations
are needed. This means:

- For polynomials with **no nullary shapes** (like streams `S = A × S`),
  every path in `PolyCofixApprox n` reaches exactly depth 0, so n is a
  tight bound on observation depth.
- For polynomials **with nullary shapes** (like lists `L = 1 + A × L`),
  paths can terminate early via nullary nodes, so `PolyCofixApprox n`
  includes both truncated infinite structures and finite structures that
  fit within depth n.

### The Agreement Relation

For approximations to describe a coherent (possibly infinite) object, they
must be consistent. The `PolyCofixAgree` relation ensures that observing at
depth n gives the same answer as observing at depth n+1 (just with less
detail at the leaves):

```lean
inductive PolyCofixAgree (P : PolyEndo X) :
    PolyCofixApprox P n x → PolyCofixApprox P (n + 1) x → Prop where
  | continue : PolyCofixAgree P (.continue x) a
  | intro : (∀ e, PolyCofixAgree P (children e) (children' e)) →
      PolyCofixAgree P (.intro x i children) (.intro x i children')
```

A depth-0 approximation (`continue`) agrees with anything - it has no
information to contradict. Two `intro` nodes agree if they have the same
shape and their children agree recursively.

### The M-type as Consistent Sequences

An M-type element is a consistent sequence of approximations:

```lean
structure PolyCofix (P : PolyEndo X) (x : X) where
  approx : ∀ n, PolyCofixApprox P n x
  consistent : ∀ n, PolyCofixAgree P (approx n) (approx (n + 1))
```

This is the "sequences of truncations" approach from Abbott et al. An M-type
element is characterized by knowing its structure to any finite depth, with
consistency ensuring the approximations are compatible. Categorically, this
is an inverse limit construction: an M-type element is a point in the limit
of the diagram `... → Approx(2) → Approx(1) → Approx(0)` where arrows
"forget the deepest level."

This matches the categorical construction of the cofree comonad. Following
Libkind and Spivak, define `P^(0) = 1` and `P^(n+1) = 1 × P(P^(n))`, with
projection maps `π^(n) : P^(n+1) → P^(n)`. Then the cofree comonad is:

```text
c_P = lim ( ··· → P^(2) → P^(1) → P^(0) )
```

Our `PolyCofixApprox P n x` corresponds to `P^(n)`, and the agreement
relation encodes the projection maps. The `PolyCofix` structure bundles
a compatible sequence - exactly the data of a point in this limit.

### Meta-level: The Construction Uses W-types

The components of the M-type construction are themselves built from
standard type formers:

**PolyCofixApprox is a W-type**: As an inductive type in Lean, it is
modeled by a polynomial functor. As discussed above, it is closely
related to the free monad on 1 - a W-type for the polynomial `1 + P(-)`.

**PolyCofixAgree is a W-type**: This inductive proposition has polynomial
structure:

- The `continue` constructor has shape with 0 children (no recursive premises)
- The `intro` constructor has shape with children indexed by the positions
  `e` of the P-shape - each child is a recursive `PolyCofixAgree` proof

**PolyCofix is a Sigma of Pi types**: The structure is equivalent to:

```text
Σ (approx : Π n, PolyCofixApprox P n x),
  Π n, PolyCofixAgree P (approx n) (approx (n + 1))
```

So M-types are constructed from:

- W-types (the inductive `PolyCofixApprox`)
- W-types (the inductive `PolyCofixAgree`)
- Pi types (the `∀ n` quantifiers)
- Sigma types (the structure bundling)

This is the sense in which "M-types come from W-types": not that M-types
ARE W-types, but that the construction of M-types as terminal coalgebras
is itself expressible using W-types (inductive definitions), Pi types,
and Sigma types.

### The Anamorphism (Unfold)

The unique coalgebra homomorphism to the terminal coalgebra is:

```lean
def polyCofixUnfoldApprox (P : PolyEndo X) (α : PolyCoalg P) (n : Nat) (x : X)
    (a : {y : α.V.left // α.V.hom y = x}) : PolyCofixApprox P n x :=
  match n with
  | 0 => .continue x
  | n + 1 =>
    let strResult := α.str.left a.val
    -- Get index and children from coalgebra structure map
    hx ▸ .intro strResult.1 elem.1 (fun e =>
      polyCofixUnfoldApprox P α n _ ⟨childVal, hChild⟩)
```

This builds the M-type by repeatedly applying the coalgebra structure map.

### Anamorphism as Catamorphism on Nat

The anamorphism exhibits another "M-from-W" pattern: the unfold on the
M-type is implemented as a **fold on the natural numbers**.

The natural numbers are themselves a W-type - the initial algebra of the
polynomial `1 + (-)`, satisfying `Nat ≅ 1 + Nat` (zero and successor).
Recursion on Nat is the catamorphism for this W-type.

The `polyCofixUnfoldApprox` function:

```lean
match n with
| 0 => .continue _
| n + 1 => ... polyCofixUnfoldApprox α n ...
```

is structural recursion on `n`, which is a fold over Nat. The "infinite
unfold" is converted to:

1. A **finite fold** (catamorphism on Nat) that builds each approximation
2. A **Pi type** `∀ n, PolyCofixApprox P n x` that bundles all finite results

Each individual computation `polyCofixUnfoldApprox α n a` terminates in
O(n) applications of the coalgebra structure map. The "infinity" of the
M-type is captured not by any single computation, but by the Pi type that
quantifies over all n.

This is how constructive type theory handles coinduction: rather than
building infinite objects directly, we build functions from Nat to finite
approximations, where each approximation is computed by terminating
recursion.

## Part 4: Free Monad and Cofree Comonad

### The Translate Polynomial (Coproduct)

Given `A : Over X` and `P : PolyEndo X`, the *translate polynomial*
`polyTranslate A P` represents `Y ↦ A + P(Y)`:

- Positions: leaves from A, or nodes from P
- Directions at a leaf: none (empty)
- Directions at a node: same as P

```lean
def polyTranslateIndex (A : Over X) (P : PolyEndo X) (x : X) : Type u :=
  { a : A.left // A.hom a = x } ⊕ polyBetweenIndex X X P x
```

### The Scale Polynomial (Product)

Given `A : Over X` and `P : PolyEndo X`, the *scale polynomial*
`polyScale A P` represents `Y ↦ A × P(Y)`:

- Positions: pairs of labels from A and nodes from P
- Directions at (a, p): same as P at p

```lean
def polyScaleIndex (A : Over X) (P : PolyEndo X) (x : X) : Type u :=
  { a : A.left // A.hom a = x } × polyBetweenIndex X X P x
```

### Free Monad

The free monad is `PolyFreeM A P = PolyFix (polyTranslate A P)`.
These are trees with A-labeled leaves and P-shaped internal nodes.

### Cofree Comonad

The cofree comonad is `PolyCofreeM A P = PolyCofix (polyScale A P)`.
These are M-type trees with A-annotations at each node.

## Part 5: The Connection

### W-types are Free Monads on Empty

When A is empty (the initial object), there are no leaves. Every position
in `polyTranslate A P` is a node from P:

```lean
def polyTranslateIndexInitialEquiv (P : PolyEndo X) (x : X) :
    polyTranslateIndex (overInitial X) P x ≃ polyBetweenIndex X X P x
```

Thus:

```lean
def polyFixEquivPolyFreeM (P : PolyEndo X) (x : X) :
    PolyFix P x ≃ PolyFreeM (overInitial X) P x
```

### M-types are Cofree Comonads on Terminal

When A is terminal (a singleton at each fiber), the label in
`polyScale A P` is uniquely determined:

```lean
def polyScaleIndexTerminalEquiv (P : PolyEndo X) (x : X) :
    polyScaleIndex (overTerminal X) P x ≃ polyBetweenIndex X X P x
```

Thus:

```lean
-- (equivalence shown in the code via approximation bijection)
PolyCofix P x ≃ PolyCofreeM (overTerminal X) P x
```

`★ W-type/M-type duality ──────────────────────`
This reveals the duality:

- W-types = Free monad on ∅ = trees with no labels (pure structure)
- M-types = Cofree comonad on 1 = streams with trivial labels

The free/cofree constructions are parametric versions that allow
non-trivial leaf labels (for W) or node annotations (for M).
`─────────────────────────────────────────────────`

`★ Pattern runs on matter ─────────────────────`
Libkind and Spivak describe the free monad as representing **patterns**
(terminating decision trees) and the cofree comonad as representing
**matter** (infinite behavior trees). Patterns start and end; matter
persists indefinitely. The free monad on P gives well-founded P-trees
(finite height for finitary P), while the cofree comonad gives
non-well-founded P-trees that can respond forever.

This terminology clarifies the duality: W-types (free monad on ∅) are
patterns with no variable slots, while M-types (cofree comonad on 1)
are matter with trivial annotations at each node.
`─────────────────────────────────────────────────`

### Free Monad and Cofree Comonad as Polynomials

The definitions above show that free monads and cofree comonads are
*pointwise* W-types and M-types respectively. But there is a further
step: showing that these constructions are *themselves polynomial
functors* (in the parameter A).

To show a functor `F` is polynomial, we exhibit it in the standard form:

```text
F(Y) ≅ Σ (p : Positions), (Directions(p) → Y)
```

The standard method to compute positions: apply the functor to the
terminal object. For a polynomial `P(Y) = Σ_{i∈I} (B_i → Y)`, we have
`P(1) ≅ Σ_{i∈I} (B_i → 1) ≅ Σ_{i∈I} 1 ≅ I`. The directions collapse
(there is exactly one function to the terminal object), leaving just
the positions.

**Free monad as polynomial**: For `FreeM_P(A) = μX. A + P(X)`:

- `Positions = FreeM_P(1)` = trees with unit-labeled leaves
  = W-type of `1 + P(-)` = `PolyFreeM 1 P`
- `Directions(t)` = leaf positions in tree `t`

So: `FreeM_P(A) ≅ Σ (t : TreeShapes), (LeafPositions(t) → A)`

These tree shapes can be understood as **terminating decision trees**: each
position in P represents a "question" or "decision point," and each direction
represents a possible "answer" or "choice." A tree shape specifies the
branching structure - which questions are asked depending on previous
answers - while the directions (leaf positions) mark where final values
are needed. In the "pattern runs on matter" terminology, tree shapes are
the patterns.

In the code, this is exhibited by:

- `PolyFreeMShape P x` = `PolyFreeM (overTerminal X) P x` (the position type)
- `polyFreeMFamily P x shape` (the family/direction type at each shape)
- `polyFreeMPoly P` : the polynomial endofunctor with these positions/families

**Cofree comonad as polynomial**: For `CofreeM_P(A) = νX. A × P(X)`:

- `Positions = CofreeM_P(1)` = M-type of `1 × P(-)` ≅ M-type of `P`
  (since `1 × P(-) ≅ P(-)`) = `PolyCofreeM 1 P ≅ PolyCofix P`
- `Directions(s)` = node positions in M-type element `s`

So: `CofreeM_P(A) ≅ Σ (s : MTypeShapes), (NodePositions(s) → A)`

In the code, this is exhibited by:

- `PolyCofreeShape P x` = `PolyCofreeM (overTerminal X) P x` (the position type)
- `polyCofreeFamily P x shape` (the family/direction type at each shape)
- `polyCofreeMPoly P` : the polynomial endofunctor with these positions/families

Note the distinction between applying to initial vs terminal:

- **Positions of free monad** = `FreeM_P(1)` = `PolyFreeM 1 P`
  = trees with unit-labeled leaves ("dot" at each leaf)
- **W-type** = `PolyFreeM ∅ P` = trees with ∅-labeled leaves
  = trees with no *variable* leaves

These are different! The W-type is the free monad applied to the
*initial* object, not the terminal. It represents "pure structure"
with no variable positions at all.

Note: "no variable leaves" does not mean "no leaves at all". The free
monad `PolyFreeM A P` has two kinds of stopping points:

1. **A-leaves**: Explicit leaves from the A summand (variable terms)
2. **Nullary P-nodes**: P-positions with empty direction type (no children)

When A = ∅, there are no variable terms (can't choose an A-leaf), but
nullary P-shapes still act as structural leaves. For example, if P is
the list polynomial with a nullary "nil" constructor, then `PolyFreeM ∅ P`
contains finite lists (terminating at nil) but with no element values.

For the cofree comonad, a simplification occurs:

- **Positions of cofree comonad** = `CofreeM_P(1)` = M-type of `1 × P(-)`
- Since `1 × P(-) ≅ P(-)`, this is ≅ `PolyCofix P` = M-type

So M-types ARE the positions of the cofree comonad (because product
with 1 is an isomorphism), but W-types are NOT the positions of the
free monad (because coproduct with ∅ is an isomorphism, but that gives
the free monad on ∅, not on 1).

### Directions (Families) for Free Monad and Cofree Comonad

Having established the position types, we now describe the direction
(family) types that complete the polynomial representation.

**Free monad directions**: For each tree shape `t : PolyFreeMShape P x`,
the direction type `polyFreeMFamily P x t` is an object of `Over X`
representing the leaf positions and their fibers:

```lean
def polyFreeMFamily (P : PolyEndo X) (x : X)
    (shape : PolyFreeMShape P x) : Over X :=
  Over.mk (f := PolyFreeMLeafFiber P shape)
```

- The underlying type is `PolyFreeMLeafPos P shape` - the type of leaf
  positions in tree `shape`
- The fiber map `PolyFreeMLeafFiber P shape` assigns to each leaf its
  fiber in X (the type at which that leaf lives)
- This is computed recursively: at an A-leaf, the fiber is the leaf's
  position in A; at a P-node, it recurses through the children

Morphisms in `Over X` from `polyFreeMFamily P x shape` to `A : Over X`
are functions assigning an A-value to each leaf position, respecting
fibers. This gives the expected form:

```text
FreeM_P(A)_x ≅ Σ (shape : TreeShapes_x), (Leaf positions of shape → A)
```

**Cofree comonad directions**: For each M-type shape
`s : PolyCofreeShape P x`, the direction type `polyCofreeFamily P x s`
represents annotation positions and their fibers:

```lean
def polyCofreeFamily (P : PolyEndo X) (x : X)
    (shape : PolyCofreeShape P x) : Over X :=
  Over.mk (f := PolyCofreeAnnotFiber P shape)
```

- The underlying type is `PolyCofreeAnnotPos P shape` - the type of
  node positions in M-type element `shape`
- This is defined as `Σ n, PolyCofreeAnnotPosAt P shape n` - pairs of
  a depth `n` and a position at that depth
- The fiber map `PolyCofreeAnnotFiber P shape` assigns to each position
  its fiber in X (the type at which that node lives)

Morphisms from `polyCofreeFamily P x shape` to `A` assign an A-value
to each node position. This gives:

```text
CofreeM_P(A)_x ≅ Σ (shape : MTypeShapes_x), (Node positions of shape → A)
```

**Polynomials from families**: The polynomial representations combine
positions and families using `ccrObjMk`:

```lean
def polyFreeMPoly (P : PolyEndo X) : PolyEndo X := fun x =>
  ccrObjMk (polyFreeMFamily P x)

def polyCofreeMPoly (P : PolyEndo X) : PolyEndo X := fun x =>
  ccrObjMk (polyCofreeFamily P x)
```

Here `ccrObjMk` constructs a CCR object from a family function, with the
index type being the domain of the family (the shape/position type) and
the family being the direction types at each shape.

**Intuitive reading of directions**:

For the **free monad**, recall that positions are tree shapes - finite
trees with P-shaped internal nodes and unit-labeled leaves (marking
"slots" for variable terms). The directions at a given tree shape are
exactly the *leaf positions* in that tree. Intuitively: a position tells
you the *shape* of a term with variables, and the directions tell you
*where the variables go*. To build an actual term `FreeM_P(A)`, you
choose a tree shape and then fill each variable slot with a value from A.

For the **cofree comonad**, positions are M-type shapes - potentially
infinite trees with P-shaped nodes. The directions at a given M-type
shape are the *node positions* throughout the (possibly infinite)
structure, indexed by depth. Intuitively: a position tells you the
*shape* of a (co)recursive structure, and the directions tell you
*where to put annotations*. To build an actual element `CofreeM_P(A)`,
you choose an M-type shape and then annotate every node (at every finite
depth) with a value from A. Since M-types can be infinite, a single
shape may have infinitely many annotation positions - but each individual
position is at some finite depth, so we can specify them all via the
depth-indexed type `Σ n, PolyCofreeAnnotPosAt P shape n`.

### Higher-Order Monad and Comonad Structure

The constructions `P ↦ polyFreeMPoly P` (free monad) and
`P ↦ polyCofreeMPoly P` (cofree comonad) are not just functorial
operations on polynomial endofunctors - they are themselves a **monad**
and **comonad** on the category of polynomial endofunctors.

**Free monad monad**: The mapping `P ↦ polyFreeMPoly P` carries:

- **Unit**: `P → polyFreeMPoly P` - embed each P-shape as a single-node
  tree (a tree with exactly one internal P-node whose children are
  all immediate leaves)
- **Multiplication**: `polyFreeMPoly (polyFreeMPoly P) → polyFreeMPoly P`
  - flatten trees-of-trees into trees by grafting

The multiplication corresponds to substituting trees for leaves: given
a tree whose leaves are themselves trees, produce a single tree.

**Cofree comonad comonad**: The mapping `P ↦ polyCofreeMPoly P` carries:

- **Counit**: `polyCofreeMPoly P → P` - extract the root shape and
  immediate annotations
- **Comultiplication**: `polyCofreeMPoly P → polyCofreeMPoly (polyCofreeMPoly P)`
  - refine each annotation position to remember its path from the root

The comultiplication corresponds to "remembering the context": each
annotation in the result knows not just its value but its position in
the overall M-type structure.

These higher-order structures are documented in the code at
`PolyAlg.lean` (see the comment near `polyFreeMPoly`).

### The Module Structure: Pattern Runs on Matter

Beyond the individual monad and comonad structures, there is an interaction
between them. Libkind and Spivak prove (Theorem 3.4) that the free monad
is a **module over the cofree comonad**. Specifically, there is a natural
map:

```text
ν_{P,Q} : m_P ⊗ c_Q → c_{P⊗Q}
```

where `m_P` is the free monad on P, `c_Q` is the cofree comonad on Q, and
`⊗` is the substitution product of polynomials.

This map formalizes "pattern runs on matter": given a finite decision tree
(pattern, from `m_P`) and an infinite behavior tree (matter, from `c_Q`),
we can run the pattern on the matter to produce a result. The pattern
determines what questions to ask; the matter provides the answers; the
result is the path taken through the pattern.

The module laws ensure this interaction is coherent:

- **Unit**: Running an empty pattern (just return) on matter does nothing
- **Associativity**: Running a compound pattern (pattern-of-patterns) is
  the same as running them sequentially

This module structure is what allows finite programs to interact with
infinite environments in a well-defined way.

## Summary

| Concept | Definition | Universal Property |
| ------- | ---------- | ------------------ |
| W-type | `PolyFix P` | Initial P-algebra |
| M-type | `PolyCofix P` | Terminal P-coalgebra |
| Free monad | `PolyFix (A + P(-))` | Left adjoint to forget |
| Cofree comonad | `PolyCofix (A × P(-))` | Right adjoint to forget |

The constructions satisfy:

- `W ≅ P(W)` (Lambek's Lemma for initial algebras)
- `M ≅ P(M)` (Lambek's Lemma for terminal coalgebras)
- `PolyFix P ≃ PolyFreeM ∅ P` (W-type is free monad on empty)
- `PolyCofix P ≃ PolyCofreeM 1 P` (M-type is cofree comonad on terminal)

## Application: Interviews Run on People

This example is taken directly from Libkind and Spivak's paper "Pattern runs
on matter: The free monad monad as a module over the cofree comonad comonad"
(arXiv:2404.16321). It illustrates the "pattern runs on matter" framework
concretely.

Consider a polynomial P whose positions are questions and whose directions
are possible answers. For example:

```text
P = {Tea?} × y^{Y,N} + {Kind?} × y^{green,black,herbal}
```

This polynomial has two positions (questions): "Do you want tea?" with two
possible answers, and "What kind of tea?" with three possible answers.

**Pattern (free monad)**: An element of `m_P` is a terminating decision tree,
i.e., an interview. For example: "Ask 'Tea?'. If Y, ask 'Kind?'. If N,
ask 'Tea?' again." The tree has finite depth; the interview eventually ends.

**Matter (cofree comonad)**: An element of `c_{[P,1]}` is a person - an
infinite behavior tree that can answer any sequence of questions. At each
node, the person provides an answer for each possible question, and the
subtrees represent how they would continue answering after each response.
A person's answers may depend on the history of questions asked.

**Running the interview**: The module action `m_P ⊗ c_{[P,1]} → c_1 ≅ N × y`
runs the interview on the person. The result is a natural number (how many
questions were asked) together with the final state. The interview's finite
structure determines when to stop; the person's infinite capacity ensures
they can always respond.

For instance, if Alice always says "N" to tea and "herbal" for kind, and
the interview is "Ask Tea?, then ask Tea? again," running this on Alice
yields 2 (two questions asked). If Bob initially says "N" but on the
second asking says "Y" and prefers "black," running the same interview
yields 2 questions but a different traversal of the interview tree.

The pattern (interview structure) is finite and terminating. The matter
(person) is infinite and persistent. The interaction produces a finite
trace through the pattern, guided by the matter's responses.

## References

- Abbott, Altenkirch, Ghani: "Containers: Constructing Strictly Positive Types"
- Avigad, Carneiro, Hudon: "Data Types as Quotients of Polynomial Functors"
- Libkind, Spivak: "Pattern runs on matter: The free monad monad as a module
  over the cofree comonad comonad" (arXiv:2404.16321)
