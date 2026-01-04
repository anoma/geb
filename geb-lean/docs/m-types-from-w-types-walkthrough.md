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
because they may contain infinite data. Instead, we use *approximations*:

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

## References

- Abbott, Altenkirch, Ghani: "Containers: Constructing Strictly Positive Types"
- Avigad, Carneiro, Hudon: "Data Types as Quotients of Polynomial Functors"
