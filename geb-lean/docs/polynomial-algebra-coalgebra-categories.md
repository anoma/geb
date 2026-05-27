<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Algebras and Coalgebras for Polynomial Functors](#algebras-and-coalgebras-for-polynomial-functors)
  - [Properties of the Forgetful Functor](#properties-of-the-forgetful-functor)
    - [Copresheaf Equivalence](#copresheaf-equivalence)
  - [1. Initial and Terminal Objects](#1-initial-and-terminal-objects)
    - [1.1 Algebras](#11-algebras)
      - [1.1.1 General Case](#111-general-case)
      - [1.1.2 Example: P(X) = A + X^2](#112-example-px--a--x%5E2)
    - [1.2 Coalgebras](#12-coalgebras)
      - [1.2.1 General Case](#121-general-case)
      - [1.2.2 Example: P(X) = A + X^2](#122-example-px--a--x%5E2)
  - [2. Free Monads and Cofree Comonads](#2-free-monads-and-cofree-comonads)
    - [2.1 Algebras (The Free Monad)](#21-algebras-the-free-monad)
      - [2.1.1 General Case](#211-general-case)
      - [2.1.2 Example: P(X) = A + X^2](#212-example-px--a--x%5E2)
    - [2.2 Coalgebras (The Cofree Comonad)](#22-coalgebras-the-cofree-comonad)
      - [2.2.1 General Case](#221-general-case)
      - [2.2.2 Example: P(X) = A + X^2](#222-example-px--a--x%5E2)
  - [3. Binary Products](#3-binary-products)
    - [3.1 Algebras](#31-algebras)
      - [3.1.1 General Case](#311-general-case)
      - [3.1.2 Example: P(X) = A + X^2](#312-example-px--a--x%5E2)
    - [3.2 Coalgebras](#32-coalgebras)
      - [3.2.1 General Case](#321-general-case)
      - [3.2.2 Example: P(X) = A + X^2](#322-example-px--a--x%5E2)
  - [4. Binary Coproducts](#4-binary-coproducts)
    - [4.1 Algebras](#41-algebras)
      - [4.1.1 General Case](#411-general-case)
      - [4.1.2 Example: P(X) = A + X^2](#412-example-px--a--x%5E2)
    - [4.2 Coalgebras](#42-coalgebras)
      - [4.2.1 General Case](#421-general-case)
      - [4.2.2 Example: P(X) = A + X^2](#422-example-px--a--x%5E2)
  - [5. Equalizers](#5-equalizers)
    - [5.1 Algebras](#51-algebras)
      - [5.1.1 General Case](#511-general-case)
      - [5.1.2 Example: P(X) = A + X^2](#512-example-px--a--x%5E2)
    - [5.2 Coalgebras](#52-coalgebras)
      - [5.2.1 General Case](#521-general-case)
      - [5.2.2 Example: P(X) = A + X^2](#522-example-px--a--x%5E2)
  - [6. Coequalizers](#6-coequalizers)
    - [6.1 Algebras](#61-algebras)
      - [6.1.1 General Case](#611-general-case)
      - [6.1.2 Example: P(X) = A + X^2](#612-example-px--a--x%5E2)
    - [6.2 Coalgebras](#62-coalgebras)
      - [6.2.1 General Case](#621-general-case)
      - [6.2.2 Example: P(X) = A + X^2](#622-example-px--a--x%5E2)
  - [7. Pullbacks](#7-pullbacks)
    - [7.1 Algebras](#71-algebras)
      - [7.1.1 General Case](#711-general-case)
      - [7.1.2 Example: P(X) = A + X^2](#712-example-px--a--x%5E2)
    - [7.2 Coalgebras](#72-coalgebras)
      - [7.2.1 General Case](#721-general-case)
      - [7.2.2 Example: P(X) = A + X^2](#722-example-px--a--x%5E2)
  - [8. Pushouts](#8-pushouts)
    - [8.1 Algebras](#81-algebras)
      - [8.1.1 General Case](#811-general-case)
      - [8.1.2 Example: P(X) = A + X^2](#812-example-px--a--x%5E2)
    - [8.2 Coalgebras](#82-coalgebras)
      - [8.2.1 General Case](#821-general-case)
      - [8.2.2 Example: P(X) = A + X^2](#822-example-px--a--x%5E2)
  - [9. Topos Structure (Coalgebras Only)](#9-topos-structure-coalgebras-only)
    - [9.1 Subobject Classifier (Omega)](#91-subobject-classifier-omega)
      - [9.1.1 General Case](#911-general-case)
      - [9.1.2 Example: P(X) = A + X^2](#912-example-px--a--x%5E2)
    - [9.2 Exponentials (Y^X)](#92-exponentials-y%5Ex)
      - [9.2.1 General Case](#921-general-case)
      - [9.2.2 Example: P(X) = A + X^2](#922-example-px--a--x%5E2)
  - [10. Requirements on the Base Category](#10-requirements-on-the-base-category)
    - [10.1 Construction-by-Construction Requirements](#101-construction-by-construction-requirements)
    - [10.2 M-Type Construction Requirements](#102-m-type-construction-requirements)
      - [10.2.1 Finitary vs. Infinitary Polynomials](#1021-finitary-vs-infinitary-polynomials)
      - [10.2.2 The Approximation Construction](#1022-the-approximation-construction)
      - [10.2.3 Summary for P(X) = A + X^2](#1023-summary-for-px--a--x%5E2)
    - [10.3 Finitary Topos Requirements](#103-finitary-topos-requirements)
  - [11. Candidate Base Categories](#11-candidate-base-categories)
    - [11.1 PER(T): Partial Equivalence Relations](#111-pert-partial-equivalence-relations)
      - [11.1.1 Categorical Properties](#1111-categorical-properties)
      - [11.1.2 Relationship to Realizability Toposes](#1112-relationship-to-realizability-toposes)
      - [11.1.3 Tree Calculus as PCA](#1113-tree-calculus-as-pca)
    - [11.2 Parametric Relations (Reynolds/Wadler)](#112-parametric-relations-reynoldswadler)
      - [11.2.1 Structure in the Codebase](#1121-structure-in-the-codebase)
      - [11.2.2 Categorical Properties](#1122-categorical-properties)
      - [11.2.3 Functions as Graphs of Relations](#1123-functions-as-graphs-of-relations)
    - [11.3 The Hybrid Approach](#113-the-hybrid-approach)
    - [11.4 Self-Representation](#114-self-representation)
    - [11.5 Comparison](#115-comparison)
    - [11.6 Open Questions](#116-open-questions)
  - [12. Concrete Descriptions of Two Topoi](#12-concrete-descriptions-of-two-topoi)
    - [12.1 The Realizability Topos RT(T)](#121-the-realizability-topos-rtt)
      - [12.1.1 Assemblies](#1211-assemblies)
      - [12.1.2 Concrete Structure](#1212-concrete-structure)
      - [12.1.3 Internal Logic](#1213-internal-logic)
    - [12.2 The Coalgebra Topos P-Coalg(1 + X^2)](#122-the-coalgebra-topos-p-coalg1--x%5E2)
      - [12.2.1 Objects and Morphisms](#1221-objects-and-morphisms)
      - [12.2.2 Terminal Coalgebra](#1222-terminal-coalgebra)
      - [12.2.3 Subobject Classifier](#1223-subobject-classifier)
      - [12.2.4 Internal Logic](#1224-internal-logic)
      - [12.2.5 Copresheaf Perspective](#1225-copresheaf-perspective)
    - [12.3 Comparison](#123-comparison)
    - [12.4 The Lambda-Bialgebra Bridge](#124-the-lambda-bialgebra-bridge)
      - [12.4.1 The Distributive Law](#1241-the-distributive-law)
      - [12.4.2 Bridging the Two Topoi](#1242-bridging-the-two-topoi)
      - [12.4.3 Reconciliation](#1243-reconciliation)
  - [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Algebras and Coalgebras for Polynomial Functors

Let **Set** denote the category of sets and functions.
Let P: **Set** -> **Set** be an accessible polynomial
endofunctor. We examine the category of P-algebras,
denoted P-**Alg**, and the category of P-coalgebras,
denoted P-**Coalg**.

The running example is the functor P(X) = A + X^2,
representing binary trees with leaves labeled by
elements of a fixed set A.

## Properties of the Forgetful Functor

The forgetful functor U: P-**Alg** -> **Set** sends
an algebra (S, alpha: P(S) -> S) to its carrier S.
The forgetful functor U: P-**Coalg** -> **Set** sends
a coalgebra (C, gamma: C -> P(C)) to its carrier C.

For an arbitrary endofunctor F on **Set**:

- U: F-**Alg** -> **Set** creates all limits,
  unconditionally. No hypothesis on F is needed: the
  F-algebra structure on the limit is induced by the
  universal property of the limit applied to the
  composites F(L) -> F(A_i) -> A_i.
- U: F-**Coalg** -> **Set** creates all colimits,
  unconditionally. No hypothesis on F is needed: the
  F-coalgebra structure on the colimit is induced by
  the universal property of the colimit applied to the
  composites A_i -> F(A_i) -> F(L).

For the converse directions, conditions on F are
required:

- U: F-**Alg** -> **Set** creates those colimits that
  F preserves.
- U: F-**Coalg** -> **Set** creates those limits that
  F preserves.

Polynomial endofunctors on **Set** preserve all
connected limits (equivalently, wide pullbacks). This
is because the identity functor preserves all limits,
constant functors preserve all limits, coproducts in
**Set** are stable under pullback (extensivity), and
products of limit-preserving functors preserve limits.
Therefore, for a polynomial P:

- U: P-**Coalg** -> **Set** creates all connected
  limits, including equalizers and pullbacks.
- U: P-**Coalg** -> **Set** does not create products
  in general, since polynomial endofunctors involving
  coproducts do not preserve products. (For example,
  `P(X x Y) = A + (X x Y)^2` differs from
  `P(X) x P(Y) = (A + X^2) x (A + Y^2)`.)

### Copresheaf Equivalence

For a polynomial endofunctor P that preserves
connected limits, P-**Coalg** is equivalent to a
copresheaf category **Set**^C, where C is the cofree
category (path category) of P (Worrell 2005, Adamek
2005). In the codebase, this equivalence is
`polyCoalgCopresheafEquiv`. This equivalence allows
the categorical constructions in P-**Coalg** to be
derived from the corresponding pointwise constructions
of copresheaves on C, providing independent
confirmation.

---

## 1. Initial and Terminal Objects

### 1.1 Algebras

#### 1.1.1 General Case

Since U: P-**Alg** -> **Set** creates all limits, the
terminal algebra is constructed on the terminal set
`1 = {*}`, equipped with the unique structure map
`P(1) -> 1`.

Because P is accessible, P-**Alg** is cocomplete.
The initial algebra (W, alpha: P(W) -> W) satisfies
`alpha` is an isomorphism (Lambek's lemma). W is the
type of well-founded P-trees (W-type).

#### 1.1.2 Example: P(X) = A + X^2

- **Terminal algebra:** The carrier is `{*}`. The
  structure map `A + {*}^2 -> {*}` sends every element
  to `*`: `leaf(a) = *` for all a in A, and
  `node(*, *) = *`.
- **Initial algebra:** W is the set of finite binary
  trees with A-labeled leaves. The isomorphism
  `alpha: A + W^2 -> W` sends `inl(a)` to the leaf
  tree labeled a and `inr(t_1, t_2)` to the tree with
  root node and subtrees t_1, t_2. Every element of W
  is uniquely either a leaf or a binary node of two
  finite trees.

### 1.2 Coalgebras

#### 1.2.1 General Case

Since U: P-**Coalg** -> **Set** creates all colimits,
the initial coalgebra is constructed on the initial set
`{} = empty`, equipped with the unique structure map
`{} -> P({})`.

Because P is accessible, P-**Coalg** is complete and
has a terminal object. The terminal coalgebra
`(Z, zeta: Z -> P(Z))` satisfies `zeta` is an
isomorphism (dual of Lambek's lemma). Z is the type of
all (finite and infinite) P-trees (M-type).

#### 1.2.2 Example: P(X) = A + X^2

- **Initial coalgebra:** The carrier is the empty set.
- **Terminal coalgebra:** Z is the set of all finite
  and infinite binary trees with A-labeled leaves. The
  isomorphism `zeta: Z -> A + Z^2` sends a leaf tree
  to `inl(a)` and a node tree with subtrees z_1, z_2
  to `inr(z_1, z_2)`. Elements of Z include all finite
  trees (which are also elements of W) and all infinite
  trees (which have branches that never terminate at a
  leaf).

---

## 2. Free Monads and Cofree Comonads

### 2.1 Algebras (The Free Monad)

#### 2.1.1 General Case

Because P is accessible, U: P-**Alg** -> **Set** has a
left adjoint F: **Set** -> P-**Alg**. For a set Y,
F(Y) is the free P-algebra generated by Y, constructed
as the initial algebra of the modified endofunctor
`P_Y(X) = Y + P(X)`. The monad `U . F` on **Set** is
the free monad of P.

#### 2.1.2 Example: P(X) = A + X^2

The modified functor is `P_Y(X) = Y + A + X^2`. Its
initial algebra F(Y) is the set of finite binary trees
with leaves labeled by elements of the disjoint union
`A + Y`. Elements of A label ordinary leaves; elements
of Y label variable leaves (generators of the free
algebra). The algebra structure evaluates the A-leaves
and binary nodes via the P-structure, leaving
Y-leaves inert.

### 2.2 Coalgebras (The Cofree Comonad)

#### 2.2.1 General Case

Because P is accessible, U: P-**Coalg** -> **Set** has
a right adjoint G: **Set** -> P-**Coalg**. For a set
Y, G(Y) is the cofree P-coalgebra over Y, constructed
as the terminal coalgebra of the modified endofunctor
`P^Y(X) = Y x P(X)`. The comonad `U . G` on **Set**
is the cofree comonad of P.

#### 2.2.2 Example: P(X) = A + X^2

The modified functor is `P^Y(X) = Y x (A + X^2)`. Its
terminal coalgebra G(Y) is the set of finite and
infinite binary trees with A-labeled leaves, where
every node (both internal nodes and leaves) carries an
annotation from Y. The coalgebra structure
`G(Y) -> Y x (A + G(Y)^2)` extracts the root's
Y-annotation and then either the leaf label (for a
leaf) or the two annotated subtrees (for an internal
node). Equivalently, G(Y) consists of elements of Z
(the terminal coalgebra) enriched with a Y-valued
annotation at every tree position.

---

## 3. Binary Products

### 3.1 Algebras

#### 3.1.1 General Case

Since U: P-**Alg** -> **Set** creates all limits, the
product of algebras `(S_1, alpha_1)` and
`(S_2, alpha_2)` has carrier `S_1 x S_2` with
structure map defined componentwise:
`alpha(p) = (alpha_1(P(pi_1)(p)), alpha_2(P(pi_2)(p)))`
for `p` in `P(S_1 x S_2)`, where `pi_i` are the
projections.

#### 3.1.2 Example: P(X) = A + X^2

The product algebra has carrier `S_1 x S_2`. The
structure map `A + (S_1 x S_2)^2 -> S_1 x S_2` acts
as:

- `inl(a) |-> (alpha_1(inl(a)), alpha_2(inl(a)))`
- `inr((x_1, x_2), (y_1, y_2)) |->
  (alpha_1(inr(x_1, y_1)), alpha_2(inr(x_2, y_2)))`

### 3.2 Coalgebras

#### 3.2.1 General Case

In any category with a terminal object T, the product
`A x B` equals the pullback `A x_T B` (since the
compatibility condition `!_A . f = !_B . g` for the
unique morphisms to T is always satisfied). In
P-**Coalg**, the terminal object is the terminal
coalgebra Z. Therefore:

`C_1 x C_2 = C_1 x_Z C_2`

where the maps are the unique coalgebra morphisms
`!_1: C_1 -> Z` and `!_2: C_2 -> Z`.

Since polynomial P preserves pullbacks (a connected
limit), U: P-**Coalg** -> **Set** creates pullbacks.
The carrier of the product is therefore the
set-theoretic pullback:

`{(c_1, c_2) in C_1 x C_2 | !_1(c_1) = !_2(c_2)}`

This is the set of pairs of states whose complete
unfoldings (images in Z under the unique morphisms)
are identical. The coalgebra structure is inherited
from the componentwise structure, which is well-defined
on this subset because matching unfoldings guarantee
matching transition shapes at every step.

Note that U does not create products (since P does not
preserve products), so the carrier of the product is
generally a proper subset of `C_1 x C_2`.

Under the copresheaf equivalence
`P-Coalg ~ Set^C`, this product corresponds to the
pointwise product of the corresponding copresheaves.

#### 3.2.2 Example: P(X) = A + X^2

The product of `(C_1, gamma_1)` and `(C_2, gamma_2)`
has carrier `R = {(c_1, c_2) | !_1(c_1) = !_2(c_2)}`
and structure map `gamma_R: R -> A + R^2` defined by:

- If `gamma_1(c_1) = inl(a)` and
  `gamma_2(c_2) = inl(a)` (same label, guaranteed by
  the equal-unfolding condition), then
  `gamma_R(c_1, c_2) = inl(a)`.
- If `gamma_1(c_1) = inr(c_1^l, c_1^r)` and
  `gamma_2(c_2) = inr(c_2^l, c_2^r)` (both branch,
  guaranteed by equal unfoldings), then
  `gamma_R(c_1, c_2) = inr((c_1^l, c_2^l),
  (c_1^r, c_2^r))`.
  The children `(c_1^l, c_2^l)` and
  `(c_1^r, c_2^r)` are in R because the unfoldings of
  the children are the subtrees of the unfoldings of
  the parents.

Equivalently, R is the largest subset of `C_1 x C_2`
that admits a P-coalgebra structure making the
projections into coalgebra morphisms.

---

## 4. Binary Coproducts

### 4.1 Algebras

#### 4.1.1 General Case

U: P-**Alg** -> **Set** does not create colimits in
general. The coproduct of `(S_1, alpha_1)` and
`(S_2, alpha_2)` is constructed as follows:

1. Form the free P-algebra `F(S_1 + S_2)` on the
   disjoint union (the initial algebra of the functor
   `X |-> (S_1 + S_2) + P(X)`).
2. Take the quotient by the smallest P-congruence
   (equivalence relation closed under the P-algebra
   operations) generated by the relations
   `alpha_1(p) ~ p` for `p` in `P(S_1)` and
   `alpha_2(p) ~ p` for `p` in `P(S_2)`.

The result is the algebra whose elements are
equivalence classes of formal P-expression trees with
leaves in `S_1 + S_2`, where any subtree that lies
entirely within `S_1` (resp. `S_2`) is identified with
its evaluation under `alpha_1` (resp. `alpha_2`).

#### 4.1.2 Example: P(X) = A + X^2

The free algebra `F(S_1 + S_2)` consists of finite
binary trees with leaves in `A + S_1 + S_2`. The
congruence identifies any tree `node(t_1, t_2)` where
`t_1, t_2` both reduce to elements of `S_1` with the
result of applying `alpha_1`, and similarly for `S_2`.
After quotienting, the coproduct contains:

- All elements of `S_1` and `S_2` (via the
  coprojections).
- Irreducible trees: those with at least one binary
  node whose children reduce to elements of different
  summands (e.g., `node(s_1, s_2)` with `s_1` in
  `S_1` and `s_2` in `S_2`), which cannot be evaluated
  by either `alpha_1` or `alpha_2`.

### 4.2 Coalgebras

#### 4.2.1 General Case

Since U: P-**Coalg** -> **Set** creates all colimits,
the coproduct of `(C_1, gamma_1)` and
`(C_2, gamma_2)` has carrier `C_1 + C_2` (disjoint
union). The structure map
`gamma: C_1 + C_2 -> P(C_1 + C_2)` applies
`P(inl) . gamma_1` to elements of `C_1` and
`P(inr) . gamma_2` to elements of `C_2`, where
`inl, inr` are the coproduct injections.

Under the copresheaf equivalence, this corresponds
to the pointwise coproduct of copresheaves.

#### 4.2.2 Example: P(X) = A + X^2

The carrier is `C_1 + C_2`. The structure map acts as:

- For `c` in `C_1`: if `gamma_1(c) = inl(a)`, then
  `gamma(inl(c)) = inl(a)`; if
  `gamma_1(c) = inr(c_l, c_r)`, then
  `gamma(inl(c)) = inr(inl(c_l), inl(c_r))`.
- Symmetrically for `c` in `C_2`.

A state originating in `C_1` transitions only to
states in `C_1`; similarly for `C_2`. No
cross-transitions occur.

---

## 5. Equalizers

### 5.1 Algebras

#### 5.1.1 General Case

Since U: P-**Alg** -> **Set** creates all limits, the
equalizer of parallel algebra homomorphisms
`f, g: (S_1, alpha_1) -> (S_2, alpha_2)` has carrier
`E = {s in S_1 | f(s) = g(s)}`, equipped with the
restriction of `alpha_1` to E.

The restriction is well-defined: for `p` in `P(E)`,
since f and g are algebra homomorphisms,
`f(alpha_1(P(incl)(p))) = alpha_2(P(f)(P(incl)(p)))`
and similarly for g. Since `P(f . incl) = P(g . incl)`
(because f and g agree on E), we get
`f(alpha_1(P(incl)(p))) = g(alpha_1(P(incl)(p)))`, so
`alpha_1(P(incl)(p))` is in E.

#### 5.1.2 Example: P(X) = A + X^2

E is the subset of `S_1` on which f and g agree. If
`s` in E and `alpha_1(inr(s, s'))` is defined for
`s, s'` in E, then `alpha_1(inr(s, s'))` is in E
because:

- `f(alpha_1(inr(s, s'))) = alpha_2(inr(f(s), f(s')))`
- `g(alpha_1(inr(s, s'))) = alpha_2(inr(g(s), g(s')))`
- Since `f(s) = g(s)` and `f(s') = g(s')`, these are
  equal.

So E is closed under the binary operation of
`alpha_1`.

### 5.2 Coalgebras

#### 5.2.1 General Case

The reasoning proceeds as follows:

1. Polynomial endofunctors preserve connected limits.
2. Equalizers are connected limits (the equalizer
   diagram, two parallel arrows between two objects, is
   a connected category).
3. U: P-**Coalg** -> **Set** creates those limits that
   P preserves.
4. Therefore U creates equalizers.

The equalizer of parallel coalgebra homomorphisms
`f, g: (C_1, gamma_1) -> (C_2, gamma_2)` has carrier
`E = {c in C_1 | f(c) = g(c)}`, with the restriction
of `gamma_1` as its coalgebra structure.

The restriction lands in `P(E)` because P preserves
the equalizer: for `c` in E,
`P(f)(gamma_1(c)) = gamma_2(f(c)) = gamma_2(g(c))
= P(g)(gamma_1(c))`, so `gamma_1(c)` is in
the equalizer of `P(f)` and `P(g)`, which equals
`P(E)` since P preserves equalizers.

#### 5.2.2 Example: P(X) = A + X^2

E is the subset of `C_1` on which f and g agree. If
`c` in E and `gamma_1(c) = inr(c_l, c_r)`, then since
f and g are coalgebra morphisms:

- `gamma_2(f(c)) = inr(f(c_l), f(c_r))`
- `gamma_2(g(c)) = inr(g(c_l), g(c_r))`

Since `f(c) = g(c)`, these are equal, giving
`f(c_l) = g(c_l)` and `f(c_r) = g(c_r)`. So
`c_l, c_r` are in E: the subset E is closed under
taking children.

---

## 6. Coequalizers

### 6.1 Algebras

#### 6.1.1 General Case

U: P-**Alg** -> **Set** does not create colimits in
general. Given parallel algebra homomorphisms
`f, g: (S_1, alpha_1) -> (S_2, alpha_2)`, the
coequalizer is the quotient `S_2 / ~`, where `~` is
the smallest P-congruence containing
`{(f(s), g(s)) | s in S_1}`. A P-congruence on
`(S_2, alpha_2)` is an equivalence relation on `S_2`
that is also a subalgebra of the product algebra
`(S_2 x S_2, alpha_2 x alpha_2)`.

The quotient `S_2 / ~` inherits a P-algebra structure
because `~` is a congruence: `alpha_2` descends to a
well-defined map `P(S_2 / ~) -> S_2 / ~`.

#### 6.1.2 Example: P(X) = A + X^2

The congruence `~` must be closed under the binary
operation: if `x ~ y`, then for any `z` in `S_2`,
`alpha_2(inr(x, z)) ~ alpha_2(inr(y, z))` and
`alpha_2(inr(z, x)) ~ alpha_2(inr(z, y))`. This
means that the quotient may identify strictly more
pairs than the equivalence relation generated by
`{(f(s), g(s))}` alone, because the congruence
closure propagates identifications through the algebra
operations.

### 6.2 Coalgebras

#### 6.2.1 General Case

Since U: P-**Coalg** -> **Set** creates all colimits,
the coequalizer of parallel coalgebra homomorphisms
`f, g: (C_1, gamma_1) -> (C_2, gamma_2)` has carrier
`Q = C_2 / ~`, where `~` is the equivalence relation
generated by `{(f(c), g(c)) | c in C_1}`. The
coalgebra structure descends to Q: the map
`gamma_2: C_2 -> P(C_2)` induces a well-defined map
`Q -> P(Q)` via `P(pi)`, where `pi: C_2 -> Q` is the
quotient projection.

#### 6.2.2 Example: P(X) = A + X^2

The state space `C_2` is partitioned by `~`. If
`c ~ d`, then since f and g are coalgebra morphisms
mapping some `e` in `C_1` to c and d respectively:

- `gamma_2(c)` and `gamma_2(d)` are either both in A
  (with the same label) or both in `C_2^2`.
- In the branching case
  `gamma_2(c) = inr(c_l, c_r)` and
  `gamma_2(d) = inr(d_l, d_r)`, the children satisfy
  `c_l ~ d_l` and `c_r ~ d_r`.

The quotient coalgebra structure on Q sends the
equivalence class `[c]` to `inl(a)` if
`gamma_2(c) = inl(a)`, and to
`inr([c_l], [c_r])` if
`gamma_2(c) = inr(c_l, c_r)`.

---

## 7. Pullbacks

### 7.1 Algebras

#### 7.1.1 General Case

Since U: P-**Alg** -> **Set** creates all limits, the
pullback of algebra homomorphisms
`f: (S_1, alpha_1) -> (S_3, alpha_3)` and
`g: (S_2, alpha_2) -> (S_3, alpha_3)` has carrier
`S_1 x_{S_3} S_2 = {(x, y) in S_1 x S_2 | f(x) = g(y)}`
with componentwise algebra structure.

#### 7.1.2 Example: P(X) = A + X^2

The pullback algebra consists of pairs `(t_1, t_2)`
from `S_1` and `S_2` satisfying `f(t_1) = g(t_2)` in
`S_3`. The algebra structure acts componentwise:

- `inl(a) |-> (alpha_1(inl(a)), alpha_2(inl(a)))`
  provided `f(alpha_1(inl(a))) = g(alpha_2(inl(a)))`.
- `inr((x_1, x_2), (y_1, y_2)) |->
  (alpha_1(inr(x_1, y_1)), alpha_2(inr(x_2, y_2)))`.

The pullback condition is preserved because f and g
are algebra homomorphisms.

### 7.2 Coalgebras

#### 7.2.1 General Case

Since polynomial P preserves pullbacks (a connected
limit), U: P-**Coalg** -> **Set** creates pullbacks.
The pullback of coalgebra homomorphisms
`f: (C_1, gamma_1) -> (C_3, gamma_3)` and
`g: (C_2, gamma_2) -> (C_3, gamma_3)` has carrier
`C_1 x_{C_3} C_2 = {(c_1, c_2) | f(c_1) = g(c_2)}`
with coalgebra structure inherited componentwise.

The coalgebra structure is well-defined because: for
`(c_1, c_2)` in the pullback, `gamma_1(c_1)` is in
`P(C_1)` and `gamma_2(c_2)` is in `P(C_2)`, with
`P(f)(gamma_1(c_1)) = gamma_3(f(c_1)) =
gamma_3(g(c_2)) = P(g)(gamma_2(c_2))`. Since P
preserves the pullback, `(gamma_1(c_1), gamma_2(c_2))`
determines an element of `P(C_1 x_{C_3} C_2)`.

#### 7.2.2 Example: P(X) = A + X^2

The pullback coalgebra pairs states `(c_1, c_2)` with
`f(c_1) = g(c_2)` in `C_3`. If
`gamma_1(c_1) = inr(c_1^l, c_1^r)`, then
`gamma_3(f(c_1)) = inr(f(c_1^l), f(c_1^r))`.
Since `f(c_1) = g(c_2)`,
`gamma_2(c_2) = inr(c_2^l, c_2^r)` with
`f(c_1^l) = g(c_2^l)` and `f(c_1^r) = g(c_2^r)`.
So the children `(c_1^l, c_2^l)` and
`(c_1^r, c_2^r)` are also in the pullback.

---

## 8. Pushouts

### 8.1 Algebras

#### 8.1.1 General Case

U: P-**Alg** -> **Set** does not create colimits in
general. The pushout of algebra homomorphisms
`f: (S_1, alpha_1) -> (S_2, alpha_2)` and
`g: (S_1, alpha_1) -> (S_3, alpha_3)` is constructed
as the coequalizer of the pair
`(inl . f, inr . g): S_1 => S_2 + S_3` in P-**Alg**,
where `S_2 + S_3` is the coproduct algebra.
Equivalently, it is the quotient of the coproduct
algebra by the smallest P-congruence identifying
`inl(f(s))` with `inr(g(s))` for all `s` in `S_1`.

#### 8.1.2 Example: P(X) = A + X^2

The pushout is the quotient of the coproduct algebra
of `S_2` and `S_3` (which contains elements of both
algebras plus irreducible mixed trees) by the
congruence equating the images of `S_1` under f and g.
This identifies elements `f(s)` in `S_2` with `g(s)`
in `S_3` for each `s` in `S_1`, and propagates these
identifications through the algebra operations.

### 8.2 Coalgebras

#### 8.2.1 General Case

Since U: P-**Coalg** -> **Set** creates all colimits,
the pushout of coalgebra homomorphisms
`f: (C_1, gamma_1) -> (C_2, gamma_2)` and
`g: (C_1, gamma_1) -> (C_3, gamma_3)` has carrier
equal to the set-theoretic pushout: the quotient of
`C_2 + C_3` by the equivalence relation identifying
`inl(f(c))` with `inr(g(c))` for all `c` in `C_1`.
The coalgebra structure descends from the coproduct
coalgebra on `C_2 + C_3`.

#### 8.2.2 Example: P(X) = A + X^2

The carrier is `(C_2 + C_3) / ~` where
`inl(f(c)) ~ inr(g(c))` for `c` in `C_1`. The
coalgebra structure is well-defined on the quotient
because f and g are coalgebra morphisms: if
`inl(f(c)) ~ inr(g(c))`, then their transitions are
compatible (both determined by `gamma_1(c)` via the
homomorphism conditions).

---

## 9. Topos Structure (Coalgebras Only)

P-**Alg** is cocomplete and has all limits (since U
creates limits), but generally lacks Cartesian closure
and a subobject classifier.

P-**Coalg** for a polynomial endofunctor P is a
presheaf topos, hence a Grothendieck topos (Worrell
2005, Adamek 2005). The operative condition is that P
preserves connected limits (equivalently, wide
pullbacks), which polynomial endofunctors on **Set**
satisfy. Under the copresheaf equivalence
`P-Coalg ~ Set^C` (where C is the cofree
category / path category of P), the topos structure
arises from the standard topos structure of a
copresheaf category.

### 9.1 Subobject Classifier (Omega)

#### 9.1.1 General Case

The subobject classifier Omega in P-**Coalg** is a
coalgebra that classifies subcoalgebras: for every
subcoalgebra `S >-> C`, there is a unique coalgebra
morphism `chi_S: C -> Omega` such that
`S = chi_S^{-1}(true)`.

Under the copresheaf equivalence, Omega corresponds to
the copresheaf of cosieves. A cosieve on an object c
of C is a set of morphisms with domain c that is
closed under postcomposition. The cosieves on C
encode the possible "truth-value patterns" on the
tree of observations, subject to a closure condition.

#### 9.1.2 Example: P(X) = A + X^2

The carrier of Omega consists of binary trees (elements
of the terminal coalgebra Z) in which every tree
position (both internal nodes and leaves) is assigned a
truth value from `{True, False}`, subject to the
cosieve condition: if a position is labeled True, then
all descendant positions (reachable by further
transitions) are also labeled True. Equivalently, the
set of True-labeled positions is downward-closed toward
the leaves.

The coalgebra structure
`zeta_Omega: Omega -> A + Omega^2` acts as for Z
(sending leaf elements to their labels and node
elements to their children), but with the
truth-labeling carried along. Multiple elements of
Omega can share the same underlying tree shape (same
image in Z under the unique morphism `Omega -> Z`)
but differ in their truth-value pattern.

The distinguished element `true` in Omega is the
maximal cosieve: every position labeled True. The
distinguished element `false` is the empty cosieve:
every position labeled False.

For a subcoalgebra `S >-> C`, the characteristic map
`chi_S: C -> Omega` sends a state `c` to the element
of Omega whose underlying tree is the unfolding of c
in Z, with a position labeled True if and only if the
corresponding state in the unfolding belongs to S.
The cosieve condition is satisfied because S is a
subcoalgebra (closed under transitions).

### 9.2 Exponentials (Y^X)

#### 9.2.1 General Case

The exponential object `Y^X` in P-**Coalg** is a
coalgebra whose elements represent coalgebra morphisms
in a "parameterized" sense. Under the copresheaf
equivalence `P-Coalg ~ Set^C`, the exponential is
computed by the standard presheaf formula:

`(Y^X)(c) = Nat(h_c x X, Y)`

where `h_c` is the representable copresheaf at c, and
`Nat` denotes natural transformations of copresheaves.
An element of `(Y^X)(c)` is a natural transformation
from the copresheaf `h_c x X` to Y.

#### 9.2.2 Example: P(X) = A + X^2

A state `f` of the exponential coalgebra `Y^X` encodes
a mapping from states of X to states of Y that is
compatible with the coalgebra structure at all
subsequent stages of observation. The coalgebra
structure `Y^X -> A + (Y^X)^2` decomposes such a
mapping according to the first observation step:

- If the mapping produces a leaf observation (both X
  and Y transition to leaves with the same label a),
  the result is `inl(a)`.
- If the mapping produces a branching observation, the
  result is `inr(f_l, f_r)`, where `f_l` and `f_r`
  are the induced mappings on the left and right
  subtrees respectively: `f_l` maps the left subtree
  of X to the left subtree of Y, and `f_r` maps the
  right subtree of X to the right subtree of Y.

---

## 10. Requirements on the Base Category

The constructions above are stated for P-**Alg** and
P-**Coalg** over **Set**. This section analyzes what
properties a base category E must have for
P-**Coalg**(E) to allow the same constructions, and
in particular for P-**Coalg**(E) to be a topos.

### 10.1 Construction-by-Construction Requirements

Each construction in P-**Coalg**(E) imposes
requirements on E:

- **Initial coalgebra** (Section 1.2): U creates
  colimits unconditionally, so E must have an initial
  object.
- **Terminal coalgebra / M-type** (Section 1.2): This
  is the most demanding requirement. E must support
  the construction of the terminal coalgebra of P.
  See Section 10.2.
- **Products of coalgebras** (Section 3.2): Products
  in P-**Coalg**(E) are pullbacks over the terminal
  coalgebra Z. E must have pullbacks, and P must
  preserve them.
- **Coproducts** (Section 4.2): U creates colimits
  unconditionally. E must have finite coproducts.
- **Equalizers** (Section 5.2): P must preserve
  equalizers (which polynomial functors do). E must
  have equalizers.
- **Coequalizers** (Section 6.2): U creates colimits
  unconditionally. E must have coequalizers.
- **Pullbacks** (Section 7.2): P must preserve
  pullbacks (which polynomial functors do). E must
  have pullbacks.
- **Pushouts** (Section 8.2): U creates colimits
  unconditionally. E must have finite colimits.
- **Subobject classifier** (Section 9.1): Constructed
  from cosieves on the path category C under the
  copresheaf equivalence. E does NOT need a subobject
  classifier.
- **Exponentials** (Section 9.2): Constructed from
  the standard copresheaf formula. E does NOT need
  exponentials or Cartesian closure.

In summary, E must be finitely complete (terminal
object, pullbacks, equalizers) and finitely cocomplete
(initial object, coproducts, coequalizers), and must
support M-types for P. The subobject classifier and
exponentials of P-**Coalg**(E) are *outputs* of the
construction, not inputs.

### 10.2 M-Type Construction Requirements

The terminal coalgebra (M-type) for P can be
constructed via Adamek's chain: the limit of the
omega-op sequence

`... -> P^3(1) -> P^2(1) -> P(1) -> 1`

where 1 is the terminal object and each arrow is the
image under P of the previous one.

This requires E to have:

1. A terminal object 1.
2. Countable inverse limits (limits of omega-op
   chains).
3. P must preserve this specific limit.

For polynomial P, the chain converges in omega steps,
and polynomial functors preserve the relevant limits.

#### 10.2.1 Finitary vs. Infinitary Polynomials

The requirements depend on the polynomial's arities:

**Finitary polynomials** (each `X^{B(a)}` has B(a)
finite, e.g. `P(X) = A + X^2`): The term `X^{B(a)}`
is a finite product `X x X x ... x X`, not a function
type. The construction requires:

- Finite products (for `X^n`)
- Finite coproducts (for the sum structure)
- Countable inverse limits (for the omega-op chain)
- A natural number object (for indexing approximation
  depth)

No exponentials or Cartesian closure is needed.

**Infinitary polynomials** (some B(a) is infinite,
e.g. `P(X) = X^Nat`): The term `X^{B(a)}` is a
genuine exponential (function type `B(a) -> X`).
The construction additionally requires:

- Exponentials for the relevant B(a) (or local
  Cartesian closure for general dependent
  polynomials)
- The omega-op chain may require more than omega steps
  to converge

#### 10.2.2 The Approximation Construction

In the GebLean codebase, M-types are constructed via
consistent sequences of finite approximations
(`PolyCofixApprox` and `PolyCofixAgree` in
`PolyAlg.lean`). An element of the M-type is a
dependent pair:

- A sequence of approximations indexed by depth
  (Pi type over Nat)
- A proof that consecutive approximations agree
  (Pi type over Nat)

This construction requires:

- W-types (for the inductive approximation types)
- Dependent products (Pi types) over Nat
- Dependent sums (Sigma types) for bundling

For finitary polynomials like `P(X) = A + X^2`, the
children function at each node is a function from a
finite type (a 2-element type for binary trees),
which is equivalent to a finite product. No general
exponentials are needed.

For infinitary polynomials, the children function
would be a function from an infinite type, requiring
genuine exponentials in E.

#### 10.2.3 Summary for P(X) = A + X^2

The M-type construction for the binary product
polynomial requires E to have:

- Finite products (for `X x X`)
- Finite coproducts (for `A + (-)`)
- Terminal object
- Natural number object
- Countable inverse limits (or equivalently, dependent
  products over Nat)

E does NOT need exponentials, Cartesian closure, or a
subobject classifier. The finite arity (2) means all
branching is captured by finite products.

### 10.3 Finitary Topos Requirements

For a finitary polynomial P and base category E,
P-**Coalg**(E) is a topos when E has:

1. Finite limits (terminal object, pullbacks,
   equalizers)
2. Finite colimits (initial object, coproducts,
   coequalizers)
3. A natural number object
4. Countable inverse limits (for the M-type chain)

The coalgebra topos construction is
"topos-generating": it takes a finitely complete,
finitely cocomplete base category with NNO and
countable limits, and produces a topos with subobject
classifier and exponentials. These are constructed
from the copresheaf/cosieve structure, not inherited
from E.

---

## 11. Candidate Base Categories

Two candidates for the base category E are considered:
partial equivalence relations (PERs) on a type, and
parametric relations in the sense of Reynolds and
Wadler. The goal is to find a base category that is
self-reflective: the theory's types and morphisms
should be representable within the theory itself.

### 11.1 PER(T): Partial Equivalence Relations

Let T be a type equipped with a partial combinatory
algebra (PCA) structure. The category PER(T) has:

- **Objects**: PERs on T (symmetric, transitive
  relations; not necessarily reflexive).
- **Morphisms R -> S**: elements t of T that "track"
  the function: for all x, y, if x R y then
  `(t . x) S (t . y)`, where `(.)` is application
  in the PCA.

The quotient `T/R` (restricted to dom(R)) is the
"type represented by R."

#### 11.1.1 Categorical Properties

PER(T) for a PCA T has the following properties
(established in the realizability literature):

- Finite limits: terminal object, products, pullbacks,
  equalizers.
- Finite colimits: initial object, coproducts,
  coequalizers.
- Locally Cartesian closed (exponentials in every
  slice).
- Regular category (kernel pairs have coequalizers;
  regular epimorphisms are stable under pullback).
- NOT exact: not every equivalence relation is
  effective (is a kernel pair).
- NOT a topos: lacks a subobject classifier and power
  objects.

PER(T) is equivalent to the category of modest sets
(Mod_T), a full subcategory of the category of
assemblies Asm(T).

#### 11.1.2 Relationship to Realizability Toposes

The realizability topos RT(T) is the ex/reg completion
of Asm(T): it freely adds quotients of equivalence
relations. RT(T) IS an elementary topos. PER(T) embeds
into RT(T) but is not itself a topos.

The coalgebra topos construction could potentially
bridge this gap: if P-**Coalg**(PER(T)) is a topos
(given the requirements in Section 10.3), it would
produce topos structure from a non-topos base.

#### 11.1.3 Tree Calculus as PCA

For T = unlabeled binary trees with the tree calculus
reduction rules (triage), T forms a PCA. The tree
calculus is Turing-complete, and its intensional
nature (rules 3a-3c allow programs to inspect program
structure) gives it a self-reflection property not
present in SK-calculus.

PER(tree calculus) would provide a self-reflective
base: programs are trees, data are trees, and PERs
on trees are (in principle) representable as trees.

### 11.2 Parametric Relations (Reynolds/Wadler)

The parametric approach defines morphisms as families
satisfying the parametricity condition: preservation
of all relations.

#### 11.2.1 Structure in the Codebase

The codebase implements parametric relations at
several levels:

- `PshRelCat C` (PshRelDouble.lean): Objects are
  presheaves, morphisms are `PshRel P Q`
  (isomorphism classes of relations). The graph
  functor `pshRelGraphFunctor` embeds ordinary
  natural transformations as graph relations.
- `TypeExprCat` (ParanaturalTopos.lean): Objects are
  type expressions, morphisms are
  `ParametricFamily (.arrow T₁ T₂)`. Morphisms from
  the unit object to T correspond to
  `ParametricFamily T`.
- The parametric copresheaf category
  `PshRelSpanObj C => Type` is a Grothendieck topos.

#### 11.2.2 Categorical Properties

The parametric copresheaf topos has all the properties
needed: it is a Grothendieck topos with all limits,
colimits, W-types, subobject classifier, and
exponentials. However, it is an external construction
(over Type) rather than an internal one (within the
theory of binary trees).

The category `TypeExprCat` currently has `var`, `app`,
and `arrow` constructors but lacks product and
coproduct type expressions, so it does not yet have
all finite (co)limits.

#### 11.2.3 Functions as Graphs of Relations

A distinguishing feature of the parametric approach:
morphisms (parametric families) arise from relations
that happen to be functional. The graph functor
`pshRelGraphFunctor` is faithful, embedding the
ordinary category of functions into the relational
category. This means functions are not primitive but
are derived from the relational structure.

### 11.3 The Hybrid Approach

PERs on binary trees can serve as the base category
E, with parametric relations derived as structure
within E:

1. **Base**: PER(T) provides types (PERs on trees)
   and morphisms (tracked functions).
2. **Relations between types**: Given PERs R and S on
   T, a relation between the types `T/R` and `T/S`
   is encoded as a PER Q on `T` (using the pairing
   combinator `node(x, y)` to encode pairs) satisfying
   compatibility with R and S.
3. **Reflexive graph structure**: The identity
   extension property (R itself, viewed as a relation
   from R to R, is distinguished) gives a reflexive
   graph category structure on PER(T), recovering the
   Dunphy-Reddy / Hermida-Reddy-Robinson framework.
4. **Coalgebra topos**: Apply the P-**Coalg**
   construction to PER(T) to obtain a topos with
   full internal logic.

This hybrid approach has precedent: Sojakova, Spitters,
and van der Weide (2018) show that the Longo-Moggi PER
model arises as an instance of the abstract relational
parametricity framework.

### 11.4 Self-Representation

For the theory to be self-reflective, its types and
morphisms must be representable within itself:

- **PERs on tree calculus**: A PER is a set of pairs
  of trees. A decidable PER can be represented as a
  tree-calculus program (a tree) that decides
  membership. The intensional self-reflection of tree
  calculus (programs inspecting programs without Godel
  numbering) makes this natural.
- **Parametric relations**: Self-representation is
  provided by the subobject classifier Omega of the
  parametric copresheaf topos, but this representation
  is abstract (sieves on representables) rather than
  computational.
- **Hybrid**: PERs provide computational
  self-representation (programs as trees); the
  coalgebra topos provides logical
  self-representation (Omega, exponentials). The
  open question is whether these coincide — whether
  the coalgebra topos of the tree calculus PCA is
  equivalent to (or embeds into) the realizability
  topos RT(tree calculus).

### 11.5 Comparison

| Property | PER(T) | Parametric | Hybrid |
| - | - | - | - |
| Finite limits | Y | Y | Y |
| Finite colimits | Y | Y | Y |
| Locally cart. closed | Y | Y | Y |
| Exact | N | Y | Via coalg. topos |
| Topos | N | Y | Via coalg. topos |
| W-types | In RT(T) | Y | Via coalg. topos |
| Subobject classifier | N | Y | Via coalg. topos |
| Computational self-repr. | Y | Abstract | Y |
| Logical self-repr. | N | Y | Via coalg. topos |

### 11.6 Open Questions

- Is the coalgebra topos P-**Coalg**(PER(tree calc.))
  equivalent to (or related to) the realizability
  topos RT(tree calculus)?
- Does PER(tree calculus) have the countable inverse
  limits needed for the M-type construction?
- Can the parametric copresheaf topos be recovered as
  P-**Coalg** of some suitable base category?
- At what point in the construction does
  self-representation become possible — can the base
  category represent its own PERs before the
  coalgebra topos construction, or only after?

---

## 12. Concrete Descriptions of Two Topoi

The polynomial `P(X) = 1 + X^2` (unlabeled binary
trees, i.e. A = 1) gives rise to two topoi built from
the same raw material — binary trees — but from
opposite directions. The realizability topos is built
from *application* (composing trees as programs); the
coalgebra topos is built from *observation*
(decomposing trees as data). This section describes
each concretely and identifies the lambda-bialgebra
structure as the bridge between them.

### 12.1 The Realizability Topos RT(T)

Let T be the set of all finite binary trees (the
initial algebra W of `P(X) = 1 + X^2`), equipped with
the tree calculus reduction rules as a PCA structure.
The partial application `a . b` is defined when
reducing `a b` terminates, and equals the normal form.

#### 12.1.1 Assemblies

The category Asm(T) has:

- **Objects (assemblies)**: A pair (X, E) where X is a
  set and `E: X -> P(T) \ {empty}` assigns to each
  element a nonempty set of *realizers* — trees that
  witness or encode that element.
- **Morphisms `f: (X, E_X) -> (Y, E_Y)`**: A function
  `f: X -> Y` that is *tracked*: there exists a tree
  `r` in T such that for all `x` in X, for all
  `t` in `E_X(x)`, the application `r . t` is defined
  and `r . t` is in `E_Y(f(x))`.

Morphisms are total functions that are uniformly
computable: a single program `r` works for all inputs.
The partiality of the PCA enters through the
application operation, but morphisms themselves are
total and tracked.

The realizability topos RT(T) is the ex/reg completion
of Asm(T). The completion freely adds quotients of
equivalence relations, making the category exact.

#### 12.1.2 Concrete Structure

- **NNO**: The natural numbers N with `E(n) = {n_T}`
  where `n_T` is the tree encoding of n. Tracked
  functions `N -> N` are the total computable functions
  on natural numbers.
- **Subobject classifier Omega**: The carrier is
  `P(T)` (all sets of trees). An element S of
  `P(T)` represents the truth value "witnessed by S."
  The element `S = empty` represents false; any
  nonempty S represents a shade of true (different
  sets of witnesses give different truth values). The
  assembly structure is `E(S) = S` for `S` nonempty,
  and `E(empty) = {k}` for a fixed realizer k.
  The law of excluded middle fails: there is no tree
  that uniformly decides all propositions.
- **Exponentials**: The exponential `[A, B]` in RT(T)
  has as elements the tracked functions from A to B,
  with realizers being the tracking trees themselves.
  The internal function space consists of computable
  functions carrying their own programs as witnesses.

#### 12.1.3 Internal Logic

The internal logic of RT(T) is a form of recursive
realizability. A proposition is true if it has a
realizer — a finite binary tree that witnesses it.
This gives a constructive logic (no excluded middle)
with a computational interpretation: every proof of
existence comes with a program that computes a witness.

### 12.2 The Coalgebra Topos P-Coalg(1 + X^2)

For `P(X) = 1 + X^2`, the category P-**Coalg**
consists of deterministic binary branching transition
systems.

#### 12.2.1 Objects and Morphisms

A P-coalgebra is a pair (X, alpha: X -> 1 + X^2).
Each state x in X is classified by alpha as:

- **Leaf**: `alpha(x) = inl(*)` — the state has no
  successors.
- **Node**: `alpha(x) = inr(l, r)` — the state has
  two successor states l and r in X.

A morphism `f: (X, alpha) -> (Y, beta)` is a function
`f: X -> Y` satisfying `beta . f = (1 + f^2) . alpha`:
leaves map to leaves, and nodes map to nodes with
corresponding children mapped by f. This is a
bisimulation-respecting map.

#### 12.2.2 Terminal Coalgebra

The terminal coalgebra Z consists of all finite and
infinite binary trees. The unique morphism from any
coalgebra (X, alpha) to Z sends each state x to its
complete unfolding: the (possibly infinite) tree
obtained by repeatedly applying alpha.

The initial algebra W (finite binary trees) embeds
into Z. Every element of Z is the limit of its finite
approximations (truncations at increasing depth).

#### 12.2.3 Subobject Classifier

The carrier of Omega consists of binary trees (elements
of Z) in which every tree position is assigned a truth
value from `{True, False}`, subject to the cosieve
condition: if a position is labeled True, then all
descendant positions are also labeled True.

This gives many truth values beyond True and False:
"true below depth 3 on the left branch," "true
everywhere except the right-right-left subtree," etc.
The truth values form a Heyting algebra indexed by
tree structure.

- The element `true` has every position labeled True.
- The element `false` has every position labeled False.

#### 12.2.4 Internal Logic

Propositions in P-**Coalg** are Omega-valued:
tree-shaped truth assignments. A statement can be
"true along some branches and false along others." This
gives a branching-time logic where truth varies along
paths through the tree of observations.

#### 12.2.5 Copresheaf Perspective

Under the copresheaf equivalence `P-Coalg ~ Set^C`
(where C is the path category with objects = depth
levels and morphisms = binary navigation strings),
a copresheaf assigns to each depth n a set `F(n)` of
"views truncated at depth n," with restriction maps
ensuring compatibility. This is the approximation
view: objects are compatible families of finite
observations, and the M-type construction in the
codebase (`PolyCofixApprox`, `PolyCofixAgree`) builds
elements of Z in exactly this way.

### 12.3 Comparison

| Aspect | RT(T) | P-Coalg(1 + X^2) |
| - | - | - |
| Built from | Application | Observation |
| Objects | Sets + computability witness | Branching systems |
| Morphisms | Tracked total functions | Bisimulation maps |
| Subobj. classifier | Witness sets | Truth-labeled trees |
| Internal logic | Realizability | Branching-time |
| Carrier of Omega | P(T) (sets of trees) | Trees with truth labels |
| Partiality | In PCA application | In infinite branches |

Both topoi are constructive (excluded middle fails in
both). Both are built from binary trees, but they
capture different structure: RT(T) captures what trees
*do* as programs; P-**Coalg** captures what trees *are*
as data.

### 12.4 The Lambda-Bialgebra Bridge

The initial algebra W (finite binary trees) is
simultaneously:

- A P-**algebra**: the structure map
  `alpha: 1 + W^2 -> W` provides constructors (leaf
  and node).
- A P-**coalgebra**: the structure map
  `gamma: W -> 1 + W^2` provides destructors
  (pattern-matching on the root).

The tree calculus reduction rules define the
interaction between these two structures. When a tree
is *observed* (coalgebra) after being *constructed*
(algebra) — i.e., when pattern-matching is applied to
an application — the reduction rules specify the
result. This is the distributive law of a
lambda-bialgebra.

#### 12.4.1 The Distributive Law

In the GSOS / operational semantics framework:

- The **free monad** T of P gives the syntax side:
  building tree terms, substituting, grafting.
- The **cofree comonad** D of P gives the behavior
  side: observing, decomposing, streaming out
  structure.
- The **distributive law** `lambda: T . D -> D . T`
  defines operational semantics: given a program
  (T-term) applied to an observable state
  (D-coalgebra), one reduction step produces an
  observable state of programs.

The tree calculus reduction rules define this
distributive law. Each rule takes an algebraic
construction (application of the tree combinator to
arguments) and produces a result described in terms of
sub-observations and sub-constructions:

1. `triangle triangle x y -> x` (discard and return)
2. `triangle (triangle a) x y -> a y (x y)` (distribute
   and apply)
3. `triangle (triangle a b) x y -> a y (b y)` (fork
   case)

The interleaving of algebra (building new trees from
pieces) and coalgebra (pattern-matching on tree
structure) is the distributive law.

#### 12.4.2 Bridging the Two Topoi

The lambda-bialgebra structure on W suggests functors
between the two topoi:

- **P-Coalg -> RT(T)**: Given a coalgebra (X, alpha),
  the tree calculus can compute on X by using the
  coalgebra structure to observe states and the
  reduction rules to process observations. The tracked
  functions are those that operate on X via the
  coalgebra structure.
- **RT(T) -> P-Coalg**: Given an assembly (X, E), the
  realizer trees in E(x) are themselves elements of W,
  which embeds into the terminal coalgebra Z. The
  assembly carries coalgebraic structure inherited from
  its realizers.
- **Geometric morphism**: The lambda-bialgebra may
  mediate a geometric morphism (adjoint pair of
  functors preserving finite limits) between the two
  topoi. The direct image functor would send
  coalgebras to assemblies (extracting computational
  content from observational structure), and the
  inverse image functor would send assemblies to
  coalgebras (embedding computational witnesses into
  observational data).

The lambda-bialgebra framework is implemented in the
codebase (`LambdaBialgebra` at
`Utilities/LambdaBialgebra.lean`, `DistributiveLaw` at
`Utilities/DistributiveLaw.lean`).

#### 12.4.3 Reconciliation

The lambda-bialgebra perspective suggests that the
realizability and coalgebra topoi are not independent
alternatives but two aspects of the same structure.
The "hybrid approach" of Section 11.3 can be
understood as: PER(T) provides the computational
substrate (algebra side), the coalgebra topos
construction provides the observational/logical
substrate (coalgebra side), and the distributive law
from the tree calculus reduction rules ensures these
are compatible.

The open question of whether P-**Coalg**(PER(T)) is
equivalent to (or embeds into) RT(T) can be restated:
does the lambda-bialgebra structure on W extend to a
geometric morphism between the two topoi, and if so, is
it an equivalence?

---

## References

- Adamek, J. "Introduction to coalgebra." *Theory and
  Applications of Categories* 14 (2005).
- Adamek, J. "On final coalgebras of continuous
  functors." *Theoretical Computer Science* 366
  (2006): 170-177.
- Gambino, N. and Kock, J. "Polynomial functors and
  polynomial monads." *Mathematical Proceedings of the
  Cambridge Philosophical Society* 154 (2013).
- Hughes, J. "A study of categories of algebras and
  coalgebras." PhD thesis, Carnegie Mellon (2001).
- Jay, B. "A combinatory account of internal
  structure." *Journal of Symbolic Logic* 89 (2024).
- Klin, B. and Nachyla, B. "Presenting functors on
  many-sorted varieties and applications."
  *Information and Computation* 265 (2019).
- Lenisa, M., Power, J., and Watanabe, H.
  "Distributivity for endofunctors, pointed and
  co-pointed endofunctors, monads and comonads."
  *ENTCS* 33 (2000).
- Rutten, J.J.M.M. "Universal coalgebra: a theory of
  systems." *Theoretical Computer Science* 249 (2000).
- Sojakova, K., Spitters, B., and van der Weide, N.
  "A general framework for relational parametricity."
  arXiv:1805.00067 (2018).
- Turi, D. and Plotkin, G. "Towards a mathematical
  operational semantics." *Proceedings of LICS* (1997).
- Van den Berg, B. and de Marchi, F. "Non-well-founded
  trees in categories." *Annals of Pure and Applied
  Logic* 146 (2007).
- Van Oosten, J. *Realizability: An Introduction to
  Its Categorical Side.* Elsevier (2008).
- Worrell, J. "A note on coalgebras and presheaves."
  *Mathematical Structures in Computer Science* 15
  (2005): 475-483.
