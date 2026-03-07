# Tree Calculus

## Overview

Tree calculus is a Turing-complete computational model in
which programs, data, and types are all binary trees. It
was developed by Barry Jay. The calculus has a single
combinator (triangle, written as a leaf node) and five
reduction rules (the "triage" rules). Programs can inspect
the structure of other programs without encoding —
reflection is native.

## Syntax

Terms are binary trees:

```text
t ::= leaf | node(t, t)
```

Following the tree calculus convention, `leaf` is written
as a triangle symbol, and application is left-associative:
`a b c` means `node(node(a, b), c)`.

A tree is classified by the number of children it has
received (equivalently, by the length of its left spine):

- **Leaf**: 0 children — the triangle symbol alone.
- **Stem**: 1 child — `node(leaf, x)`, written
  `triangle x`.
- **Fork**: 2 children — `node(node(leaf, x), y)`,
  written `triangle x y`.

## Reduction Rules

The five triage reduction rules define computation.
Each rule fires when a fork is applied to an argument
(i.e., three children are present). The first two rules
give S and K combinator behavior; the last three
(triage proper) provide structural case analysis.

```text
1. triangle triangle y z        --> y
2. triangle (triangle x) y z    --> x z (y z)
3. triangle (triangle w x) y triangle       --> w
4. triangle (triangle w x) y (triangle u)   --> x u
5. triangle (triangle w x) y (triangle u v) --> y u v
```

Rules 1-2 encode the K and S combinators of combinatory
logic, establishing Turing completeness. Rules 3-5
(triage) enable reflection: a program can inspect whether
its argument is a leaf (rule 3), stem (rule 4), or fork
(rule 5), and dispatch accordingly. This case analysis
operates directly on the tree structure of the argument,
without any encoding.

### Reduction as Case Analysis

Rules 3-5 can be read as a single case-analysis
operator. Given a fork `triangle w x` applied to
arguments `y` and `z`:

- If `z` is a leaf: return `w`.
- If `z` is a stem `triangle u`: return `x u`.
- If `z` is a fork `triangle u v`: return `y u v`.

The three branches `w`, `x`, `y` correspond to the
leaf, stem, and fork cases respectively, giving a
"triage" on the structure of `z`.

## Connection to Polynomial Functors

Binary trees are the initial algebra (W-type) of the
polynomial endofunctor `P(X) = 1 + X^2` on Set, or
equivalently, `polyProd X` (the product polynomial
`B mapsto B *_X B`) with unit leaves via
`polyTranslate (overTerminal X) (polyProd X)` in the
GebLean codebase.

The leaf/stem/fork classification corresponds to the
binary-to-finite-branching isomorphism described in the
design document: a binary tree `T` is isomorphic to a
root label together with a list of children
`1 *_X List(T)`, and the triage rules perform case
analysis on lists of length 0, 1, or 2.

Primitive recursion over trees is the catamorphism
(`polyFixFold`) into a `P`-algebra. The tree calculus
extends this with general recursion (via the S combinator)
and structural case analysis (via triage).

## Self-Reflection

Tree calculus is self-reflective: programs can inspect
the structure of other programs (and of themselves)
using the triage rules, without Gödel encoding or any
other representation change. A program *is* a binary
tree, and triage analyzes binary trees. This makes
meta-programming native:

- A self-evaluator can be written as a tree that
  evaluates other trees according to the reduction
  rules.
- A program recognizer can be written as a tree that
  inspects whether another tree belongs to a given
  syntactic class (e.g., the primitive-recursive
  fragment).
- Program transformations (optimizers, compilers) are
  trees operating on trees.

This property is the basis for the bootstrapping
strategy described in the design document: the
primitive-recursive self-recognizer is a tree-calculus
program that decides membership in the
primitive-recursive fragment of tree calculus.

## Partial Combinatory Algebra

The set of binary trees, equipped with the reduction
rules as a partial application operation, forms a
partial combinatory algebra (PCA). The PCA structure
gives rise to:

- **Assemblies**: sets whose elements carry tree
  realizers (computational witnesses).
- **The realizability topos**: the ex/reg completion
  of the assembly category, providing full
  intuitionistic higher-order logic with computational
  content.

See the design document sections "Universe B:
Realizability Topos" and "12.1 The Realizability
Topos RT(T)" for details.

## References

### Specification and Implementations

- [Tree Calculus homepage](https://treecalcul.us/)
- [Specification](https://treecalcul.us/specification/)
  — formal definition of syntax and reduction rules
- [Example implementations](https://treecalcul.us/implementation/)
  — includes a self-evaluator, OCaml and JavaScript
  implementations, and links to Haskell, Rust, and
  regular-expression evaluators

### Book and Formalization

- [*Reflective Programs in Tree Calculus* (book PDF)](https://github.com/barry-jay-personal/tree-calculus/blob/master/tree_book.pdf)
  — Barry Jay's book covering the theory, including
  self-evaluation, self-recognition, operational
  semantics, and connections to lambda calculus
- [Coq formalization and book source](https://github.com/barry-jay-personal/tree-calculus)
  — machine-checked proofs of correctness for the
  reduction rules, confluence, and related properties

### Introductions and Blog Posts

- [A Visual Introduction to Tree Calculus](https://olydis.medium.com/a-visual-introduction-to-tree-calculus-2f4a34ceffc2)
  — illustrated reduction rules with diagrams
- [Tree Calculus in Action: Fusion Analysis](https://olydis.medium.com/tree-calculus-in-action-fusion-analysis-64ca5c2ffbee)
  — fusion optimization for tree calculus programs
- [Wolfram Language implementation](https://community.wolfram.com/groups/-/m/t/2316020)
  — tree calculus in Mathematica
- [Author's blog post index](https://github.com/barry-jay-personal/blog/tree/main)
  — Barry Jay's blog posts on tree calculus and related
  topics

### Related Design Documents

- [TermCat design](plans/2026-03-06-termcat-design.md)
  — categories from binary trees, bootstrapping
  strategy, internal logic and self-reflection
- [Polynomial algebra and coalgebra categories](polynomial-algebra-coalgebra-categories.md)
  — P-Alg and P-Coalg universal properties,
  realizability topos, coalgebra topos, and the
  lambda-bialgebra bridge (Section 12)
- [M-types from W-types walkthrough](m-types-from-w-types-walkthrough.md)
  — polynomial functor infrastructure, free monad and
  cofree comonad constructions
- [Coalgebra-copresheaf equivalence](./../.session/docs/coalgebra-copresheaf-math.md)
  — mathematical details of `Coalg(P) ~ Set^{C_P}`
