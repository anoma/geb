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

## Book Structure

The book *Reflective Programs in Tree Calculus* (Jay, 2021)
is organized in two parts:

- **Part I** (Chapters 1-6): Tree calculus itself.
  Extensional programs (Chapter 4) treat arguments as
  opaque functions; intensional programs (Chapter 5)
  treat arguments as inspectable data structures;
  reflective programs (Chapter 6) combine both to build
  self-evaluators. Chapter 2 introduces equational
  reasoning and structural induction via arithmetic.
  Chapter 3 defines tree calculus and the triage rules.
- **Part II** (Chapters 7-10): Comparisons with other
  models of computation via rewriting theory. Chapter 7
  introduces rewriting and proves soundness. Chapter 8
  shows combinatory logic is incomplete for program
  analysis (no meaningful translation from tree calculus
  to combinatory logic). Chapter 9 introduces
  VA-calculus (a variant of lambda-calculus with
  variables and abstraction). Chapter 10 compares with
  SF-calculus (factorisation calculus).
- **Appendix A**: A critique of the Church-Turing Thesis,
  arguing that natural trees are as legitimate as natural
  numbers, and that program analysis within tree
  calculus demonstrates expressive power beyond what
  the traditional thesis accounts for.

All named theorems in the book have machine-checked
proofs in the accompanying Coq formalization.

## Type System

The paper *Typed Program Analysis without Encodings* (Jay,
PEPM '25) develops a type system for tree calculus. Tree
types have the grammar:

```text
T ::= L | S U | F U V | U -> V
```

where `L` is the leaf type, `S U` is the stem type (a stem
whose child has type `U`), `F U V` is the fork type (left
child `U`, right child `V`), and `U -> V` is the function
type. Subtyping is defined on these types.

Two derivation rules suffice for the entire type system:

1. **Leaf subtyping**: `Gamma |- leaf : T` when `L <: T`.
2. **Application**: `Gamma |- t u : V` when
   `Gamma |- t : U -> V` and `Gamma |- u : U`.

Type constants include `Bool` (the type of `tt` and `ff`),
`Nat` (Peano naturals encoded as trees), and `Omega_2`
(a fixpoint type satisfying `Omega_2 = Omega_2 -> Omega_2`).

### Verified Theorems (from the Paper)

The following theorems are stated in the paper and verified
in the accompanying Coq formalization. Coq lemma names are
given in parentheses where available.

#### Confluence and Normal Forms

- **Theorem 3.1** (`confluence_tree_calculus`):
  Reduction of triage calculus is confluent.
- **Theorem 3.2** (`head_reduction_to_factorable_form`):
  Reduction to factorable form can always begin with
  head reduction.

#### Typing of Combinators

- **Theorem 3.3** (`derive_basic`): K, S, I, and
  `swap{f}` are derivable with their expected types.
- **Theorem 3.4** (`programs_have_types`): Every
  program `p` has a canonical type `progty(p)`.

#### Lambda-Abstraction

- **Theorem 4.1** (`star_beta`): Lambda-abstraction
  satisfies beta reduction:
  `(lambda x. t) u --> {u/x} t`.
- **Theorem 4.2** (`derive_star`): Lambda-abstractions
  can be typed in context.

#### Fixpoint Combinator

- **Theorem 6.1** (`Z_red`):
  `Z{f} x --> f (Z{f}) x`
  (fixpoint combinator reduction).
- **Theorem 6.2** (`derive_Z`): The fixpoint combinator
  can be typed.

#### Programs on Trees

- **Theorem 7.1** (`derive_size`):
  `size : forall X. X -> Nat`.
- **Theorem 7.2** (`equality_of_programs`):
  `equal M N` reduces to `tt` if `M = N`, else `ff`.
- **Theorem 7.3** (`derive_equal`):
  `equal : forall X. forall Y. X -> Y -> Bool`.

#### Self-Interpreter

- **Theorem 8.1** (`branch_first_eval_iff_bf`):
  `t, u || p` iff `bf t u --> p` (self-interpreter
  correctness). The self-interpreter `bf` has type
  `forall X. forall Y. (X -> Y) -> (X -> Y)` and
  consists of 877 nodes.

#### Subtyping

- **Theorem 9.1** (`derive_subtype`): Subtyping is
  admissible.
- **Theorems 10.1-10.5**: Subtyping lemmas for
  fork-of-leaf, fork-of-stem, and fork-of-fork cases.

#### Subject Reduction

- **Theorem 10.6** (`reduction_preserves_typing`):
  If `Gamma |- t1 : T` and `t1 --> t2` then
  `Gamma |- t2 : T`.

## Equational Presentation (Book)

The book uses three equational rules named after the
combinators they encode:

```text
(K)  triangle triangle y z       = y
(S)  triangle (triangle x) y z   = y z (x z)
(F)  triangle (triangle w x) y z = z w x
```

Rule (K) deletes the third argument. Rule (S) duplicates
the third argument (with a permutation of the first two).
Rule (F) decomposes the first argument, exposing its
branches `w` and `x` to the third argument `z`.

This 3-rule equational presentation differs from the
5-rule directed reduction of the specification (see
"Reduction Rules" above). In the 5-rule version, rule (F)
is split into three cases by pattern-matching on `z`
(leaf, stem, fork). Also, the S rule in the book permutes
arguments: book has `y z (x z)` while the specification
has `x z (y z)`. The two presentations are equivalent in
the sense that they define the same computable functions
and the same notions of program and value, but the
direction and granularity of individual reduction steps
differ.

## Derived Combinators (Book, Chapter 3)

The following combinators are defined in terms of the
node operator `triangle`:

```text
K     = triangle triangle
I     = triangle (triangle triangle) (triangle triangle)
D     = triangle (triangle triangle) (triangle triangle triangle)
d{x}  = triangle (triangle x)
```

`K` satisfies `K y z = y`. `I` satisfies `I x = x`.
`D` satisfies `D x y z = y z (x z)` (same as the S rule).
The abbreviation `d{x}` represents a stem with child `x`.

The traditional S combinator (satisfying `S x y z = x z (y z)`)
is derived as:

```text
S = d{K D} (d{K} (K D))
```

### Booleans

```text
true    = K = triangle triangle
false   = K I
and     = d{K (K I)}
or      = d{K K} I
implies = d{K K}
not     = d{K K} (d{K (K I)} I)
iff     = triangle (triangle I not) triangle
```

### Pairs

```text
Pair         = triangle
first{p}     = triangle p triangle K
second{p}    = triangle p triangle (K I)
```

So `first{Pair x y} = x` and `second{Pair x y} = y`.

### Natural Numbers

The number `n` is represented as `K^n triangle` (i.e.,
`n` successive applications of `K` to `triangle`). Zero
is `triangle`; the successor of `n` is `K n`.

```text
successor   = K
isZero      = d{K^4 I} (d{K K} triangle)
predecessor = d{K^2 I} (d{K triangle} triangle)
```

`isZero` returns `true` on zero and `false` on positive
numbers. `predecessor` returns `n` given `successor n`,
and returns `triangle triangle` (= `K`) on zero.

### Fundamental Queries

The parametric triage operator `query{is0, is1, is2}`
dispatches on whether its argument is a leaf, stem,
or fork:

```text
query{is0, is1, is2} triangle     = is0
query{is0, is1, is2} (triangle x) = is1
query{is0, is1, is2} (triangle x y) = is2
```

Its definition is:

```text
query{is0, is1, is2} =
  d{K is1} (d{K^2 I} (d{K^5 is2} (d{K^3 is0} triangle)))
```

The three fundamental queries are instances:

```text
isLeaf = query{K, K I, K I}
isStem = query{K I, K, K I}
isFork = query{K I, K I, K}
```

## Programs

The following programs are defined in the paper and book.
Each is a binary tree; its size is the number of nodes.

- `isLeaf`, `isStem`, `isFork`: fundamental queries
  (Chapter 3). Test whether a tree is a leaf, stem,
  or fork respectively. Defined via the parametric
  `query` operator.
- `size`: computes the number of nodes in a tree
  (Chapter 5). Type: `forall X. X -> Nat`.
- `equal`: decides equality of two trees (Chapter 5).
  Type: `forall X. forall Y. X -> Y -> Bool`.
- `bf` (branch-first evaluator): a self-interpreter
  that evaluates tree calculus terms (Chapter 6).
  877 nodes.
  Type: `forall X. forall Y. (X -> Y) -> (X -> Y)`.
- `Z{f}` (fixpoint combinator): satisfies
  `Z{f} x --> f (Z{f}) x`. Used to define recursive
  functions.

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
