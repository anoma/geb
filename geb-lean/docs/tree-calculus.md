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

## Self-Evaluators (Book, Chapter 6)

Four evaluation strategies are defined for tree calculus,
each with a corresponding self-evaluator program:

1. **Branch-first evaluation** (`M, N => P`): all
   branches are evaluated before the root. Analogous
   to eager evaluation. The self-evaluator `bf`
   satisfies: if `M, N => P` then `bf M N = P`
   (Theorem 15, `branch_first_eval_to_bf`). The
   evaluator `bf` can be applied to itself.
2. **Root evaluation** (`M => P`): evaluates just enough
   to determine whether the root is a leaf, stem, or
   fork. Produces factorable forms whose branches may
   contain unevaluated computations, represented via
   *quotation*. The self-evaluator `root` satisfies:
   if `M => P` then `root M = P`
   (Theorem 16, `root_eval_to_root`).
3. **Root-and-branch evaluation** (`M Downarrow P`):
   root evaluation followed by recursive branch
   evaluation. The self-evaluator `rb` satisfies:
   if `'M Downarrow P` then `rb 'M = P`
   (Theorem 17, `rb_eval_implies_rb`).
4. **Root-first evaluation**: root-and-branch evaluation
   applied to quotations of programs. The self-evaluator
   `rf` satisfies: if `'(M N) Downarrow P` then
   `rf M N = P`
   (Theorem 18, `root_first_eval_to_rf`).

Branch-first evaluation is deterministic: for each
application there is a unique rule that can be applied
(Theorem 14, `branch_first_eval_program`: if
`M, N => P` then `P` is a program).

### Quotation

Quotation of a program `M` produces a binary tree with
no stems (all applications become forks of quotations):

```text
'triangle = triangle
'(M N)    = triangle ('M) ('N)
```

Quotation of arbitrary computations is not definable as
a program (it does not preserve evaluation). Quotation
of programs is definable:

```text
quote = Y_2{lambda* x. isStem x
            (triangle (x triangle) (K triangle)
              (lambda* q. (lambda* x1. K (K (q x1)))))
            (triangle x (K triangle)
              (lambda* x1. lambda* x2.
                lambda q. triangle (K (q x1)) (q x2)))}
```

### Construction of bf

The branch-first self-evaluator is structured as:

```text
bf = Y_2{onFork{triage{bf_leaf,
                        bf_stem{eager},
                        bf_fork}}}
```

where `onFork{f}` leaves leaves and stems unchanged
and applies `f` to the branches of forks. The three
triage cases implement the K, S, and F rules
respectively, with `eager` forcing evaluation of
arguments before applying the rule.

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
PEPM '25) develops a type system for tree calculus. The
system is distinctive in several respects: programs are
typed as both data structures (via tree types) and
functions (via function types), with a subtyping relation
connecting the two views. The expressive power of the
system is determined entirely by the choice of subtyping
axioms. Two type derivation rules suffice for all typing
judgments; the subtyping relation carries the entire
computational content.

The system is developed in stages across the paper.
Section 2 types traditional combinatory logic (SK-calculus)
with subtyping. Section 3 extends to triage calculus.
Sections 4-8 introduce extensions (lambda-abstraction,
booleans and naturals, fixpoints, generic queries, and
self-interpretation), each requiring additional subtyping
axioms. Section 9 presents the combined system. Section 10
proves subject reduction. The account below follows the
combined system of Section 9, noting which axioms are
needed for which features.

### Type Grammar

The full type grammar (Section 9) is:

```text
T, U, V  ::=  L  |  S U  |  F U V  |  U -> V
             |  X  |  forall X. T  |  A T
```

The type formers are:

- `L` — leaf type. The type of the leaf node (triangle).
- `S U` — stem type. The type of a stem whose child
  has type `U`. A stem is a tree of the form
  `triangle M` where `M : U`.
- `F U V` — fork type. The type of a fork whose left
  child has type `U` and right child has type `V`. A
  fork is a tree of the form `triangle M N` where
  `M : U` and `N : V`.
- `U -> V` — function type. The type of a function
  from `U` to `V`.
- `X` — type variable.
- `forall X. T` — universally quantified type.
  Quantification over type variables, as in System F.
  Instantiation is handled by subtyping (see below),
  not by a separate elimination rule.
- `A T` — "as-function" type. Records that `T` is
  expected to eventually become a function type. Used
  to type the self-interpreter (see the section on
  the A type former below).

The first three formers (`L`, `S`, `F`) are the *tree
type formers*: they describe the structure of a program
viewed as data. The function type `U -> V` describes a
program viewed as a function. The subtyping relation
connects these two views.

### Tree Types and progty

Every program (closed normal form) `p` has a canonical
*tree type* `progty(p)`, defined by structural recursion:

```text
progty(triangle)    =  L
progty(triangle q)  =  S progty(q)
progty(triangle q r) = F progty(q) progty(r)
```

The tree type records the exact shape of a program: whether
it is a leaf, a stem (and the type of its child), or a
fork (and the types of both children). Every program is
typeable at its tree type:

- **Theorem 3.4** (`programs_have_types`):
  `p : progty(p)` for every program `p`.

### Subtyping Relation

The subtyping relation `U < V` (read "`U` is a subtype
of `V`") is the central mechanism of the type system. Each
reduction rule of the calculus inspires a subtyping axiom
that captures when a tree type can be used as a function
type.

#### Structural Subtyping Axioms

The first three axioms describe how applying arguments to a
tree builds up its tree type:

```text
L      <  U -> S U
S U    <  V -> F U V
F L U  <  V -> U
```

The first says that a leaf, when given an argument of type
`U`, produces a stem `S U`. The second says that a stem
`S U`, when given an argument of type `V`, produces a
fork `F U V`. The third is the K-combinator rule:
`K = triangle triangle` has tree type `F L L`; the
axiom `F L U < V -> U` says that `K u` returns `u`
regardless of the next argument. More generally, any fork
whose first component is a leaf acts as a K-like
projection.

#### Reduction-Inspired Subtyping Axioms

Each reduction rule produces a subtyping axiom. The
five triage reduction rules yield:

**Rule 1 (K rule)**: `triangle triangle y z --> y`.
Since `K = triangle triangle : F L L`, applying `K`
to `y : V` gives `F L V`, and the next application
must return `y`. This is captured by `F L U < V -> U`
(axiom 3 above).

**Rule 2 (S rule)**:
`triangle (triangle x) y z --> x z (y z)`.
Given `x : U -> V -> T`, `y : U -> V`, `z : U`, the
result `x z (y z)` has type `T`. The subtyping axiom
is:

```text
F (S (U -> V -> T)) (U -> V)  <  U -> T
```

**Rules 3-5 (triage rules)**:
`triangle (triangle w x) y z --> triage(w, x, y)`
where the result depends on the structure of `z`. The
three cases yield:

```text
F (F U V) W        <  L -> U
F (F U (V1 -> V2)) W  <  S V1 -> V2
F (F U V) (W1 -> W2 -> W3)  <  F W1 W2 -> W3
```

Rule 3 (leaf case): if `z` is a leaf, return `w`.
Rule 4 (stem case): if `z` is a stem `triangle u`,
return `x u`. Rule 5 (fork case): if
`z` is a fork `triangle u v`, return `y u v`.

#### Quantifier Distribution Axioms

Quantified types distribute over the type formers:

```text
forall X. S U       <  S (forall X. U)
forall X. F U V     <  F (forall X. U) (forall X. V)
forall X. A U       <  A (forall X. U)
forall X. U -> V    <  (forall X. U) -> (forall X. V)
```

Instantiation and generalization:

```text
forall X. T    <  {U/X} T
T              <  forall X. T   (if X is not free in T)
```

These rules handle parametric polymorphism. The
instantiation rule `forall X. T < {U/X} T` replaces a
separate elimination form: instead of explicit type
application, subtyping performs instantiation.

#### Fixpoint Subtyping

The fixpoint type `Omega_2` is defined as
`progty(omega_2)` where `omega_2` is the fixpoint
combinator component. Its subtyping axiom is:

```text
Omega_2  <  Omega_2 -> Fix (forall X_vec. U -> V)
```

where `Fix T = (T -> T) -> T` and `X_vec` is a
sequence of type variables. This axiom allows typing
recursive functions defined via `Z{f}`. Without it,
only terminating (primitive-recursive) functions are
typeable.

#### Closure Conditions

The subtyping relation is the smallest relation
satisfying the axioms above and closed under:

- **Reflexivity**: `T < T`.
- **Transitivity**: if `T < U` and `U < V` then
  `T < V`.
- **Contravariance of function types**: if
  `U2 < U1` and `V1 < V2` then
  `U1 -> V1 < U2 -> V2`.

#### Minimal Collection of Axioms

The paper's Figure 3 presents a minimal collection of
subtyping axioms for the base system (without
quantifiers, A types, or fixpoint types):

```text
L                                  <  U -> S U
S U                                <  V -> F U V
F L U                              <  V -> U
F (S (U -> V -> T)) (U -> V)      <  U -> T
F (F U V) W                        <  L -> U
F (F U (V1 -> V2)) W              <  S V1 -> V2
F (F U V) (W1 -> W2 -> W3)        <  F W1 W2 -> W3
```

The full collection (Figure 10) adds the quantifier
distribution axioms, the fixpoint axiom, the A type
axioms (see below), and the specialized axioms for
typing the self-interpreter's components.

### Type Derivation Rules

Only two derivation rules are needed for the entire
type system:

**Leaf rule**: A leaf can have any type that `L` is a
subtype of.

```text
  Leaf < T
-----------
 triangle : T
```

**Application rule**: If the function has type `U -> V`
and the argument has type `U`, the result has type `V`.

```text
 M : U -> V    N : U
----------------------
      M N : V
```

With term variables and type contexts (Section 4), two
more rules are added:

**Variable rule**: A variable has any supertype of its
context assignment.

```text
 Gamma(x) < T
--------------
 Gamma |- x : T
```

**Lambda rule**: Lambda-abstraction builds function
types.

```text
 Gamma, x : U |- t : T
------------------------
 Gamma |- lambda x. t : U -> T
```

The general subsumption rule (if `M : U` and `U < V`
then `M : V`) is not a separate derivation rule; it
follows by induction on the structure of `M`:

- **Theorem 9.1** (`derive_subtype`): For all type
  contexts `Gamma` and terms `t`, if
  `Gamma |- t : T1` and `T1 < T2` then
  `Gamma |- t : T2`.

### Type Constants

Type constants for booleans and natural numbers are
defined as quantified function types, following
System F:

```text
Bool  =  forall X. X -> X -> X
Nat   =  forall X. (X -> X) -> (X -> X)
```

The subtyping of `Bool` supports conditionals:
`Bool < U -> U -> U` for any `U`. The subtyping of
`Nat` supports iterators: `Nat < (U -> U) -> (U -> U)`
for any `U`.

The representation of standard values is:

```text
true   =  K             : Bool
false  =  K I           : Bool
zero   =  K I           : Nat
succ   =  S_1{S_1{K triangle}{S_1{K triangle} K}}
                         : Nat -> Nat
```

Note that `false` and `zero` are both represented by
`K I`. Tagging (see Section 5 of the paper) can
disambiguate them.

### Typing of Standard Combinators

The subtyping axioms suffice to derive the expected
types of all standard combinators:

- **Theorem 3.3** (`derive_basic`): For all types
  `U`, `V`, and `T`:

```text
K         :  U -> V -> U
S         :  (U -> V -> T) -> (U -> V) -> (U -> T)
I         :  T -> T
swap{f}   :  V -> U -> T       (given f : U -> V -> T)
wait{M,N} :  V -> T
              (given M : U -> V -> T and N : U)
wait2{M,N,P} : W -> T
              (given M : U -> V -> W -> T,
                     N : U, P : V)
```

### The A Type Former

The `A T` type ("as-function type") is introduced in
Section 8 to address a specific technical obstacle in
typing the breadth-first self-interpreter `bf`.

#### Motivation

When `bf` encounters a fork `triangle u v`, it must
recursively evaluate both branches: `bf (bf u z) (bf v z)`.
The types of `bf u z` and `bf v z` are not known to be
function types at the point where `bffs` (the stem handler
of `bf`) is being typed — the typing of `bffs` cannot
"look ahead" to see that its results will eventually be
applied. The `A T` type records the expectation that `T`
will become a function type once enough information is
available.

#### Subtyping Rules for A

```text
T          <  A T
A (U -> V) <  U -> V
```

The first rule says that any term of type `T` also has
type `A T` — the `A` wrapper can always be added. The
second says that if `A` wraps a function type, the `A`
can be removed — `A (U -> V)` is a function type.

Together, these rules allow deferred resolution: a
subexpression can be given type `A T` initially, and
once the context establishes that `T` is a function
type, the `A` dissolves.

#### Additional Axioms for bf

The self-interpreter's components require two further
subtyping axioms connecting `A` types with tree types:

```text
F (S (bffsa U)) (A V)
    <  A (F (S U) V)

F (F U (A V)) (bfffa (A W))
    <  A (F (F U V) W)
```

where `bffsa` and `bfffa` are defined in terms of
the types of `bf`'s subcomponents:

```text
bfffa U = F (S (F L (forall X. forall Y.
            (X -> A X))) (A U))
bffsa U = F (S (F L (forall X. forall Y.
            (X -> Y) -> (X -> Y))))
            (bfffa (A U))
```

With these axioms, `bf` receives the type:

```text
bf : forall X. forall Y. (X -> Y) -> (X -> Y)
```

This type says that `bf` takes a function and returns
a function of the same type. The self-interpreter can
be applied to itself (`bf bf`), and the type is
preserved.

### Covariance and the General Triage Rule

The subtyping rules for triage (rules 3-5) have a
general form that uses covariance. Define abbreviations:

```text
AsLf{Z, T}  =  {L / Z} T
AsSm{Z, T}  =  forall X. X -> {S X / Z} T
AsFk{Z, T}  =  forall X. forall Y.
                  X -> Y -> {F X Y / Z} T
                  (if X, Y are not free in T)
```

Then the general triage subtyping rule is:

```text
F (F AsLf{Z,T} AsSm{Z,T}) AsFk{Z,T}
    <  forall Z. Z -> T
```

provided `Z` appears *covariantly* in `T`. Covariance
is defined in the standard way (positive position in
function types). This general rule subsumes all three
triage axioms as special cases and captures the
polymorphism of generic queries.

For example, `isLeaf` has a triage type where `T` is
instantiated to `Bool`, and `size` has a triage type
where `T` is instantiated to `Nat`.

### Typing of Generic Queries

Generic queries have types of the form
`forall X. X -> Bool` (or `-> Nat`, etc.). Their typing
uses the general triage subtyping rule. The queries
are:

```text
isLeaf  =  triage{true, K false, K^2 false}
isStem  =  triage{false, K true, K^2 false}
isFork  =  triage{false, K false, K^2 true}
```

Each has type `forall X. X -> Bool`. The program `size`
has type `forall X. X -> Nat`.

- **Theorem 7.1** (`derive_size`):
  `size : forall X. X -> Nat`.

The program `equal` has a more general type:

- **Theorem 7.3** (`derive_equal`):
  `equal : forall X. forall Y. X -> Y -> Bool`.

The generality from `forall X. X -> Bool` to
`forall X. forall Y. X -> Y -> Bool` is needed because
equality compares two trees that may have different
types.

### Typing of Fixpoint Functions

Recursive functions are constructed via `Z{f}`, which
satisfies:

- **Theorem 6.1** (`Z_red`):
  `Z{f} x --> f Z{f} x`.

The typing of `Z{f}` uses the `Omega_2` fixpoint type.
Given `f` of type
`(forall X_vec. U -> V) -> (forall X_vec. U -> V)`,
the fixpoint combinator produces:

- **Theorem 6.2** (`derive_Z`): For all type contexts
  `Gamma`, sequences of type variables `X_vec`, and
  types `U` and `V`:

```text
 Gamma |- f : (forall X_vec. U -> V)
                -> (forall X_vec. U -> V)
-----------------------------------------
 Gamma |- Z{f} : forall X_vec. U -> V
```

### Typing of Lambda-Abstraction

Lambda-abstraction is defined as a macro (not a
primitive) using star abstraction (see the Abstraction
section above). The typing rule for lambda-abstraction
follows:

- **Theorem 4.1** (`star_beta`):
  `(lambda x. t) u --> {u/x} t`.
- **Theorem 4.2** (`derive_star`): For all type
  contexts `Gamma`, term variables `x`, and terms `t`:

```text
 Gamma, x : U |- t : T
-----------------------
 Gamma |- lambda x. t : U -> T
```

### Subject Reduction

The culminating property of the type system: reduction
preserves typing.

- **Theorem 10.6** (`reduction_preserves_typing`):
  For all type contexts `Gamma`, terms `t1` and `t2`,
  and types `T`: if `Gamma |- t1 : T` and
  `t1 --> t2` then `Gamma |- t2 : T`.

The proof proceeds by examining each reduction rule
and showing that the corresponding subtyping axiom
captures the type-preservation argument. The five
triage reduction rules yield five intermediate
theorems:

- **Theorem 10.1** (`subtype_from_fork_of_leaf_to_fun`):
  `F L V < Z -> T` implies `V < T` for all `V`,
  `Z`, `T`.
- **Theorem 10.2**
  (`subtype_from_fork_of_stem_to_funty`):
  If `F (S U) V < Z -> T` then there exists `Y`
  such that `U < Z -> Y -> T` and `V < Z -> Y`.
- **Theorem 10.3** (`subtype_from_fork_of_fork_of_leaf`):
  If `F (F W U) V < L -> T` then `W < T`.
- **Theorem 10.4** (`subtype_from_fork_of_fork_of_stem`):
  If `F (F W U) V < S Z -> T` then `U < Z -> T`.
- **Theorem 10.5** (`subtype_from_fork_of_fork_of_fork`):
  If `F (F W U) V < F Z1 Z2 -> T` then
  `V < Z1 -> Z2 -> T`.

### Properties of the Type System

The type system has several distinctive properties:

1. **Every program is typeable.** The tree type
   `progty(p)` provides a canonical type for every
   program `p`. Unlike many type systems, there are no
   untypeable normal forms.

2. **Subtyping encodes operational semantics.** Each
   reduction rule of the calculus corresponds to a
   subtyping axiom. The proof that reduction preserves
   typing recapitulates the correctness proof of each
   combinator.

3. **Two derivation rules suffice.** The leaf rule and
   the application rule generate all typing judgments.
   The entire complexity of the system resides in the
   subtyping relation.

4. **Parametric polymorphism via subtyping.** Universal
   quantification is introduced by subtyping
   (`T < forall X. T` when `X` is not free in `T`)
   and eliminated by subtyping
   (`forall X. T < {U/X} T`). No separate type-level
   lambda or application is needed.

5. **The fixpoint axiom is isolable.** Removing the
   `Omega_2` subtyping axiom restricts the system to
   terminating (primitive-recursive) programs. The
   other axioms continue to type all fold-definable
   functions.

6. **The A type former is conservative.** Adding or
   removing the `A` type axioms affects only the
   typeability of the self-interpreter and similar
   programs. Other typings are not affected.

### Type Inference (Open)

The paper does not address type inference. The author's
blog posts (January-March 2025) explore this question
and identify several obstacles:

- The subtyping relation makes inference harder than
  in Hindley-Milner: checking `T < U -> V` and
  inferring the result type `V` are mutually
  recursive.
- Each program has a *principal type* (its tree type
  `progty(p)`), but the relationship between principal
  types and function types is mediated by subtyping,
  which may not be decidable in the full system.
- The additional axioms for generic queries (`A`
  types, covariance) add further layers to the
  inference problem.
- A unique-type approach (where every combinator has
  exactly one inferred type) is under investigation
  but faces the difficulty that a single combinator
  may serve as both data and function.

Whether type inference is decidable for the full system
remains an open question.

### Confluence and Normal Forms (from the Paper)

- **Theorem 3.1** (`confluence_tree_calculus`):
  Reduction of triage calculus is confluent.
- **Theorem 3.2** (`head_reduction_to_factorable_form`):
  Reduction to factorable form can always begin with
  head reduction.

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
- `wait{x, y}`: delays application of `x` to `y`
  until a third argument is supplied (Chapter 4).
  `wait{x, y} z = x y z`. Definition:
  `wait{x, y} = d{I} (d{K y} (K x))`.
- `Y_2{f}` (stable fixpoint function): satisfies
  `Y_2 f x = f x (Y_2 f)` (Chapter 4, Theorem 10).
  Unlike the standard Y combinator, `Y_2{f}` is
  always a program (binary tree in normal form) when
  `f` is. Built from `Z{swap{f}}` using `wait` and
  `self_apply = d{I} I`.
- `plus`: addition of natural numbers, defined via
  `Y_2` (Chapter 4).
- `list_map`, `list_foldleft`, `list_foldright`:
  standard list operations, defined via `Y_2`
  (Chapter 4).

## Abstraction (Book, Chapter 4)

Bracket abstraction `[x]t` and star abstraction
`lambda* x. t` provide variable binding in tree
calculus. Both satisfy the beta rule:

```text
([x]t) u = {u/x} t       (Theorem 8, bracket_beta)
(lambda* x. t) u = {u/x} t  (Theorem 9, star_beta)
```

Bracket abstraction is defined by:

```text
[x] x   = I
[x] y   = K y        (y != x)
[x] O   = K O        (O an operator)
[x] u v = d{[x]v} ([x]u)
```

Bracket abstractions are always stable (none of the
evaluation rules can fire on them), but the output can
be up to 5 times larger than the input: if `M` has size
`k`, then `[x]M` has size `5k - 2`.

Star abstraction optimizes bracket abstraction by
exploiting variable occurrence:

```text
lambda* x. t   = K t           (x not in t)
lambda* x. t x = t             (x not in t)
lambda* x. x   = I
lambda* x. t u = d{lambda* x. u} (lambda* x. t)
                                   (otherwise)
```

Star abstractions may require evaluation (unlike bracket
abstractions), but produce smaller output. Any combinator
`M` is also `lambda* x. M x`, so star abstractions
subsume combinators.

### Waiting and Stable Fixpoints

The `wait` combinator delays evaluation: `wait{M, N}`
must receive a third argument `P` before `M` is applied
to `N`. This is used to define stable fixpoint functions.

The standard Y combinator satisfies `Y f = f (Y f)` but
`Y f` is not a program (it has no normal form). The
`Y_2` combinator instead satisfies `Y_2 f x = f x (Y_2 f)`
(Theorem 10, `fixpoint_function`), and `Y_2{f}` is
always a program when `f` is.

Construction:

```text
self_apply = d{I} I
Z{f}       = wait{self_apply,
               d{wait1{self_apply} (K f)}}
swap{f}    = d{K f} d{d{K} (K triangle)} (K triangle)
Y_2{f}     = Z{swap{f}}
```

## Intensional Programs (Book, Chapter 5)

Intensional programs query the internal structure of
their arguments. Extensional programs (Chapter 4) treat
arguments as opaque functions; intensional programs treat
them as inspectable data structures.

### Verified Theorems (Book, Chapter 5)

- **Theorem 11** (`equal_programs`):
  `equal M M = K` for all programs `M`.
- **Theorem 12** (`unequal_programs`):
  If `M` is not identical to `N` then
  `equal M N = K I` for all programs `M` and `N`.
- **Theorem 13** (`tree_calculus_supports_tagging`):
  Tree calculus supports tagging: there exist term
  forms `tag` and `getTag` such that
  `tag{t, f} x = f x` and `getTag(tag{t, f}) = t`.

### Tagging

A tag attaches metadata `t` to a function `f` without
affecting its functional behavior:

```text
tag{t, f}  = d{t} (d{f} (K K))
getTag     = lambda* p. first{first{p} triangle}
untag      = lambda* x. fst{fst{snd{x}} triangle}
```

Tags can carry type information, comments, or any other
data. A tagged fixpoint combinator `Y_2t{t, f}` threads
tags through recursive calls.

### Triage Combinator

The `triage_comb` operator generalizes the fundamental
queries by accepting three function arguments `f0`, `f1`,
`f2` for the leaf, stem, and fork cases:

```text
triage{f0, f1, f2} triangle     = f0
triage{f0, f1, f2} (triangle x) = f1 x
triage{f0, f1, f2} (triangle x y) = f2 x y
```

The programs `size` and `equal` can be re-expressed
using `triage`.

### Simple Types (Internal)

The book defines simple types internally as trees:

```text
T ::= o | iota | T -> T

[o]       = triangle "Bool"     (stem)
[iota]    = triangle "Nat"      (stem)
[U -> T]  = triangle [U] [T]    (fork)
```

A typed term `t^T` is represented as `tag{T, t}`.
Type checking is defined as a tree-calculus program
`type_check` that verifies function types match argument
types using `equal` on the type tags. Typed application
`typed_app` applies the untagged functions and re-tags
the result.

### Pattern Matching

Pattern-matching functions have the form:

```text
p1 => s1 | p2 => s2 | ... | pk => sk | r
```

Each extension `p => s | r` is defined as
`wait{p => s, r}`, so extensions are always programs.
Pattern cases are defined by structural induction on
patterns `p, q ::= x | triangle | triangle p | triangle p q`.

### Data Structures

Lists use the leaf/fork convention:

```text
nil       = triangle           (leaf)
cons h t  = triangle h t       (fork)
```

Bits are `0 = triangle` and `1 = K triangle`. Bytes
are 8-tuples of bits. ASCII characters are represented
by their bytecodes. Strings are lists of characters.

## Rewriting Theory (Book, Chapter 7)

Chapter 7 orients the equational rules as directed
rewriting rules and develops the metatheory of reduction.

### Reduction and Simultaneous Reduction

Reduction `-->` is the compatible closure of the three
oriented rules (K, S, F). Simultaneous reduction `-->`
(written `s_red1` in the Coq formalization) allows
multiple redexes to be contracted in a single step,
including within subterms.

### Verified Theorems (Book, Chapter 7)

- **Theorem 32** (`diamond_s_red1`):
  Simultaneous reduction has the diamond property:
  if `M --> N1` and `M --> N2` (by simultaneous
  reduction), then there exists `P` with `N1 --> P`
  and `N2 --> P`.
- **Theorem 33** (`confluence_tree_calculus`):
  Reduction of tree calculus is confluent. (Follows
  from the diamond property of simultaneous reduction,
  since simultaneous reduction contains single-step
  reduction and is contained in its transitive closure.)
- **Corollary 34**: Every tree has at most one normal
  form.
- **Theorem 35** (`halting_problem_insoluble`):
  The halting problem is insoluble in tree calculus:
  there is no tree-calculus program that decides whether
  an arbitrary program halts. (Proved by diagonalization.)
- **Theorem 36** (`standardization`):
  Standard reduction theorem. Every reduction sequence
  can be rearranged into a standard sequence (head
  reductions first, then internal reductions).
- **Corollary 37** (`leftmost_reduction`):
  If a term has a normal form, leftmost outermost
  reduction finds it.
- **Theorem 38** (`head_reduction_to_factorable_form`):
  Every program can be head-reduced to a factorable form
  (leaf, stem, or fork).

### Self-Evaluator Completeness

- **Theorem 40** (`bf_to_branch_first_eval`):
  Converse of branch-first evaluator soundness: if
  `bf M N` reduces to a program `P`, then `M, N => P`
  by branch-first evaluation.
- **Corollary 41** (`branch_first_eval_iff_bf`):
  Branch-first evaluation is equivalent to `bf`:
  `M, N => P` if and only if `bf M N -->* P`.
- **Theorem 42** (`root_eval_iff_root`):
  Root evaluation is equivalent to `root`:
  `M => P` if and only if `root M -->* P`.
- **Theorem 43** (`rb_eval_iff_rb`):
  Root-and-branch evaluation is equivalent to `rb`:
  `'M Downarrow P` if and only if `rb 'M -->* P`.
- **Theorem 44** (`rf_eval_iff_rf`):
  Root-first evaluation is equivalent to `rf`:
  `'(M N) Downarrow P` if and only if `rf M N -->* P`.

Each completeness result shows that the self-evaluator
does no more and no less than its corresponding
evaluation strategy.

## Incompleteness of Combinatory Logic (Book, Chapter 8)

SK-calculus has reduction rules `K x y --> x` and
`S x y z --> x z (y z)`. It is combinatorially complete
(every combinator can be represented) and confluent
(Theorem 45). However, it cannot decide equality of its
own programs: there is no SK-term `eq` such that
`eq M M x y -->* x` for all programs `M` and
`eq M N x y -->* y` when `M` is not identical to `N`.

The reason is that SK-calculus cannot separate identity
programs. An *identity program* is a program `M` such
that `M x -->* x`. A *separator* for programs `M1`, `M2`
is a program `s` with `s M1 x y --> x` and
`s M2 x y --> y`. Both `SKK` and `SKS` are identity
programs, but they cannot be separated in SK-calculus.

A *meaningful translation* between applicative rewriting
systems preserves: (1) computational equality, (2)
application structure, (3) values (programs translate to
programs), and (4) variables. There is a meaningful
translation from SK-calculus to tree calculus (mapping
`S` to `S` and `K` to `K`), but no meaningful translation
in the other direction.

### Verified Theorems (Book, Chapter 8)

- **Theorem 45** (`confluence_SK`):
  Reduction of SK-calculus is confluent.
- **Lemma 46** (`pentagon_id_red_s_red1`):
  Identity reduction and simultaneous reduction satisfy
  a pentagon property.
- **Lemma 47** (`pentagon_id_red_s_red`):
  Generalization of Lemma 46 to multiple parallel
  reductions.
- **Theorem 48** (`no_separable_identities_in_SK`):
  Identity programs do not have separators in
  SK-calculus. (Proved by applying the pentagon lemma
  to show that any separator for two identity programs
  would force its two outputs to share a reduct,
  contradicting confluence.)
- **Theorem 49**
  (`equality_of_programs_is_not_definable_in_SK`):
  There is no equality term in SK-calculus. (Follows
  from Theorem 48, since `eq` applied to `SKK` and
  `SKS` would be a separator.)
- **Definition 50**: A *meaningful translation* between
  applicative rewriting systems preserves equality,
  application, values, and variables.
- **Theorem 51**
  (`meaningful_translation_from_sk_to_tree`):
  There is a meaningful translation from SK-calculus
  to tree calculus.
- **Lemma 52**
  (`meaningful_translation_preserves_identity_programs`):
  Meaningful translations from SK-calculus to tree
  calculus preserve identity programs.
- **Lemma 53**
  (`meaningful_translation_preserves_separators`):
  Meaningful translations from SK-calculus to tree
  calculus preserve separators.
- **Theorem 54** (`no_translation_tree_to_sk`):
  There is no meaningful translation from tree calculus
  to SK-calculus. (Tree calculus has separable identity
  programs `tag{K, I}` and `tag{KI, I}`, which any
  meaningful translation would carry to separable
  identity programs in SK-calculus, contradicting
  Theorem 48.)

## VA-Calculus (Book, Chapter 9)

VA-calculus is a variant of lambda-calculus with two
ternary operators `V` and `A`. `V` builds de Bruijn
indices; `A` builds abstractions carrying an environment.
Terms are `M, N ::= V | A | M N`. The seven reduction
rules handle suspension, zero index, successor index,
application within abstractions, empty environment,
substitution, and nested abstraction — all without
meta-theoretic side conditions on scope.

Programs of VA-calculus are applications of `V` or `A`
to zero, one, or two arguments. VA-calculus is
combinatorially complete (S and K are definable via star
abstraction) and confluent, but cannot define equality
of its own programs (for the same reason as SK-calculus:
inseparable identity programs exist).

Meaningful translations exist in both directions between
VA-calculus and tree calculus. The translation from
VA-calculus to tree calculus uses tagging to record which
reduction rule applies to each operator. The translation
from tree calculus to VA-calculus uses tagging (which
VA-calculus supports via its first-class substitutions)
to encode the leaf/stem/fork structure. However, the
round-trip (double translation) is not definable within
VA-calculus, so the translations do not make VA-calculus
complete.

### Verified Theorems (Book, Chapter 9)

- **Theorem 55** (`confluence_va_calculus`):
  VA-calculus is confluent. (Proved via simultaneous
  reduction with non-overlapping rules.)
- **Theorem 56** (`bracket_beta`):
  Bracket abstraction in VA-calculus satisfies beta:
  `([x]t) u -->* {u/x} t`.
- **Theorem 57** (`star_beta`):
  Star abstraction in VA-calculus satisfies beta:
  `(lambda* x. t) u --> {u/x} t`.
- **Theorem 58**
  (`meaningful_translation_from_sk_to_va`):
  There is a meaningful translation from SK-calculus
  to VA-calculus.
- **Theorem 59**
  (`equality_of_programs_is_not_definable_in_va`):
  Equality of normal forms is not definable in
  VA-calculus. (Proved as for SK-calculus, using
  identity programs `I` and `AVI` which are
  inseparable.)
- **Theorem 60** (`meaningful_translation_va_to_tree`):
  There is a meaningful translation from VA-calculus
  to tree calculus. (Uses tagged fixpoint combinators
  `Y_2t` to translate `V` and `A`, with tags encoding
  which reduction rule applies.)
- **Theorem 61**
  (`meaningful_translation_from_tree_to_va`):
  There is a meaningful translation from tree calculus
  to VA-calculus. (Uses tagging within VA-calculus to
  encode the leaf/stem/fork dispatch.)
- **Corollary 62**: There is no meaningful translation
  from VA-calculus to combinatory logic. (Composing
  with Theorem 61 would yield a translation from tree
  calculus to SK-calculus, contradicting Theorem 54.)

## SF-Calculus (Book, Chapter 10)

SF-calculus uses two operators `S` and `F`. `S` provides
duplication (`S x y z --> x z (y z)`); `F` provides
factorisation, dispatching on whether its first argument
is an atom or a compound (partially applied operator).
The two conceptual rules for `F` are:

```text
F x y z --> y        (if x is an atom)
F (w x) y z --> z w x  (if w x is a compound)
```

These are expanded into seven non-overlapping reduction
rules (Figure 10.1 in the book). Programs are
irreducible terms, which can be thought of as binary
trees with nodes labelled by `S` or `F`.

SF-calculus embeds SK-calculus (`K = FF`) and supports
program equality, tagging, and pattern matching. The
factorisation operator `F` provides a general approach
to divide-and-conquer: if the argument is a compound,
divide it (extract left and right components); if it is
an atom, conquer it. The component functions `left` and
`right` extract the two parts of a compound:
`left (w x) = w`, `right (w x) = x`.

SF-calculus and tree calculus have equivalent expressive
power: meaningful translations exist in both directions.
Both translations use tagging to preserve intensional
information about the source operators.

### Verified Theorems (Book, Chapter 10)

- **Theorem 63**: Reduction of SF-calculus is confluent.
- **Theorem 64** (`equal_sf_programs`):
  `equal p p --> K` for all SF-programs `p`.
- **Theorem 65** (`unequal_sf_programs`):
  `equal p q --> KI` for all SF-programs `p` and `q`
  that are not equal.
- **Theorem 66** (`meaningful_translation_from_tree_to_sf`):
  There is a meaningful translation from tree calculus
  to SF-calculus. (Translates the triangle operator
  using tags to record which reduction rule applies.)
- **Theorem 67** (`meaningful_translation_from_sf_to_tree`):
  There is a meaningful translation from SF-calculus to
  tree calculus. (Uses `ternary_op{f}`, a tagged
  fixpoint combinator that delays evaluation until three
  arguments are received. Maps `S` to
  `ternary_op{S}` and `F` to `ternary_op{getTag}`.)

## Completeness Hierarchy (Book, Chapter 11)

The book distinguishes three levels of completeness for
models of computation:

- **Extensionally complete** (= combinatorially complete):
  supports all combinators. SK-calculus, VA-calculus,
  SF-calculus, and tree calculus are all extensionally
  complete.
- **Intensionally complete**: supports arbitrary program
  analyses via pattern matching. Tree calculus and
  SF-calculus are intensionally complete. SK-calculus,
  VA-calculus, and the traditional models (Turing
  machines, lambda-calculus, mu-recursive functions)
  are not.
- **Program-complete**: Turing-complete, supports the
  same class of functions of binary trees as tree
  calculus, and supports an invertible function from
  programs to binary natural trees. Tree calculus is
  program-complete by definition. SF-calculus is
  program-complete (the translation from programs to
  natural trees is definable by pattern matching).
  The traditional models are not program-complete
  because their programs are not binary trees.

The Church-Turing Thesis equates computational models
by the class of *numerical functions* they compute;
meaningful translation (Definition 50) is a stricter
comparison that also preserves application structure,
values, and variables. Under meaningful translation,
tree calculus is strictly more expressive than
combinatory logic (translation exists in one direction
only).

## Models of Computability (Book, Appendix A)

Appendix A (by Jay and Vergara) defines formal notions
of *model of computability* and *simulation* to compare
expressive power across different computational models.

A *model of computability* `(D, F)` consists of a domain
`D` (a set of values) and a collection `F` of partial
functions from powers of `D` to `D`. A *simulation* of
`(D1, F1)` in `(D2, F2)` is an injective encoding
`rho : D1 -> D2` such that every function in `F1` can be
simulated in `F2` via the encoding. A *recoding* is the
composition `rho2 . rho1 : D1 -> D1` obtained from
simulations in both directions. Model `(D2, F2)` is *at
least as expressive* as `(D1, F1)` if the recoding is
computable in `F2`. The two are *weakly equivalent* if
each is at least as expressive as the other; they are
*equivalent* if the recodings have computable inverses.

Two versions of the Church-Turing Thesis are
distinguished:

- **(NCT)** Numerical Church's Thesis: every effectively
  calculable numerical function is general recursive.
- **(SCT)** Symbolic Church's Thesis: every effectively
  calculable function can be simulated by a general
  recursive function.

Similarly, two versions of Turing's Thesis:

- **(NTT)** Numerical: every numerical function that would
  naturally be regarded as computable is Turing
  computable.
- **(STT)** Symbolic: every function that would naturally
  be regarded as computable can be simulated by a
  Turing-computable function.

### Verified Theorems (Book, Appendix A)

- **Corollary 68**: Church's delta (equality of closed
  normal lambda-terms) is lambda-definable (follows
  from Kleene's statement).
- **Corollary 69**: Church's delta is not
  lambda-definable (follows from Barendregt).
  (These two corollaries exhibit the contradiction in
  the standard account.)
- **Theorem 70**: Any model of computability that is at
  least as expressive as the recursive function model
  can define equality of values.
- **Corollary 71**: The normal model of computability for
  SK-calculus is not weakly equivalent to the recursive
  function model. (SK-calculus cannot define equality
  of values.)
- **Corollary 72**: No lambda-model of higher-order
  programming is weakly equivalent to the recursive
  model of computability.
- **Theorem 73**: Turing's Numerical Thesis is logically
  equivalent to Church's Numerical Thesis.
- **Theorem 74**: The recursive model of computability is
  weakly equivalent to any Turing model.
- **Corollary 75**: Turing's Symbolic Thesis is logically
  equivalent to Church's Symbolic Thesis.
- **Corollary 76**: No lambda-model of higher-order
  programming is weakly equivalent to the Turing model.
- **Theorem 77**: The normal model of computability for
  SF-calculus is equivalent to the recursive model.
  (Both recodings are computable: Godelisation in one
  direction, pattern-matching in the other.)

## Coq Formalization

The Coq formalization at
[barry-jay-personal/tree-calculus](https://github.com/barry-jay-personal/tree-calculus)
provides machine-checked proofs for all named theorems
in the book. The nine `.v` files correspond to the
book's chapters.

### File: Tree_Calculus.v (Chapters 2-3)

Defines the `Tree` type (with constructors `Node` and
`App`), the quotient construction for equational
reasoning, and the basic combinators:

- `K`, `I`, `D`, `Sop`, `d`
- Booleans: `conjunction`, `disjunction`, `implies`,
  `negation`, `bi_implies`
- Pairs: `Pair`, `first`, `second`
- Naturals: `zero`, `successor`, `isZero`, `predecessor`
- Queries: `query`, `isLeaf`, `isStem`, `isFork`
- The `program` inductive predicate

### File: Rewriting_partI.v (Chapters 3-6)

Defines the directed reduction relation `t_red1` (five
rules: `k_red`, `s_red`, `f_red`, `appl_red`,
`appr_red`) and its multi-step closure `t_red`. Contains
all extensional, intensional, and reflective program
constructions:

- **Extensional**: `bracket`, `star`, `substitute`,
  `occurs`, fixpoints (`Y`, `Z`, `Y2`, `self_apply`,
  `swap`), waiting (`W`, `wait`, `wait1`), arithmetic
  (`plus`, `times`, `minus`), lists (`t_nil`, `t_cons`,
  `list_map`, `list_foldleft`, `list_foldright`),
  mu-recursive function translation (`recfun`,
  `rf_to_tree`)
- **Intensional**: `size`, `equal`, `tag`, `getTag`,
  `untag`, `triage`, pattern matching (`extension`,
  `tree_case`)
- **Reflective**: `eager`, `bf`, `quote`, `root`, `rb`,
  `rf`, evaluation relations (`branch_first_eval`,
  `root_eval`, `rb_eval`, `root_first_eval`)
- Theorems: `bracket_beta`, `star_beta`, `Z_red`,
  `fixpoint_function`, `Y2_program`, `equal_programs`,
  `unequal_programs`,
  `tree_calculus_support_tagging`,
  `branch_first_eval_to_bf`, `root_eval_to_root`,
  `rb_eval_implies_rb`, `root_first_eval_to_rf`

### File: Rewriting_theorems.v (Chapter 7)

Develops the metatheory of reduction:

- **Simultaneous reduction**: `s_red1`, `s_red`
- **Diamond property**: `diamond_s_red1_s_red1`
  (simultaneous reduction has the diamond property)
- **Confluence**: `confluence_tree_calculus`
- **Stability**: `programs_are_stable`,
  `programs_are_stable2`
- **Halting**: `halting_problem_insoluble`
- **Standardization**: `standardization`,
  `leftmost_reduction`,
  `head_reduction_to_factorable_form`
- **Evaluator completeness**:
  `branch_first_eval_iff_bf`, `root_eval_iff_root`,
  `rb_eval_iff_rb`, `root_first_eval_iff_rf`
- **Active/needy analysis**: `active`, `needs`,
  `bf_needy`, `root_needy`, `rb_needy` (used to prove
  evaluator completeness by showing evaluators do no
  more than their strategy allows)

### File: Extensional_Programs.v (Chapter 4)

Alternative development of extensional programs with
the directed reduction relation. Contains:

- `bracket_beta`, `star_beta`, `Z_red`,
  `fixpoint_function`
- Arithmetic: `plus_zero`, `plus_successor`
- mu-recursive functions: `rf_to_tree_preserves_eval`
- Lists: `map_nil`, `map_cons`, `list_foldleft_nil`,
  `list_foldleft_cons`, `list_foldright_nil`,
  `list_foldright_cons`

### File: Intensional_Programs.v (Chapter 5)

- `size_leaf`, `size_stem`, `size_fork`
- `equal_programs`, `unequal_programs`
- `tag_apply`, `getTag_tag`, `untag_tag`
- `triage_leaf`, `triage_stem`, `triage_fork`
- Pattern matching: `extension_leaf`, `extension_stem`,
  `extension_fork`
- Typed application: `typed_app_red`, `type_check`

### File: Reflective_Programs.v (Chapter 6)

- `branch_first_eval_to_bf` (soundness of bf)
- `root_eval_to_root` (soundness of root)
- `rb_eval_implies_rb` (soundness of rb)
- `root_first_eval_to_rf` (soundness of rf)
- `quote_red`, `eager_of_factorable`
- `bf_leaf_red`, `bf_stem_red`, `bf_fork_red`

### File: Incompleteness_of_Combinatory_Logic.v (Ch 8)

Defines the `SK` inductive type and its reduction
relation `sk_red1`:

- `confluence_sk_red` (SK-calculus is confluent)
- `no_separable_identities_in_SK` (identity programs
  have no separators)
- `equality_of_programs_is_not_definable_in_SK`
- `meaningful_translation_from_sk_to_tree`
- `no_translation_tree_to_sk`

### File: Lambda_Abstraction_in_VA_Calculus.v (Ch 9)

Defines the `VA` inductive type with operators `Vop`
and `Lam`:

- `confluence_va_calculus`
- `meaningful_translation_from_sk_to_va`
- `equality_of_programs_is_not_definable_in_va`
- `meaningful_translation_from_tree_to_va`
- `meaningful_translation_from_ac_to_tree` (VA to tree)
- Translation machinery: `kernel`, `V_t`, `A_t`

### File: Divide_and_Conquer_in_SF_Calculus.v (Ch 10)

Defines the `SF` inductive type with operators `Sop`
and `Fop`:

- `equal_sf_programs`, `unequal_sf_programs`
- `meaningful_translation_from_tree_to_sf`
- `meaningful_translation_from_sf_to_tree`
- Translation machinery: `kernel`, `tree_to_sf`,
  `sf_to_tree`

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
