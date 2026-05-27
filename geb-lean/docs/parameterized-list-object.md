<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Parameterized List Objects and Their Relationship to PBTOs](#parameterized-list-objects-and-their-relationship-to-pbtos)
  - [Motivation and Context](#motivation-and-context)
    - [Background: Parameterized NNOs and PBTOs](#background-parameterized-nnos-and-pbtos)
    - [Primitive Recursive Arithmetic and the Grzegorczyk Hierarchy](#primitive-recursive-arithmetic-and-the-grzegorczyk-hierarchy)
    - [Trees as Lists of Trees](#trees-as-lists-of-trees)
  - [Definitions](#definitions)
    - [Is/Has Factoring Pattern](#ishas-factoring-pattern)
    - [Parameterized Snoclist Object (PSO)](#parameterized-snoclist-object-pso)
    - [Parameterized (Cons-)List Object (PLO)](#parameterized-cons-list-object-plo)
    - [Relationship to PNNO](#relationship-to-pnno)
    - [PSTO and PLTO](#psto-and-plto)
  - [Correspondence Between PBTO, PSTO, and PLTO](#correspondence-between-pbto-psto-and-plto)
    - [PBTO implies PSTO](#pbto-implies-psto)
    - [PSTO implies PBTO](#psto-implies-pbto)
    - [PSTO implies PLTO (and vice versa)](#psto-implies-plto-and-vice-versa)
  - [References](#references)
    - [Category Theory](#category-theory)
    - [Tree Calculus](#tree-calculus)
    - [Computability](#computability)
  - [File Structure](#file-structure)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Parameterized List Objects and Their Relationship to PBTOs

## Motivation and Context

### Background: Parameterized NNOs and PBTOs

The parameterized natural numbers object (PNNO) is the universal
object described at
<https://ncatlab.org/nlab/show/natural+numbers+object#withparams>.
It depends only on the ambient category having finite products; given
those, the PNNO captures the notion of what functions can be written
using primitive recursive arithmetic.

This project has a development of a "parameterized binary tree object"
(PBTO), which is the analogue of the PNNO for unlabeled binary trees
(just as natural numbers can be seen as unlabeled lists).  The PBTO
consists of an object `T` with `leaf : 1 -> T` and
`branch : T x T -> T`, satisfying: for any `f : A -> X` and
`g : X x X -> X`, there exists a unique `phi : A x T -> X` such that
`phi(a, leaf) = f(a)` and
`phi(a, branch(t1, t2)) = g(phi(a, t1), phi(a, t2))`.

Proposition 2.3 of the nLab page shows how the universal property may
be given a richer interface (the "paramorphism") without making any
additional assumptions: the step function also receives the parameter
and the sub-objects (predecessor for NNO, subtrees for BTO).  The
paramorphism section of `TreeLogic.lean` contains the derivation and
proof of this enhanced interface and its universal property.

### Primitive Recursive Arithmetic and the Grzegorczyk Hierarchy

Primitive recursive arithmetic, as captured by a PNNO (or, we expect,
PBTO), can be partitioned into levels of arithmetic strength:
<https://en.wikipedia.org/wiki/Grzegorczyk_hierarchy>.

The third level, `E_3`, has properties which merit its own name,
ELEMENTARY: <https://en.wikipedia.org/wiki/ELEMENTARY>.

ELEMENTARY is not all of PR (the primitive-recursive functions), which
in turn is not all of higher-order arithmetic (HOA) -- for example,
HOA can write the Ackermann function, whereas PR cannot.  However,
ELEMENTARY is strong enough to write, as far as we can tell, every
function that is generally used in computer science and programming.
This likely relates to:

- <https://en.wikipedia.org/wiki/ELEMENTARY#Iterated_stack_automata>
- <https://en.wikipedia.org/wiki/ELEMENTARY#Higher-order_logic>

If we can do stack machines and represent higher-order languages, that
covers the foundations of programming.

No category-theoretic characterization of ELEMENTARY is known, in
contrast to the universal-property characterization of PR by the
PNNO/PBTO.  Finding such a characterization is the eventual goal of
this line of work.

### Trees as Lists of Trees

The tree calculus (<https://treecalcul.us/specification/>) uses
unlabeled binary trees as expressions.  That page notes that "We can
think of expressions as unlabeled trees."  In category-theoretic terms,
the unlabeled binary-tree object can also be seen as an object defined
as "a list of itself" -- the fixpoint of the `List` endofunctor (which
is polynomial).

The binary tree type satisfies `T = 1 + T x T`.  Lists of `T`
satisfy `L(T) = 1 + T x L(T)`.  Setting `L(T) = T`, we get
`T = 1 + T x T`, which is consistent.  So the same object `T` serves
as both the binary tree object and the "list of T" object.

The correspondence uses **left-associative** structure.  Looking at
the tree `branch(branch(branch(leaf, a), b), c)`, this is a tree
whose left spine encodes the list `[a, b, c]` with the elements as
right children.  This is a **snoclist** (reversed list):

- `leaf` = empty snoclist
- `branch(l, b)` = `snoc(l, b)` (append element `b` to snoclist `l`)

The left subtree is the accumulated list; the right subtree is the
latest element.  This matches the Idris 2 implementation in
`.claude/docs/TreeCalculus.idr`, where `NSExp` (S-expressions without
atoms) is defined as `InNS : List NSExp -> NSExp`, storing reversed
lists internally.  The conversion functions `RNSExpToNatTree` and
`NatTreeToRNSExp` witness the isomorphism, with round-trip proofs.

## Definitions

### Is/Has Factoring Pattern

Each universal property is factored into two classes:

- `Is*` takes the object(s) as parameters and states the universal
  property holds for those objects.
- `Has*` bundles an object together with an `Is*` instance.

This allows expressing "object `T` is a PLO of itself" as
`IsPSO T T` without needing object equality constraints.

### Parameterized Snoclist Object (PSO)

For an object `B` in a category with chosen finite products, a
parameterized snoclist object of `B` is an object `L` with:

- `nil : 1 -> L`
- `snoc : L x B -> L`
- Elimination (left fold): for any `f : A -> X` and
  `g : X x B -> X`, a unique `phi : A x L -> X` satisfying:
  - Base: `phi(a, nil) = f(a)`
  - Step: `phi(a, snoc(l, b)) = g(phi(a, l), b)`

This corresponds to the parameterized initial algebra of the functor
`X |-> 1 + X x B`.

The step equation in product utilities:

```text
cfpMap (id A) snoc >> elim f g
  = cfpLiftRecElem (elim f g) >> g
```

where `cfpLiftRecElem` extracts `(phi(a, l), b)` from
`A x (L x B)`.

### Parameterized (Cons-)List Object (PLO)

The dual: an object `L` with:

- `nil : 1 -> L`
- `cons : B x L -> L`
- Elimination (right fold): for any `f : A -> X` and
  `g : B x X -> X`, a unique `phi : A x L -> X` satisfying:
  - Base: `phi(a, nil) = f(a)`
  - Step: `phi(a, cons(b, l)) = g(b, phi(a, l))`

This corresponds to the parameterized initial algebra of the functor
`X |-> 1 + B x X`.

### Relationship to PNNO

A PSO (or PLO) for the terminal object (`B = 1`) is a PNNO:

- `snoc : L x 1 -> L` corresponds to `s : L -> L` via `L x 1 ~ L`.
- `g : X x 1 -> X` corresponds to `g : X -> X` via `X x 1 ~ X`.

Similarly for PLO using `1 x L ~ L` and `1 x X ~ X`.

### PSTO and PLTO

A parameterized snoclist-of-trees object (PSTO) is a PSO where
`B = L`:

- `IsPSTO T` = `IsPSO T T`
- `HasPSTO` = `T` + `IsPSTO T`

A parameterized list-of-trees object (PLTO) is a PLO where `B = L`:

- `IsPLTO T` = `IsPLO T T`
- `HasPLTO` = `T` + `IsPLTO T`

For PSTO, the constructors are `nil : 1 -> T` and
`snoc : T x T -> T`, which match `leaf` and `branch` of the PBTO.

## Correspondence Between PBTO, PSTO, and PLTO

### PBTO implies PSTO

Given a PBTO with `T`, `leaf`, `branch`, the same object `T`
satisfies the PSTO universal property with `nil = leaf` and
`snoc = branch`.

**Construction:** For `f : A -> X` and `g : X x T -> X`, define
the PSO elimination via the PBTO catamorphism on the enriched
carrier `T x X`:

- Base: `f'(a) = (leaf, f(a))`
- Step: `g'((t1, x1), (t2, x2)) = (branch(t1, t2), g(x1, t2))`
- `phi = snd . PBTO.elim f' g'`

The step function uses `x1` (the recursive result on the left
subtree, which is the accumulated snoclist) and `t2` (the right
subtree, which is the latest element passed as data).

**Uniqueness** follows from the PBTO uniqueness via the pairing
trick: any `psi` satisfying the PSO equations gives rise to
`theta'(a, t) = (t, psi(a, t))` which satisfies the PBTO equations.

### PSTO implies PBTO

This requires deriving branching recursion (both subtrees) from
linear recursion (left subtree only).  Approaches:

1. **Via PNNO:** PSTO implies PSO(1) implies PNNO.  Use the PNNO
   together with the PSTO to iterate the fold over both subtrees.
   The existing `iterNat` infrastructure may help.

2. **Bauer's mutual-recursion trick:** Use the parameter to
   encode mutual recursion as a single parameterized fold.  See
   <https://cs.stackexchange.com/a/144184>.  The parameter can
   serve as a "slice" carrying the recursive result from the
   other subtree.

3. **Direct enriched-carrier construction:** Thread enough state
   through the fold to process both subtrees, using the snoclist
   structure of T itself as a stack.

### PSTO implies PLTO (and vice versa)

A snoclist of `B`s and a cons-list of `B`s are equivalent by
reversal.  The `rev` operation maps `snoc(l, b)` to
`cons(b, rev(l))` and vice versa.  For snoclist-of-trees and
list-of-trees (where `B = L`), reversal operates at every level:
each element is itself reversed recursively.

The reversal can be defined using the PSO (or PLO) elimination
rule, so no additional assumptions beyond the PSO (or PLO)
structure are needed.

## References

### Category Theory

- nLab, "natural numbers object" (parameterized NNO):
  <https://ncatlab.org/nlab/show/natural+numbers+object#withparams>
- nLab, "Lawvere theory":
  <https://ncatlab.org/nlab/show/Lawvere+theory>
- Bauer, mutual recursion via parameterized recursion:
  <https://cs.stackexchange.com/a/144184>

### Tree Calculus

- Tree calculus specification:
  <https://treecalcul.us/specification/>
- Idris 2 implementation:
  `.claude/docs/TreeCalculus.idr`

### Computability

- Grzegorczyk hierarchy:
  <https://en.wikipedia.org/wiki/Grzegorczyk_hierarchy>
- ELEMENTARY:
  <https://en.wikipedia.org/wiki/ELEMENTARY>

## File Structure

- `GebLean/PSO.lean` -- `IsPSO`, `HasPSO`, `IsPSTO`,
  `HasPSTO`, PSO(1) ~ PNNO, PBTO-to-PSTO construction
- `GebLean/PLO.lean` -- `IsPLO`, `HasPLO`, `IsPLTO`,
  `HasPLTO`, PLO(1) ~ PNNO, PSTO-to-PLTO reversal
- `docs/parameterized-list-object.md` -- This document
- `.session/workstreams/parameterized-list-object.md` --
  Task tracking
