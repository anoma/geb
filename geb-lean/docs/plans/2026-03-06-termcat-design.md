# TermCat Design: Categories from Binary Trees

## Overview

This document records the design exploration for
`GebLean/PLang/TermCat.lean`, which defines categories
constructed from binary trees — the free monad of the product
polynomial endofunctor `polyProd X` on `Over X`.

The binary tree type `polyProdFreeM X` is the tree-theoretic
analogue of the natural numbers: the NNO is the initial algebra
of `B mapsto 1 + B`, while `polyProdFreeM` is the initial
algebra of `B mapsto A +_X (B times_X B)`. The design explores
multiple categorical structures that arise from this analogy,
from Lawvere-style theories to tree calculus semantics.

## Existing Codebase Infrastructure

### Polynomial Functor Foundations

- `polyProd X` (`PLang/Syntax.lean:42`):
  Product polynomial `A mapsto A times_X A` on `Over X`.
- `polyProdFreeM X` (`PLang/Syntax.lean:215`):
  Free monad of `polyProd` (labeled binary trees).
- `polyProdCofreeM X` (`PLang/Syntax.lean:227`):
  Cofree comonad (annotated infinite binary streams).
- `polyProdType` (`PLang/Syntax.lean:239`):
  Specialization to `PUnit` (plain `Type`).
- `polyProd_eval_iso` (`PLang/Syntax.lean:164`):
  Polynomial eval isomorphic to `overSelfProd`.
- `polyProdNatIso` (`PLang/Syntax.lean:183`):
  Natural isomorphism of eval functor.

### Free Monad Structure

- `PolyFreeM A P x` (`PolyAlg.lean:2817`):
  Free monad type (`= PolyFix (polyTranslate A P) x`).
- `polyFreeMCarrier A P` (`PolyAlg.lean:2823`):
  Free monad carrier as `Over X` object.
- `polyFreeMPure` (`PolyAlg.lean:3423`):
  Unit: embed `A`-value as leaf.
- `polyFreeMBind` (`PolyAlg.lean:3453`):
  Bind: substitute at leaves.
- `polyFreeM_pure_bind` (`PolyAlg.lean:3466`):
  Left identity law.
- `polyFreeM_bind_pure` (`PolyAlg.lean:3474`):
  Right identity law.
- `polyFreeM_bind_assoc` (`PolyAlg.lean:3494`):
  Associativity law.
- `PolyFreeMShape P x` (`PolyAlg.lean:3602`):
  Tree shapes (leaves labeled trivially).
- `PolyFreeMLeafPos` (`PolyAlg.lean:3612`):
  Leaf position type in a shape.
- `PolyFreeMLeafFiber` (`PolyAlg.lean:3623`):
  Fiber assignment at leaf positions.
- `polyFreeMPoly P` (`PolyAlg.lean:3642`):
  Free monad as polynomial endofunctor.
- `polyFreeMFromShape` (`PolyAlg.lean:3695`):
  Build tree from shape + leaf data.
- `polyFreeMToShape` (`PolyAlg.lean:3713`):
  Extract shape from tree.

### Monad and Comonad Polynomial Structure

- `polyFreeMPolyUnit P` (`PolyAlg.lean:8588`):
  Monad unit: `polyBetweenId X -> polyFreeMPoly P`.
- `polyFreeMPolyMult P` (`PolyAlg.lean:8625`):
  Monad mult: `T . T -> T` (shape grafting).
- `polyCofreeMPolyCounit P` (`PolyAlg.lean:8088`):
  Comonad counit: extract root.
- `polyCofreeMPolyComult P` (`PolyAlg.lean:8102`):
  Comonad comult: all subtrees.
- `polyCofreeComonad X P` (`PolyAlg.lean:7968`):
  Cofree comonad as `Comonad (Over X)`.

### Fold and Unfold (Universal Morphisms)

- `polyFixFold` (`PolyAlg.lean:308`):
  Catamorphism (fold from initial algebra).
- `polyFixFoldHom` (`PolyAlg.lean:320`):
  Fold as algebra homomorphism.
- `polyFixFoldUnique_at` (`PolyAlg.lean:382`):
  Uniqueness of fold.
- `polyCofixUnfold` (`PolyAlg.lean:1378`):
  Anamorphism (unfold to terminal coalgebra).
- `polyCofixUnfoldHom` (`PolyAlg.lean:1400`):
  Unfold as coalgebra homomorphism.

### Translate and Scale

- `polyTranslate A P` (`PolyAlg.lean:2766`):
  Coproduct polynomial `A +_X P(-)`.
- `polyScale A P` (`PolyAlg.lean:2804`):
  Product polynomial `A times_X P(-)`.
- `polyTranslateIndex`:
  `{ a : A.left // ... } + polyBetweenIndex X X P x`.
- `polyScaleIndex`:
  `{ a : A.left // ... } * polyBetweenIndex X X P x`.

### Algebra and Coalgebra Categories

- `PolyAlg P` (`PolyAlg.lean:111`):
  Category of P-algebras.
- `PolyAlg.forget P` (`PolyAlg.lean:118`):
  Forgetful functor to `Over X`.
- `PolyCoalg P` (`PolyAlg.lean:591`):
  Category of P-coalgebras.
- `polyCoalgForgetFunctor P` (`PolyAlg.lean:591`):
  Forgetful functor.
- `polyForgetCofreeAdjunction P` (`PolyAlg.lean:7664`):
  Forget -| Cofree adjunction.

### Polynomial Universal Morphisms

- `polyBetweenProd` (`PolyUMorph.lean:73`):
  Products of polynomial families.
- `polyBetweenProdLift` (`PolyUMorph.lean:178`):
  Universal pairing.
- `polyBetweenCoprod` (`PolyUMorph.lean:420`):
  Coproducts of polynomial families.
- `polyBetweenCoprodDesc` (`PolyUMorph.lean:470`):
  Universal copairing.
- `polyBetweenEq` (`PolyUMorph.lean:624`):
  Equalizers.
- `polyBetweenCoeq` (`PolyUMorph.lean:914`):
  Coequalizers.
- `pbBinaryProdObj` (`PolyUMorph.lean:1556`):
  Binary product.
- `pbBinaryLift` (`PolyUMorph.lean:1600`):
  Binary product universal morphism.
- `polyBetweenId X` (`Polynomial.lean:1431`):
  Identity polynomial endofunctor.
- `polyBetweenComp` (`Polynomial.lean`):
  Composition of polynomials.

### Coalgebra-Copresheaf Equivalence (Topos)

- `PolyCofreeCat P` (`CofreeCategory.lean:36`):
  Cofree category of P.
- `PolyCofreeCatHom` (`CofreeCategory.lean:43`):
  Morphisms in cofree category.
- `polyCoalgCopresheafEquiv P`
  (`CofreeCategory.lean:3327`):
  `PolyCoalg P ~= (PolyCofreeCat P => Type u)`.
- `comonadCoalgCopresheafEquiv P`
  (`CofreeCategory.lean:3341`):
  Via comonad coalgebras.
- `polyCoalgHasLimitsOfSize`
  (`CofreeCategory.lean:3361`):
  Coalgebras have all limits.
- `polyCoalgHasColimitsOfSize`
  (`CofreeCategory.lean:3367`):
  Coalgebras have all colimits.

### Distributive Law and Lambda-Bialgebras

- `DistributiveLaw T D`
  (`Utilities/DistributiveLaw.lean`):
  `T . D => D . T` with coherences.
- `polyFreeMCoalgStrAt`
  (`PolyDistributiveLaw.lean:45`):
  P-coalgebra on `T(C)` from P-coalgebra on C.
- `polyFreeMCoalgStr`
  (`PolyDistributiveLaw.lean:77`):
  Full coalgebra structure map.
- `LambdaBialgebra law`
  (`Utilities/LambdaBialgebra.lean:26`):
  Algebra + coalgebra + pentagon.
- `LambdaBialgebra.Hom`
  (`Utilities/LambdaBialgebra.lean:78`):
  Morphisms of lambda-bialgebras.

### Essentially Algebraic Theories

- `IndexedEAT X` (`PLang/IndexedEAT.lean:79`):
  Poly + equations + equivalence relation.
- `EATCongruence T` (`PLang/IndexedEAT.lean:110`):
  Equations respected by structure map.

### GSOS Rules (Incomplete)

- `polyIdBehaviorPoly Q` (`PolyGSOS.lean`):
  `Id * Q` polynomial.
- `PolyGSOSRule P Q` (`PolyGSOS.lean`):
  Rule: `P . (Id * Q) => Q . T_P`.

### Dinatural Numbers (Analogy)

- `DinaturalNumbers.lean:1-37`:
  Endo-paranaturals of Hom correspond to N.

The comment at line 28 notes that generalizing to categories
with NNO would use global elements `1 -> N`. The binary tree
object would analogously use global elements `1 -> T`.

## Approaches Considered

### Approach A: Parametrized Binary Tree Object (Lawvere)

Define a "parametrized binary tree object" (PBTO) as the
tree-theoretic analogue of the parametrized NNO. The
parametrized NNO in a category with finite products
satisfies: for any `f : A -> B` and
`g : A * N * B -> B`, there exists a unique
`phi : A * N -> B` such that `phi(a, 0) = f(a)` and
`phi(a, s(n)) = g(a, n, phi(a, n))`.

For binary trees, the analogous universal property is: for
any `f : A -> B` and `g : A * T * B * B -> B`, there
exists a unique `phi : A * T -> B` such that:

- `phi(a, leaf) = f(a)`
- `phi(a, fork(l, r)) = g(a, fork(l,r), phi(a,l), phi(a,r))`

The stronger form (where `g` has access to `fork(l, r)` as
well as `phi(a, l)` and `phi(a, r)`) corresponds to a
paramorphism. The weaker form (where `g` sees only
`phi(a, l)` and `phi(a, r)`) corresponds to a catamorphism.

#### Polynomial Encoding of PBTO

In polynomial terms:

- `polyTranslate A (polyProd X)` is the endofunctor
  `B mapsto A +_X (B *_X B)`
- `polyFixCarrier (polyTranslate A (polyProd X))` =
  `polyFreeMCarrier A (polyProd X)` is the initial algebra
- `polyFixFold` provides the catamorphism (weaker form)
- A `polyTranslate A (polyProd X)`-algebra on `B` consists
  of:
  - A leaf map `f : A -> B` (the `Sum.inl` case)
  - A fork map `g : B *_X B -> B` (the `Sum.inr` case)
- `polyFixFold` gives the unique `phi` extending this
  algebra

#### Lawvere Theory Structure

The Lawvere theory of binary trees would be:

- Objects: formal finite products `T^n` (for `n in N`) of
  a generating object `T`
- Morphisms `T^m -> T^n`: `n`-tuples of primitive
  tree-recursive functions with `m` parameters
- Composition: substitution

The functions constructible from this structure (with
finite products and parametrized PBTO) are the primitive
tree-recursive functions — the analogue of how the
parametrized NNO yields exactly the primitive recursive
functions.

With cartesian closure (exponentials),
non-primitive-recursive tree functions become definable,
paralleling the NNO case.

#### Approach A Trade-offs

- (+) Well-understood universal property, directly
  analogous to NNO
- (+) `polyFixFold` and `polyFixFoldUnique` provide the
  recursion principle and its uniqueness
- (+) Clean separation of syntax (trees) from semantics
  (fold targets)
- (+) Extends to finite-limit theory by adding equalizers
  (for definable subsets)
- (-) Limited computational expressiveness: only primitive
  tree-recursion
- (-) No reflection / intensionality (cannot inspect tree
  structure within the theory)
- (-) Lawvere theories not formalized in mathlib; would
  build from scratch
- (-) The parametrized form requires working with products
  in `Over X`, which are pullbacks

#### Approach A References

- [nLab: Natural numbers object (with parameters)](https://ncatlab.org/nlab/show/natural+numbers+object#withparams)
- Freyd's characterization of NNO via colimits in a topos
- `DinaturalNumbers.lean:28-30`
  (notes on NNO generalization)

### Approach B: Tree Calculus with Bialgebra Semantics

Model the tree calculus (or triage calculus variant) as
operational semantics on binary trees, using the distributive
law and lambda-bialgebra structure.

Tree calculus is a Turing-complete calculus on binary trees
with a single operator `triangle`. Terms are binary trees;
values are irreducible trees. The triage calculus variant
has five reduction rules:

1. `triangle triangle y z --> y`
   (leaf applied to two args: K-like, returns first)
1. `triangle (triangle x) y z --> x z (y z)`
   (stem applied to two args: S-like, distributes)
1. `triangle (triangle w x) y triangle --> w`
   (fork with two args, third is leaf: return `w`)
1. `triangle (triangle w x) y (triangle u) --> x u`
   (fork with two args, third is stem: apply `x`)
1. `triangle (triangle w x) y (triangle u v) --> y u v`
   (fork with two args, third is fork: apply `y`)

Rules 1-2 encode the K and S combinators of combinatory
logic, establishing Turing completeness. Rules 3-5 (triage)
enable reflection: programs can inspect the structure of
other programs.

#### Partial Combinatory Algebra

Tree calculus defines a partial combinatory algebra (PCA):

- The carrier is the set of binary tree values
- Application is (partial) tree reduction
- K = `triangle triangle` and
  S = `triangle (triangle x)` for appropriate `x`
- The PCA is functionally complete: every computable
  partial function on trees is representable

A PCA gives rise to a realizability topos via:

1. Assemblies: sets with "realizers" drawn from the PCA
1. The realizability topos is the ex/reg completion of
   assemblies

#### Polynomial Encoding of Reduction

The reduction rules can be encoded as:

- A coalgebra of a suitable polynomial capturing "one
  reduction step"
- The coalgebra maps a tree to either a value (no
  reduction possible) or a reduced tree (one step taken)
- This is a `polyTranslate (terminal) P`-coalgebra where
  `P` captures the reduction step

Alternatively, using GSOS rules
(`PolyGSOSRule` from `PolyGSOS.lean`):

- A GSOS rule `P . (Id * Q) -> Q . T_P` describes
  operational semantics where `P` is the syntax
  constructor, `Q` is the behavior (observation), and
  `T_P` is the free monad (terms)
- The triage rules fit this pattern: the behavior
  observation is "is this a leaf, stem, or fork?"

#### Lambda-Bialgebra for Tree Calculus

The distributive law `lambda : T . D -> D . T` where
`T = polyFreeMonad (polyProd X)` and
`D = polyCofreeComonad (polyProd X)` is already
constructed in `PolyDistributiveLaw.lean`.

A lambda-bialgebra for this distributive law on an object
`C` consists of:

- A `T`-algebra structure `a : T(C) -> C`
  (fold: can build trees)
- A `D`-coalgebra structure `d : C -> D(C)`
  (unfold: can observe/reduce)
- Compatibility: `T(d) ; lambda_C ; D(a) = a ; d`

The category of lambda-bialgebras with homomorphisms forms
a setting for tree calculus models: objects have both syntax
(algebra) and behavior (coalgebra), interacting coherently.

#### Topos Connections

`polyCoalgCopresheafEquiv` shows:

```text
PolyCoalg (polyProd X)
  ~= (PolyCofreeCat (polyProd X) => Type u)
```

This means coalgebras of the product polynomial form a
copresheaf topos. The cofree category
`PolyCofreeCat (polyProd X)` has:

- Objects: `(x : X, s : PolyCofreeShape (polyProd X) x)`
  — pairs of a fiber point and an infinite binary tree
  shape
- Morphisms: paths in the tree (depth + position +
  fiber/shape compatibility)

Whether this copresheaf topos relates to the realizability
topos of the tree calculus PCA is an open question.

#### Approach B Trade-offs

- (+) Turing-complete computational model
- (+) Reflective: programs can inspect their own structure
  (triage)
- (+) Connects to realizability toposes and PCA theory
- (+) Uses the distributive law and lambda-bialgebra
  infrastructure
- (+) The coalgebra category is a topos via
  `polyCoalgCopresheafEquiv`
- (-) Reduction is partial (trees reduce only with 3+
  arguments)
- (-) Encoding the 5 rules in polynomial morphisms
  requires care
- (-) The GSOS infrastructure in the codebase is
  incomplete
- (-) Connection between coalgebra topos and realizability
  topos is speculative
- (-) More mathematically involved than Approach A

#### Approach B References

- [Tree calculus reference](../tree-calculus.md) — syntax,
  reduction rules, PCA structure, self-reflection,
  references to implementations and formalization
- [nLab: Realizability topos](https://ncatlab.org/nlab/show/realizability+topos)
- [nLab: Partial combinatory algebra](https://ncatlab.org/nlab/show/partial+combinatory+algebra)
- `PolyDistributiveLaw.lean`
  (canonical distributive law construction)
- `Utilities/LambdaBialgebra.lean`
  (lambda-bialgebra definition)
- `CofreeCategory.lean:3327`
  (`polyCoalgCopresheafEquiv`)
- `PolyGSOS.lean` (GSOS rule structure, incomplete)

### Approach C: Hybrid — Incremental Layering

Combine Approaches A and B incrementally:

- **Phase 1**: Parametrized binary tree object and its
  Kleisli category
- **Phase 2**: Tree calculus reduction rules as additional
  structure
- **Phase 3**: Lambda-bialgebra and topos connections

Each phase produces independently valuable results; later
phases build on earlier ones without requiring rework.

#### Approach C Trade-offs

- (+) Incremental: each phase is independently valuable
  and testable
- (+) Phase 1 establishes the foundation needed by all
  other approaches
- (+) The Kleisli category from Phase 1 provides a
  concrete category of "tree programs" before adding
  reduction
- (+) Phases 2-3 can be pursued in either order
- (-) More total work than either approach alone
- (-) Phase boundaries may require design adjustments

## Candidate Categories (Detailed)

### Category 1: Binary-Product Algebras

`PolyAlg (polyProd X)`

**Objects**: Pairs
`(B : Over X, g : polyEndoFunctor X (polyProd X) B -> B)`
— an object `B` equipped with a binary product operation.

Via the `polyProd_eval_iso`, the algebra structure map is
equivalent to `g : overSelfProd B -> B`, i.e.
`g : B *_X B -> B`.

**Morphisms**: Algebra homomorphisms
`(B, g_B) -> (C, g_C)` — morphisms `h : B -> C` in
`Over X` such that `h . g_B = g_C . (h * h)`.

**Free objects**: `polyFreeMCarrier A (polyProd X)` is the
free `polyProd X`-algebra on `A`. The fold `polyFixFold`
gives the universal morphism to any algebra.

**Category 1 properties**:

- Already defined as `PolyAlg (polyProd X)`
- Has a forgetful functor to `Over X` via
  `PolyAlg.forget`
- The forgetful functor has a left adjoint (free algebra
  construction)
- Objects are "magmas" in `Over X` (sets with a binary
  operation, no associativity or other axioms required)
- Monoids, groups, lattices, etc. are all objects of this
  category (with additional equations not captured by the
  algebra structure alone)

**Category 1 use cases**: studying binary operations
abstractly; the fold gives a recursion principle for
defining functions out of trees into any algebra.

### Category 2: Kleisli Category

`Kleisli(polyFreeMPoly (polyProd X))`

**Objects**: Objects of `Over X`.

**Morphisms**: `A ->_T B` is
`A -> polyFreeMCarrier B (polyProd X)` — a function
assigning to each element of `A` a binary tree with
`B`-labeled leaves.

**Composition**: Given `f : A ->_T B` and
`g : B ->_T C`, the composite `g ._T f : A ->_T C` is
obtained by:

1. Apply `f` to get a tree with `B`-leaves
1. Substitute each `B`-leaf using `g` to get a
   tree-of-trees
1. Flatten using monadic multiplication
   `polyFreeMPolyMult`

**Identity**: `eta_A : A ->_T A` is
`polyFreeMPure A (polyProd X)` — embed each element as a
single-leaf tree.

**Category 2 properties**:

- Composition uses `polyFreeMBind` (or equivalently
  `polyFreeMPolyMult`)
- The monad laws (`polyFreeM_pure_bind`,
  `polyFreeM_bind_pure`, `polyFreeM_bind_assoc`) give
  category laws
- Contains `Over X` as a subcategory via the monad unit
- Morphisms represent "tree-building programs": given an
  input, produce a tree of outputs
- The Kleisli category is equivalent to the full
  subcategory of `PolyAlg (polyProd X)` on free algebras

**Category 2 use cases**: the "programming" category —
morphisms are programs that produce structured
(tree-shaped) output.

### Category 3: Lawvere Theory

**Objects**: Natural numbers `n in N`, representing formal
finite products `T^n` of the tree object `T`.

**Morphisms**: `n -> m` is an `m`-tuple of Kleisli
morphisms `T^n ->_T T`, where `T^n` is the `n`-fold
coproduct of the terminal object in `Over X` (or the
`n`-fold product in the opposite category).

In polynomial terms, this is the full subcategory of the
Kleisli category on objects of the form
`polyBetweenCoprod (Fin n) (fun _ => overTerminal X)`.

**Category 3 properties**:

- The opposite category is the Lawvere theory in the
  traditional sense
- Models of the theory in `Over X` are
  `polyProd X`-algebras
- Captures the "syntactic" aspect: morphisms are
  tree-expressions with variables
- Requires defining finite coproducts in `Over X` and
  their interaction with the Kleisli structure
- Neither Lawvere theories nor their models are in mathlib

**Category 3 use cases**: presenting the algebraic theory
of "magmas" (binary operations) syntactically; studying
which equations hold or fail.

### Category 4: Binary Decomposition Coalgebras

`PolyCoalg (polyProd X)`

**Objects**: Pairs
`(C : Over X, k : C -> polyEndoFunctor X (polyProd X) C)`
— an object `C` equipped with a binary decomposition
operation `k : C -> C *_X C`.

**Morphisms**: Coalgebra homomorphisms
`(C, k_C) -> (D, k_D)` — morphisms `h : C -> D` in
`Over X` such that `k_D . h = (h * h) . k_C`.

**Cofree objects**: `polyCofreeCarrier A (polyProd X)` is
the cofree `polyProd X`-coalgebra on `A`. The unfold
`polyCofixUnfold` gives the universal morphism from any
coalgebra.

**Category 4 properties**:

- Equivalent to copresheaves on
  `PolyCofreeCat (polyProd X)` via
  `polyCoalgCopresheafEquiv` — this is a topos
- Has all limits and colimits of size `(u, u)`
- The cofree category has objects `(x, s)` where `s` is
  an infinite binary tree shape at fiber `x`, and
  morphisms are paths (depth + position)
- Objects are "co-magmas" — sets with a decomposition
  into pairs
- Streams, processes, automata are natural examples

**Category 4 use cases**: behavioral/observational
semantics; the topos structure provides a logical
framework; connects to realizability via tree calculus.

### Category 5: Lambda-Bialgebras

**Objects**: Triples `(C, a, d)` where:

- `a : T(C) -> C` is a
  `polyFreeMonad (polyProd X)`-algebra
- `d : C -> D(C)` is a
  `polyCofreeComonad (polyProd X)`-coalgebra
- The pentagon compatibility holds:
  `T(d) ; lambda_C ; D(a) = a ; d`

**Morphisms**: Maps `h : C -> C'` that are simultaneously
algebra homomorphisms and coalgebra homomorphisms.

**Category 5 properties**:

- Uses the distributive law from
  `PolyDistributiveLaw.lean`
- Objects have both "syntax" (algebra: can build trees)
  and "behavior" (coalgebra: can observe/decompose)
- The compatibility condition ensures these interact
  coherently
- Subsumes both the algebra and coalgebra categories via
  forgetful functors
- Tree calculus reduction, if it satisfies the
  compatibility condition, would give a lambda-bialgebra

**Category 5 use cases**: models of tree calculus with
coherent syntax/semantics interaction; studying fixed-point
semantics.

### Category 6: Co-Kleisli Category

`CoKleisli(polyCofreeMPoly (polyProd X))`

**Objects**: Objects of `Over X`.

**Morphisms**: `A ->_D B` is
`polyCofreeCarrier A (polyProd X) -> B` — a function that
observes an annotated infinite binary stream and produces a
`B`-value.

**Composition**: Dual to Kleisli composition, using
comonadic comultiplication `polyCofreeMPolyComult`.

**Category 6 properties**:

- Dual to the Kleisli category (Category 2)
- Morphisms represent "observation programs": given a
  stream of inputs, produce a single output
- Contains `Over X` as a subcategory via the comonad
  counit
- The co-Kleisli category is equivalent to the full
  subcategory of `PolyCoalg (polyProd X)` on cofree
  coalgebras

**Category 6 use cases**: observational/behavioral
programming; stream processing.

## Relationship Between Categories

```text
                  forget
  PolyAlg(polyProd X) ------> Over X
       ^                       |   ^
       |                       |   |
  free |                 eta   |   | epsilon
       |                       v   |
       |               Kleisli(T)  |
       |                       |   |
       |               Cofree  |   | CoKleisli(D)
       |                       v   |
       v               forget      |
  PolyCoalg(polyProd X) ----> Over X
       |
       | polyCoalgCopresheafEquiv
       v
  (PolyCofreeCat(polyProd X) => Type u)
  [topos]
```

The lambda-bialgebra category sits at the intersection of
`PolyAlg` and `PolyCoalg`, connected by the distributive
law.

## Implementation Considerations

### Working in Over X

All definitions should work in `Over X` for general
`X : Type u`, using polynomial-functor universal properties
throughout. The specialization to `Type` (via `X = PUnit`)
is available whenever useful but should not be the primary
development target.

The polynomial infrastructure (`polyFixFold`,
`polyFreeMBind`, `polyFreeMPolyUnit`,
`polyFreeMPolyMult`, etc.) is already developed for
`Over X`, so the categorical constructions can be built
directly on this foundation.

### One Definition at a Time

Per the project workflow guidelines, each definition should
be written, compiled, and verified individually before
moving to the next. This is especially relevant for the
Kleisli category, where the category laws depend on the
monad laws which have already been proven.

### Universal Properties Only

Interaction with binary trees should go through universal
morphisms (fold, unfold, bind, pure, monad unit/mult,
comonad counit/comult) rather than manual pattern-matching
on tree constructors. This ensures that the definitions are
portable across different representations of binary trees.

## Binary-to-Finite-Branching Isomorphism

Binary trees with left-associative application are
isomorphic to finite-branching trees (rose trees). The
expression `(((a b) c) d)` can equivalently be read as a
node `a` with children `[b, c, d]`. See
[treecalcul.us/specification](https://treecalcul.us/specification/)
for this observation.

### The Isomorphism

For labeled binary trees `T = polyFreeMCarrier A (polyProd X)`:

```text
T  ~=  A *_X List(T)
```

A labeled binary tree is a root label `a : A` together
with a (possibly empty) list of subtree children, all at
the same fiber. The maps are:

- Forward: `leaf(a) |-> (a, [])`;
  `fork(t1, t2) |-> let (a, cs) = fwd(t1); (a, cs ++ [t2])`
- Backward: `(a, []) |-> leaf(a)`;
  `(a, ts) |-> foldl fork (leaf(a)) ts`

### Leaf, Stem, and Fork

Under this isomorphism, the tree calculus classification
by child count becomes:

- **Leaf**: 0 children — `(a, [])`
- **Stem**: 1 child — `(a, [t])`
- **Fork**: 2 children — `(a, [t1, t2])`

The triage rules (3a-3c) perform case analysis on this
child count. This resolves the earlier question of why
"stem" is not a constructor of the binary tree type: it
is a constructor of the finite-branching view, which
classifies trees by the length of their child list.

### Polynomial Interpretation

In `Over X`, the list functor is the free monad of the
identity polynomial:

```text
List(B) = polyFreeMCarrier B (polyBetweenId X)
```

So the isomorphism relates two free monads:

```text
polyFreeMCarrier A (polyProd X)
  ~=  A *_X polyFreeMCarrier T (polyBetweenId X)
```

where `T = polyFreeMCarrier A (polyProd X)` on the right.
This is a fixed-point characterization: binary trees
(free monad of product) satisfy the rose-tree equation
(root label times free monad of identity applied to
self).

### Implementation Plan

This isomorphism should be formalized early, as it:

1. Provides the leaf/stem/fork case analysis needed for
   tree calculus reduction rules
1. Connects `polyProdFreeM` to `polyBetweenId`, relating
   two polynomial structures already in the codebase
1. Should be constructed using only universal morphisms
   (fold for the forward direction, the algebra structure
   for the backward direction)

## Internal Logic and Self-Reflection

The theory should be able to reflect on itself not only
computationally (as tree calculus does — programs computing
on programs) but also *logically*: the theory should be
able to express and reason about its own morphisms,
propositions, and proofs, using its own terms.

This means that in addition to the *external* level (Lean
morphisms, copresheaves into Lean's `Type`), there is an
*internal* level: morphisms within the theory, copresheaves
into the theory's own topos, and a logic expressed by the
theory's own subobject classifier. The two levels must be
connected.

### External vs Internal Level

**External level** (in Lean):

- Objects of `Over X`, morphisms in `Over X`
- `PolyCoalg (polyProd X)` — coalgebras with Lean-level
  structure maps
- Copresheaves `PolyCofreeCat (polyProd X) => Type u`
- Lambda-bialgebras with Lean-level algebra/coalgebra maps

**Internal level** (within the theory):

- Morphisms expressible as binary tree terms
- Propositions and proofs within the topos's internal
  logic
- "Internal copresheaves" — copresheaves into the topos
  itself, not into Lean's `Type`
- Self-referential reasoning: the theory can state
  properties about its own terms and prove them using
  its own terms

### Role of Polynomials

Polynomial endofunctors can be expressed internally and
used to form inductive and coinductive types within the
theory. A polynomial `p : PolyEndo X` represents a
dependent type `Sigma (x : X), (B(x) -> X)` (following
Gambino-Kock). Composition of polynomials corresponds to
substitution, the free monad gives inductive types, and
the cofree comonad gives coinductive types.

However, the category of polynomial functors is not a
topos, so polynomials alone cannot provide a full internal
logic. The topos structure must come from elsewhere — the
polynomial level provides *syntax and types* while the
topos level provides *logic and propositions*.

### Candidate Internal Universes

#### Universe A: Coalgebra Topos

Via `polyCoalgCopresheafEquiv`, the category
`PolyCoalg (polyProd X)` is equivalent to copresheaves
on `PolyCofreeCat (polyProd X)`, which is a topos. This
topos has:

- A subobject classifier `Omega` — as a copresheaf,
  `Omega(c)` is the set of sieves on `c` in
  `PolyCofreeCat (polyProd X)`. Under the coalgebra
  equivalence, `Omega` is a specific coalgebra
  `(V_Omega, k_Omega)` carrying "truth values" with
  binary decomposition.
- Exponential objects `[A, B]` (internal hom) — as a
  copresheaf, `[F, G](c) = Nat(y(c) * F, G)`. Under
  the coalgebra equivalence, these are specific
  coalgebras.
- Power objects `Omega^A` (internal predicates on A).
- Full higher-order intuitionistic logic.

An "internal morphism from A to B" is a global element
`1 -> [A, B]` in this topos. An "internal proposition"
is a global element `1 -> Omega`. This is the most
categorical approach and connects directly to
`polyCoalgCopresheafEquiv`, which already exists in the
codebase.

#### Universe B: Realizability Topos

If tree calculus is formalized as a PCA, the associated
realizability topos has:

- Objects: assemblies `(X, E)` where `X` is a set and
  `E : X -> P(T)` assigns realizers (sets of trees) to
  each element
- A proposition is "realized" if a tree computes a
  witness
- The internal logic is intuitionistic with computational
  content: every proof is a program

The realizability topos connects computational and
logical reflection: a statement about trees is
"internally provable" iff there is a tree that *computes*
the proof.

Whether the coalgebra topos (Universe A) and the
realizability topos (Universe B) are *equivalent* is an
open question. If they are, this would be very
convenient: it would mean that the two perspectives
(coalgebraic/categorical and computational/realizability)
are not a choice but two views of the same structure.

#### Universe C: Free Topos with Binary Tree Object

The free topos with NNO is a well-studied construction:
the initial object in the 2-category of toposes equipped
with a natural numbers object. It is the "generic" topos
for reasoning about natural numbers, containing no more
logical content than what follows from the topos axioms
and the NNO universal property.

By analogy, the *free topos with unlabeled-binary-tree
object* would be the initial topos equipped with an
object `T` and morphisms `leaf : 1 -> T` and
`fork : T * T -> T` satisfying the initial algebra
universal property (parametrized PBTO).

This has several notable properties:

- It is likely logically equivalent to the free topos
  with NNO: both are freely generated by an inductive
  type (natural numbers = free algebra of `1 + (-)`,
  binary trees = free algebra of `1 + (-) * (-)`).
  The two inductive types are mutually encodable (a
  natural number encodes as a right-leaning tree; a
  tree encodes as a natural number via any tree
  traversal), so the resulting toposes should have the
  same internal logic up to interpretation.
- However, binary trees are much more convenient for
  expressing data structures: pairs, lists, tagged
  unions, nested records, etc. all embed directly
  into binary trees without choosing a specific pairing
  function on natural numbers.
- The free topos abstracts away the specific pairing
  function — it provides a *universal* binary tree
  object rather than a particular encoding of pairs
  into some other type.
- The morphisms of the free topos are exactly the
  primitive tree-recursive functions (the Lawvere
  theory from Approach A), and the logic is the
  internal logic of the topos generated by those
  morphisms.

This perspective connects to Approach A (the Lawvere
theory / PBTO) and provides a canonical "minimal"
internal logic for binary trees.

### Impact on Design

#### The Kleisli category needs internal representation

The external Kleisli category (Phase 1) is a `Category`
instance in Lean. For self-reflection, we also need a
coalgebra (or copresheaf) that *represents* the Kleisli
category within the topos — an "internal Kleisli object"
whose global elements correspond to Kleisli morphisms.

#### Reduction should be expressible internally

The tree calculus reduction rules (Phase 2) should be
defined both as external Lean functions *and* as
coalgebra morphisms within the topos. The
GSOS/lambda-bialgebra framework gives a coalgebraic
(hence internal-to-the-topos) characterization of
operational semantics.

#### The subobject classifier is a first-class object

We should define `Omega` — the subobject classifier of
`PolyCoalg (polyProd X)` — as a concrete coalgebra, not
just assert its existence from topos theory. This is the
"type of propositions" internal to the theory.

Since `PolyCoalg (polyProd X) ~= copresheaves`, we can
compute `Omega` concretely: `Omega(c)` is the set of
sieves on `c` in `PolyCofreeCat (polyProd X)`. The
cofree category's morphisms are tree paths (depth +
position), so sieves are downward-closed sets of tree
paths.

#### Exponentials give internal function spaces

For any two coalgebras `A` and `B`, the exponential
`[A, B]` in the topos gives the "internal function
space." Under the copresheaf equivalence:

```text
[F, G](c) = Nat(y(c) * F, G)
```

We should compute these concretely and relate them to
coalgebras.

#### Polynomials provide internal type formation

Polynomial endofunctors expressed within the theory give
internal inductive/coinductive types. The free monad
construction gives internal inductive types; the cofree
comonad gives internal coinductive types. These sit
inside the topos but do not exhaust its logical content
(since the polynomial category is not a topos).

### Relationship Between Levels

```text
Polynomial level         Coalgebra topos level
(syntax, types)          (logic, propositions)
       |                         |
       |  free/cofree            | copresheaf equiv
       v                         v
  PolyAlg / PolyCoalg    Copresheaves on CofreeCat
       |                         |
       |  PCA structure          | realizability
       v                         v
  Tree calculus           Realizability topos
  (computation)           (realized proofs)
```

The polynomial level gives syntax and types. The
coalgebra topos gives logic and propositions. Tree
calculus gives computation. The realizability topos (if
it exists and is related) connects computation to logic:
a proposition is true when a tree computes its proof.

The free topos with binary tree object sits above all
of these as the "universal" setting: any topos with a
binary tree object receives a unique logical functor
from the free topos.

## Open Questions

1. **Paramorphism vs catamorphism**: Should the PBTO
   universal property include access to the original
   subtrees (paramorphism) or only the recursive results
   (catamorphism)? The catamorphism is `polyFixFold`; the
   paramorphism requires additional infrastructure.

1. **Tree calculus encoding**: What is the polynomial
   morphism that best encodes the 5 triage rules? Can the
   GSOS framework (`PolyGSOSRule`) be completed and used,
   or is a direct coalgebra encoding better? The
   binary-to-finite-branching isomorphism provides a
   natural decomposition for the triage cases.

1. **Realizability connection**: Does the coalgebra topos
   `PolyCoalg (polyProd X) ~= copresheaves` relate to the
   realizability topos of the tree calculus PCA? If so,
   how?

1. **Finite-limit extension**: For the Lawvere theory
   (Approach A), how do equalizers in the polynomial
   category (`polyBetweenEq`) interact with the Kleisli
   structure? Can we get a finite-limit theory by combining
   products and equalizers?

1. **Triage via child-count decomposition**: The
   binary-to-finite-branching isomorphism decomposes trees
   as `A *_X List(T)`. The list `List(T)` can be split by
   length into `1 + T + T*T + T*T*T + ...`. The triage
   rules use only the first three cases (0, 1, 2
   children). Can this truncation be expressed as a
   polynomial equalizer or quotient?

1. **Unlabeled trees**: Specializing to unlabeled trees by
   applying the free monad to the terminal object gives
   `PolyFreeMShape (polyProd X)`. The tree calculus
   operates on unlabeled trees. Should the Kleisli category
   use the terminal object as the generating object?

1. **Coalgebra topos vs realizability topos**: Are these
   equivalent for the tree calculus PCA? If so, the
   coalgebraic and realizability perspectives would be
   two views of the same structure, and the choice of
   "internal universe" would not be a choice at all.

1. **Free topos with binary tree object**: Is the free
   topos with binary tree object (initial algebra of
   `1 + (-) * (-)`) logically equivalent to the free
   topos with NNO (initial algebra of `1 + (-)`)? Both
   are freely generated by an inductive type, and the
   two types are mutually encodable.

1. **Concrete subobject classifier**: What does `Omega`
   look like concretely as a coalgebra of `polyProd X`?
   Sieves on objects `(x, s)` of
   `PolyCofreeCat (polyProd X)` are downward-closed sets
   of tree paths — what structure does this carry?

1. **Internal Kleisli representation**: Can the external
   Kleisli category be represented as a coalgebra or
   copresheaf within the topos, so that the internal
   logic can reason about Kleisli morphisms?

1. **Primitive-recursive fragment definition**: What is
   the precise syntactic criterion for the
   primitive-recursive subset of tree calculus? The
   criterion must be tight enough that membership is
   decidable by a primitive-recursive program, and
   broad enough to include fold over binary trees with
   parameters.

1. **Self-recognizer expressibility**: Can a correct
   and complete recognizer for the primitive-recursive
   fragment be written within the fragment itself? If
   the fragment is too weak to express its own
   recognizer, it must be widened; if too strong, it
   may not terminate.

1. **Proof-carrying code format**: When extending
   beyond the syntactic criterion (Option 2), what
   constitutes a valid termination proof expressed as a
   tree? Candidates include: ordinal notations below
   epsilon_0, well-founded recursion witnesses, or
   sized-type annotations. The format must be
   verifiable by a primitive-recursive checker.

1. **Language tower granularity**: What intermediate
   language layers sit between the primitive-recursive
   subset and full tree calculus? Candidates include:
   multiply recursive functions (Ackermann-level),
   System T (higher-order primitive recursion),
   System F (polymorphism), and bar recursion. Each
   layer would have its own type-checker written in
   the layer below.

## Jay's Type System and Its Relevance

The paper *Typed Program Analysis without Encodings*
(Jay, PEPM '25) develops a type system for tree calculus
that has several properties relevant to our design. A
detailed description of the type system is in
[tree-calculus.md](../tree-calculus.md#type-system). This
section analyzes how the type system, or ideas from it,
could inform the construction of our own language.

### Summary of the Type System

The type grammar is
`T ::= L | S U | F U V | U -> V | X | forall X.T | A T`.
The first three formers are *tree types* that describe
a program's structure as data; `U -> V` describes it as
a function. A subtyping relation connects the two views:
each reduction rule of the calculus inspires a subtyping
axiom (e.g., `F L U < V -> U` for the K rule). Only
two derivation rules are needed (leaf subtyping and
application); the subtyping relation carries the entire
computational content. Every program is typeable. Subject
reduction holds: if `t : T` and `t --> t'` then `t' : T`.

### Structural Correspondence with Polynomials

The tree type formers `L`, `S U`, `F U V` correspond
directly to the coproduct structure of
`polyTranslate A (polyProd X)`:

- `L` corresponds to the `Sum.inl` (leaf/label) case of
  `polyTranslate`.
- `S U` and `F U V` correspond to the `Sum.inr` case
  (the `polyProd` branch), decomposed via the
  binary-to-finite-branching isomorphism into stem (1
  child) and fork (2 children) cases.

The tree type `progty(p)` is essentially the shape
information captured by `PolyFreeMShape P`: it records
which constructor (leaf, stem, or fork) appears at each
node of the tree. In polynomial terms, the tree type
functor is a dependent polynomial whose positions encode
the node types.

This means that our polynomial infrastructure can
represent tree types natively: a tree type is a section
of the shape polynomial, and the subtyping relation is
a preorder on such sections.

### Subtyping as a Preorder Category

The subtyping relation `U < V` defines a preorder on
types. This preorder can be formalized as a thin
category (at most one morphism between any two objects):

- Objects: types.
- Morphisms: subtyping witnesses `U < V`.

The subtyping axioms are generating morphisms; closure
under reflexivity, transitivity, and contravariance of
function types is the free completion. This category is
an enriched version of the type structure: it carries
the operational semantics of the calculus.

The preorder category could be constructed within our
polynomial framework. The types are elements of a
W-type (built from `L`, `S`, `F`, `->`, `forall`, `A`
as constructors), and the subtyping relation is a
decidable binary relation on that W-type generated by
the axioms.

### Implications for the Primitive-Recursive Fragment

The `Omega_2` subtyping axiom
(`Omega_2 < Omega_2 -> Fix (forall X_vec. U -> V)`) is
the sole axiom that enables typing of general recursive
functions. Removing it restricts the system to
terminating (primitive-recursive) programs — functions
definable via `polyFixFold` into suitable algebras.

This gives a *type-theoretic characterization* of the
primitive-recursive fragment that complements the
*syntactic characterization* described in the
bootstrapping strategy below. The two characterizations
are:

1. **Syntactic**: a term is primitive-recursive if it
   uses fold (`polyFixFold`) but no general fixed-point
   combinators (`Y`, `Z`, `omega_2`).
2. **Type-theoretic**: a term is primitive-recursive if
   it is typeable in the system without the `Omega_2`
   subtyping axiom.

The self-recognizer (Phase 2) could use either
characterization, or both: the syntactic check is
easier to implement as a tree-calculus program; the
type-theoretic check is more principled but requires
a type-checker.

### Implications for the Self-Recognizer

The self-recognizer needs to decide whether a given tree
is in the primitive-recursive fragment. Jay's type system
suggests two approaches:

1. **Syntactic recognizer**: inspect the tree structure
   for the absence of fixpoint combinators. This is a
   pattern-matching task on trees, directly expressible
   using triage.

2. **Type-checking recognizer**: implement a type-checker
   for the restricted system (without `Omega_2`) as a
   tree-calculus program. A term is in the
   primitive-recursive fragment if and only if the
   type-checker accepts it.

The syntactic approach is simpler and should come first
(as planned). The type-checking approach is an
intermediate step toward proof-carrying code (Phase 4),
since a type derivation is a form of termination
evidence.

### The A Type Former and Self-Interpretation

The `A T` type ("as-function type") was introduced to
handle a specific difficulty in typing the
self-interpreter `bf`: when `bf` recursively evaluates
both branches of a fork, the results are not yet known
to be function types. The `A T` wrapper defers this
obligation.

For our bootstrapping strategy, this has two
implications:

1. **Self-recognizer typing**: if we want the
   self-recognizer itself to be typed (in addition to
   termination-proved), the `A` type former may be
   needed to type the recognition of programs that
   will eventually be applied.

2. **Language tower**: higher layers of the language
   tower (Phase 4) may need `A`-like type formers
   to express deferred typing obligations, especially
   when building type-checkers that must reason about
   programs before they are fully applied.

### Parametric Polymorphism and the Language Tower

Jay's system combines parametric polymorphism
(`forall X`) with subtyping. Instantiation of quantified
types is handled by subtyping rather than by a separate
elimination rule. This design has implications for
our language tower:

- **Polymorphism at the base**: System F-style
  polymorphism does not need to be added as a separate
  language layer. It can be incorporated into the base
  type system via the subtyping relation. The type
  constants `Bool = forall X. X -> X -> X` and
  `Nat = forall X. (X -> X) -> (X -> X)` are already
  polymorphic.

- **Subtyping subsumes instantiation**: in conventional
  systems, universal types require explicit type
  application. In Jay's system, subtyping handles
  this: `forall X. T < {U/X} T`. This is potentially
  simpler to implement as a tree-calculus program,
  since subtyping checking is a recursive computation
  on type trees.

- **Layer separation**: the language tower could be
  organized by which subtyping axioms are available at
  each layer, rather than by which type formers are
  available. The base layer has the structural and
  reduction axioms but not `Omega_2`. The next layer
  adds `Omega_2` for general recursion. Further layers
  could add `A` types, covariance axioms, etc.

### Covariance and Parametricity

The general triage subtyping rule requires the type
variable `Z` to appear *covariantly* in `T`. This
connects to the parametricity / free theorems
perspective referenced in CLAUDE.md: covariant functors
on types correspond to polynomial functors, and the
covariance condition is the type-level analogue of the
polynomial condition.

In our polynomial setting, this means:

- Generic queries (like `isLeaf`, `size`, `equal`) are
  natural transformations of a covariant functor.
- The covariance requirement on the triage rule is the
  type-theoretic expression of the fact that triage
  defines a natural transformation.
- Our `polyFixFold` (catamorphism) already captures
  covariant functorial action on types. The connection
  between fold and the covariance condition in the
  triage subtyping rule should be made precise.

### Tags and Proof-Carrying Code

Jay's paper notes that typed tree calculus can be
embedded within untyped tree calculus using tags. A
tag attaches metadata (such as type information) to a
term without changing its functional behavior:
`tag{t, f} x = f x` and `getTag(tag{t, f}) = t`.

This directly informs the proof-carrying code design
(Phase 4, Option 2). A "termination proof" could be:

- A type derivation tree, encoded as a tagged tree.
  Each node carries its type as a tag. The verifier
  checks that the tags form a valid derivation.
- An ordinal notation or well-founded recursion
  witness, similarly encoded as a tagged tree.

The tagging mechanism is already defined within tree
calculus (Section 5 of the paper), so no additional
infrastructure is needed for attaching evidence to
programs.

### Type Inference and Decidability

The paper does not address type inference, and the
author's subsequent blog posts (January-March 2025)
identify significant obstacles: the mutual recursion
between subtyping checking and result-type inference,
and the difficulty of handling `A` types and covariance
in an inference algorithm.

For our purposes, this has implications:

- **The primitive-recursive fragment may be easier.**
  Without `Omega_2`, `A` types, or covariance axioms,
  the subtyping relation is simpler. Type inference
  for the restricted system may be decidable, even if
  inference for the full system is not.
- **Type-checking vs type inference.** For the
  self-recognizer, we need type-*checking* (given a
  term and a type, verify the derivation), not type
  *inference* (given a term, find a type). Type-
  checking is typically easier than inference and may
  be feasible even when inference is not.
- **Type-checking as a tree-calculus program.** The
  subtyping relation is defined by structural recursion
  on types, and type derivation is defined by
  structural recursion on terms. Both are candidates
  for implementation as tree-calculus programs in the
  primitive-recursive fragment (they are fold-definable
  over the type and term trees).

### Open Questions from the Type System

The following questions arise from the type system
analysis and relate to our existing open questions:

- **Type-theoretic vs syntactic characterization of the
  primitive-recursive fragment**: are they equivalent?
  That is, is a tree-calculus term typeable without
  `Omega_2` if and only if it avoids general fixpoint
  combinators?

- **Type-checking in the primitive-recursive fragment**:
  is type-checking for the restricted system (without
  `Omega_2`) decidable? If so, can the type-checker be
  written as a primitive-recursive tree-calculus
  program?

- **Subtyping as polynomial preorder**: can the
  subtyping relation be expressed as a morphism in the
  polynomial category, making it part of the internal
  structure rather than external meta-theory?

- **Covariance and parametricity**: does the covariance
  condition in the general triage rule correspond to
  naturality of the fold / catamorphism?

- **Tags and realizability**: do tagged terms (carrying
  type derivations) correspond to realizers in the
  realizability topos? That is, is a type derivation
  for a term exactly a realizer witnessing the
  assembly morphism?

## Bootstrapping Strategy: Tree Calculus First

### Motivation

The original plan considered starting with a weak language
(primitive tree-recursive functions via the Lawvere theory /
PBTO from Approach A) and extending upward toward Turing
completeness. An alternative strategy reverses this: start
with tree calculus (already Turing-complete and
self-reflective), carve out a terminating subset, and use
that subset to bootstrap further language layers.

The reason to avoid starting with a Turing-complete
calculus is that type-checking requires termination: a
type-checker that might loop is not a type-checker.
However, the realizability topos construction requires
termination witnesses anyway — elements of RT(T) are
assemblies carrying realizers, and morphisms are tracked
by trees that are *total* on their domain. Building
termination witnesses is therefore not extra work but
part of the target construction.

### The Approach

1. **Start with tree calculus.** Formalize the five
   triage reduction rules on
   `PolyFix (polyTranslate (overTerminal X) (polyProd X))`
   — finite unlabeled binary trees. Tree calculus is
   well-studied, with algorithms and proofs formalized
   in Barry Jay's book (*Reflective Programs in Tree
   Calculus*) and in Coq. See
   [tree calculus reference](../tree-calculus.md) for
   syntax, reduction rules, and references.

2. **Identify the primitive-recursive subset.** Define a
   syntactic fragment of tree calculus terms that can
   only compute primitive-recursive functions over binary
   trees. This fragment corresponds to functions definable
   via `polyFixFold` (catamorphism) into suitable algebras
   — the parametrized binary tree object from Approach A.
   Terms in this fragment use fold but not general
   fixed-point combinators (such as Y or Turing's
   fixed-point combinator expressed in tree calculus).

3. **Prove termination in Lean.** Show that every term
   in the syntactic fragment terminates: reduction
   always reaches a normal form. The proof strategy is
   structural: fold on a well-founded tree terminates
   because the tree's height decreases at each recursive
   call. Lean verifies this against standard mathematics.

4. **Write a self-recognizer.** Implement a tree-calculus
   program, *itself in the primitive-recursive subset*,
   that decides whether a given tree is in the
   primitive-recursive subset. Tree calculus's triage
   rules enable this directly: the recognizer inspects
   the structure of its input (another tree) without
   Gödel encoding. Prove in Lean that this recognizer
   is correct (sound and complete with respect to the
   syntactic criterion) and that it terminates.

5. **Bootstrap.** The self-recognizer serves as a
   gatekeeper: only programs it accepts are eligible to
   serve as type-checkers for further language layers.
   These layers can define more expressive type systems
   (System T, System F, etc.), each verified by a
   type-checker in the layer below, building up in
   stages — but always with tree calculus as the ambient
   computational universe.

### Design Principles

- **Minimize code to self-description.** The goal is to
  reach a self-describing language — one that can express
  itself without external interpretation — with as
  little code and as little structural overhead as
  possible. Tree calculus is well-suited because its
  syntax (binary trees) and semantics (five reduction
  rules) are both minimal.

- **Lean verifies assumptions, does not interpret.**
  Lean's role is to verify that the bootstrapping
  assumptions hold (termination of the
  primitive-recursive subset, correctness of the
  self-recognizer) against standard mathematics. Once
  verified, the language operates on its own terms. Lean
  is a proof checker for the foundation, not an
  interpreter for the language.

- **Syntactic criterion first, proof-carrying code
  later.** At least two possibilities exist for recognizing
  terminating programs:

  - *Syntactic criterion (Option 1)*: Define a syntactic
    fragment and check membership. This is conservative
    (rejects some terminating programs) but sound and
    decidable. It connects to the Lawvere theory / PBTO
    approach (Approach A): the syntactic fragment is
    the Lawvere theory of binary tree algebras, where
    every morphism is definable by catamorphism.

  - *Proof-carrying code (Option 2)*: A program is
    accepted when accompanied by a termination proof
    (itself a tree). The checker verifies proof validity.
    This is more expressive but requires defining valid
    termination proofs within the system. It connects
    to the realizability topos approach (Approach B):
    realizers carry computational evidence, and the
    termination proof is part of that evidence. Tree
    calculus's self-reflective nature (triage rules
    allow programs to inspect proof structure) makes
    this a natural extension.

  Option 1 is the starting point. Option 2 is a
  subsequent application of the reflective capabilities,
  built *within* the language on top of Option 1's
  type-checkable syntax.

### Why Tree Calculus First Works

- **Self-application is native.** Triage rules let
  programs inspect other programs structurally. The
  self-recognizer ("is this program primitive-recursive?")
  is a tree operating on trees, which is what tree
  calculus does natively. In a system based on System T
  or primitive recursive functionals, writing a
  self-recognizer would require encoding programs as
  data first.

- **Termination witnesses are realizability
  infrastructure.** The termination proofs built for
  primitive-recursive operators are the realizers needed
  for the realizability topos. Each primitive-recursive
  function gets a realizer (a tree) that witnesses its
  totality. This work directly constructs the assembly
  structure of RT(T).

- **Polynomial infrastructure connects directly.** Tree
  calculus operates on elements of
  `PolyFix (polyTranslate (overTerminal X) (polyProd X))`.
  The fold `polyFixFold` gives catamorphism, which is
  primitive recursion over trees. The primitive-recursive
  subset corresponds to functions definable via
  `polyFixFold` into suitable algebras.

- **The subset recognizer bootstraps the tower.** Once
  termination-checked, the primitive-recursive subset
  can define more sophisticated type systems, which
  verify termination of broader program classes, building
  up in layers — always within the ambient tree calculus.

### Relationship to Earlier Approaches

The bootstrapping strategy subsumes the earlier phased
plan (Approaches A, B, C) but reorders it:

- **Approach A (PBTO / Lawvere theory)** becomes the
  *syntactic criterion* for the primitive-recursive
  subset — the same mathematical content, but situated
  within tree calculus rather than developed
  independently.

- **Approach B (tree calculus / bialgebra semantics)**
  becomes the *starting point* rather than a later
  phase. The reduction rules, PCA structure, and
  lambda-bialgebra are formalized first.

- **Approach C (hybrid / incremental)** is preserved:
  the layers (primitive-recursive, then richer type
  systems, then proof-carrying code) are incremental,
  each independently valuable.

The Kleisli category, coalgebra topos, and internal
representation work from the original plan remain
relevant and can proceed in parallel with the
bootstrapping.

## Recommended Execution Order

### Phase 1: Kleisli Category and Isomorphism

1. Define `treeFoldAlg` — convenience wrapper packaging a
   leaf map and fork map into a
   `polyTranslate A (polyProd X)`-algebra
1. Define `treeFold` — the parametrized fold, specialized
   to `polyProd`
1. Prove `treeFold_unique` — uniqueness, from
   `polyFixFoldUnique`
1. Prove the binary-to-finite-branching isomorphism:
   `polyFreeMCarrier A (polyProd X) ~=`
   `A *_X polyFreeMCarrier T (polyBetweenId X)` using
   fold for the forward direction and algebra structure
   for the backward direction
1. Define `treeKleisliHom` — the morphism type
   `A -> polyFreeMCarrier B (polyProd X)`
1. Define `treeKleisliComp` — composition via bind/graft
1. Define `treeKleisliId` — identity via pure/unit
1. Prove `treeKleisli_id_comp`, `treeKleisli_comp_id`,
   `treeKleisli_comp_assoc` — category laws from monad
   laws
1. Define `treeKleisliCategory` — the Category instance

### Phase 1.5: Internal Representation

1. Define `Omega` concretely as a coalgebra of
   `polyProd X` — the subobject classifier of the
   coalgebra topos
1. Compute what sieves on `PolyCofreeCat (polyProd X)`
   look like concretely (downward-closed sets of tree
   paths)
1. Define the exponential `[A, B]` concretely for
   specific coalgebras A, B
1. Represent the Kleisli category (or at least its
   morphism set) as a coalgebra/copresheaf within the
   topos

### Phase 2: Tree Calculus Reduction and Bootstrapping

1. Use the finite-branching isomorphism to define
   leaf/stem/fork case analysis (child count 0, 1, 2)
1. Define the 5 triage reduction rules both externally
   (Lean functions) and internally (coalgebra morphisms)
1. Show confluence (the 5 rules are non-overlapping)
1. Define the PCA structure (K and S from rules 1-2)
1. Define the primitive-recursive syntactic fragment:
   terms that compute only via `polyFixFold` into
   algebras, excluding general fixed-point combinators
1. Prove in Lean that all terms in the syntactic
   fragment terminate (reduction reaches a normal form)
1. Implement the self-recognizer: a tree-calculus
   program, itself in the primitive-recursive fragment,
   that decides membership in the fragment
1. Prove in Lean that the self-recognizer is correct
   (sound and complete) and terminates
1. Connect to GSOS if the infrastructure is available

### Phase 3: Lambda-Bialgebra and Topos

1. Specialize the distributive law to `polyProd X`
1. Construct a lambda-bialgebra from the tree calculus
   reduction
1. Explore the coalgebra topos structure for tree
   behaviors
1. Investigate the realizability topos and its
   relationship to the coalgebra topos

### Phase 4: Language Tower and Proof-Carrying Code

1. Use the primitive-recursive self-recognizer as a
   gatekeeper to define which programs are eligible
   to serve as type-checkers
1. Define richer type systems (System T, System F
   analogues) as tree-calculus programs, type-checked
   by the primitive-recursive layer
1. Investigate proof-carrying code (Option 2): extend
   the recognizer to accept programs accompanied by
   termination proofs expressed as trees, verified by
   the recognizer using triage
1. Investigate the free topos with binary tree object
1. Compare its internal logic with the free topos with
   NNO — are they logically equivalent?
1. Relate the free topos to the coalgebra topos and/or
   the realizability topos
1. Study how polynomials expressed internally provide
   inductive/coinductive type formation within the
   topos
