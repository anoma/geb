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

- [Tree Calculus spec](https://treecalcul.us/specification/)
- [Barry Jay's Coq formalization](https://github.com/barry-jay-personal/tree-calculus)
- Barry Jay, "Reflective Programs in Tree Calculus"
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

## Open Questions

1. **Paramorphism vs catamorphism**: Should the PBTO
   universal property include access to the original
   subtrees (paramorphism) or only the recursive results
   (catamorphism)? The catamorphism is `polyFixFold`; the
   paramorphism requires additional infrastructure.

1. **Tree calculus encoding**: What is the polynomial
   morphism that best encodes the 5 triage rules? Can the
   GSOS framework (`PolyGSOSRule`) be completed and used,
   or is a direct coalgebra encoding better?

1. **Realizability connection**: Does the coalgebra topos
   `PolyCoalg (polyProd X) ~= copresheaves` relate to the
   realizability topos of the tree calculus PCA? If so,
   how?

1. **Finite-limit extension**: For the Lawvere theory
   (Approach A), how do equalizers in the polynomial
   category (`polyBetweenEq`) interact with the Kleisli
   structure? Can we get a finite-limit theory by combining
   products and equalizers?

1. **Triage as coalgebra**: The triage operation (case
   analysis on leaf/stem/fork) is a 3-way decomposition.
   Is there a polynomial whose coalgebras capture triage?
   The translate polynomial `polyTranslate` gives
   `1 + (- * -)`, which distinguishes leaves from forks —
   but stems (`triangle x`) are application of one
   argument, not a constructor of the binary tree type.

1. **Unlabeled trees**: Specializing to unlabeled trees by
   applying the free monad to the terminal object gives
   `PolyFreeMShape (polyProd X)`. The tree calculus
   operates on unlabeled trees. Should the Kleisli category
   use the terminal object as the generating object?

## Recommended Execution Order

### Phase 1: Kleisli Category (Primary Target)

1. Define `treeFoldAlg` — convenience wrapper packaging a
   leaf map and fork map into a
   `polyTranslate A (polyProd X)`-algebra
1. Define `treeFold` — the parametrized fold, specialized
   to `polyProd`
1. Prove `treeFold_unique` — uniqueness, from
   `polyFixFoldUnique`
1. Define `treeKleisliHom` — the morphism type
   `A -> polyFreeMCarrier B (polyProd X)`
1. Define `treeKleisliComp` — composition via bind/graft
1. Define `treeKleisliId` — identity via pure/unit
1. Prove `treeKleisli_id_comp`, `treeKleisli_comp_id`,
   `treeKleisli_comp_assoc` — category laws from monad
   laws
1. Define `treeKleisliCategory` — the Category instance

### Phase 2: Tree Calculus Reduction

1. Define the 5 triage reduction rules as morphisms (or
   as a coalgebra)
1. Show confluence (the 5 rules are non-overlapping)
1. Define the PCA structure (K and S from rules 1-2)
1. Connect to GSOS if the infrastructure is available

### Phase 3: Lambda-Bialgebra and Topos

1. Specialize the distributive law to `polyProd X`
1. Construct a lambda-bialgebra from the tree calculus
   reduction
1. Explore the coalgebra topos structure for tree
   behaviors
1. Investigate the realizability connection
