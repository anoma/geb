<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Polynomial Functors Between Presheaf Categories (Parametric Right Adjoints)](#polynomial-functors-between-presheaf-categories-parametric-right-adjoints)
  - [Mathematical Definition](#mathematical-definition)
  - [Relationship to Polynomial Functors Between Slices](#relationship-to-polynomial-functors-between-slices)
  - [Equivalent Characterizations](#equivalent-characterizations)
    - [LCCC Decomposition](#lccc-decomposition)
    - [Discrete Fibration Form](#discrete-fibration-form)
  - [Implementation in GebLean](#implementation-in-geblean)
    - [Representation](#representation)
    - [Source Files](#source-files)
    - [Existing Infrastructure Used](#existing-infrastructure-used)
  - [Discrete-Category Equivalence](#discrete-category-equivalence)
  - [Mathematical References](#mathematical-references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Polynomial Functors Between Presheaf Categories (Parametric Right Adjoints)

## Mathematical Definition

A **parametric right adjoint (PRA)** between presheaf categories
`[I^op, Set]` and `[J^op, Set]` is a functor determined by the
following data:

- A presheaf `A : [J^op, Set]` (the **positions** presheaf)
- A functor `E : el(A)^op -> [I^op, Set]` (the **directions**
  functor), where `el(A)` is the category of elements of `A`

The PRA functor `P : [I^op, Set] -> [J^op, Set]` acts on a
presheaf `Z` by:

```text
P(Z)(j) = coprod_{a in A(j)} Hom_{[I^op, Set]}(E(j,a), Z)
```

Each summand is the set of natural transformations from the
directions presheaf `E(j,a)` to `Z`. The result is a presheaf
on `J` via the functoriality of `(A, E)`: given `g : j -> j'`
in `J`, the restriction map uses `A`'s action on positions and
`E`'s action on directions (precomposing natural
transformations).

## Relationship to Polynomial Functors Between Slices

PRAs generalize polynomial functors between slice categories
of `Type`. A polynomial functor `Over X -> Over Y` is given by
a `Y`-indexed family of pairs `(I_y, F_y)` where `I_y : Type`
and `F_y : I_y -> Over X`:

```text
P(A)(y) = Sigma_{i : I_y} Hom_{Over X}(F_y(i), A)
```

When `I` and `J` are discrete categories (types with only
identity morphisms), `Presheaf I ~ Type^I ~ Over I`. In this
case, the PRA formula reduces to the slice polynomial formula:
the presheaf `A` is just a `J`-indexed family of types, and
the directions functor `E` is just a family of objects in
`Over I`, recovering `PolyFunctorBetweenCat I J`.

The difference in the non-discrete case: positions `A(j)` vary
functorially in `j` (not just pointwise), and directions
`E(j,a)` are full presheaves on `I` (not just objects of
`Over I`), with compatible transition maps indexed by the
category of elements of `A`.

## Equivalent Characterizations

### LCCC Decomposition

For a morphism `p : B -> A` in `[I^op, Set]` (endofunctor
case), the PRA factors as:

```text
[I^op, Set] --B*--> [I^op, Set]/B --Pi_p--> [I^op, Set]/A --Sigma_A--> [I^op, Set]
```

where `B*` is base change (product), `Pi_p` is the dependent
product (right Kan extension along the map on categories of
elements), and `Sigma_A` is the dependent sum (forgetful
functor). No pushouts or coends appear: `Sigma` is just
forgetting, `B*` is a product, and `Pi_p` is a limit.

### Discrete Fibration Form

A PRA between presheaf categories equals the composite:

```text
DFib/I --d*--> DFib/E --c*--> DFib/K --p!--> DFib/J
```

for a polynomial `I <-d- E -c-> K -p-> J` where `p` is a
discrete fibration and `(d, c)` is a two-sided discrete
fibration.

## Implementation in GebLean

### Representation

The PRA is represented as a functor from `J^{op}` into the
category of coproducts of covariant representables on the
domain presheaf category:

```lean
abbrev PresheafPRACat (I J) : Cat :=
  Cat.of (J^{op} ⥤ CoprodCovarRepCat (I^{op} ⥤ Type))
```

At each `j : J`, the functor gives a polynomial
`(A(j), E_j) : CoprodCovarRepCat (Presheaf I)`. The functor
action on morphisms in `J^{op}` provides the restriction maps
(reindexing on positions, precomposition on directions),
making the evaluation a presheaf on `J` without any separate
naturality condition or `Subtype`.

### Source Files

| File | Contents |
| ---- | -------- |
| `GebLean/PresheafPRA.lean` | Definition, accessors, evaluation functor |
| `GebLean/Polynomial.lean` | `CoprodCovarRepCat`, `ccrEval`, `ccrToFunctor` |
| `GebLean/Utilities/Presheaf.lean` | `Presheaf`, `Copresheaf`, Yoneda |
| `GebLean/Utilities/Elements.lean` | `ElementsContra'`, slice-presheaf equiv |
| `GebLean/Utilities/Families.lean` | `FamilyCat`, `ccrIndex`, `ccrFamily` |

### Existing Infrastructure Used

- `CoprodCovarRepCat D`: objects are `(I : Type, F : I -> D)`,
  representing `A |-> Sigma_i Hom_D(F(i), A)`. Morphisms have
  reindexing on positions and contravariantly-directed fiber
  morphisms.
- `ccrEval P A`: evaluates to `Sigma_i (F(i) -> A)`.
- `ccrEvalMap f`: functorial action via postcomposition.
- `polyBetweenEvalFunctor`: the slice-category analogue, for
  reference on how evaluation functors are structured.
- `sliceEquivPresheaf`: `Over F ≌ PSh(el(F))`, connecting
  slices of presheaf categories to presheaves on categories
  of elements.

## Discrete-Category Equivalence

When `I` and `J` are discrete categories (types `X` and
`Y`), the presheaf PRA category recovers the
slice-polynomial category:

```text
PolyFunctorBetweenCat X Y ≌
  PresheafPRACat (Discrete X) (Discrete Y)
```

This equivalence (`polyBetweenPresheafPRAEquiv` in
`PresheafPRADiscrete.lean`) composes three categorical
equivalences:

1. `piEquivalenceFunctorDiscrete`: families `Y → C`
   correspond to functors `Discrete Y ⥤ C`
2. `Discrete.opposite.symm.congrLeft`: `Discrete Y`
   is self-dual, converting to `(Discrete Y)ᵒᵖ`
3. `ccrOverDiscreteEquiv`: `CoprodCovarRepCat'(Over X)`
   is equivalent to
   `CoprodCovarRepCat((Discrete X)ᵒᵖ ⥤ Type)` via
   the slice-presheaf equivalence and the op'/op
   transfer

The evaluation functors are compatible: the polynomial
evaluation of `PolyFunctorBetweenCat` agrees with the
PRA evaluation of `PresheafPRACat` under the equivalence
(up to the `overDiscretePresheafEquiv` on domain and
codomain).

## Mathematical References

- nLab: [parametric right adjoint](https://ncatlab.org/nlab/show/parametric+right+adjoint)
  (definition, generic morphisms, presheaf formula)
- Gambino and Kock, "Polynomial functors and polynomial
  monads" (general theory in LCCC categories)
- Weber, "Polynomials in categories with pullbacks" (LCCC
  setting)
- Street, "The petit topos of globular sets" (introduced
  PRAs)
- Berger, Mellies, and Weber, "Monads with arities and their
  associated theories" (monads with arities via PRAs)
