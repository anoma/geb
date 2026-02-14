# Yoneda Relation Parametricity

## Status: Planning

## Goal

Define a category-theoretic notion of parametric polymorphism
using the Yoneda relation double category that:

- Recovers Reynolds/Wadler parametricity for Set
- Generalizes to an arbitrary category C
- Agrees with paranaturality for initial algebras, terminal
  coalgebras, and dinatural numbers
- Differs from paranaturality for the divergence type
  `((X -> X) -> X) -> X`

See `docs/ParametricityViaYonedaRelations.md` for the
mathematical analysis.

## Completed

- [x] Yoneda relation double category (`YonedaRelDouble.lean`)
- [x] Documentation of Reynolds/Wadler framework and its
  categorical content (`docs/ParametricityViaYonedaRelations.md`)
- [x] Formal separation of paranaturality and parametricity
  for the divergence type (`ParanaturalTopos.lean`,
  `ParametricityDivergence` section)
- [x] `TypeExpr` inductive type for type expressions over
  `Type` with `relInterp` (relational interpretation)
- [x] `ParametricFamily T` structure bundling a polymorphic
  family with its parametricity proof
- [x] Bridge equivalences: `algebraParametricEquivParanat`,
  `dinaturalParametricEquivParanat`
- [x] Chained equivalences: `initialAlgebraParametricEquiv`
  (`μF.a ≃ ParametricFamily (algebraTypeExpr F)`),
  `dinaturalNumbersParametricEquiv`
  (`ℕ ≃ ParametricFamily dinaturalTypeExpr`)
- [x] Refactored `divEndoRel`, `divArgRel`, `divFullRel` as
  `TypeExpr.relInterp` of named sub-type-expressions
- [x] Generalized `TypeExpr` from `{leaf, arrow}` to
  `{var, app F T, arrow}` supporting functor application
  on arbitrary subexpressions (e.g., `F(X → X)`)
- [x] `functorRelLift` (canonical relation lifting for
  functors) and `functorRelLift_graphRel`
- [x] `relInterp_of_offDiag`, `relInterp_implies_wedge`,
  `ParametricFamily.wedge`: parametricity implies the
  profunctor wedge condition (but not conversely for
  nested arrows -- the wedge is paranaturality)

## Continuation

The generalization of `TypeExpr`/`ParametricFamily` from
`Type` to arbitrary categories, and the embedding of
parametric transformations into the twisted-arrow topos,
are tracked in `parametric-generalization.md`.

## Implementation plan

### Phase 1: Relation lifting through type constructors

Define how Yoneda relations are lifted through type
constructors, yielding new Yoneda relations.

#### 1a. Product lifting

Given `R : YonedaProdOver A A'` and `S : YonedaProdOver B B'`,
define the product relation on `(A x B, A' x B')`.

This should be analogous to Reynolds' product lifting:
pairs are related iff each component is related. In
presheaf terms, this should be a pullback or product
construction on the presheaf level.

#### 1b. Function-space lifting

Given `R : YonedaProdOver A A'` and `S : YonedaProdOver B B'`,
define the function-space relation on `(A -> B, A' -> B')`.

This is where the divergence from paranaturality occurs.
Reynolds says: `(f, f')` are related iff for all
`(x, x') in R`, `(f x, f' x') in S`. In presheaf terms,
this should use the internal hom of the presheaf category
(exponential object `[R, S]`), composed with appropriate
projections.

When `C = Set`, this must recover Reynolds' function-space
relation. The presheaf category on `Set` is the category
of functors `Set^op -> Set`, which has exponentials given
by the standard internal hom.

#### 1c. Universal quantification lifting

Given a family of relations indexed by Yoneda relations,
define the universal quantification. Reynolds says: `(g, g')`
are related iff for every relation `R`, the instantiations
are related in `F(R)`.

This should correspond to an end-like construction in the
double category.

### Phase 2: Parametric families

Define what it means for a family
`alpha : (I : C) -> F(I,I) -> G(I,I)` to be parametric
with respect to a given type expression for `F` and `G`.

The definition should be: for every Yoneda relation
`R : YonedaRel I J`, the appropriate 2-cell exists in
the double category, where "appropriate" is determined by
the relation lifting through the type expression.

### Phase 3: Test cases

#### 3a. Divergence test

Show that for `divSource` and `divTarget`, the
Yoneda-relation-based parametricity condition matches
`DivParametric`, not `DivParanatural`. This requires
checking that:

- `divApplyId` satisfies the Yoneda parametricity condition
- The condition is not equivalent to paranaturality

#### 3b. Agreement tests

Show that for the algebra profunctor, coalgebra profunctor,
and hom profunctor, the Yoneda parametricity condition
is equivalent to paranaturality.

### Phase 4: Double-categorical formulation

Express the parametricity condition purely in terms of the
double category structure, without reference to the
type expression. This may require defining additional
structure on the double category (e.g., a notion of
"relational universe" or "relational fibration").

## Open questions

1. The function-space lifting requires C to have internal
   homs (or at least that the presheaf category does). For
   the divergence type `((X -> X) -> X) -> X`, we need
   the exponential `(X -> X)` as an internal construction.
   In Set this is trivial. For general C, we may need to
   work in PSh(C) (which is always a topos) rather than C.

2. The type expression `((X -> X) -> X) -> X` involves
   self-application of the variable X. The relation lifting
   through `X -> X` involves both the covariant and
   contravariant directions of the same relation. This mixed
   variance is exactly what makes the construction
   profunctorial rather than purely functorial.

3. How should the "type expression" be formalized? Options:
   - A syntactic grammar of types (like System F types)
   - A categorical construction (polynomial functors,
     species, etc.)
   - An iterated arrow category / factorization approach
     (as explored in Q20-Q22 of the paranatural
     investigations workstream)

4. The relationship between the double-categorical approach
   and the E(Fact)-parametricity or Arr(C)-level testing
   approaches from the paranatural investigations workstream
   should be clarified.
