# Workstream: Endofunctor CCC for PshRelEdge

## Status

Blocked on polynomial functor generalization.
The general endofunctor CCC has a universe gap;
the resolution is to restrict to polynomial
endofunctors, which requires generalizing
`PolyFunctorBetweenCat` from slice categories
to presheaf categories.

## Completed Definitions

All in `PshRelEdgeSeparation.lean`, section
`EndoIhom`:

- `endoIhom F G : PshRelEdge C ==> PshRelEdge C`
  The powered end `int_{(i,c)} [F(y), G(y)]^{Hom(E,y)}`
- `endoIhomFunctor F` : `G |-> [F, G]`
  (candidate right adjoint, functorial in G)
- `endoIhomMapG` + 4 bifunctoriality lemmas
- `endoIhomCurry` : full curry
  `Nat(F tensor H, G) -> Nat(H, [F, G])`
- `endoIhomProj` : end projection at representables
- `endoIhomCurrySrcApp` : curry product component
- `endoDinatSpanCond_currySrcApp` : dinatural for curry

In `RepresentableDensity.lean`:

- `spanRepresentableFunctor` :
  `(WalkingSpan x C^op)^op ==> SpanPSh`
- `pshRelEdgeRepresentableFunctor` :
  `(WalkingSpan x C^op)^op ==> PshRelEdge C`
- `pshRelEdgeRepresentableIsDense` :
  density of the representable embedding
- `endoIhomUncurryAtRep` : uncurry at representables

## Universe Gap Analysis

### The gap

Mathlib's `MonoidalClosed.FunctorCategory.closed`
requires ends over `Under j` for endofunctors `j`.
`Under j` has objects at `Type (max (u+1) (v+1))`,
but `PshRelEdge.{u,v,max u v} C` only has
`HasLimitsOfSize.{max u v, max u v}`. The gap is
one universe level and cannot be closed by
choosing a larger `w` (the ladder shifts up).

### Why it affects both categories

`PshRelEdge C` and `PshSpanCat C` have identical
universe levels:

- Objects: `Type (max (u+1) (v+1))`
- Morphisms: `Type (max u v)`
- Endofunctor nat trans: `Type (max (u+1) (v+1))`

The reflective inclusion does not change universes.
The gap affects `[PshSpanCat, PshSpanCat]` equally.

### Why density alone doesn't suffice

The uncurry at general edges requires extending
a natural transformation from representables to
all edges. This works for presheaf-valued functors
(by the Yoneda/density lemma) but NOT for arbitrary
PshRelEdge-valued endofunctors: the extension
requires `F` and `H` to preserve the density
colimit, which fails for arbitrary endofunctors.

### What DOES work

- `endoIhomCurry` (forward direction): works for
  ALL endofunctors, no density needed
- `endoIhomUncurryAtRep` (at representables):
  uses object-level CCC, fully computable
- Injectivity of curry: follows from density
  (faithfulness of restricted Yoneda)
- Round-trip at representables: follows from
  object-level CCC round-trip

## Resolution: Polynomial Endofunctors

### The idea

Restrict from ALL endofunctors to POLYNOMIAL
endofunctors. The category `Poly(E)` of polynomial
endofunctors on a locally cartesian closed
category `E` is cartesian closed, computed using
dependent products in `E`. No large limits needed.

### Why polynomials suffice

Type-formers (dependent types, sums, products,
identity types, W-types, universes) are all
represented by polynomial functors. Restricting
to polynomials does not lose any type-formers
needed for the parametricity construction.

### Existing infrastructure

`PolyFunctorBetweenCat X Y` (in `PolyUMorph.lean`)
already has a `MonoidalClosed` instance (line 4262)
for the CARTESIAN product (not Dirichlet). This
gives `[P, Q]` satisfying
`Nat(R x P, Q) ~= Nat(R, [P, Q])` for polynomials
between `Over X` and `Over Y` (slice categories of
`Type u`).

### What needs to be built

1. Generalize `PolyFunctorBetweenCat` from slice
   categories `Over X` to presheaf categories
   `PSh(D)` (or equivalently `PshSpanCat C`).
   The standard formula is the "parametric right
   adjoint" construction — see
   `ncatlab.org/nlab/show/parametric+right+adjoint`.

2. Show the generalized polynomial category has
   `MonoidalClosed` (cartesian product), building
   on the existing `PolyFunctorBetweenCat` CCC
   as a foundation.

3. Connect to `PshRelEdge C` via the reflective
   adjunction: lift polynomial endofunctors on
   `PshRelEdge C` to `PshSpanCat C`, take the
   exponential there, reflect back.

### Development plan

This is a separate development thread:

- **Thread**: Polynomial functors on presheaf
  categories (parametric right adjoints)
- **Foundation**: `PolyFunctorBetweenCat` +
  `MonoidalClosed` in `PolyUMorph.lean`
- **Target**: `MonoidalClosed` for polynomial
  endofunctors on `PshSpanCat C`, transferred
  to `PshRelEdge C` via reflective inclusion
- **Reference**: parametric right adjoint
  (ncatlab.org/nlab/show/parametric+right+adjoint)

## Dependencies

```text
PolyFunctorBetweenCat CCC (done)
         |
         v
Poly on PSh(D) (new thread)
         |
         v
Poly on PshSpanCat C
         |
         v
Poly on PshRelEdge C (via reflection)
         |
         v
Task #156 (dialgebra edge functor)
         |
         v
Task #157 (dialgebra parametricity)
```
