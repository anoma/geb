# Workstream: Polynomial Functors on Presheaf Categories

## Status

Not started. Prerequisite for endofunctor CCC
on PshRelEdge C.

## Goal

Generalize `PolyFunctorBetweenCat` (polynomial
functors between slice categories `Over X`) to
polynomial functors on presheaf categories
`PSh(D)`, and show the resulting category is
cartesian closed.

## Mathematical Background

### Parametric right adjoints

A polynomial functor on a presheaf category
`PSh(D)` is equivalently a "parametric right
adjoint" — a functor that preserves connected
limits and is accessible. The standard reference
is the nLab page on parametric right adjoints:
`ncatlab.org/nlab/show/parametric+right+adjoint`

For a LCCC category `E`, a polynomial functor
`P : E -> E` is determined by a diagram
`A <- B -> A` (or more generally a morphism
`p : B -> A` in `E`), giving
`P(X) = Sigma_{a:A} X^{B_a}`.

For presheaf categories `E = PSh(D)`, the
morphism `p : B -> A` is a morphism of
presheaves, and the polynomial `P` acts on
presheaves by dependent sum + exponential
computed in the presheaf topos.

### Cartesian closure

The category of polynomial endofunctors on
`E` with the pointwise (cartesian) product is
cartesian closed when `E` is LCCC. The internal
hom `[P, Q]` is computed using:

- Dependent products `Pi` in `E`
- The interaction between `Sigma` and `Pi`
  (Beck-Chevalley condition)

### Existing infrastructure

`PolyFunctorBetweenCat X Y` in `PolyUMorph.lean`
provides:

- Polynomial functors between `Over X` and `Over Y`
- Cartesian product of polynomials
- Internal hom `polyBetweenHomFunctor Q`
- `MonoidalClosed` instance (line 4262)
- Dirichlet product and its closure (separate)

This covers the case `E = Type u` (slice
categories). The generalization to `E = PSh(D)`
requires lifting from slices to presheaves.

## Plan

### Layer 1: Polynomial functors on PSh(D)

Define `PolyEndoPSh D` — polynomial endofunctors
on `PSh(D)` for a small category `D`.

A polynomial on `PSh(D)` is determined by:

- A presheaf `A : PSh(D)` (positions)
- A family `B : PSh(D)/A -> PSh(D)` (directions)
  equivalently, a morphism `p : B -> A` in `PSh(D)`

The polynomial functor `P(X) = Sigma_{a:A} X^{B_a}`
is computed using:

- `Sigma_p : PSh(D)/A -> PSh(D)` (dependent sum)
- `Pi_p : PSh(D)/A -> PSh(D)` (dependent product,
  exists because `PSh(D)` is LCCC)
- `Delta_p : PSh(D) -> PSh(D)/A` (pullback)

Concretely: `P = Sigma_p . (Delta_p)^* . Pi_p`
where `(Delta_p)^*` is the pullback functor.

### Layer 2: Build on PolyFunctorBetweenCat

The key insight: `PSh(D)` is a colimit of
representable presheaves, each of which is
a slice `Over (y(d))` for `d : D`. Polynomial
functors on `PSh(D)` can be described as
compatible families of polynomial functors on
each slice, glued via the Grothendieck
construction.

Alternatively: use the equivalence
`PSh(D)/A ≃ PSh(∫ A)` (where `∫ A` is the
category of elements of `A`) to reduce
polynomial operations on presheaves to
operations on slice categories.

### Layer 3: Cartesian closure

Show `PolyEndoPSh D` with the cartesian product
is cartesian closed. The proof lifts the
existing `MonoidalClosed` instance from
`PolyFunctorBetweenCat` using the
slice-presheaf correspondence.

### Layer 4: Connection to PshRelEdge

- `PshSpanCat C ≃ PSh(WalkingSpan^op x C)`
  (currying equivalence)
- Polynomial endofunctors on `PshSpanCat C`
  correspond to `PolyEndoPSh (WalkingSpan^op x C)`
- The reflective adjunction
  `PshRelEdge C <-> PshSpanCat C` lifts
  polynomial endofunctors between the two
  categories (via `incl . F . sep`)
- The CCC structure transfers via the
  exponential ideal property

## Files

- `GebLean/PolyPresheaf.lean` (new) — polynomial
  functors on presheaf categories
- `GebLean/PolyUMorph.lean` (modify) — connect
  existing CCC to the new presheaf version
- `GebLean/Utilities/RepresentableDensity.lean`
  (modify) — connection to PshRelEdge

## References

- nLab: parametric right adjoint
  `ncatlab.org/nlab/show/parametric+right+adjoint`
- Gambino-Kock: "Polynomial functors and
  polynomial monads" (for the general theory)
- Weber: "Polynomials in categories with
  pullbacks" (for the LCCC setting)
- Existing `PolyFunctorBetweenCat` + `MonoidalClosed`
  in `PolyUMorph.lean`
