# QPF Connection Investigation

Status: Not Started

## Objective

Investigate the connection between our polynomial endofunctor constructions
and mathlib's QPF (Quotients of Polynomial Functors) framework.

## Background

The `GebLean.PolyAlg` module defines polynomial endofunctors on slice
categories `Over X`, with initial algebras (W-types) and terminal coalgebras
(M-types). Mathlib has a separate framework for polynomial functors and their
quotients in:

- `Mathlib.Data.PFunctor.Univariate.Basic` - Univariate polynomial functors
- `Mathlib.Data.PFunctor.Multivariate.Basic` - Multivariate polynomial functors
- `Mathlib.Data.QPF.Univariate.Basic` - Quotients of polynomial functors
- `Mathlib.Data.QPF.Multivariate.Basic` - Multivariate QPFs
- `Mathlib.Data.PFunctor.Univariate.M` - M-types for univariate PFunctors

## Questions to Investigate

1. How does `PolyEndo X` relate to mathlib's `PFunctor`?
2. Can our `PolyFix` / `PolyCofix` be connected to mathlib's W/M constructions?
3. Are there benefits to expressing our constructions as QPFs?
4. What additional structure would QPF provide (e.g., for nested datatypes)?

## References

- Avigad, Carneiro, Hudon (2019). "Data Types as Quotients of Polynomial
  Functors"
- mathlib4 QPF documentation
