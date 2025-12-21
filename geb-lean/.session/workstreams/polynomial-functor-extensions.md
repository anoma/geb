# Polynomial Functor Extensions

Status: Not Started

## Objective

Extend the polynomial endofunctor framework in `GebLean.PolyAlg` with
additional categorical structure, factorization systems, and connections
to related mathematical frameworks.

## Planned Work

### 1. Small Adjunctions with Type

There are several adjunctions between categories of polynomial functors
and `Type`. These should be formalized.

### 2. Free Monad as a Monad on Polynomial Endofunctors

The operation `P ↦ Free P` (taking the free monad of a polynomial
endofunctor) is itself a monad on the category of polynomial endofunctors
over any `X : Type`. Dually, `P ↦ Cofree P` is a comonad. These monadic
and comonadic structures should be made explicit.

### 3. Left Multi-Adjoints

Implement the notion of left multi-adjoint, which is closely related to
parametric right adjoints.

### 4. Epi/Mono Factorization

Implement epi/mono factorization for morphisms of polynomial functors.

### 5. Vertical/Cartesian Factorization

Implement vertical/Cartesian factorization for polynomial functors.

### 6. Universal Morphisms and Categorical Structure

Formalize universal morphisms in categories of polynomial functors:

- Limits and colimits (all exist)
- Exponential objects
- Parallel product (Dirichlet product)
- Left Kan extensions

### 7. Dual-Variance Polynomial Functors

Investigate dual-variance versions of polynomial functors and their
connections to:

- Paranatural category theory
- Twisted-arrow categories
- The connected Grothendieck construction (already implemented in
  `GebLean.Utilities.Grothendieck`)

### 8. Double Category of Slice Polynomial Functors

Extend the slice/Over polynomial functor implementation to the double
category (which is also a framed bicategory) of slice polynomial functors.

References:

- nLab polynomial-functor page
- Gambino and Kock's notes on polynomial functors

## Dependencies

- `GebLean.Polynomial` - Polynomial functor infrastructure
- `GebLean.PolyAlg` - Algebras, coalgebras, and universal constructions
  (initial algebras, terminal coalgebras)
- `GebLean.Utilities.Grothendieck` - Connected Grothendieck construction
- `GebLean.Utilities.TwistedArrow` - Twisted arrow categories

## References

- nLab: polynomial functor
- Gambino, Kock. "Polynomial functors and polynomial monads"
