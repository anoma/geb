import GebLean.Polynomial

/-!
# Adjunctions Involving Polynomial Functors

This module defines adjunctions between categories of polynomial functors
and related categories (such as `Type` and slice categories).

## Adjunctions

The following adjunctions are implemented:

* Free/forgetful adjunction between polynomial functors and `Type`
* Cofree/forgetful adjunction (dual construction)
* Slice-based adjunctions relating `PolyFunctorBetweenCat X Y` to slices

These adjunctions capture the sense in which polynomial functors arise as
free constructions and have forgetful functors with both left and right
adjoints.

## References

* https://ncatlab.org/nlab/show/polynomial+functor
-/

namespace GebLean

open CategoryTheory

universe u

end GebLean
