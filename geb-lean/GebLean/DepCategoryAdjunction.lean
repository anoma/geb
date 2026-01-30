import GebLean.DepCategoryCat

/-!
# Reflective Adjunction from Cat to DepCategoryData

This file constructs the reflective adjunction showing that `Cat` (the category
of categories) is a reflective subcategory of `DepCategoryData`.

## Overview

The file `DepCategoryCat.lean` establishes that `DepCategoryCat` (a full
subcategory of `DepCategoryData` satisfying existence, uniqueness, subsingleton,
and category law conditions) is equivalent to mathlib's `Cat`.

This file constructs the reflective adjunction by working entirely within
subcategories of `DepCategoryData`, without direct reference to `Cat`. The
adjunction is then composed with the equivalence to obtain the final result.

## Main constructions

(To be implemented)

* Inclusion functor: `DepCategoryCat ⥤ DepCategoryData`
* Reflector functor: `DepCategoryData ⥤ DepCategoryCat`
* Unit and counit natural transformations
* Triangle identities proving the adjunction
* Proof that the counit is a natural isomorphism (reflectivity)

## References

See `DepCategoryCat.lean` for the definition of `DepCategoryCat` and its
equivalence with `Cat`.
-/

namespace GebLean

namespace CategoryJudgments

open CategoryTheory

end CategoryJudgments

end GebLean
