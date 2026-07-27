/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.Univariate.W
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# The W-type algebra as an initial object

Packages the choice-free initiality of `PFunctor.wAlgebra` — the `Unique`
instance on its hom-sets — as mathlib's `Limits.IsInitial`, making it
available to the colimit API.

## Main definitions

* `PFunctor.wIsInitial` — the W-type algebra is an initial object of the
  category of algebras.

## Main statements

* `PFunctor.wIsInitial_to` — the initiality witness's morphism into an
  algebra is the fold.

## Implementation notes

`Limits.IsInitial.ofUnique` is `Classical.choice`-dependent, so this
packaging is kept in a separate module from the choice-free
`Univariate.W`. Consumers wanting a choice-free development use
`PFunctor.wUniqueHom` directly, which is a `def` rather than an
`instance`, so it is introduced here with `haveI`.

## References

* [GambinoHyland2004]

## Tags

polynomial functor, W-type, initial algebra, initial object
-/

public section

universe uA uB

open CategoryTheory

namespace PFunctor

/-- The W-type algebra is an initial object of the category of algebras
of `P.functor`. -/
def wIsInitial (P : PFunctor.{uA, uB}) :
    Limits.IsInitial (P.wAlgebra) :=
  haveI (B : Endofunctor.Algebra (PFunctor.functor.{uA, uB, max uA uB} P)) :
      Unique (P.wAlgebra ⟶ B) := P.wUniqueHom B
  Limits.IsInitial.ofUnique _

/-- The initiality witness's morphism into an algebra is the fold. -/
theorem wIsInitial_to (P : PFunctor.{uA, uB})
    (B : Endofunctor.Algebra (PFunctor.functor.{uA, uB, max uA uB} P)) :
    (P.wIsInitial).to B = P.wElim B :=
  haveI := P.wUniqueHom B
  Subsingleton.elim _ _

end PFunctor
