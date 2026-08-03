/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.CategoryTheory.FinCat.Category
public import Mathlib.CategoryTheory.FinCategory.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.OfMap

/-!
# The diagonal `FinCategory`

Where the object and morphism levels of `FinCat.Obj.category` coincide,
the generated category is small, and mathlib's `CategoryTheory.FinCategory`
applies. `Fintype` is choice-dependent, so this is the one `FinCat`
module permitted to depend on `Classical.choice`; it holds this
instance and nothing else.

## Main definitions

* `CategoryTheory.FinCat.Obj.finCategory` — the `FinCategory` instance
  at coinciding object and morphism levels.

## Implementation notes

`CategoryTheory.FinCategory` requires a `SmallCategory` argument, so no
instance of it exists at independent object and morphism levels; the `@`
ascription below pins both to `FinCat.Obj.category.{u, u}`. mathlib's
universe-polymorphic analogue, `CategoryTheory.CountableCategory`, is a
`Prop` class with `countableObj` and `countableHom` fields; no
corresponding finite class exists upstream.

`Fintype`'s `complete` field routes membership through
`Finset.instSetLike`, which carries `Classical.choice`, so this instance
depends on `Classical.choice` no matter how its `Fintype` fields are
constructed.

## Tags

finite category, fintype, choice, small category
-/

@[expose] public section

namespace CategoryTheory

namespace FinCat

/-- Where the object and morphism levels coincide the generated
category is small, and its objects and hom-sets are finite. -/
instance Obj.finCategory.{u} (S : FinCat) :
    @FinCategory (Obj.{u} S) (Obj.category.{u, u} S) where
  fintypeObj :=
    Fintype.ofEquiv (ULift.{u} (Fin S.objCount))
      ⟨Obj.mk, Obj.idx, fun _ ↦ rfl, fun _ ↦ rfl⟩
  fintypeHom := fun X Y ↦ ULift.fintype (S.Mor X.idx.down Y.idx.down)

end FinCat

end CategoryTheory
