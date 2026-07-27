/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.Slice.Basic
public import Geb.Mathlib.Data.PFunctor.Univariate.Functor
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Slice polynomial functors: categorical wrapper

Packages the constructive core (`Slice.Basic`) as a
`CategoryTheory.Functor` between `Over` categories. mathlib's `Over` is
`Classical.choice`-dependent at the type level, so this categorical
packaging is kept in a separate module from the choice-free core.

## Main definitions

* `SliceDomPFunctor.domSubfunctor` — the compatible assignments as a
  subfunctor of the underlying polynomial functor.
* `SliceDomPFunctor.domFunctor` — the functor `Over dom ⥤ Type`.
* `SlicePFunctor.functor` — the functor `Over dom ⥤ Over cod`.

## Main statements

* `SlicePFunctor.functor_obj` / `functor_map` — the categorical
  functor's object and morphism maps are definitionally the
  core `SlicePFunctor.obj` / `map`.
* `SlicePFunctor.functor_comp_forget` — the wrapper forgets back to
  `domFunctor`.

## Implementation notes

`domSubfunctor` is the subfunctor of `Over.forget dom ⋙ PFunctor.functor`
cut out by the compatibility predicate, and `domFunctor` reads it as a
functor, so the functor laws come from `Subfunctor.toFunctor` and
`Subfunctor.ι` is the inclusion into the underlying polynomial functor.
`Over` structure maps are read as functions, the
slice-morphism hypothesis is `SliceDomPFunctor.over_hom_comp` (the
function-level form of `Over.w`), and the subfunctor's closure condition
is the core `map`'s output compatibility. The composite instantiates
`PFunctor.functor` at `v := uD`, written explicitly as
`PFunctor.functor.{uA, uB, uD}`. `functor` is the `Functor.toOver` lift
along the shape-output map `q`; it is `@[expose]` so `functor_obj` /
`functor_map` can state the definitional equalities as exported `rfl`
theorems. `cod` is pinned to `domFunctor`'s codomain universe
`max uA uB uD` because `Functor.toOver` requires its over-base object
to inhabit the codomain category of the lifted functor, so the core's
`cod`-universe polymorphism cannot survive into the categorical layer.

## References

* [AltenkirchGhaniHancockMcBrideMorris2015]
* [GambinoHyland2004]
* [GambinoKock2013]

## Tags

polynomial functor, slice category, Over, container, PFunctor
-/

public section

universe uA uB uD

open CategoryTheory

namespace SliceDomPFunctor

/-- The function-level form of `Over.w`: a slice morphism `g : Y ⟶ Z`
commutes with the projections, `Z.hom ∘ g.left = Y.hom`, read as functions. -/
theorem over_hom_comp {dom : Type uD} {Y Z : Over dom} (g : Y ⟶ Z) :
    Z.hom ∘ g.left = Y.hom := by
  funext z
  exact congrFun (Over.w g) z

/-- The `r`-compatible assignments, as a subfunctor of the underlying
polynomial functor pulled back along the forgetful functor. The `obj`
field is the compatibility predicate; the `map` field is its closure
under the polynomial functor's action, supplied by the core `map`. -/
@[expose] def domSubfunctor {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom) :
    Subfunctor (Over.forget dom ⋙ PFunctor.functor.{uA, uB, uD} F.toPFunctor) where
  obj Y := {x | F.Compatible (Y.hom) x.1 x.2}
  map i x hx := (F.map (i.left) (over_hom_comp i) ⟨x, hx⟩).2

/-- The functor `Over dom ⥤ Type` restricting the `PFunctor`
interpretation to `r`-compatible assignments: the subfunctor
`domSubfunctor` read as a functor. `Subfunctor.ι` is the inclusion into
the underlying polynomial functor. -/
@[expose] def domFunctor {dom : Type uD} (F : SliceDomPFunctor.{uA, uB} dom) :
    CategoryTheory.Functor (Over dom) (Type (max uA uB uD)) :=
  F.domSubfunctor.toFunctor

end SliceDomPFunctor

namespace SlicePFunctor

/-- Output-index naturality: `domFunctor.map g` fixes the shape component,
so post-composing with the shape-output map `q` is preserved. This is
the `Functor.toOver` triangle obligation for `functor`, shared with
`functor_comp_forget`. -/
private theorem output_triangle {dom : Type uD} {cod : Type (max uA uB uD)}
    (F : SlicePFunctor.{uA, uB, uD, max uA uB uD} dom cod)
    {Y Z : Over dom} (g : Y ⟶ Z) :
    F.toSliceDomPFunctor.domFunctor.map g ≫ (↾fun z ↦ F.q z.1.1) =
      (↾fun z ↦ F.q z.1.1) := by
  ext z
  exact congrArg F.q (F.toSliceDomPFunctor.map_fst (g.left)
    (SliceDomPFunctor.over_hom_comp g) z)

/-- The slice polynomial functor `Over dom ⥤ Over cod`: the
`Functor.toOver` lift of `domFunctor` along the shape-output map `q`. -/
@[expose] def functor {dom : Type uD} {cod : Type (max uA uB uD)}
    (F : SlicePFunctor.{uA, uB, uD, max uA uB uD} dom cod) :
    CategoryTheory.Functor (Over dom) (Over cod) :=
  Functor.toOver F.toSliceDomPFunctor.domFunctor cod
    (fun _ ↦ ↾(fun z ↦ F.q z.1.1))
    (by intro Y Z g; exact F.output_triangle g)

/-- The wrapper forgets back to `domFunctor`. -/
theorem functor_comp_forget {dom : Type uD} {cod : Type (max uA uB uD)}
    (F : SlicePFunctor.{uA, uB, uD, max uA uB uD} dom cod) :
    F.functor ⋙ Over.forget cod = F.toSliceDomPFunctor.domFunctor := by
  rw [functor]
  exact Functor.toOver_comp_forget _ _ _ fun g ↦ F.output_triangle g

/-- `functor.obj` is the core `obj`, packaged with `Over.mk`. The
categorical object map carries no data beyond the core. -/
theorem functor_obj {dom : Type uD} {cod : Type (max uA uB uD)}
    (F : SlicePFunctor.{uA, uB, uD, max uA uB uD} dom cod) (Y : Over dom) :
    F.functor.obj Y = Over.mk (↾ F.obj (Y.hom)) :=
  rfl

/-- `functor.map`'s underlying function is the core `map`. An `Over`
morphism's only data is its `left` component, so this fixes the categorical
morphism map up to its `Prop`-valued commuting condition. -/
theorem functor_map {dom : Type uD} {cod : Type (max uA uB uD)}
    (F : SlicePFunctor.{uA, uB, uD, max uA uB uD} dom cod) {Y Z : Over dom} (g : Y ⟶ Z) :
    (F.functor.map g).left =
      ↾ F.map (g.left) (SliceDomPFunctor.over_hom_comp g) :=
  rfl

end SlicePFunctor
