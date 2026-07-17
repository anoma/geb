/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Basic
public import Mathlib.CategoryTheory.Elements

/-!
# Presheaf polynomial functors: categorical wrapper

Packages the constructive core (`Presheaf.Basic`) as `CategoryTheory.Functor`
values: the domain-side functor `(Iᵒᵖ ⥤ Type) ⥤ Type` and the presheaf
polynomial functor `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)`. The
functor-category packaging — constructing `CategoryTheory.Functor` objects
over presheaf categories and discharging their laws — is
`Classical.choice`-dependent, so this packaging is kept in a separate
module from the choice-free core. The notation `↾` (`TypeCat.ofHom`) is
itself choice-free: `objPresheaf` uses `↾` and depends only on `propext`
and `Quot.sound`. This
module also relates the core to mathlib's category of elements:
`elemMap_eq_categoryOfElements_map` proves the choice-free core `elemMap` is
the object map of mathlib's `Classical.choice`-dependent
`CategoryOfElements.map`.

## Main definitions

* `PresheafDomPFunctorData.domFunctor` — the functor `(Iᵒᵖ ⥤ Type) ⥤ Type`.
* `PresheafDomPFunctorData.toElements` — the bridge from the core's `I`-indexed
  element set to mathlib's category of elements `Z.Elements`.
* `PresheafPFunctor.functor` — the functor `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)`.

## Main statements

* `PresheafPFunctor.functor_obj` / `functor_map` — the categorical functor's
  object map is the core `objPresheaf`, and its morphism map is the
  dom `map` restricted to the `q`-indexed fiber.
* `PresheafDomPFunctorData.elemMap_eq_categoryOfElements_map` — the core's
  choice-free `elemMap` is the object map of mathlib's
  `Classical.choice`-dependent `CategoryOfElements.map`, across `toElements`.

## Implementation notes

`domFunctor` reuses the core `obj`/`map`. A functor-category hom
`h : Z ⟶ Z'` is definitionally a `CategoryTheory.NatTrans Z Z'`, the input
the core `map` expects, so `map` promotes the core `map` with `↾`; the
identity law discharges by `ext` and the core `map_id`, and the composition
law by `ext` and `rfl`. Unlike the slice wrapper there is no `Functor.toOver`
shortcut: the codomain is a plain type category, not an `Over` category.

`functor` assembles directly: its object map is `objPresheaf`, and its morphism
map is the core `mapPresheaf` — the natural transformation a
functor-category hom `α` induces, whose component is the dom `map α` restricted
to the `q`-indexed fiber (the dom map preserves the output index, so it
restricts), with naturality `map_objRestr`. The outer functor laws come from
the dom `map_id` / `map_comp`. There is no `Functor.toOver`
analogue for presheaf codomains. The morphism universes of `I` and `J` are
named (`vI`, `vJ`) so the input presheaf's value universe `uZ` and the
`PresheafPFunctor` arity universes `uA` / `uB` pin the output presheaf's value
universe `max uI uZ uA uB` explicitly.

## References

* [Weber2007]
* [GambinoHyland2004]
* [GambinoKock2013]

## Tags

polynomial functor, presheaf, parametric right adjoint, p.r.a.,
PFunctor, functor category
-/

public section

open CategoryTheory

universe uI uJ uA uB uZ vI vJ

namespace PresheafDomPFunctorData

/-- The functor `(Iᵒᵖ ⥤ Type) ⥤ Type` of a presheaf-domain polynomial
functor: the core `obj`/`map` packaged on the presheaf category. A
functor-category hom is definitionally the bare `NatTrans` the core `map`
consumes; the identity law comes from the core `map_id`, the composition law
by `rfl`. -/
@[expose] def domFunctor {I : Type uI} [Category I]
    (F : PresheafDomPFunctorData.{uI, uA, uB} I) :
    CategoryTheory.Functor (Iᵒᵖ ⥤ Type uZ) (Type (max uI uZ uA uB)) where
  obj Z := F.obj Z
  map {Z Z'} h := ↾(F.map h)
  map_id Z := by
    ext z
    exact congrFun (F.map_id Z) z
  map_comp _ _ := rfl

/-- The bridge from the core's `I`-indexed element set `Σ i, Z.obj ⟨i⟩` to
mathlib's `Iᵒᵖ`-indexed category of elements `Z.Elements`, sending `⟨i, z⟩` to
`⟨op i, z⟩`. -/
@[expose] def toElements {I : Type uI} [Category.{vI} I] (Z : Iᵒᵖ ⥤ Type uZ) :
    (Σ i : I, Z.obj ⟨i⟩) → Z.Elements := fun p ↦ ⟨⟨p.1⟩, p.2⟩

/-- The core's `elemMap` is the object map of the functor on categories of
elements that `α` induces — mathlib's `CategoryOfElements.map` — across the
index bridge `toElements`. `CategoryOfElements.map` consumes a functor-category
hom and is `Classical.choice`-dependent, so the core takes a bare `NatTrans` and
defines `elemMap` directly; this theorem certifies the two agree. -/
theorem elemMap_eq_categoryOfElements_map {I : Type uI} [Category.{vI} I]
    {Z Z' : Iᵒᵖ ⥤ Type uZ} (α : NatTrans Z Z') :
    toElements Z' ∘ elemMap α = (CategoryOfElements.map α).obj ∘ toElements Z :=
  rfl

end PresheafDomPFunctorData

namespace PresheafPFunctor

/-- The presheaf polynomial functor `(Iᵒᵖ ⥤ Type) ⥤ (Jᵒᵖ ⥤ Type)` of `F`: its
object map is the output presheaf `objPresheaf`, and its morphism map
is `mapPresheaf` (the induced presheaf morphism). The functor
laws come from the dom `map_id` / `map_comp`. -/
@[expose] def functor {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) :
    CategoryTheory.Functor (Iᵒᵖ ⥤ Type uZ) (Jᵒᵖ ⥤ Type (max uI uZ uA uB)) where
  obj Z := F.objPresheaf Z
  map {Z Z'} α := F.mapPresheaf α
  map_id Z := by
    ext j w
    exact Subtype.ext (congrFun (F.toPresheafDomPFunctorData.map_id Z) w.1)
  map_comp α β := by
    ext j w
    exact Subtype.ext (congrFun (F.toPresheafDomPFunctorData.map_comp α β) w.1)

/-- `functor.obj` is the output presheaf `objPresheaf`. The
categorical object map carries no data beyond the core. -/
theorem functor_obj {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) (Z : Iᵒᵖ ⥤ Type uZ) :
    F.functor.obj Z = F.objPresheaf Z :=
  rfl

/-- `functor.map`'s component over `j`, applied to a `q`-indexed fiber element,
applies the dom `map` to the underlying element: its underlying dom value is
the dom `map α` of the input's. -/
theorem functor_map {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    (F : PresheafPFunctor.{uI, uJ, uA, uB, vI, vJ} I J) {Z Z' : Iᵒᵖ ⥤ Type uZ}
    (α : Z ⟶ Z') (X : Jᵒᵖ) (w : (F.functor.obj Z).obj X) :
    (F.functor.map α).app X w =
      (⟨F.toPresheafDomPFunctorData.map α w.1, w.2⟩ : (F.functor.obj Z').obj X) :=
  rfl

end PresheafPFunctor
