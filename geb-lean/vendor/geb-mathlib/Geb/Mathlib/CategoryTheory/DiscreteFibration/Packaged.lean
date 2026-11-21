/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.CategoryTheory.DiscreteFibration.FiberPresheaf

/-!
# Discrete fibrations: the packaged statements

The forms of the discrete-fibration correspondence that bundle their
content into a mathlib construction: the converse of the pullback
formulation, the equalities of composite functors, the equivalence of
categories, and the natural isomorphism.

## Main definitions

* `IsDiscreteFibration.equiv` and
  `IsDiscreteFibration.toDiscreteFibration`, recovering lifting data from
  a bijective `codPair`.
* `DiscreteFibration.elementsEquivalence`, the equivalence between `C`
  and the category of elements of its own fibre presheaf.
* `Functor.CoElements.fiberPresheafIso`, the natural isomorphism between
  the fibre presheaf of `π F` and `F`.

## Main statements

* `isDiscreteFibration_iff_nonempty`: the two formulations of a discrete
  fibration agree.
* `DiscreteFibration.toElements_comp_π` and
  `DiscreteFibration.ofElements_comp`: both functors lie over `B`.
* `DiscreteFibration.toElements_comp_ofElements` and
  `DiscreteFibration.ofElements_comp_toElements`: both composites are
  identity functors.

## Implementation notes

Every declaration here depends on `Classical.choice`, and only through a
mathlib construction that does: `Equiv.ofBijective`, `Functor.comp` in
each statement mentioning `⋙`, `Equivalence.mk`, and
`NatIso.ofComponents`.  Each has an elementwise counterpart in
`Geb/Mathlib/CategoryTheory/DiscreteFibration/Pullback.lean` or
`Geb/Mathlib/CategoryTheory/DiscreteFibration/FiberPresheaf.lean` that
carries the same content within the `propext`/`Quot.sound` budget, which
is why this module is the only one of the group admitted to
`GebMeta.classicalAllowedModules`.

## References

* [LoregianRiehl2018]
* [nLabDiscreteFibration]

## Tags

discrete fibration, equivalence of categories, category of elements
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂

namespace CategoryTheory

open Opposite

variable {C : Type u₁} [Category.{v₁} C] {B : Type u₂} [Category.{v₂} B]

/-- The bijection `Arrow C ≃ Arrow B ×_B C` of a discrete fibration in the
pullback-square sense.  Classical: `Equiv.ofBijective` uses choice. -/
noncomputable def IsDiscreteFibration.equiv {p : C ⥤ B}
    (H : IsDiscreteFibration p) : Arrow C ≃ CodPullback p :=
  Equiv.ofBijective _ H

/-- `equiv` acts as `codPair`. -/
theorem IsDiscreteFibration.equiv_apply {p : C ⥤ B}
    (H : IsDiscreteFibration p) (a : Arrow C) : H.equiv a = codPair p a := rfl

/-- Classical converse: a bijective `codPair p` yields lifting data.  Uses
`Classical.choice`; kept apart from the constructive development. -/
noncomputable def IsDiscreteFibration.toDiscreteFibration {p : C ⥤ B}
    (H : IsDiscreteFibration p) : DiscreteFibration p := by
  have hl : ∀ q, codPair p (H.equiv.symm q) = q := fun q =>
    (H.equiv_apply _).symm.trans (H.equiv.apply_symm_apply q)
  have hr : ∀ {b : B} {c : C} (g : b ⟶ p.obj c),
      (H.equiv.symm ⟨(Arrow.mk g, c), rfl⟩).right = c :=
    fun g => congrArg (fun q : CodPullback p => q.val.2) (hl _)
  have hm : ∀ {b : B} {c : C} (g : b ⟶ p.obj c),
      Arrow.mk (p.map (H.equiv.symm ⟨(Arrow.mk g, c), rfl⟩).hom) =
        Arrow.mk g :=
    fun g => congrArg (fun q : CodPullback p => q.val.1) (hl _)
  refine
    { src := fun {b c} g => (H.equiv.symm ⟨(Arrow.mk g, c), rfl⟩).left
      hom := fun {b c} g =>
        (H.equiv.symm ⟨(Arrow.mk g, c), rfl⟩).hom ≫ eqToHom (hr g)
      obj_src := fun {b c} g =>
        congrArg (fun q : CodPullback p => q.val.1.left) (hl _)
      map_hom := fun {b c} g => ?_
      unique := fun {b c} g {c'} h eh hh => ?_ }
  · obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff _ _).1 (hm g)
    simp only [Functor.id_obj] at hf ⊢
    simp only [Functor.map_comp, eqToHom_map, hf]
    simp
  · refine sigma_eq_of_arrow_eq h _ ?_ (hr g)
    apply H.equiv.injective
    rw [H.equiv.apply_symm_apply, H.equiv_apply]
    exact Subtype.ext (Prod.ext
      ((Arrow.mk_eq_mk_iff _ _).2 ⟨eh, rfl, by simpa using hh⟩).symm rfl)

/-- A discrete fibration in the pullback sense admits lifting data. -/
theorem IsDiscreteFibration.nonempty {p : C ⥤ B}
    (H : IsDiscreteFibration p) : Nonempty (DiscreteFibration p) :=
  ⟨H.toDiscreteFibration⟩

/-- The two formulations agree: the codomain square is a pullback exactly
when lifting data exists.  Lifting data is a `Subsingleton`, so the
`Nonempty` on the right loses nothing. -/
theorem isDiscreteFibration_iff_nonempty {p : C ⥤ B} :
    IsDiscreteFibration p ↔ Nonempty (DiscreteFibration p) :=
  ⟨fun H => H.nonempty, fun ⟨D⟩ => D.isDiscreteFibration⟩

namespace DiscreteFibration

variable {p : C ⥤ B} (D : DiscreteFibration p)
include D

/-- `toElements` lies over `B`. -/
theorem toElements_comp_π :
    D.toElements ⋙ Functor.CoElements.π D.fiberPresheaf = p := rfl

/-- `ofElements` lies over `B`. -/
theorem ofElements_comp : D.ofElements ⋙ p = Functor.CoElements.π D.fiberPresheaf :=
  Functor.ext (fun x => D.obj_elt x) (fun x y f => by
    rw [Functor.comp_map, D.map_ofElements_map]
    rfl)

/-- `ofElements` undoes `toElements`. -/
theorem toElements_comp_ofElements : D.toElements ⋙ D.ofElements = 𝟭 C :=
  Functor.ext (fun c => rfl) (fun c c' f => by
    change D.ofElements.map (D.toElements.map f) = 𝟙 _ ≫ f ≫ 𝟙 _
    rw [D.ofElements_map_toElements_map, Category.id_comp, Category.comp_id])

/-- `toElements` undoes `ofElements`. -/
theorem ofElements_comp_toElements :
    D.ofElements ⋙ D.toElements = 𝟭 D.fiberPresheaf.CoElements :=
  Functor.ext (fun x => (D.coElements_eq_toElements_obj x).symm) (fun x y f => by
    obtain ⟨c, rfl⟩ : ∃ c, x = D.toElements.obj c :=
      ⟨_, D.coElements_eq_toElements_obj x⟩
    obtain ⟨c', rfl⟩ : ∃ c', y = D.toElements.obj c' :=
      ⟨_, D.coElements_eq_toElements_obj y⟩
    change D.toElements.map (D.ofElements.map f) = 𝟙 _ ≫ f ≫ 𝟙 _
    rw [D.toElements_map_ofElements_map, Category.id_comp, Category.comp_id])

/-- The two functors assemble into an equivalence, so a discrete fibration
over `B` is the category of elements of its own fibre presheaf.  Both
composites are identity functors on the nose, so the unit and counit are
`eqToIso`s. -/
def elementsEquivalence : C ≌ D.fiberPresheaf.CoElements :=
  .mk D.toElements D.ofElements (eqToIso D.toElements_comp_ofElements.symm)
    (eqToIso D.ofElements_comp_toElements)

end DiscreteFibration

namespace Functor.CoElements

variable (F : Bᵒᵖ ⥤ Type v₃)

/-- The fiber presheaf of `π F` is naturally isomorphic to `F` (up to the
universe lift forced by `F.CoElements : Type (max u₂ v₃)`): the fiber over
`b` is `{x : F.CoElements // x.base = b}`, and `x ↦ x.elt`, transported
along `x.base = b`, is a bijection onto `F b`. -/
def fiberPresheafIso :
    (discreteFibration F).fiberPresheaf ≅ F ⋙ uliftFunctor.{u₂, v₃} :=
  NatIso.ofComponents
    (fun b => ((fiberPresheafEquiv F b.unop).trans Equiv.ulift.symm).toIso)
    (fun {b b'} g => funext fun x => by
      have h := fiberPresheafEquiv_restrict F g.unop x
      rw [Quiver.Hom.op_unop] at h
      exact congrArg ULift.up h)

end Functor.CoElements

end CategoryTheory
