/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.CategoryTheory.DiscreteFibration.Elements

/-!
# The fibre presheaf of a discrete fibration

The presheaf `b ↦ p⁻¹(b)` of a discrete fibration, restriction along `g`
being the domain of the unique lift of `g` ([LoregianRiehl2018] § 2.1;
[nLabDiscreteFibration]), together with the functors between `C` and the
category of elements of that presheaf.

## Main definitions

* `DiscreteFibration.restrict` and `DiscreteFibration.fiberPresheaf`, the
  fibre presheaf.
* `DiscreteFibration.toElements` and `DiscreteFibration.ofElements`, the
  functors between `C` and `(fiberPresheaf D).CoElements`.
* `Functor.CoElements.fiberPresheafEquiv`, the bijection between the
  fibre of `π F` over `b` and `F b`.

## Main statements

* `DiscreteFibration.π_toElements_obj`, `.π_toElements_map` and
  `.obj_ofElements_obj`: both functors lie over `B`.
* `DiscreteFibration.ofElements_map_toElements_map`,
  `.ofElements_obj_toElements_obj`,
  `.coElements_eq_toElements_obj` and
  `.toElements_map_ofElements_map`: the two functors are mutually
  inverse.
* `Functor.CoElements.fiberPresheafEquiv_restrict`: restriction in the
  fibre presheaf of `π F` is restriction in `F`.

## Implementation notes

The statements here are elementwise, on objects and on morphisms
separately.  Their packaged forms, which mention `⋙` or bundle the
bijections, inherit `Classical.choice` from the mathlib constructions
they use and live in
`Geb/Mathlib/CategoryTheory/DiscreteFibration/Packaged.lean`.

`obj_elt` restates a fibre element's defining property with `x.base` in
place of `unop (op x.base)`, which the `eqToHom` composites below need in
order to match.

## References

* [LoregianRiehl2018]
* [nLabDiscreteFibration]

## Tags

discrete fibration, fibre, presheaf, category of elements
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂

namespace CategoryTheory

open Opposite

variable {C : Type u₁} [Category.{v₁} C] {B : Type u₂} [Category.{v₂} B]

namespace DiscreteFibration

variable {p : C ⥤ B} (D : DiscreteFibration p)
include D

/-- Restriction along `g : b ⟶ b'` of a fiber element `c'` over `b'`: the
domain of the unique lift of `g` with codomain `c'`. -/
def restrict {b b' : B} (g : b ⟶ b') (c' : p.Fiber b') : p.Fiber b :=
  ⟨D.src (g ≫ eqToHom c'.property.symm), D.obj_src _⟩

@[simp] theorem restrict_val {b b' : B} (g : b ⟶ b') (c' : p.Fiber b') :
    (D.restrict g c').val = D.src (g ≫ eqToHom c'.property.symm) := rfl

/-- Restriction along an identity is the identity. -/
theorem restrict_id {b : B} (c : p.Fiber b) : D.restrict (𝟙 b) c = c :=
  Subtype.ext (D.src_eq _ (𝟙 c.val) c.property (by simp))

/-- Restriction is contravariantly functorial. -/
theorem restrict_comp {b b' b'' : B} (g : b ⟶ b') (g' : b' ⟶ b'')
    (c : p.Fiber b'') :
    D.restrict (g ≫ g') c = D.restrict g (D.restrict g' c) := by
  apply Subtype.ext
  exact D.src_eq ((g ≫ g') ≫ eqToHom c.property.symm)
    (D.hom (g ≫ eqToHom (D.obj_src (g' ≫ eqToHom c.property.symm)).symm) ≫
      D.hom (g' ≫ eqToHom c.property.symm))
    (D.obj_src _) (by simp [D.map_hom])

/-- The fiber presheaf `b ↦ p⁻¹(b)` of a discrete fibration. -/
def fiberPresheaf : Bᵒᵖ ⥤ Type u₁ where
  obj b := p.Fiber b.unop
  map g := fun c => D.restrict g.unop c
  map_id _ := funext fun c => D.restrict_id c
  map_comp g g' := funext fun c => D.restrict_comp g'.unop g.unop c

/-- The fiber presheaf's value on objects.  Not a `simp` lemma: it rewrites
the object arguments carried by the coercion in `fiberPresheaf_map`'s left-hand
side, which would take that lemma out of simp-normal form.  Mathlib omits
the corresponding `yoneda_obj_obj` for the same reason, supplying
`unif_hint`s instead. -/
theorem fiberPresheaf_obj (b : Bᵒᵖ) : D.fiberPresheaf.obj b = p.Fiber b.unop := rfl

@[simp] theorem fiberPresheaf_map {b b' : Bᵒᵖ} (g : b ⟶ b')
    (c : p.Fiber b.unop) : D.fiberPresheaf.map g c = D.restrict g.unop c := rfl

/-! ### `C` and the category of elements of `fiberPresheaf D` -/

attribute [local simp] eqToHom_map

/-- An element of the fiber presheaf at `x` lies over `x.base`.  This
restates the fiber element's own property, whose type reads
`p.obj x.elt.1 = unop (op x.base)`: the `unop (op _)` blocks the `eqToHom`
composites below from matching. -/
theorem obj_elt (x : D.fiberPresheaf.CoElements) : p.obj x.elt.val = x.base :=
  x.elt.property

/-- `c ↦ (p c, c)`. -/
def toElements : C ⥤ D.fiberPresheaf.CoElements where
  obj c := Functor.CoElements.mk (p.obj c) ⟨c, rfl⟩
  map {c c'} f :=
    Functor.CoElements.homMk (p.map f)
      (Subtype.ext (D.src_eq (p.map f ≫ eqToHom rfl) f rfl
        (by change p.map f = eqToHom rfl ≫ p.map f ≫ eqToHom rfl; simp)))
  map_id c := Functor.CoElements.hom_ext (p.map_id c)
  map_comp f g := Functor.CoElements.hom_ext (p.map_comp f g)

@[simp] theorem toElements_obj (c : C) :
    D.toElements.obj c =
      Functor.CoElements.mk (F := D.fiberPresheaf) (p.obj c) ⟨c, rfl⟩ := rfl

@[simp] theorem homBase_toElements_map {c c' : C} (f : c ⟶ c') :
    Functor.CoElements.homBase (D.toElements.map f) = p.map f := rfl

/-- The object underlying the source of `f` is the domain of the unique
lift of `homBase f`. -/
theorem obj_eq_src {x y : D.fiberPresheaf.CoElements} (f : x ⟶ y) :
    x.elt.val = D.src (Functor.CoElements.homBase f ≫ eqToHom (D.obj_elt y).symm) :=
  (congrArg Subtype.val (Functor.CoElements.map_homBase_elt f)).symm

/-- The unique lift of `homBase f`, transported to a morphism between the
underlying objects of `C`. -/
def ofElementsMap {x y : D.fiberPresheaf.CoElements} (f : x ⟶ y) :
    x.elt.val ⟶ y.elt.val :=
  eqToHom (D.obj_eq_src f) ≫
    D.hom (Functor.CoElements.homBase f ≫ eqToHom (D.obj_elt y).symm)

/-- `ofElementsMap f` lies over `homBase f`. -/
theorem map_ofElementsMap {x y : D.fiberPresheaf.CoElements} (f : x ⟶ y) :
    p.map (D.ofElementsMap f) =
      eqToHom (D.obj_elt x) ≫ Functor.CoElements.homBase f ≫
        eqToHom (D.obj_elt y).symm := by
  rw [ofElementsMap, Functor.map_comp, eqToHom_map, D.map_hom]
  simp

/-- `(b, c) ↦ c`. -/
def ofElements : D.fiberPresheaf.CoElements ⥤ C where
  obj x := x.elt.val
  map f := D.ofElementsMap f
  map_id x :=
    D.map_injective (by rw [D.map_ofElementsMap, p.map_id]; simp)
  map_comp f g :=
    D.map_injective (by
      rw [D.map_ofElementsMap, p.map_comp, D.map_ofElementsMap,
        D.map_ofElementsMap]
      simp)

@[simp] theorem ofElements_obj (x : D.fiberPresheaf.CoElements) :
    D.ofElements.obj x = x.elt.val := rfl

/-- `ofElements` lies over `Functor.CoElements.π`, elementwise on
morphisms. -/
theorem map_ofElements_map {x y : D.fiberPresheaf.CoElements} (f : x ⟶ y) :
    p.map (D.ofElements.map f) =
      eqToHom (D.obj_elt x) ≫ Functor.CoElements.homBase f ≫
        eqToHom (D.obj_elt y).symm :=
  D.map_ofElementsMap f

/-- `toElements` lies over `B`, elementwise on objects. -/
theorem π_toElements_obj (c : C) :
    (Functor.CoElements.π D.fiberPresheaf).obj (D.toElements.obj c) = p.obj c := rfl

/-- `toElements` lies over `B`, elementwise on morphisms. -/
theorem π_toElements_map {c c' : C} (f : c ⟶ c') :
    (Functor.CoElements.π D.fiberPresheaf).map (D.toElements.map f) = p.map f := rfl

/-- `ofElements` lies over `B`, elementwise on objects. -/
theorem obj_ofElements_obj (x : D.fiberPresheaf.CoElements) :
    p.obj (D.ofElements.obj x) = (Functor.CoElements.π D.fiberPresheaf).obj x :=
  D.obj_elt x

/-- `ofElements` undoes `toElements` on morphisms. -/
theorem ofElements_map_toElements_map {c c' : C} (f : c ⟶ c') :
    D.ofElements.map (D.toElements.map f) = f := by
  apply D.map_injective
  rw [D.map_ofElements_map]
  change 𝟙 _ ≫ p.map f ≫ 𝟙 _ = p.map f
  simp

/-- `ofElements` undoes `toElements` on objects. -/
theorem ofElements_obj_toElements_obj (c : C) :
    D.ofElements.obj (D.toElements.obj c) = c := rfl

/-- An element of a fiber is `toElements` of its underlying object of
`C`. -/
theorem mk_eq_toElements_obj {b : B} (c : p.Fiber b) :
    Functor.CoElements.mk (F := D.fiberPresheaf) b c = D.toElements.obj c.val := by
  obtain ⟨c, rfl⟩ := c
  rfl

/-- Every object of the category of elements of `fiberPresheaf D` is
`toElements` of its underlying object of `C`. -/
theorem coElements_eq_toElements_obj (x : D.fiberPresheaf.CoElements) :
    x = D.toElements.obj x.elt.val :=
  (Functor.CoElements.mk_base_elt x).symm.trans (D.mk_eq_toElements_obj x.elt)

/-- `toElements` undoes `ofElements` on morphisms. -/
theorem toElements_map_ofElements_map {c c' : C}
    (f : D.toElements.obj c ⟶ D.toElements.obj c') :
    D.toElements.map (D.ofElements.map f) = f :=
  Functor.CoElements.hom_ext (by
    rw [homBase_toElements_map, D.map_ofElements_map]
    change 𝟙 _ ≫ Functor.CoElements.homBase f ≫ 𝟙 _ =
      Functor.CoElements.homBase f
    rw [Category.id_comp, Category.comp_id])

end DiscreteFibration

/-! ### The fibre presheaf of `π F` -/

namespace Functor.CoElements

variable (F : Bᵒᵖ ⥤ Type v₃)

/-- Choice-free and universe-free form of `fiberPresheafIso` below: the fiber of
`π F` over `b` is in bijection with `F b`. -/
def fiberPresheafEquiv (b : B) : (π F).Fiber b ≃ F.obj (op b)
    where
  toFun x := F.map (eqToHom x.property.symm).op x.val.elt
  invFun y := ⟨mk b y, rfl⟩
  left_inv x := by
    obtain ⟨x, hb⟩ := x
    subst hb
    refine Subtype.ext ?_
    exact (congrArg (mk x.base)
      (congrFun (F.map_id (op x.base)) x.elt)).trans
      (mk_base_elt x)
  right_inv y :=
    show F.map (𝟙 (op b)) y = y from
      congrFun (F.map_id _) y

/-- Naturality of `fiberPresheafEquiv`: restriction in the fiber presheaf of
`π F` is restriction in `F`. -/
theorem fiberPresheafEquiv_restrict {b b' : B} (g : b ⟶ b')
    (x : (π F).Fiber b') :
    fiberPresheafEquiv F b ((discreteFibration F).restrict g x) =
      F.map g.op (fiberPresheafEquiv F b' x) := by
  obtain ⟨x, hb⟩ := x
  subst hb
  change F.map (𝟙 _) (F.map (g ≫ 𝟙 _).op x.elt) =
    F.map g.op (F.map (𝟙 _) x.elt)
  rw [Category.comp_id, F.map_id, F.map_id]
  rfl

end Functor.CoElements

end CategoryTheory
