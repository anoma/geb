/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.CategoryTheory.DiscreteFibration.Pullback
public import Mathlib.CategoryTheory.Elements

/-!
# The category of elements of a presheaf, over its base

Mathlib's `CategoryTheory.Functor.Elements` presents the category of
elements of `F : Bᵒᵖ ⥤ Type v₃` over `Bᵒᵖ`.  This module transposes it so
that its morphisms are morphisms of `B`, the presentation in which the
projection to `B` is a discrete fibration ([LoregianRiehl2018] § 2.1;
[nLabDiscreteFibration]).

## Main definitions

* `Functor.CoElements F`, the opposite of `F.Elements`, with the
  interface `mk`, `base`, `elt`, `homMk`, `homBase`.
* `Functor.CoElements.π F`, the projection to `B`.
* `Functor.CoElements.discreteFibration F`, the lifting data on `π F`.

## Main statements

* `Functor.CoElements.sigma_eq`: every morphism is the canonical lift of
  its image in `B`.
* `Functor.CoElements.isDiscreteFibration_π`: `π F` is a discrete
  fibration in the pullback sense too.

## Implementation notes

The transposition is what makes the lift of `g` with codomain
`⟨b', x'⟩` literally `g : ⟨b, F g x'⟩ ⟶ ⟨b', x'⟩`, with the source
computed rather than known only up to an `eqToHom`.  `CoElements` is a
semireducible `def`, as `CoGrothendieck` is in
`Geb/Mathlib/CategoryTheory/Grothendieck.lean`, so that dot notation and
instance search stop at it.

## References

* [LoregianRiehl2018]
* [nLabDiscreteFibration]

## Tags

category of elements, presheaf, discrete fibration, Grothendieck
construction
-/

@[expose] public section

universe v₂ v₃ u₂

namespace CategoryTheory

open Opposite

variable {B : Type u₂} [Category.{v₂} B]

/-- The category of elements of a presheaf `F : Bᵒᵖ ⥤ Type v₃`, presented
over `B`: the opposite of mathlib's `Functor.Elements`, which presents it
over `Bᵒᵖ`.  An object is an object `b` of `B` with an element of `F b`,
and a morphism `⟨b, x⟩ ⟶ ⟨b', x'⟩` is a morphism `g : b ⟶ b'` of `B` with
`F g x' = x`.

The `Co` prefix marks the presentation whose morphisms are morphisms of
the base rather than of its opposite, as in `CoGrothendieck`. -/
@[implicit_reducible]
def Functor.CoElements (F : Bᵒᵖ ⥤ Type v₃) : Type (max u₂ v₃) := F.Elementsᵒᵖ

namespace Functor.CoElements

/-- The category structure on `F.CoElements`, inherited from the opposite
of `F.Elements`. -/
instance category (F : Bᵒᵖ ⥤ Type v₃) : Category.{v₂} F.CoElements :=
  inferInstanceAs (Category F.Elementsᵒᵖ)

variable {F : Bᵒᵖ ⥤ Type v₃}

/-- The object of `B` an element lies over. -/
def base (x : F.CoElements) : B := (Opposite.unop x).1.unop

/-- The element of `F` at `base x`. -/
def elt (x : F.CoElements) : F.obj (op x.base) := (Opposite.unop x).2

/-- An object of `F.CoElements` from an object of `B` and an element. -/
def mk (b : B) (x : F.obj (op b)) : F.CoElements := Opposite.op ⟨op b, x⟩

@[simp] theorem base_mk (b : B) (x : F.obj (op b)) : (mk b x).base = b := rfl

@[simp] theorem elt_mk (b : B) (x : F.obj (op b)) : (mk b x).elt = x := rfl

@[simp] theorem mk_base_elt (x : F.CoElements) : mk x.base x.elt = x := rfl

/-- The morphism of `B` underlying a morphism of `F.CoElements`. -/
def homBase {x y : F.CoElements} (f : x ⟶ y) : x.base ⟶ y.base :=
  (Quiver.Hom.unop f).1.unop

/-- The compatibility equation a morphism of `F.CoElements` satisfies. -/
theorem map_homBase_elt {x y : F.CoElements} (f : x ⟶ y) :
    F.map (homBase f).op y.elt = x.elt := (Quiver.Hom.unop f).2

/-- A morphism of `F.CoElements` from a morphism of `B` and the
compatibility equation. -/
def homMk {x y : F.CoElements} (g : x.base ⟶ y.base)
    (hg : F.map g.op y.elt = x.elt) : x ⟶ y :=
  Quiver.Hom.op (CategoryOfElements.homMk (Opposite.unop y) (Opposite.unop x) g.op hg)

@[simp] theorem homBase_homMk {x y : F.CoElements} (g : x.base ⟶ y.base)
    (hg : F.map g.op y.elt = x.elt) : homBase (homMk g hg) = g := rfl

@[ext] theorem hom_ext {x y : F.CoElements} {f g : x ⟶ y}
    (h : homBase f = homBase g) : f = g :=
  Quiver.Hom.unop_inj (Subtype.ext (Quiver.Hom.unop_inj h))

@[simp] theorem homBase_id (x : F.CoElements) : homBase (𝟙 x) = 𝟙 x.base := rfl

@[simp] theorem homBase_comp {x y z : F.CoElements} (f : x ⟶ y) (g : y ⟶ z) :
    homBase (f ≫ g) = homBase f ≫ homBase g := rfl

@[simp] theorem homBase_eqToHom {x y : F.CoElements} (h : x = y) :
    homBase (eqToHom h) = eqToHom (congrArg base h) := by
  subst h; rfl

/-- The projection `∫F ⥤ B`. -/
def π (F : Bᵒᵖ ⥤ Type v₃) : F.CoElements ⥤ B where
  obj x := x.base
  map f := homBase f

@[simp] theorem π_obj (x : F.CoElements) : (π F).obj x = x.base := rfl

@[simp] theorem π_map {x y : F.CoElements} (f : x ⟶ y) :
    (π F).map f = homBase f := rfl

/-- Every morphism of `F.CoElements` is the canonical lift of its image in
`B`: a morphism into `y` over `g : b ⟶ y.base` has source `mk b (F g y.elt)`
and equals `homMk g rfl`.  The compatibility equation is left loose so that
it can be substituted. -/
theorem sigma_eq (b : B) (e : F.obj (op b)) (y : F.CoElements)
    (g : b ⟶ y.base) (hg : F.map g.op y.elt = e) :
    (⟨mk b e, homMk g hg⟩ : Σ x, x ⟶ y) =
      ⟨mk b (F.map g.op y.elt), homMk g rfl⟩ := by
  subst hg
  rfl

/-- The lift of `g : b ⟶ b'` with codomain `⟨b', x'⟩` is
`g : ⟨b, F g x'⟩ ⟶ ⟨b', x'⟩`.  No `eqToHom` occurs: the source is
*computed*, not merely known to exist. -/
def discreteFibration (F : Bᵒᵖ ⥤ Type v₃) : DiscreteFibration (π F) where
  src {b y} g := mk b (F.map g.op y.elt)
  hom {_ _} g := homMk g rfl
  obj_src _ := rfl
  map_hom _ := (Category.id_comp _).symm
  unique {b y} g {x} f e hh := by
    obtain rfl : x.base = b := e
    have hg : homBase f = g := hh.trans (Category.id_comp g)
    subst hg
    exact sigma_eq x.base x.elt y (homBase f) (map_homBase_elt f)

/-- The projection from a category of elements is a discrete fibration in
the pullback sense. -/
theorem isDiscreteFibration_π (F : Bᵒᵖ ⥤ Type v₃) :
    IsDiscreteFibration (π F) :=
  (discreteFibration F).isDiscreteFibration

end Functor.CoElements

end CategoryTheory
