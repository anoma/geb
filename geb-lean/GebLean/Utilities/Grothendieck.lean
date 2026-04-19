import Mathlib.CategoryTheory.Category.Cat.AsSmall
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Grothendieck
import Mathlib.CategoryTheory.Products.Basic
import GebLean.Utilities.Equalities
import GebLean.Utilities.Opposites
import GebLean.Utilities.Elements

/-!
# The contravariant Grothendieck construction

Given a functor `F : Cᵒᵖ ⥤ Cat`, the objects of `GrothendieckContra F`
consist of dependent pairs `(b, f)`, where `b : C` and `f : F.obj (op b)`,
and a morphism `(b, f) ⟶ (b', f')` is a pair `β : b ⟶ b'` in `C`, and
`φ : f ⟶ (F.map (op β)).obj f'`.

This is the dual of the covariant Grothendieck construction in
`Mathlib.CategoryTheory.Grothendieck`, where morphisms consist of
`β : b ⟶ b'` and `φ : (F.map β).obj f ⟶ f'`.

## Implementation notes

This file dualizes `Mathlib.CategoryTheory.Grothendieck`, providing the
contravariant version of each construction. We try to adhere to mathlib
names, while placing them in the `GrothendieckContra` namespace.

To avoid wrapping and unwrapping `op` constructors in the implementations,
we convert functors `F : Cᵒᵖ ⥤ Cat` to functors `F' : Cᵒᵖ' ⥤ Cat` using an
alternative opposite category construction `op'`, which provides
definitional equality `op' (op' C) = C`.

## References

* https://ncatlab.org/nlab/show/Grothendieck+construction#Definition

-/

namespace GebLean

open CategoryTheory GebLean

/--
Congruence lemma for `Cat.Hom.toFunctor` applied to objects.
Given an equality of `Cat.Hom` morphisms, derives equality at the level of
functor application to objects.
-/
theorem catHom_congr_obj {C D : Cat} {f g : Cat.Hom C D} (h : f = g) (x : C) :
    f.toFunctor.obj x = g.toFunctor.obj x :=
  Functor.congr_obj (congrArg Cat.Hom.toFunctor h) x

/--
Congruence lemma for `Cat.Hom.toFunctor` applied to morphisms.
Given an equality of `Cat.Hom` morphisms, derives heterogeneous equality at
the level of functor application to morphisms.
-/
theorem catHom_congr_map {C D : Cat} {f g : Cat.Hom C D} (h : f = g)
    {x y : C} (m : x ⟶ y) :
    f.toFunctor.map m ≍ g.toFunctor.map m :=
  h ▸ HEq.refl _

@[simp]
def GrothendieckCatF.{u, v} {C : Type u} [CI : Category.{v, u} C] :
  (Cat.of C ⥤ Cat.{v, u}) ⥤ Cat.{v, u} :=
    Grothendieck.functor.{u, v} (E := Cat.of C) ⋙ Over.forget (Cat.of C)

@[simp]
def GrothendieckCat.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F : C ⥤ Cat.{v₂, u₂}) : Cat.{max v v₂, max u u₂} :=
    Cat.of.{max v v₂, max u u₂} (Grothendieck.{u, v, u₂, v₂} (C := C) F)

@[simp]
def GrothendieckContraCatOp.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) : Cat.{max v v₂, max u u₂} :=
    GrothendieckCat.{u, v, u₂, v₂} (C := Cᵒᵖ') (Cat.postCompOpFunctor'.obj F')

@[simp]
def GrothendieckContraCat.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) : Cat.{max v v₂, max u u₂} :=
    Cat.opFunctorObj' (GrothendieckContraCatOp F')

@[simp]
def GrothendieckContra.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) : Type (max u u₂) :=
    GrothendieckContraCat.{u, v, u₂, v₂} (C := C) (CI := CI) F'

@[reducible, simp]
def GrothendieckContraCatInst.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    Category.{max v v₂, max u u₂}
      (GrothendieckContra.{u, v, u₂, v₂} (C := C) (CI := CI) F') :=
  (GrothendieckContraCat.{u, v, u₂, v₂} (C := C) (CI := CI) F').str

@[reducible, simp]
def GrothendieckContraCatStructInst.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    CategoryStruct.{max v v₂, max u u₂}
      (GrothendieckContra.{u, v, u₂, v₂} (C := C) (CI := CI) F') :=
  (GrothendieckContraCatInst.{u, v, u₂, v₂} (C := C) (CI := CI) F').toCategoryStruct

@[reducible, simp]
def GrothendieckContraQuivInst.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    Quiver.{max v v₂, max u u₂}
      (GrothendieckContra.{u, v, u₂, v₂} (C := C) (CI := CI) F') :=
  (GrothendieckContraCatStructInst.{u, v, u₂, v₂} (C := C) (CI := CI) F').toQuiver

def gcFuncToGcContra.{u, v, u₂, v₂, u₃, v₃} {C : Type u}
  [CI : Category.{v, u} C]
  (D E : (Cᵒᵖ' ⥤ Cat.{v₂, u₂}) ⥤ Cat.{v₃, u₃})
  (G : (F : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) -> (D.obj F) ⥤ (E.obj F)ᵒᵖ')
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    ((D.obj (Cat.postCompOpFunctor'.obj F'))ᵒᵖ' ⥤
     (E.obj (Cat.postCompOpFunctor'.obj F'))) :=
  Functor.op'
    (C := (D.obj (Cat.postCompOpFunctor'.obj F')))
    (D := (E.obj (Cat.postCompOpFunctor'.obj F'))ᵒᵖ')
  <| G
  <| Cat.postCompOpFunctor'.obj (C := Cᵒᵖ' ⥤ Cat) (D := Cᵒᵖ' ⥤ Cat) F'

def gcDomFuncToGcContra.{u, v, u₂, v₂, u₃, v₃} {C : Type u}
  [CI : Category.{v, u} C]
  (D : (Cᵒᵖ' ⥤ Cat.{v₂, u₂}) ⥤ Cat.{v₃, u₃})
  (G :
    (F : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) ->
    (Grothendieck.{u, v, u₂, v₂} (C := Cᵒᵖ') F) ⥤ (D.obj F)ᵒᵖ')
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    (GrothendieckContraCat.{u, v, u₂, v₂} (C := C) (CI := CI) F' ⥤
     D.obj (Cat.postCompOpFunctor'.obj F')) :=
  Functor.op'
    (C := GrothendieckContraCatOp.{u, v, u₂, v₂} (C := C) F')
    (D := (D.obj (Cat.postCompOpFunctor'.obj F'))ᵒᵖ')
  <| G
  <| Cat.postCompOpFunctor'.obj (C := Cᵒᵖ' ⥤ Cat) (D := Cᵒᵖ' ⥤ Cat) F'

def gcCodFuncToGcContra.{u, v, u₂, v₂, u₃, v₃} {C : Type u}
  [CI : Category.{v, u} C]
  (D : (Cᵒᵖ' ⥤ Cat.{v₂, u₂}) ⥤ Cat.{v₃, u₃})
  (G :
    (F : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) ->
    ((D.obj F)ᵒᵖ' ⥤ Grothendieck.{u, v, u₂, v₂} (C := Cᵒᵖ') F))
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    (D.obj (Cat.postCompOpFunctor'.obj F') ⥤
     GrothendieckContraCat.{u, v, u₂, v₂} (C := C) (CI := CI) F') :=
  Functor.op'
    (C := (D.obj (Cat.postCompOpFunctor'.obj F'))ᵒᵖ')
    (D := GrothendieckContraCatOp.{u, v, u₂, v₂} (C := C) F')
  <| G
  <| Cat.postCompOpFunctor'.obj (C := Cᵒᵖ' ⥤ Cat) (D := Cᵒᵖ' ⥤ Cat) F'

/--
Transfer a functor from mathlib's covariant Grothendieck construction where
Grothendieck categories appear in both domain and codomain.
-/
def gcDomCodFuncToGcContra.{u, v, u₂, v₂} {C : Type u}
  [CI : Category.{v, u} C]
  (G :
    (F G : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) ->
    (Grothendieck.{u, v, u₂, v₂} (C := Cᵒᵖ') F ⥤
     Grothendieck.{u, v, u₂, v₂} (C := Cᵒᵖ') G))
  (F' G' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    (GrothendieckContraCat.{u, v, u₂, v₂} (C := C) (CI := CI) F' ⥤
     GrothendieckContraCat.{u, v, u₂, v₂} (C := C) (CI := CI) G') :=
  Functor.op'
    (C := GrothendieckContraCatOp.{u, v, u₂, v₂} (C := C) F')
    (D := GrothendieckContraCatOp.{u, v, u₂, v₂} (C := C) G')
  <| G
    (Cat.postCompOpFunctor'.obj (C := Cᵒᵖ' ⥤ Cat) (D := Cᵒᵖ' ⥤ Cat) F')
    (Cat.postCompOpFunctor'.obj (C := Cᵒᵖ' ⥤ Cat) (D := Cᵒᵖ' ⥤ Cat) G')

@[simp]
def gcHom.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    GrothendieckContra.{u, v, u₂, v₂} (C := C) (CI := CI) F' ->
    GrothendieckContra.{u, v, u₂, v₂} (C := C) (CI := CI) F' ->
    Type (max v v₂) :=
  (GrothendieckContraQuivInst.{u, v, u₂, v₂} (C := C) (CI := CI) F').Hom

@[simp]
def gcId.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    (X : GrothendieckContra.{u, v, u₂, v₂} (C := C) (CI := CI) F') ->
    gcHom.{u, v, u₂, v₂} (C := C) (CI := CI) F' X X :=
  (GrothendieckContraCatStructInst.{u, v, u₂, v₂} (C := C) (CI := CI) F').id

@[simp]
def gcComp.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    {X Y Z : GrothendieckContra.{u, v, u₂, v₂} (C := C) (CI := CI) F'} ->
    gcHom.{u, v, u₂, v₂} (C := C) (CI := CI) F' X Y ->
    gcHom.{u, v, u₂, v₂} (C := C) (CI := CI) F' Y Z ->
    gcHom.{u, v, u₂, v₂} (C := C) (CI := CI) F' X Z :=
  (GrothendieckContraCatStructInst.{u, v, u₂, v₂} (C := C) (CI := CI) F').comp

@[simp]
def gcConv.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) {X Y : GrothendieckContra (C := C) F'}
  (f g : gcHom F' X Y) (w_base : f.base = g.base) :
    ((Cat.postCompOpFunctor'.obj F').map f.base).toFunctor.obj Y.fiber ⟶
    ((Cat.postCompOpFunctor'.obj F').map g.base).toFunctor.obj Y.fiber :=
      eqToHom (by rw [w_base])

set_option backward.isDefEq.respectTransparency false in
@[ext (iff := false)]
theorem gcExt.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) {X Y : GrothendieckContra (C := C) F'}
  (f g : gcHom F' X Y) (w_base : f.base = g.base)
    (w_fiber : f.fiber = (gcConv F' f g w_base) ≫ g.fiber) : f = g := by
  cases f; cases g
  congr
  dsimp at w_base
  unfold gcConv at w_fiber
  cat_disch

@[simp]
theorem gcf_id_base.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (X : GrothendieckContra F') :
    (gcId F' X).base = 𝟙 X.base :=
      rfl

@[simp]
theorem gcf_id_base_eq.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (X : GrothendieckContra F') :
    ((Cat.postCompOpFunctor'.obj F').map (gcId F' X).base).toFunctor.obj X.fiber =
      X.fiber :=
  of_eq_true
    (Eq.trans
      (congrArg (fun x ↦ x.toFunctor.obj X.fiber = X.fiber) (F'.map_id X.base))
      (eq_self X.fiber))

@[simp]
theorem gcf_id_fiber.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (X : GrothendieckContra F') :
    (gcId F' X).fiber = eqToHom (gcf_id_base_eq F' X) :=
      rfl

@[simp]
theorem gcf_id_fiber_cod_eq.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
    (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (X : GrothendieckContra F') :
  (F'.map (𝟙 X.base)).toFunctor.obj X.fiber = X.fiber :=
    (catHom_congr_obj (F'.map_id X.base).symm X.fiber).symm

@[simp]
theorem gcf_id_fiber_eq.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
    (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (X : GrothendieckContra F') :
  (X.fiber ⟶ (F'.map (𝟙 X.base)).toFunctor.obj X.fiber) = (X.fiber ⟶ X.fiber) :=
    (congrArg (Quiver.Hom X.fiber) (gcf_id_fiber_cod_eq F' X).symm).symm

@[simp]
theorem gcf_id_fiber_eq_op.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
    (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (X : GrothendieckContra F') :
  ((F'.map (𝟙 X.base)).toFunctor.obj X.fiber ⟶ X.fiber) = (X.fiber ⟶ X.fiber) :=
    (congrFun (congrArg Quiver.Hom (gcf_id_fiber_cod_eq F' X).symm)
      X.fiber).symm

@[simp]
theorem gcf_id_fiber_eq_rev.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
    (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (X : GrothendieckContra F') :
  ((F'.map (𝟙 X.base)).toFunctor.obj X.fiber ⟶ X.fiber) =
  (X.fiber ⟶ (F'.map (𝟙 X.base)).toFunctor.obj X.fiber) :=
    Eq.trans (gcf_id_fiber_eq_op F' X) (gcf_id_fiber_eq F' X).symm

@[simp]
theorem gcf_comp_fiber_cod_eq.{u, v, u₂, v₂} {C : Type u}
    [CI : Category.{v, u} C] (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    {X Y Z : GrothendieckContra F'} (f : gcHom F' X Y) (g : gcHom F' Y Z) :
  (F'.map f.base).toFunctor.obj ((F'.map g.base).toFunctor.obj Z.fiber) =
  (F'.map (g.base ≫ f.base)).toFunctor.obj Z.fiber :=
    (symm <| catHom_congr_obj (F'.map_comp g.base f.base) Z.fiber)

@[simp]
theorem gcf_comp_fiber_eq.{u, v, u₂, v₂} {C : Type u}
    [CI : Category.{v, u} C] (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    {X Y Z : GrothendieckContra F'} (f : gcHom F' X Y) (g : gcHom F' Y Z) :
  ((F'.map f.base).toFunctor.obj Y.fiber ⟶
    (F'.map f.base).toFunctor.obj ((F'.map g.base).toFunctor.obj Z.fiber)) =
  ((F'.map f.base).toFunctor.obj Y.fiber ⟶
    (F'.map (g.base ≫ f.base)).toFunctor.obj Z.fiber) :=
  (congrArg
    (Quiver.Hom ((F'.map f.base).toFunctor.obj Y.fiber))
    (gcf_comp_fiber_cod_eq F' f g).symm).symm

@[simp]
theorem gcf_comp_fiber_eq_op.{u, v, u₂, v₂} {C : Type u}
    [CI : Category.{v, u} C] (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    {X Y Z : GrothendieckContra F'} (f : gcHom F' X Y) (g : gcHom F' Y Z) :
  ((F'.map f.base).toFunctor.obj ((F'.map g.base).toFunctor.obj Z.fiber) ⟶
    (F'.map f.base).toFunctor.obj Y.fiber) =
  ((F'.map (g.base ≫ f.base)).toFunctor.obj Z.fiber ⟶
    (F'.map f.base).toFunctor.obj Y.fiber) :=
  (congrFun
    (congrArg Quiver.Hom (gcf_comp_fiber_cod_eq F' f g).symm)
    ((F'.map f.base).toFunctor.obj Y.fiber)).symm

@[simp]
theorem gcf_comp_base.{u, v, u₂, v₂} {C : Type u}
    [CI : Category.{v, u} C] (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    {X Y Z : GrothendieckContra F'} (f : gcHom F' X Y) (g : gcHom F' Y Z) :
  (gcComp F' f g).base = g.base ≫ f.base :=
    rfl

@[simp]
theorem gcf_comp_fiber_precomp.{u, v, u₂, v₂} {C : Type u}
    [CI : Category.{v, u} C] (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    {X Y Z : GrothendieckContra F'} (f : gcHom F' X Y) (g : gcHom F' Y Z) :
 ((Cat.postCompOpFunctor'.obj F').map (g.base ≫ f.base)).toFunctor.obj Z.fiber =
  ((Cat.postCompOpFunctor'.obj F').map f.base).toFunctor.obj
    (((Cat.postCompOpFunctor'.obj F').map g.base).toFunctor.obj Z.fiber) :=
  of_eq_true
    (Eq.trans
      (congrArg
        (fun x ↦ x.toFunctor.obj Z.fiber =
          (F'.map f.base).toFunctor.obj ((F'.map g.base).toFunctor.obj Z.fiber))
        (F'.map_comp g.base f.base))
      (eq_self ((F'.map f.base).toFunctor.obj
        ((F'.map g.base).toFunctor.obj Z.fiber))))

@[simp]
theorem gcf_comp_fiber.{u, v, u₂, v₂} {C : Type u}
    [CI : Category.{v, u} C] (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    {X Y Z : GrothendieckContra F'} (f : gcHom F' X Y) (g : gcHom F' Y Z) :
  (gcComp F' f g).fiber =
    eqToHom (gcf_comp_fiber_precomp F' f g) ≫
    ((Cat.postCompOpFunctor'.obj F').map f.base).toFunctor.map g.fiber ≫
    f.fiber
      := rfl

set_option backward.isDefEq.respectTransparency false in
theorem gcf_congr.{u, v, u₂, v₂} {C : Type u}
    [CI : Category.{v, u} C] (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    {X Y : GrothendieckContra F'} {f g : gcHom F' X Y} (h : f = g) :
  f.fiber = eqToHom (by subst h; rfl) ≫ g.fiber :=
    by subst h ; simp

def gcf_eqToHom.{u, v, u₂, v₂} {C : Type u}
    [CI : Category.{v, u} C] (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    {X Y : GrothendieckContra F'} (h : X = Y) : gcHom F' X Y :=
  letI := GrothendieckContraCatInst F'
  eqToHom h

@[simp]
theorem gcf_fiber_eqToHom.{u, v, u₂, v₂} {C : Type u}
    [CI : Category.{v, u} C] (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    {X Y : GrothendieckContra F'} (h : X = Y) :
  (gcf_eqToHom F' h).fiber =
  eqToHom (by subst h ; exact gcf_id_fiber_cod_eq F' X) :=
    by subst h ; rfl

@[simp]
theorem gcf_eqToHom_eq.{u, v, u₂, v₂} {C : Type u}
    [CI : Category.{v, u} C] (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    {X Y : GrothendieckContra F'} (hF : X = Y) :
  gcf_eqToHom F' hF =
  { base := eqToHom (by subst hF; rfl)
    fiber := eqToHom (by subst hF; exact gcf_id_fiber_cod_eq F' X) } :=
  by subst hF ; rfl

universe w u v u₁ v₁ u₂ v₂

section Covariant

/-!
## Covariant Grothendieck construction utilities

This section provides utilities for mathlib's covariant Grothendieck construction,
including `functorTo` which constructs functors INTO a Grothendieck category.
-/

variable {C : Type u} [Category.{v} C]
variable {D : Type u₁} [Category.{v₁} D]
variable (F : C ⥤ Cat.{v₂, u₂})

namespace Grothendieck

@[ext (iff := false)]
theorem obj_ext (X Y : Grothendieck F) (w_base : X.base = Y.base)
    (w_fiber : X.fiber ≍ Y.fiber) : X = Y := by
  cases X; cases Y
  simp only at w_base
  subst w_base
  simp only [heq_eq_eq] at w_fiber
  subst w_fiber
  rfl

/--
For functors valued in `Grothendieck E`, the fiber of `(eqToHom h).app X`
equals an `eqToHom` at the fiber level.
-/
@[simp]
theorem eqToHom_app_fiber {E : Type*} [Category E] {H : E ⥤ Cat}
    {F G : C ⥤ Grothendieck H} (h : F = G) (X : C) :
    ((eqToHom h).app X).fiber = eqToHom (by subst h; simp) := by
  subst h
  rfl

/--
The base component of `eqToHom` between Grothendieck objects is `eqToHom` of the
induced equality on bases.
-/
@[simp]
theorem base_eqToHom {X Y : Grothendieck F} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg Grothendieck.base h) := by
  subst h
  rfl

/--
The fiber component of `eqToHom` between Grothendieck objects.
-/
@[simp]
theorem fiber_eqToHom {X Y : Grothendieck F} (h : X = Y) :
    (eqToHom h).fiber = eqToHom (by subst h; simp) := by
  subst h
  rfl

/--
When two Grothendieck objects have the same base (definitionally), the base
component of `eqToHom` is the identity.
-/
theorem base_eqToHom_same_base {c : C} {x y : F.obj c}
    (h : (⟨c, x⟩ : Grothendieck F) = ⟨c, y⟩) :
    (eqToHom h).base = 𝟙 c := by
  simp only [base_eqToHom, eqToHom_refl]

theorem conj_eqToHom_fiber_heq {W X Y Z : Grothendieck F}
    (h : W = X) (f : X ⟶ Y) (h' : Y = Z) :
    (eqToHom h ≫ f ≫ eqToHom h').fiber ≍ f.fiber := by
  subst h h'
  simp only [eqToHom_refl]
  have heq : (𝟙 W ≫ f ≫ 𝟙 Y) = f := by simp
  exact heq.symm ▸ HEq.refl _

section FunctorTo

/-! ### Client-Facing Types

These are the types that clients need to understand and provide when constructing
functors into the Grothendieck construction.
-/

/--
The type of fiber functions for `functorTo`.
Given a base functor `baseFunc : D ⥤ C`, a fiber function assigns to each
`d : D` an object in the fiber category `F.obj (baseFunc.obj d)`.
-/
abbrev FunctorToFib (baseFunc : D ⥤ C) := ∀ d, F.obj (baseFunc.obj d)

/--
The type of morphism functions for `functorTo`.
Given a fiber function `fib`, a morphism function assigns to each morphism
`g : d ⟶ d'` in `D` a morphism from the transported fiber to the target fiber.
-/
abbrev FunctorToHom (baseFunc : D ⥤ C) (fib : FunctorToFib F baseFunc) :=
  ∀ {d d' : D} (g : d ⟶ d'), (F.map (baseFunc.map g)).toFunctor.obj (fib d) ⟶ fib d'

/-! ### Internal Implementation Types

These types are used internally and are derived automatically from functor laws.
Clients do not need to provide these.
-/

/--
The type of identity equality proofs for `functorTo`.
This equality is derived automatically from `baseFunc.map_id` and `F.map_id`.
-/
abbrev FunctorToEqId (baseFunc : D ⥤ C) (fib : FunctorToFib F baseFunc) :=
  ∀ d, (F.map (baseFunc.map (𝟙 d))).toFunctor.obj (fib d) = fib d

/--
Derive the identity equality from functor laws.
-/
lemma functorToEqIdProof (baseFunc : D ⥤ C) (fib : FunctorToFib F baseFunc) :
    FunctorToEqId F baseFunc fib := fun d => by
  rw [baseFunc.map_id, F.map_id]
  rfl

/--
The type of composition equality proofs for `functorTo`.
This equality is derived automatically from `baseFunc.map_comp` and `F.map_comp`.
-/
abbrev FunctorToEqComp (baseFunc : D ⥤ C) (fib : FunctorToFib F baseFunc) :=
  ∀ {d d' d'' : D} (g : d ⟶ d') (h : d' ⟶ d''),
    (F.map (baseFunc.map (g ≫ h))).toFunctor.obj (fib d) =
    (F.map (baseFunc.map h)).toFunctor.obj
      ((F.map (baseFunc.map g)).toFunctor.obj (fib d))

/--
Derive the composition equality from functor laws.
-/
lemma functorToEqCompProof (baseFunc : D ⥤ C) (fib : FunctorToFib F baseFunc) :
    FunctorToEqComp F baseFunc fib := fun g h => by
  rw [baseFunc.map_comp, F.map_comp]
  rfl

/-! ### Client-Facing Coherence Types

These types define the coherence conditions that clients need to prove.
The equality proofs used in these conditions are derived automatically.
-/

/--
The identity coherence property for `functorTo`.
States that `hom (𝟙 d)` equals the canonical isomorphism from the derived equality.
-/
abbrev FunctorToHomId (baseFunc : D ⥤ C) (fib : FunctorToFib F baseFunc)
    (hom : FunctorToHom F baseFunc fib) :=
  ∀ d, hom (𝟙 d) = eqToHom (functorToEqIdProof F baseFunc fib d)

/--
The composition coherence property for `functorTo`.
States that `hom (g ≫ h)` decomposes into transport, `hom g`, and `hom h`.
-/
abbrev FunctorToHomComp (baseFunc : D ⥤ C) (fib : FunctorToFib F baseFunc)
    (hom : FunctorToHom F baseFunc fib) :=
  ∀ {d d' d'' : D} (g : d ⟶ d') (h : d' ⟶ d''),
    hom (g ≫ h) = eqToHom (functorToEqCompProof F baseFunc fib g h) ≫
      (F.map (baseFunc.map h)).toFunctor.map (hom g) ≫ hom h

/--
The data required to construct a functor into the Grothendieck construction.

This bundles together all the components needed for `functorTo`:
- A base functor `baseFunc : D ⥤ C`
- Fiber objects for each object in `D`
- Fiber morphisms for each morphism in `D`
- Coherence conditions for identity and composition
  (equality proofs are derived automatically)
-/
structure FunctorToData where
  /-- The base functor from `D` to `C` -/
  baseFunc : D ⥤ C
  /-- Fiber objects: for each `d : D`, an object in `F.obj (baseFunc.obj d)` -/
  fib : FunctorToFib F baseFunc
  /-- Fiber morphisms: for each `g : d ⟶ d'`, a morphism between fibers -/
  hom : FunctorToHom F baseFunc fib
  /-- Coherence: `hom (𝟙 d) = eqToHom (functorToEqIdProof ...)` -/
  hom_id : FunctorToHomId F baseFunc fib hom
  /-- Coherence: `hom (g ≫ h)` decomposes correctly -/
  hom_comp : FunctorToHomComp F baseFunc fib hom

variable (data : FunctorToData F (D := D))

/--
Construct a functor into the Grothendieck construction from bundled data.
-/
def functorTo : D ⥤ Grothendieck F where
  obj d := ⟨data.baseFunc.obj d, data.fib d⟩
  map {d d'} g := ⟨data.baseFunc.map g, data.hom g⟩
  map_id d := Grothendieck.ext _ _ (data.baseFunc.map_id d) (by
    simp only [Grothendieck.id_fiber, data.hom_id, eqToHom_trans])
  map_comp {d d' d''} g h := Grothendieck.ext _ _ (data.baseFunc.map_comp g h) (by
    simp only [Grothendieck.comp_fiber, data.hom_comp]
    cat_disch)

/--
The functor `functorTo` composed with `forget` equals `baseFunc`.
-/
theorem functorTo_comp_forget :
    functorTo F data ⋙ Grothendieck.forget F = data.baseFunc := rfl

variable (G : D ⥤ Grothendieck F)

/--
Extract `FunctorToData` from a functor into the Grothendieck construction.

This is the inverse to `functorTo`, demonstrating that `functorTo` is the
unique introduction rule for functors into Grothendieck categories.
-/
def ofFunctor : FunctorToData F (D := D) where
  baseFunc := G ⋙ Grothendieck.forget F
  fib d := (G.obj d).fiber
  hom g := (G.map g).fiber
  hom_id d := by
    change (G.map (𝟙 d)).fiber = eqToHom _
    have h : G.map (𝟙 d) = 𝟙 (G.obj d) := G.map_id d
    rw [Grothendieck.congr h, Grothendieck.id_fiber, eqToHom_trans]
  hom_comp g h := by
    change (G.map (g ≫ h)).fiber = eqToHom _ ≫ _ ≫ _
    have hcomp : G.map (g ≫ h) = G.map g ≫ G.map h := G.map_comp g h
    rw [Grothendieck.congr hcomp, Grothendieck.comp_fiber]
    simp only [Functor.comp_map, Grothendieck.forget_map]
    cat_disch

/--
Round-trip theorem: `functorTo (ofFunctor G) = G`.

Building a functor from the extracted data recovers the original functor.
-/
theorem functorTo_ofFunctor : functorTo F (ofFunctor F G) = G := rfl

/--
Round-trip theorem: `ofFunctor (functorTo data) = data`.

Extracting data from a constructed functor recovers the original data.
-/
theorem ofFunctor_functorTo : ofFunctor F (functorTo F data) = data := rfl

/--
Equivalence between functors into `Grothendieck F` and `FunctorToData F`.

This establishes that `functorTo` is the unique way to construct functors into
Grothendieck categories: every such functor arises from some `FunctorToData`,
and the correspondence is bijective.
-/
def functorToEquiv : (D ⥤ Grothendieck F) ≃ FunctorToData F (D := D) where
  toFun := ofFunctor F
  invFun := functorTo F
  left_inv := functorTo_ofFunctor F
  right_inv := ofFunctor_functorTo F

end FunctorTo

/-!
## Sections of Grothendieck Constructions

A section of the forgetful functor `forget (G ⋙ F) : Grothendieck (G ⋙ F) ⥤ D`
is a functor `s : D ⥤ Grothendieck (G ⋙ F)` such that `s ⋙ forget (G ⋙ F) = 𝟭 D`.

Such sections correspond to choosing:
- For each `d : D`, an object in the fiber `F.obj (G.obj d)`
- For each morphism `g : d ⟶ d'`, a compatible fiber morphism

This is equivalent to `FunctorToData` with a fixed base functor.
-/

section SectionData

variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ Cat.{v₂, u₂})

/--
The type of fiber functions for a section of `forget F : Grothendieck F ⥤ C`.
-/
abbrev SectionFib := ∀ c, F.obj c

variable {F}

/--
The type of morphism functions for a section.
-/
abbrev SectionHom (fib : SectionFib F) :=
  ∀ {c c' : C} (f : c ⟶ c'), (F.map f).toFunctor.obj (fib c) ⟶ fib c'

/--
The identity coherence condition for sections.
-/
abbrev SectionHomId (fib : SectionFib F) (hom : SectionHom fib) :=
  ∀ c, hom (𝟙 c) = eqToHom (functorToEqIdProof F (𝟭 C) fib c)

/--
The composition coherence condition for sections.
-/
abbrev SectionHomComp (fib : SectionFib F) (hom : SectionHom fib) :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c''),
    hom (f ≫ g) = eqToHom (functorToEqCompProof F (𝟭 C) fib f g) ≫
      (F.map g).toFunctor.map (hom f) ≫ hom g

variable (F)

/--
The data for a section of `forget F : Grothendieck F ⥤ C`.

A section assigns to each object in `C` a fiber element in `F.obj c`, to each
morphism a compatible fiber morphism, with identity and composition coherence.

Given a section `s : SectionData F`, the functor `s.toFunctor : C ⥤ Grothendieck F`
satisfies `s.toFunctor ⋙ forget F = 𝟭 C`.
-/
structure SectionData where
  /-- Fiber objects for each `c : C` -/
  fib : SectionFib F
  /-- Fiber morphisms for each morphism in `C` -/
  hom : SectionHom fib
  /-- Identity coherence -/
  hom_id : SectionHomId fib hom
  /-- Composition coherence -/
  hom_comp : SectionHomComp fib hom

variable {F}
variable (sec : SectionData F)

set_option backward.isDefEq.respectTransparency false in
/--
Construct a functor `C ⥤ Grothendieck F` from section data.

This functor is a section of `forget F`: it satisfies
`toFunctor ⋙ forget F = 𝟭 C`.
-/
def SectionData.toFunctor : C ⥤ Grothendieck F where
  obj c := ⟨c, sec.fib c⟩
  map {c c'} f := ⟨f, sec.hom f⟩
  map_id c := Grothendieck.ext _ _ rfl (by
    simp only [Grothendieck.id_fiber, sec.hom_id, eqToHom_trans])
  map_comp {c c' c''} f g := Grothendieck.ext _ _ rfl (by
    simp only [Grothendieck.comp_fiber, sec.hom_comp]
    cat_disch)

/--
The section functor composed with forget equals the identity.
-/
theorem SectionData.toFunctor_comp_forget :
    sec.toFunctor ⋙ Grothendieck.forget F = 𝟭 C := rfl

variable {D : Type u₁} [Category.{v₁} D]
variable (F)

/--
The factorization of `FunctorToData F` via sections and `pre`.

A `FunctorToData F (D := D)` decomposes into:
- A base functor `baseFunc : D ⥤ C`
- Section data for `baseFunc ⋙ F`

The original functor is recovered as `sec.toFunctor ⋙ pre F baseFunc`.
-/
def FunctorToData.toSigmaSectionData (data : FunctorToData F (D := D)) :
    Σ (baseFunc : D ⥤ C), SectionData (baseFunc ⋙ F) :=
  ⟨data.baseFunc, {
    fib := data.fib
    hom := data.hom
    hom_id := data.hom_id
    hom_comp := data.hom_comp
  }⟩

/--
Reconstruct `FunctorToData F` from a base functor and section data.
-/
def FunctorToData.ofSigmaSectionData
    (data : Σ (baseFunc : D ⥤ C), SectionData (baseFunc ⋙ F)) :
    FunctorToData F (D := D) :=
  { baseFunc := data.1
    fib := data.2.fib
    hom := data.2.hom
    hom_id := data.2.hom_id
    hom_comp := data.2.hom_comp }

/--
Round-trip: `ofSigmaSectionData (toSigmaSectionData data) = data`
-/
theorem FunctorToData.ofSigmaSectionData_toSigmaSectionData
    (data : FunctorToData F (D := D)) :
    FunctorToData.ofSigmaSectionData F (FunctorToData.toSigmaSectionData F data) =
      data := rfl

/--
Round-trip: `toSigmaSectionData (ofSigmaSectionData data) = data`
-/
theorem FunctorToData.toSigmaSectionData_ofSigmaSectionData
    (data : Σ (baseFunc : D ⥤ C), SectionData (baseFunc ⋙ F)) :
    FunctorToData.toSigmaSectionData F (FunctorToData.ofSigmaSectionData F data) =
      data := rfl

/--
Equivalence between `FunctorToData F` and `Σ (baseFunc : D ⥤ C), SectionData (baseFunc ⋙ F)`.

This establishes that functors into the Grothendieck construction decompose
into a choice of base functor plus section data for the pulled-back construction.
-/
def FunctorToData.equivSigmaSectionData :
    FunctorToData F (D := D) ≃ Σ (baseFunc : D ⥤ C), SectionData (baseFunc ⋙ F) where
  toFun := FunctorToData.toSigmaSectionData F
  invFun := FunctorToData.ofSigmaSectionData F
  left_inv := FunctorToData.ofSigmaSectionData_toSigmaSectionData F
  right_inv := FunctorToData.toSigmaSectionData_ofSigmaSectionData F

/--
Construct the functor `D ⥤ Grothendieck F` via the section-pre factorization.

Given a base functor and section data, this constructs the functor as:
`sec.toFunctor ⋙ pre F baseFunc`

This makes explicit that functors into Grothendieck constructions factor through
the pullback construction via `pre`.
-/
def FunctorToData.toFunctorViaPre
    (baseFunc : D ⥤ C) (sec : SectionData (baseFunc ⋙ F)) : D ⥤ Grothendieck F :=
  sec.toFunctor ⋙ Grothendieck.pre F baseFunc

/--
The two ways of constructing a functor from `FunctorToData` agree.

`functorTo F data = sec.toFunctor ⋙ pre F baseFunc`

where `sec` is the section data extracted from `data`.
-/
theorem FunctorToData.functorTo_eq_toFunctorViaPre (data : FunctorToData F (D := D)) :
    functorTo F data =
      FunctorToData.toFunctorViaPre F data.baseFunc
        (FunctorToData.toSigmaSectionData F data).2 := rfl

end SectionData

section NatTransTo

/--
The type of fiber morphism functions for `natTransTo`.
Given a base natural transformation `baseNat : dataG.baseFunc ⟶ dataH.baseFunc`,
a fiber morphism function assigns to each `d : D` a morphism from the transported
source fiber to the target fiber.
-/
abbrev NatTransToFibMor (dataG dataH : FunctorToData F (D := D))
    (baseNat : dataG.baseFunc ⟶ dataH.baseFunc) :=
  ∀ d, (F.map (baseNat.app d)).toFunctor.obj (dataG.fib d) ⟶ dataH.fib d

/--
The type of base equality proofs for `natTransTo`.
This equality follows from naturality of `baseNat` and functoriality of `F`.
Clients can provide any proof of this equality.
-/
abbrev NatTransToEqBase (dataG dataH : FunctorToData F (D := D))
    (baseNat : dataG.baseFunc ⟶ dataH.baseFunc) :=
  ∀ {d d' : D} (f : d ⟶ d'),
    (F.map (dataG.baseFunc.map f ≫ baseNat.app d')).toFunctor.obj (dataG.fib d) =
    (F.map (baseNat.app d ≫ dataH.baseFunc.map f)).toFunctor.obj (dataG.fib d)

/--
The fiber naturality condition for `natTransTo`.
This expresses that the two paths from source to target fiber (via composition
in the Grothendieck category) are equal after accounting for type transports.

Both sides start from `(F.map (dataG.baseFunc.map f ≫ baseNat.app d')).obj (dataG.fib d)`
and end at `dataH.fib d'`.
-/
abbrev NatTransToFibNat (dataG dataH : FunctorToData F (D := D))
    (baseNat : dataG.baseFunc ⟶ dataH.baseFunc)
    (fibMor : NatTransToFibMor F dataG dataH baseNat)
    (eq_base : NatTransToEqBase F dataG dataH baseNat) :=
  ∀ {d d' : D} (f : d ⟶ d'),
    eqToHom (catHom_congr_obj
        (F.map_comp (dataG.baseFunc.map f) (baseNat.app d')) (dataG.fib d)) ≫
      (F.map (baseNat.app d')).toFunctor.map (dataG.hom f) ≫
      fibMor d' =
    eqToHom ((eq_base f).trans (catHom_congr_obj
        (F.map_comp (baseNat.app d) (dataH.baseFunc.map f)) (dataG.fib d))) ≫
      (F.map (dataH.baseFunc.map f)).toFunctor.map (fibMor d) ≫
      dataH.hom f

/--
The data required to construct a natural transformation between functors
into the Grothendieck construction.

This bundles together all the components needed for `natTransTo`:
- A base natural transformation between the base functors
- Fiber morphisms for each object
- Equality proof for base naturality (for eqToHom flexibility)
- Fiber naturality condition
-/
structure NatTransToData (dataG dataH : FunctorToData F (D := D)) where
  /-- Natural transformation between base functors -/
  baseNat : dataG.baseFunc ⟶ dataH.baseFunc
  /-- Fiber morphisms: for each `d`, a morphism between fibers -/
  fibMor : NatTransToFibMor F dataG dataH baseNat
  /-- Equality proof from base naturality -/
  eq_base : NatTransToEqBase F dataG dataH baseNat
  /-- Fiber naturality condition -/
  fibNat : NatTransToFibNat F dataG dataH baseNat fibMor eq_base

variable (dataG dataH : FunctorToData F (D := D))
variable (nat : NatTransToData F dataG dataH)

set_option backward.isDefEq.respectTransparency false in
/--
Construct a natural transformation between functors into the Grothendieck
construction from bundled data.
-/
def natTransTo : functorTo F dataG ⟶ functorTo F dataH where
  app d := ⟨nat.baseNat.app d, nat.fibMor d⟩
  naturality {d d'} f := by
    have w_base : (dataG.baseFunc.map f ≫ nat.baseNat.app d') =
        (nat.baseNat.app d ≫ dataH.baseFunc.map f) :=
      nat.baseNat.naturality f
    refine Grothendieck.ext _ _ w_base ?_
    simp only [Grothendieck.comp_fiber, functorTo]
    have h := @nat.fibNat d d' f
    cat_disch

variable (α : functorTo F dataG ⟶ functorTo F dataH)

/--
The base natural transformation extracted from a natural transformation
between functors into Grothendieck.
-/
def ofNatTransBaseNat : dataG.baseFunc ⟶ dataH.baseFunc where
  app d := (α.app d).base
  naturality {d d'} f := by
    have h := α.naturality f
    simp only [functorTo] at h
    exact congrArg Grothendieck.Hom.base h

/--
Extract `NatTransToData` from a natural transformation between functors
into the Grothendieck construction.
-/
def ofNatTrans : NatTransToData F dataG dataH where
  baseNat := ofNatTransBaseNat F dataG dataH α
  fibMor d := (α.app d).fiber
  eq_base {d d'} f := by
    simp only [ofNatTransBaseNat]
    have h := α.naturality f
    simp only [functorTo] at h
    have hbase := congrArg Grothendieck.Hom.base h
    simp only [Grothendieck.comp_base] at hbase
    exact catHom_congr_obj (congrArg F.map hbase) (dataG.fib d)
  fibNat {d d'} f := by
    simp only [ofNatTransBaseNat, functorTo]
    have h := α.naturality f
    simp only [functorTo] at h
    have hfiber := Grothendieck.congr h
    simp only [Grothendieck.comp_fiber] at hfiber
    calc _ = _ := by cat_disch
      _ = _ := hfiber
      _ = _ := by cat_disch

/--
Converting a natural transformation to data and back gives the original.
-/
theorem natTransTo_ofNatTrans : natTransTo F dataG dataH (ofNatTrans F dataG dataH α) = α := by
  ext d
  rfl

/--
Converting data to a natural transformation and back gives the original.
-/
theorem ofNatTrans_natTransTo :
    ofNatTrans F dataG dataH (natTransTo F dataG dataH nat) = nat := rfl

/--
Equivalence between `NatTransToData` and natural transformations between
functors into Grothendieck categories.
-/
def natTransToEquiv :
    NatTransToData F dataG dataH ≃ (functorTo F dataG ⟶ functorTo F dataH) where
  toFun := natTransTo F dataG dataH
  invFun := ofNatTrans F dataG dataH
  left_inv := ofNatTrans_natTransTo F dataG dataH
  right_inv := natTransTo_ofNatTrans F dataG dataH

end NatTransTo

section FunctorToDataCategory

variable (data : FunctorToData F (D := D))

/--
The identity `NatTransToData` for a `FunctorToData`, defined via the correspondence
with identity natural transformations.
-/
def NatTransToData.id : NatTransToData F data data :=
  ofNatTrans F data data (𝟙 (functorTo F data))

/--
Composition of `NatTransToData`, defined via the correspondence with natural
transformation composition.
-/
def NatTransToData.comp {dataG dataH dataK : FunctorToData F (D := D)}
    (nat1 : NatTransToData F dataG dataH)
    (nat2 : NatTransToData F dataH dataK) : NatTransToData F dataG dataK :=
  ofNatTrans F dataG dataK (natTransTo F dataG dataH nat1 ≫ natTransTo F dataH dataK nat2)

/--
Category instance on `FunctorToData F (D := D)` using `NatTransToData` as morphisms.
-/
instance functorToDataCategory : Category (FunctorToData F (D := D)) where
  Hom := NatTransToData F
  id := NatTransToData.id F
  comp {X Y Z} := NatTransToData.comp (F := F)
  id_comp {_ _} nat := by
    unfold NatTransToData.id NatTransToData.comp
    conv_rhs => rw [← ofNatTrans_natTransTo F _ _ nat]
    congr 1
    exact Category.id_comp _
  comp_id {_ _} nat := by
    unfold NatTransToData.id NatTransToData.comp
    conv_rhs => rw [← ofNatTrans_natTransTo F _ _ nat]
    congr 1
    exact Category.comp_id _
  assoc {_ _ _ _} nat1 nat2 nat3 := by
    unfold NatTransToData.comp
    congr 1
    exact Category.assoc _ _ _

/--
Functor from `FunctorToData F` to the functor category `D ⥤ Grothendieck F`.
Sends `data` to `functorTo F data` and morphisms via `natTransTo`.
-/
def functorToDataToFunctorCat : FunctorToData F (D := D) ⥤ (D ⥤ Grothendieck F) where
  obj := functorTo F
  map := natTransTo F _ _
  map_id _ := rfl
  map_comp _ _ := rfl

/--
Functor from the functor category `D ⥤ Grothendieck F` to `FunctorToData F`.
Sends `G` to `ofFunctor F G` and morphisms via `ofNatTrans`.
-/
def functorCatToFunctorToData : (D ⥤ Grothendieck F) ⥤ FunctorToData F (D := D) where
  obj := ofFunctor F
  map {G H} α := ofNatTrans F (ofFunctor F G) (ofFunctor F H) α
  map_id _ := rfl
  map_comp _ _ := rfl

/--
Categorical isomorphism between `FunctorToData F` and the functor category
`D ⥤ Grothendieck F`.
-/
def functorToDataIsoCat : FunctorToData F (D := D) ≅Cat (D ⥤ Grothendieck F) where
  hom := (functorToDataToFunctorCat F (D := D)).toCatHom
  inv := (functorCatToFunctorToData F (D := D)).toCatHom
  hom_inv_id := rfl
  inv_hom_id := rfl

end FunctorToDataCategory

section FunctorFromData

/-!
### FunctorFromData: Bundled data for functors FROM Grothendieck constructions

This section provides the dual to `FunctorToData`: a complete characterization of
functors FROM a Grothendieck construction `Grothendieck F ⥤ E`.

Every such functor is determined by:
- A family of fiber functors `fib : ∀ c, F.obj c ⥤ E`
- Natural transformations `hom f : fib c ⟶ F.map f ⋙ fib c'` for each `f : c ⟶ c'`
- Coherence conditions for identity and composition
-/

variable {E : Type*} [Category E]

/--
The type of fiber functors for `Grothendieck.functorFrom`.
For each `c : C`, we have a functor from the fiber `F.obj c` to `E`.
-/
abbrev FunctorFromFib := ∀ c, F.obj c ⥤ E

/--
The type of natural transformation data for `Grothendieck.functorFrom`.
For each morphism `f : c ⟶ c'`, we have a natural transformation
`fib c ⟶ F.map f ⋙ fib c'`.
-/
abbrev FunctorFromHom (fib : FunctorFromFib F (E := E)) :=
  ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ (F.map f).toFunctor ⋙ fib c'

/--
The identity coherence property for `Grothendieck.functorFrom`.
States that `hom (𝟙 c)` equals the canonical isomorphism from `F.map_id`.
-/
abbrev FunctorFromHomId (fib : FunctorFromFib F (E := E))
    (hom : FunctorFromHom F fib) :=
  ∀ c, hom (𝟙 c) = eqToHom (by simp only [CategoryTheory.Functor.map_id]; rfl)

/--
The composition coherence property for `Grothendieck.functorFrom`.
States that `hom (f ≫ g)` decomposes as the composition of `hom f`, whiskered `hom g`,
and the canonical isomorphism from `F.map_comp`.
-/
abbrev FunctorFromHomComp (fib : FunctorFromFib F (E := E))
    (hom : FunctorFromHom F fib) :=
  ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
    hom f ≫ Functor.whiskerLeft (F.map f).toFunctor (hom g) ≫
    eqToHom (by simp only [Functor.map_comp]; rfl)

/--
Bundled data for constructing a functor from the Grothendieck construction.

This structure captures all the data needed to define a functor `Grothendieck F ⥤ E`:
- Fiber functors from each `F.obj c` to `E`
- Natural transformations relating fibers along base morphisms
- Coherence conditions ensuring functoriality
-/
structure FunctorFromData where
  /-- Fiber functors: for each `c : C`, a functor `F.obj c ⥤ E` -/
  fib : FunctorFromFib F (E := E)
  /-- Natural transformations: for each `f : c ⟶ c'`, `fib c ⟶ F.map f ⋙ fib c'` -/
  hom : FunctorFromHom F fib
  /-- Identity coherence -/
  hom_id : FunctorFromHomId F fib hom
  /-- Composition coherence -/
  hom_comp : FunctorFromHomComp F fib hom

variable (data : FunctorFromData F (E := E))

/--
Construct a functor from the Grothendieck construction using bundled data.
This wraps mathlib's `Grothendieck.functorFrom`.
-/
def functorFromData : Grothendieck F ⥤ E :=
  Grothendieck.functorFrom data.fib data.hom data.hom_id data.hom_comp

variable {F} (H : Grothendieck F ⥤ E)

set_option backward.isDefEq.respectTransparency false in
/--
Extract bundled data from a functor `Grothendieck F ⥤ E`:
- `fib c := ι F c ⋙ H` extracts the fiber functors
- `hom f := ιNatTrans f ▷ H` constructs the natural transformations using
  the canonical lifted base morphism
-/
def ofFunctorFrom : FunctorFromData F (E := E) where
  fib c := Grothendieck.ι F c ⋙ H
  hom {c c'} f := Functor.whiskerRight (Grothendieck.ιNatTrans (F := F) f) H
  hom_id c := by
    ext x
    simp only [Functor.comp_obj, Grothendieck.ι_obj, Functor.whiskerRight_app, eqToHom_app,
      Grothendieck.ιNatTrans]
    have heq : (⟨c, x⟩ : Grothendieck F) = ⟨c, (F.map (𝟙 c)).toFunctor.obj x⟩ := by
      simp only [CategoryTheory.Functor.map_id]
      rfl
    have h : (Grothendieck.Hom.mk (base := 𝟙 c)
        (fiber := 𝟙 ((F.map (𝟙 c)).toFunctor.obj x)) :
        Grothendieck.Hom (F := F) ⟨c, x⟩ ⟨c, (F.map (𝟙 c)).toFunctor.obj x⟩) = eqToHom heq := by
      rw [Grothendieck.eqToHom_eq]
      simp
    rw [h, eqToHom_map]
  hom_comp c₁ c₂ c₃ f g := by
    ext x
    simp only [Functor.comp_obj, Grothendieck.ι_obj, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, eqToHom_app,
      Grothendieck.ιNatTrans]
    rw [← Category.assoc, ← H.map_comp]
    have heq_obj : (⟨c₃, (F.map g).toFunctor.obj ((F.map f).toFunctor.obj x)⟩ :
        Grothendieck F) = ⟨c₃, (F.map (f ≫ g)).toFunctor.obj x⟩ := by
      congr 1
      exact (catHom_congr_obj (F.map_comp f g) x).symm
    rw [← eqToHom_map H heq_obj, ← H.map_comp]
    congr 1
    apply Grothendieck.ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/--
Round-trip: constructing a functor from extracted data gives back the original functor.
-/
theorem functorFromData_ofFunctorFrom : functorFromData F (ofFunctorFrom H) = H := by
  fapply _root_.CategoryTheory.Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp only [functorFromData, ofFunctorFrom, Grothendieck.functorFrom_map,
      Functor.comp_obj, Functor.comp_map, Grothendieck.ι_obj, Grothendieck.ι_map,
      Functor.whiskerRight_app, Category.id_comp, Category.comp_id, eqToHom_refl]
    rw [← H.map_comp]
    congr 1
    apply Grothendieck.ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/--
Round-trip: the fiber functors from extracted data equal the original fiber functors.
-/
theorem ofFunctorFrom_functorFromData_fib :
    (ofFunctorFrom (functorFromData F data)).fib = data.fib := by
  funext c
  fapply _root_.CategoryTheory.Functor.ext
  · intro x
    simp only [ofFunctorFrom, functorFromData, Grothendieck.functorFrom_obj,
      Functor.comp_obj, Grothendieck.ι_obj]
  · intro x y f
    simp only [ofFunctorFrom, functorFromData, Grothendieck.functorFrom_map,
      Functor.comp_obj, Functor.comp_map, Grothendieck.ι_obj, Grothendieck.ι_map,
      Category.id_comp, Category.comp_id, eqToHom_refl]
    have h := congrFun (congrArg NatTrans.app (data.hom_id c)) x
    simp only [eqToHom_app] at h
    rw [h, Functor.map_comp, ← Category.assoc, eqToHom_map]
    simp

set_option backward.isDefEq.respectTransparency false in
/--
Round-trip: the natural transformations from extracted data equal the original
natural transformations at each component.

The two natural transformations have different types because their fiber functors
differ propositionally. This theorem states that the `.app` components are equal
up to `eqToHom` coercions.
-/
theorem ofFunctorFrom_functorFromData_hom_app {c c' : C} (f : c ⟶ c') (x : F.obj c) :
    ((ofFunctorFrom (functorFromData F data)).hom f).app x =
    eqToHom (congrFun (congrArg Functor.obj
      (congrFun (ofFunctorFrom_functorFromData_fib data) c)) x) ≫
    (data.hom f).app x ≫
    eqToHom (congrFun (congrArg Functor.obj
      (congrFun (ofFunctorFrom_functorFromData_fib data) c'))
        ((F.map f).toFunctor.obj x)).symm := by
  simp only [ofFunctorFrom, Functor.whiskerRight_app, functorFromData,
    Grothendieck.ιNatTrans, Grothendieck.ι_obj, Grothendieck.functorFrom_map]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, eqToHom_refl]
  convert Category.comp_id ((data.hom f).app x) using 2

end FunctorFromData

section FunctorFromDataCategory

variable {E : Type*} [Category E]
variable (dataG dataH : FunctorFromData F (E := E))

/--
The fiber natural transformations for `NatTransFromData`.
For each `c : C`, a natural transformation `dataG.fib c ⟶ dataH.fib c`.
-/
abbrev NatTransFromFib :=
  ∀ c, dataG.fib c ⟶ dataH.fib c

/--
The coherence condition for `NatTransFromData`.
For each `f : c ⟶ c'`, the following square commutes:

```
dataG.fib c --fibNat c--> dataH.fib c
    |                         |
dataG.hom f               dataH.hom f
    |                         |
    v                         v
F.map f ⋙ dataG.fib c' --> F.map f ⋙ dataH.fib c'
          (F.map f ◁ fibNat c')
```
-/
abbrev NatTransFromCoherence (fibNat : NatTransFromFib F dataG dataH) :=
  ∀ {c c' : C} (f : c ⟶ c'),
    dataG.hom f ≫ Functor.whiskerLeft (F.map f).toFunctor (fibNat c') =
      fibNat c ≫ dataH.hom f

/--
The data for a natural transformation between functors from the Grothendieck
construction.

This bundles together:
- Fiber natural transformations for each base object
- Coherence condition ensuring compatibility with the `hom` structure
-/
@[ext]
structure NatTransFromData where
  /-- Fiber natural transformations: for each `c`, `dataG.fib c ⟶ dataH.fib c` -/
  fibNat : NatTransFromFib F dataG dataH
  /-- Coherence: `dataG.hom f ≫ (F.map f ◁ fibNat c') = fibNat c ≫ dataH.hom f` -/
  coherence : NatTransFromCoherence F dataG dataH fibNat

variable (natData : NatTransFromData F dataG dataH)

set_option backward.isDefEq.respectTransparency false in
/--
Construct a natural transformation between functors from the Grothendieck
construction from bundled data.
-/
def natTransFrom : functorFromData F dataG ⟶ functorFromData F dataH where
  app X := (natData.fibNat X.base).app X.fiber
  naturality {X Y} f := by
    simp only [functorFromData, Grothendieck.functorFrom_map]
    have h := congrFun (congrArg NatTrans.app (natData.coherence f.base)) X.fiber
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
    rw [Category.assoc, (natData.fibNat Y.base).naturality f.fiber]
    rw [← Category.assoc, ← Category.assoc, h, Category.assoc]

variable {dataG dataH}
variable (α : functorFromData F dataG ⟶ functorFromData F dataH)

/--
Extract the fiber natural transformations from a natural transformation
between functors from Grothendieck. Uses `eqToHom` to cast between
`Grothendieck.ι F c ⋙ functorFromData F data` and `data.fib c`.
-/
def ofNatTransFromFibNat : NatTransFromFib F dataG dataH := fun c =>
  eqToHom (congrFun (ofFunctorFrom_functorFromData_fib dataG) c).symm ≫
  Functor.whiskerLeft (Grothendieck.ι F c) α ≫
  eqToHom (congrFun (ofFunctorFrom_functorFromData_fib dataH) c)

set_option backward.isDefEq.respectTransparency false in
/--
Extract `NatTransFromData` from a natural transformation between functors
from the Grothendieck construction.
-/
def ofNatTransFrom : NatTransFromData F dataG dataH where
  fibNat := ofNatTransFromFibNat F α
  coherence {c c'} f := by
    ext x
    simp only [ofNatTransFromFibNat, NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
    have nat := α.naturality ((Grothendieck.ιNatTrans (F := F) f).app x)
    simp only [functorFromData, Grothendieck.functorFrom_map,
      Grothendieck.ιNatTrans, Grothendieck.ι_obj, Functor.comp_obj] at nat
    simp only [CategoryTheory.Functor.map_id, Category.comp_id] at nat
    simp only [eqToHom_refl', Category.id_comp, Category.comp_id, Grothendieck.ι_obj]
    exact nat

set_option backward.isDefEq.respectTransparency false in
variable (dataG dataH) in
/--
Converting a natural transformation to data and back gives the original.
-/
theorem natTransFrom_ofNatTransFrom :
    natTransFrom F dataG dataH (ofNatTransFrom F α) = α := by
  ext X
  simp only [natTransFrom, ofNatTransFrom, ofNatTransFromFibNat,
    NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
  simp only [eqToHom_refl', Category.id_comp, Category.comp_id, Grothendieck.ι_obj]

set_option backward.isDefEq.respectTransparency false in
variable (dataG dataH) in
/--
Converting data to a natural transformation and back gives the original.
-/
theorem ofNatTransFrom_natTransFrom :
    ofNatTransFrom F (natTransFrom F dataG dataH natData) = natData := by
  ext c x
  simp only [ofNatTransFrom, ofNatTransFromFibNat,
    NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, natTransFrom]
  simp only [eqToHom_refl', Category.id_comp, Category.comp_id, Grothendieck.ι_obj]

/--
Equivalence between `NatTransFromData` and natural transformations between
functors from Grothendieck categories.
-/
def natTransFromEquiv :
    NatTransFromData F dataG dataH ≃
    (functorFromData F dataG ⟶ functorFromData F dataH) where
  toFun := natTransFrom F dataG dataH
  invFun := ofNatTransFrom F
  left_inv := ofNatTransFrom_natTransFrom F dataG dataH
  right_inv := natTransFrom_ofNatTransFrom F dataG dataH

variable (data : FunctorFromData F (E := E))

/--
The identity `NatTransFromData` on a `FunctorFromData`.
-/
def NatTransFromData.id : NatTransFromData F data data where
  fibNat c := 𝟙 (data.fib c)
  coherence {c c'} f := by
    ext x
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app, Category.id_comp]
    exact Category.comp_id _

variable (dataK : FunctorFromData F (E := E))

set_option backward.isDefEq.respectTransparency false in
/--
Composition of `NatTransFromData` values.
-/
def NatTransFromData.comp (natDataGH : NatTransFromData F dataG dataH)
    (natDataHK : NatTransFromData F dataH dataK) :
    NatTransFromData F dataG dataK where
  fibNat c := natDataGH.fibNat c ≫ natDataHK.fibNat c
  coherence {c c'} f := by
    ext x
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    have hGH := congrFun (congrArg NatTrans.app (natDataGH.coherence f)) x
    have hHK := congrFun (congrArg NatTrans.app (natDataHK.coherence f)) x
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hGH hHK
    rw [← Category.assoc, hGH, Category.assoc, hHK, ← Category.assoc]

/--
`natTransFrom` preserves identity.
-/
theorem natTransFrom_id :
    natTransFrom F data data (NatTransFromData.id F data) = 𝟙 (functorFromData F data) := by
  ext X
  simp only [natTransFrom, NatTransFromData.id, NatTrans.id_app, functorFromData,
    Grothendieck.functorFrom_obj]

variable (natDataGH : NatTransFromData F dataG dataH)
variable (natDataHK : NatTransFromData F dataH dataK)

set_option backward.isDefEq.respectTransparency false in
/--
`natTransFrom` preserves composition.
-/
theorem natTransFrom_comp :
    natTransFrom F dataG dataK (NatTransFromData.comp F dataK natDataGH natDataHK) =
    natTransFrom F dataG dataH natDataGH ≫ natTransFrom F dataH dataK natDataHK := by
  ext X
  simp only [natTransFrom, NatTransFromData.comp, NatTrans.comp_app]

/--
Category instance on `FunctorFromData F (E := E)` using `NatTransFromData` as morphisms.
-/
instance functorFromDataCategory : Category (FunctorFromData F (E := E)) where
  Hom := NatTransFromData F
  id := NatTransFromData.id F
  comp {X Y Z} := NatTransFromData.comp F Z
  id_comp {X Y} nat := by
    ext c x
    simp only [NatTransFromData.comp, NatTransFromData.id, Category.id_comp]
  comp_id {X Y} nat := by
    ext c x
    simp only [NatTransFromData.comp, NatTransFromData.id, Category.comp_id]
  assoc {W X Y Z} nat1 nat2 nat3 := by
    ext c x
    simp only [NatTransFromData.comp, Category.assoc]

/--
Functor from `FunctorFromData F` to the functor category `Grothendieck F ⥤ E`.
Sends `data` to `functorFromData F data` and morphisms via `natTransFrom`.
-/
def functorFromDataToFunctorCat : FunctorFromData F (E := E) ⥤ (Grothendieck F ⥤ E) where
  obj := functorFromData F
  map := natTransFrom F _ _
  map_id data := natTransFrom_id F data
  map_comp {dataX dataY dataZ} nat1 nat2 := natTransFrom_comp F (dataG := dataX)
    (dataH := dataY) (dataK := dataZ) (natDataGH := nat1) (natDataHK := nat2)

/--
Composition of natural transformations with `eqToHom` round-trips through intermediate
functors: the middle `eqToHom` terms cancel.
-/
lemma eqToHom_comp_natTrans_comp_app {A : Type*} [Category A]
    {G' G H H' K K' : A ⥤ E} (pG : G' = G) (pH : H' = H) (pK : K' = K)
    (α : G ⟶ H) (β : H ⟶ K) (X : A) :
    (eqToHom pG ≫ (α ≫ β) ≫ eqToHom pK.symm).app X =
    (eqToHom pG ≫ α ≫ eqToHom pH.symm).app X ≫ (eqToHom pH ≫ β ≫ eqToHom pK.symm).app X := by
  simp only [NatTrans.comp_app, eqToHom_app]
  simp only [Category.assoc]
  congr 2
  simp only [← Category.assoc]
  simp only [eqToHom_trans, eqToHom_refl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/--
Functor from the functor category `Grothendieck F ⥤ E` to `FunctorFromData F`.
Sends `H` to `ofFunctorFrom H` and morphisms via round-trip through `functorFromData`.
-/
def functorCatToFunctorFromData : (Grothendieck F ⥤ E) ⥤ FunctorFromData F (E := E) where
  obj := ofFunctorFrom
  map {G H} α := ofNatTransFrom F
    (eqToHom (functorFromData_ofFunctorFrom G) ≫ α ≫
     eqToHom (functorFromData_ofFunctorFrom H).symm)
  map_id G := by
    simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]
    exact ofNatTransFrom_natTransFrom F _ _ (NatTransFromData.id F (ofFunctorFrom G))
  map_comp {G H K} α β := by
    apply NatTransFromData.ext
    funext c
    ext x
    dsimp only [functorFromDataCategory, CategoryStruct.comp,
      NatTransFromData.comp]
    simp only [ofNatTransFrom, ofNatTransFromFibNat,
      NatTrans.vcomp_app, NatTrans.comp_app,
      Functor.whiskerLeft_app, eqToHom_app,
      eqToHom_refl', Category.id_comp, Category.comp_id,
      Grothendieck.ι_obj]

/--
Counit isomorphism for the equivalence: the round-trip through `FunctorFromData` gives
back the original functor up to the canonical equality.
-/
def functorFromDataEquivCounitIso :
    functorCatToFunctorFromData (F := F) (E := E) ⋙ functorFromDataToFunctorCat (F := F) ≅
    𝟭 (Grothendieck F ⥤ E) :=
  NatIso.ofComponents
    (fun G => eqToIso (functorFromData_ofFunctorFrom G))
    (fun {G H} α => by
      simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
      simp only [functorFromDataToFunctorCat, functorCatToFunctorFromData]
      rw [natTransFrom_ofNatTransFrom]
      simp only [eqToIso.hom, Category.assoc]
      simp only [eqToHom_trans, eqToHom_refl, Category.comp_id])

set_option backward.isDefEq.respectTransparency false in
/--
Forward morphism for the unit isomorphism: `data ⟶ ofFunctorFrom (functorFromData F data)`.
Uses the equality `ofFunctorFrom_functorFromData_fib` to build the natural transformation.
-/
def functorFromDataEquivUnitHom (data : FunctorFromData F (E := E)) :
    data ⟶ ofFunctorFrom (functorFromData F data) where
  fibNat c := eqToHom (congrFun (ofFunctorFrom_functorFromData_fib data) c).symm
  coherence {c c'} f := by
    ext x
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
    simp only [ofFunctorFrom_functorFromData_hom_app, eqToHom_refl', Category.id_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
Backward morphism for the unit isomorphism: `ofFunctorFrom (functorFromData F data) ⟶ data`.
-/
def functorFromDataEquivUnitInv (data : FunctorFromData F (E := E)) :
    ofFunctorFrom (functorFromData F data) ⟶ data where
  fibNat c := eqToHom (congrFun (ofFunctorFrom_functorFromData_fib data) c)
  coherence {c c'} f := by
    ext x
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
    simp only [ofFunctorFrom_functorFromData_hom_app, eqToHom_refl', Category.id_comp,
      Category.comp_id]
    simp

/--
Unit isomorphism component for the equivalence.
-/
def functorFromDataEquivUnitComponent (data : FunctorFromData F (E := E)) :
    data ≅ (functorFromDataToFunctorCat (F := F) ⋙
      functorCatToFunctorFromData (F := F)).obj data := by
  simp only [Functor.comp_obj, functorFromDataToFunctorCat, functorCatToFunctorFromData]
  exact { hom := functorFromDataEquivUnitHom (F := F) data
          inv := functorFromDataEquivUnitInv (F := F) data
          hom_inv_id := by
            apply NatTransFromData.ext
            funext c
            unfold CategoryStruct.comp CategoryStruct.id functorFromDataCategory
            simp only [functorFromDataEquivUnitHom, functorFromDataEquivUnitInv,
              NatTransFromData.comp, NatTransFromData.id, eqToHom_trans, eqToHom_refl]
          inv_hom_id := by
            apply NatTransFromData.ext
            funext c
            unfold CategoryStruct.comp CategoryStruct.id functorFromDataCategory
            simp only [functorFromDataEquivUnitHom, functorFromDataEquivUnitInv,
              NatTransFromData.comp, NatTransFromData.id, eqToHom_trans, eqToHom_refl] }

set_option backward.isDefEq.respectTransparency false in
/--
Unit isomorphism for the equivalence.
-/
def functorFromDataEquivUnitIso :
    𝟭 (FunctorFromData F (E := E)) ≅
    functorFromDataToFunctorCat (F := F) ⋙ functorCatToFunctorFromData (F := F) :=
  NatIso.ofComponents
    (fun data => functorFromDataEquivUnitComponent (F := F) data)
    (fun {data data'} nat => by
      apply NatTransFromData.ext
      funext c
      ext x
      simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
      unfold CategoryStruct.comp functorFromDataCategory
      simp only [functorFromDataToFunctorCat, functorCatToFunctorFromData,
        functorFromDataEquivUnitComponent, functorFromDataEquivUnitHom,
        NatTransFromData.comp, ofNatTransFrom, ofNatTransFromFibNat,
        NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, natTransFrom]
      simp)

/--
The category of `FunctorFromData F` is equivalent to the functor category
`Grothendieck F ⥤ E`.
-/
def functorFromDataEquivCat :
    FunctorFromData F (E := E) ≌ (Grothendieck F ⥤ E) where
  functor := functorFromDataToFunctorCat (F := F)
  inverse := functorCatToFunctorFromData (F := F)
  unitIso := functorFromDataEquivUnitIso (F := F)
  counitIso := functorFromDataEquivCounitIso (F := F)
  functor_unitIso_comp data := by
    apply NatTrans.ext
    funext X
    simp only [functorFromDataEquivUnitIso, NatIso.ofComponents_hom_app,
      functorFromDataEquivCounitIso, functorFromDataToFunctorCat, functorCatToFunctorFromData,
      functorFromDataEquivUnitComponent, Functor.comp_obj]
    simp only [eqToIso.hom, NatTrans.comp_app, NatTrans.id_app]
    simp only [natTransFrom, functorFromDataEquivUnitHom, eqToHom_app]
    simp only [functorFromData, Grothendieck.functorFrom_obj]
    simp

end FunctorFromDataCategory

end Grothendieck

end Covariant

variable {C : Type u} [CInst : Category.{v, u} C]
variable {D : Type u₁} [DInst : Category.{v₁, u₁} D]

variable (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})

/--
The contravariant Grothendieck construction for a functor `F' : Cᵒᵖ' ⥤ Cat`
gives a category whose

* objects `X` consist of `X.base : C` and `X.fiber : F'.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : X.fiber ⟶ (F'.map base).obj Y.fiber`

In the `ᵒᵖ'` form, the corresponding definition is:
-/
structure GrothendieckContra' where
  /-- The underlying object in `C` -/
  base : C
  /-- The object in the fiber of the base object. -/
  fiber : F'.obj base

namespace GrothendieckContra'

variable {F'}

@[ext (iff := false)]
theorem obj_ext (X Y : GrothendieckContra' F') (w_base : X.base = Y.base)
    (w_fiber : X.fiber ≍ Y.fiber) : X = Y := by
  cases X; cases Y
  simp only at w_base
  subst w_base
  simp only [heq_eq_eq] at w_fiber
  subst w_fiber
  rfl

/-- A morphism in the contravariant Grothendieck category `F' : Cᵒᵖ' ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : X.fiber ⟶ (F'.map base).obj Y.fiber`.
-/
structure Hom (X Y : GrothendieckContra' F') where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism from the source fiber object to the pullback of the target fiber object. -/
  fiber : X.fiber ⟶ (F'.map base).toFunctor.obj Y.fiber

@[ext (iff := false)]
theorem ext {X Y : GrothendieckContra' F'} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : f.fiber ≫ eqToHom (by rw [w_base]) = g.fiber) : f = g := by
  cases f; cases g
  congr
  dsimp at w_base
  cat_disch

@[simp]
theorem id_fiber_cod_eq (X : GrothendieckContra' F') :
  (F'.map (𝟙 X.base)).toFunctor.obj X.fiber = X.fiber :=
    catHom_congr_obj (F'.map_id X.base) X.fiber

@[simp]
theorem id_fiber_eq (X : GrothendieckContra' F') :
  (X.fiber ⟶ (F'.map (𝟙 X.base)).toFunctor.obj X.fiber) = (X.fiber ⟶ X.fiber) :=
    (congrArg (Quiver.Hom X.fiber) (id_fiber_cod_eq X).symm).symm

@[simp]
theorem id_fiber_eq_op (X : GrothendieckContra' F') :
  ((F'.map (𝟙 X.base)).toFunctor.obj X.fiber ⟶ X.fiber) = (X.fiber ⟶ X.fiber) :=
    (congrFun (congrArg Quiver.Hom (id_fiber_cod_eq X).symm) X.fiber).symm

@[simp]
theorem id_fiber_eq_rev (X : GrothendieckContra' F') :
  ((F'.map (𝟙 X.base)).toFunctor.obj X.fiber ⟶ X.fiber) =
  (X.fiber ⟶ (F'.map (𝟙 X.base)).toFunctor.obj X.fiber) :=
    Eq.trans (id_fiber_eq_op X) (id_fiber_eq X).symm

/-- The identity morphism in the contravariant Grothendieck category.
-/
def id (X : GrothendieckContra' F') : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (id_fiber_cod_eq X).symm

instance (X : GrothendieckContra' F') : Inhabited (Hom X X) :=
  ⟨id X⟩

@[simp]
theorem comp_fiber_cod_eq {X Y Z : GrothendieckContra' F'}
  (f : Hom X Y) (g : Hom Y Z) :
    (F'.map f.base).toFunctor.obj ((F'.map g.base).toFunctor.obj Z.fiber) =
    (F'.map (g.base ≫ f.base)).toFunctor.obj Z.fiber :=
      (symm <| catHom_congr_obj (F'.map_comp g.base f.base) Z.fiber)

@[simp]
theorem comp_fiber_eq {X Y Z : GrothendieckContra' F'}
  (f : Hom X Y) (g : Hom Y Z) :
  ((F'.map f.base).toFunctor.obj Y.fiber ⟶
    (F'.map f.base).toFunctor.obj ((F'.map g.base).toFunctor.obj Z.fiber)) =
  ((F'.map f.base).toFunctor.obj Y.fiber ⟶
    (F'.map (g.base ≫ f.base)).toFunctor.obj Z.fiber) :=
  (congrArg
    (Quiver.Hom ((F'.map f.base).toFunctor.obj Y.fiber))
    (comp_fiber_cod_eq f g ).symm).symm

@[simp]
theorem comp_fiber_eq_op {X Y Z : GrothendieckContra' F'}
  (f : Hom X Y) (g : Hom Y Z) :
  ((F'.map f.base).toFunctor.obj ((F'.map g.base).toFunctor.obj Z.fiber) ⟶
    (F'.map f.base).toFunctor.obj Y.fiber) =
  ((F'.map (g.base ≫ f.base)).toFunctor.obj Z.fiber ⟶
    (F'.map f.base).toFunctor.obj Y.fiber) :=
  (congrFun
    (congrArg Quiver.Hom (comp_fiber_cod_eq f g).symm)
    ((F'.map f.base).toFunctor.obj Y.fiber)).symm

/-- Composition of morphisms in the contravariant Grothendieck category.
-/
def comp {X Y Z : GrothendieckContra' F'} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber := f.fiber ≫ (F'.map f.base).toFunctor.map g.fiber ≫
    eqToHom (comp_fiber_cod_eq f g)

attribute [local simp] eqToHom_map CategoryTheory.Functor.map_id

instance GrothendieckContraInst' : Category (GrothendieckContra' F') where
  Hom X Y := GrothendieckContra'.Hom X Y
  id X := GrothendieckContra'.id X
  comp f g := GrothendieckContra'.comp f g
  comp_id {X Y} f := by
    ext
    · simp [comp, id]
    · dsimp [comp, id]
      simp
  id_comp {X Y} f := by
    ext
    · simp [comp, id]
    · dsimp [comp, id]
      slice_lhs 1 3 =>
        erw [Functor.congr_hom (congrArg Cat.Hom.toFunctor (F'.map_id X.base)) f.fiber]
      simp
  assoc f g h := by
    ext
    · simp [comp]
    · dsimp [comp]
      slice_lhs 2 4 =>
        erw [Functor.congr_hom (congrArg Cat.Hom.toFunctor (F'.map_comp g.base f.base)) h.fiber]
      simp

abbrev GrothendieckContraCat' : Cat := Cat.of (GrothendieckContra' F')

@[simp]
theorem id_base (X : GrothendieckContra' F') : (id X).base = 𝟙 X.base := rfl

@[simp]
theorem id_base_eq (X : GrothendieckContra' F') :
  (F'.map X.id.base).toFunctor.obj X.fiber = X.fiber :=
    catHom_congr_obj (F'.map_id X.base) X.fiber

theorem id_fiber_val (X : GrothendieckContra' F') :
    (id X).fiber = eqToHom (id_base_eq X).symm := rfl

@[simp]
theorem comp_base {X Y Z : GrothendieckContra' F'} (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).base = f.base ≫ g.base := rfl

@[simp]
theorem comp_fiber {X Y Z : GrothendieckContra' F'} (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).fiber = f.fiber ≫ (F'.map f.base).toFunctor.map g.fiber ≫
      eqToHom (comp_fiber_cod_eq f g) :=
        rfl

/-! ### Category-level lemmas

These lemmas relate the category operations `𝟙` and `≫` to the underlying
base and fiber components. They are definitionally equal to the `id_*` and
`comp_*` lemmas above, but having explicit versions for category notation
allows simp to apply them directly.
-/

@[simp]
theorem cat_id_base (X : GrothendieckContra' F') :
    (𝟙 X : X ⟶ X).base = 𝟙 X.base := rfl

@[simp]
theorem cat_id_fiber (X : GrothendieckContra' F') :
    (𝟙 X : X ⟶ X).fiber = eqToHom (id_base_eq X).symm := rfl

@[simp]
theorem cat_comp_base {X Y Z : GrothendieckContra' F'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base := rfl

@[simp]
theorem cat_comp_fiber {X Y Z : GrothendieckContra' F'}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).fiber = f.fiber ≫ (F'.map f.base).toFunctor.map g.fiber ≫
      eqToHom (comp_fiber_cod_eq f g) := rfl

theorem congr {X Y : GrothendieckContra' F'} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = g.fiber ≫ eqToHom (by subst h; rfl) := by
  subst h
  simp

@[simp]
theorem base_eqToHom {X Y : GrothendieckContra' F'} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg GrothendieckContra'.base h) := by
  subst h
  rfl

@[simp]
theorem fiber_eqToHom {X Y : GrothendieckContra' F'} (h : X = Y) :
    (eqToHom h).fiber = eqToHom (by subst h; exact (id_fiber_cod_eq X).symm) := by
  subst h
  rfl

theorem conj_eqToHom_fiber_heq {W X Y Z : GrothendieckContra' F'}
    (h : W = X) (f : X ⟶ Y) (h' : Y = Z) :
    (eqToHom h ≫ f ≫ eqToHom h').fiber ≍ f.fiber := by
  subst h h'
  simp only [eqToHom_refl]
  have heq : (𝟙 W ≫ f ≫ 𝟙 Y) = f := by simp
  exact heq.symm ▸ HEq.refl _

lemma eqToHom_eq {X Y : GrothendieckContra' F'} (hF : X = Y) :
    eqToHom hF = { base := eqToHom (by subst hF; rfl)
                   fiber := eqToHom (by subst hF; exact (id_fiber_cod_eq X).symm) } := by
  subst hF
  rfl

lemma eqToHom_proof_irrel {D : Type*} [Category D] {a b : D}
    (h₁ h₂ : a = b) : eqToHom h₁ = eqToHom h₂ := by
  cases h₁
  rfl

lemma comp_comp_eqToHom_eq {D : Type*} [Category D] {a b c d : D}
    (f : a ⟶ b) (g : b ⟶ c) (h₁ h₂ : c = d) :
    f ≫ g ≫ eqToHom h₁ = f ≫ g ≫ eqToHom h₂ := by
  exact congrArg (f ≫ g ≫ ·) (eqToHom_proof_irrel h₁ h₂)

section Isomorphism

def grothendieckContraIsoHomObj :
    GrothendieckContra F' → GrothendieckContra' F' :=
  fun X ↦ ⟨X.base, X.fiber⟩

def grothendieckContraIsoHomMap
    {X Y : GrothendieckContra F'} :
    gcHom F' X Y →
    (grothendieckContraIsoHomObj X ⟶ grothendieckContraIsoHomObj Y) :=
  fun f ↦ ⟨f.base, f.fiber⟩

theorem grothendieckContraIsoHomMapId_base_components
    (base : C) (fiber : F'.obj base) :
    (grothendieckContraIsoHomMap (gcId F' ⟨base, fiber⟩)).base =
    (id ⟨base, fiber⟩).base :=
  Eq.trans (gcf_id_base F' ⟨base, fiber⟩) (id_base ⟨base, fiber⟩).symm

theorem gcf_id_base_eq_components (base : C) (fiber : F'.obj base) :
    gcf_id_base_eq F' ⟨base, fiber⟩ = id_base_eq ⟨base, fiber⟩ := rfl

theorem grothendieckContraIsoHomMapId_fiber_components
    (base : C) (fiber : F'.obj base) :
    (grothendieckContraIsoHomMap (gcId F' ⟨base, fiber⟩)).fiber =
    (id ⟨base, fiber⟩).fiber := by
  simp only [grothendieckContraIsoHomMap, gcf_id_fiber, id_fiber_val]
  exact Cat.eqToHom_postCompOp_eq F' base
    (gcf_id_base_eq F' ⟨base, fiber⟩)
    (id_base_eq ⟨base, fiber⟩).symm

set_option backward.isDefEq.respectTransparency false in
theorem grothendieckContraIsoHomMapId
    (X : GrothendieckContra F') :
    grothendieckContraIsoHomMap (gcId F' X) = 𝟙 (grothendieckContraIsoHomObj X) := by
  cases X with | mk base fiber =>
  have h_base := @grothendieckContraIsoHomMapId_base_components _ CInst F' base fiber
  have h_fiber := @grothendieckContraIsoHomMapId_fiber_components _ CInst F' base fiber
  refine GrothendieckContra'.ext _ _ h_base ?_
  rw [h_fiber]
  rw [id_fiber_val]
  simp only [eqToHom_trans, cat_id_fiber]

theorem grothendieckContraIsoHomMapComp_base_components
    {X Y Z : GrothendieckContra F'}
    (f : gcHom F' X Y)
    (g : gcHom F' Y Z) :
    (grothendieckContraIsoHomMap (gcComp F' f g)).base =
    (grothendieckContraIsoHomMap f ≫ grothendieckContraIsoHomMap g).base := by
  simp only [grothendieckContraIsoHomMap, grothendieckContraIsoHomObj]
  rw [gcf_comp_base]
  rfl

theorem grothendieckContraIsoHomMapComp_fiber_eq
    {X Y Z : GrothendieckContra F'} (f : gcHom F' X Y) (g : gcHom F' Y Z) :
    eqToHom (gcf_comp_fiber_precomp F' f g) ≫
      ((Cat.postCompOpFunctor'.obj F').map f.base).toFunctor.map g.fiber ≫ f.fiber =
    (grothendieckContraIsoHomMap f ≫ grothendieckContraIsoHomMap g).fiber := by
  unfold Cat.Hom.toFunctor
  simp only [CategoryOp'.eq_1, CategoryOp'Inst,
    Cat.postCompOpFunctor',
    Cat.opFunctor'.eq_1,
    Functor.op'.eq_1, functorOp'Obj.eq_1,
    Functor.whiskeringRight_obj_obj, Functor.comp_obj,
    Cat.opFunctorObj', Cat.of, Bundled.of,
    CategoryStruct.comp, Functor.comp_map,
    Functor.toCatHom_toFunctor,
    grothendieckContraIsoHomObj,
    grothendieckContraIsoHomMap, comp_fiber]
  unfold Cat.Hom.toFunctor
  simp +instances only [CategoryOp'.eq_1, CategoryOp'Inst,
    Cat.postCompOpFunctor',
    Cat.opFunctor'.eq_1,
    Functor.op'.eq_1, functorOp'Obj.eq_1,
    Functor.whiskeringRight_obj_obj, Functor.comp_obj,
    Cat.opFunctorObj', Cat.of, Bundled.of,
    CategoryStruct.comp,
    Category.assoc]
  apply congrArg
  apply congrArg
  apply Cat.eqToHom_postCompOp_eq

theorem grothendieckContraIsoHomMapComp_fiber_components
    {X Y Z : GrothendieckContra F'}
    (f : gcHom F' X Y)
    (g : gcHom F' Y Z) :
    (grothendieckContraIsoHomMap (gcComp F' f g)).fiber =
    (grothendieckContraIsoHomMap f ≫ grothendieckContraIsoHomMap g).fiber := by
  simp only [grothendieckContraIsoHomMap, grothendieckContraIsoHomObj]
  rw [gcf_comp_fiber]
  exact grothendieckContraIsoHomMapComp_fiber_eq f g

set_option backward.isDefEq.respectTransparency false in
theorem grothendieckContraIsoHomMapComp
    {X Y Z : GrothendieckContra F'}
    (f : gcHom F' X Y)
    (g : gcHom F' Y Z) :
    grothendieckContraIsoHomMap (gcComp F' f g) =
    grothendieckContraIsoHomMap f ≫ grothendieckContraIsoHomMap g := by
  have h_base := grothendieckContraIsoHomMapComp_base_components f g
  have h_fiber := grothendieckContraIsoHomMapComp_fiber_components f g
  refine GrothendieckContra'.ext _ _ h_base ?_
  rw [h_fiber]
  simp

def grothendieckContraIsoHom :
    GrothendieckContraCat F' ⥤ GrothendieckContra' F' where
  obj := grothendieckContraIsoHomObj
  map := grothendieckContraIsoHomMap
  map_id := grothendieckContraIsoHomMapId
  map_comp := grothendieckContraIsoHomMapComp

def grothendieckContraIsoInvObj :
    GrothendieckContra' F' → GrothendieckContra F' :=
  fun X ↦ ⟨X.base, X.fiber⟩

def grothendieckContraIsoInvMap
    {X Y : GrothendieckContra' F'} :
    (X ⟶ Y) → gcHom F' (grothendieckContraIsoInvObj X) (grothendieckContraIsoInvObj Y) :=
  fun f ↦ ⟨f.base, f.fiber⟩

theorem grothendieckContraIsoInvMapId_base_components
    (X : GrothendieckContra' F') :
    (grothendieckContraIsoInvMap (𝟙 X)).base = (gcId F' (grothendieckContraIsoInvObj X)).base := by
  simp [grothendieckContraIsoInvMap, grothendieckContraIsoInvObj]
  rfl

theorem grothendieckContraIsoInvMapId_fiber_components
    (X : GrothendieckContra' F') :
    (grothendieckContraIsoInvMap (𝟙 X)).fiber =
    (gcId F' (grothendieckContraIsoInvObj X)).fiber := by
  cases X with | mk base fiber =>
  simp only
    [grothendieckContraIsoInvMap, grothendieckContraIsoInvObj,
     cat_id_fiber, gcf_id_fiber]
  exact (Cat.eqToHom_postCompOp_eq F' base _ _).symm

set_option backward.isDefEq.respectTransparency false in
theorem grothendieckContraIsoInvMapId
    (X : GrothendieckContra' F') :
    grothendieckContraIsoInvMap (𝟙 X) = gcId F' (grothendieckContraIsoInvObj X) := by
  have h_base := grothendieckContraIsoInvMapId_base_components X
  have h_fiber := grothendieckContraIsoInvMapId_fiber_components X
  refine gcExt F' _ _ h_base ?_
  rw [h_fiber]
  simp

theorem grothendieckContraIsoInvMapComp_base_components
    {X Y Z : GrothendieckContra' F'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (grothendieckContraIsoInvMap (f ≫ g)).base =
    (gcComp F' (grothendieckContraIsoInvMap f) (grothendieckContraIsoInvMap g)).base := by
  simp only [grothendieckContraIsoInvMap,
    grothendieckContraIsoInvObj]
  rfl

theorem grothendieckContraIsoInvMapComp_fiber_eq
    {X Y Z : GrothendieckContra' F'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.fiber ≫ (F'.map f.base).toFunctor.map g.fiber ≫ eqToHom (comp_fiber_cod_eq f g) =
    eqToHom (gcf_comp_fiber_precomp F' (grothendieckContraIsoInvMap f)
      (grothendieckContraIsoInvMap g)) ≫
    ((Cat.postCompOpFunctor'.obj F').map (grothendieckContraIsoInvMap f).base).toFunctor.map
      (grothendieckContraIsoInvMap g).fiber ≫
    (grothendieckContraIsoInvMap f).fiber := by
  simp +instances only [
    grothendieckContraIsoInvMap,
    grothendieckContraIsoInvObj,
    CategoryStruct.comp,
    Cat.postCompOpFunctor', Cat.opFunctorObj',
    Cat.of, Cat.str, Bundled.of,
    CategoryOp'.eq_1, CategoryOp'Inst,
    CategoryOpQuivInst.eq_1,
    Cat.opFunctor'.eq_1,
    Functor.op'.eq_1, functorOp'Obj.eq_1,
    Functor.whiskeringRight_obj_obj,
    Functor.comp_obj, Functor.comp_map,
    Functor.toCatHom_toFunctor, Category.assoc]
  apply congrArg
  apply congrArg
  apply Eq.symm
  apply Cat.eqToHom_postCompOp_eq

theorem grothendieckContraIsoInvMapComp_fiber_components
    {X Y Z : GrothendieckContra' F'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (grothendieckContraIsoInvMap (f ≫ g)).fiber =
    (gcComp F' (grothendieckContraIsoInvMap f) (grothendieckContraIsoInvMap g)).fiber := by
  simp only [grothendieckContraIsoInvMap, grothendieckContraIsoInvObj]
  unfold GrothendieckContraInst'
  unfold CategoryStruct.comp
  simp only []
  rw [comp_fiber]
  rw [gcf_comp_fiber]
  simp only []
  exact grothendieckContraIsoInvMapComp_fiber_eq f g

set_option backward.isDefEq.respectTransparency false in
theorem grothendieckContraIsoInvMapComp
    {X Y Z : GrothendieckContra' F'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    grothendieckContraIsoInvMap (f ≫ g) =
    gcComp F' (grothendieckContraIsoInvMap f) (grothendieckContraIsoInvMap g) := by
  have h_base := grothendieckContraIsoInvMapComp_base_components f g
  have h_fiber := grothendieckContraIsoInvMapComp_fiber_components f g
  refine gcExt F' _ _ h_base ?_
  rw [h_fiber]
  simp

def grothendieckContraIsoInv :
    GrothendieckContra' F' ⥤ GrothendieckContraCat F' where
  obj := grothendieckContraIsoInvObj
  map := grothendieckContraIsoInvMap
  map_id := grothendieckContraIsoInvMapId
  map_comp := grothendieckContraIsoInvMapComp

set_option backward.isDefEq.respectTransparency false in
theorem grothendieckContraIsoHomInvId :
    grothendieckContraIsoHom ⋙ grothendieckContraIsoInv = 𝟭 (GrothendieckContraCat F') := by
  fapply _root_.CategoryTheory.Functor.ext
  · intro X
    cases X
    rfl
  · intro X Y f
    cases f
    simp
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem grothendieckContraIsoInvHomId :
    grothendieckContraIsoInv ⋙ grothendieckContraIsoHom = 𝟭 (GrothendieckContra' F') := by
  fapply _root_.CategoryTheory.Functor.ext
  · intro X
    cases X
    rfl
  · intro X Y f
    cases f
    simp
    rfl

/--
Categorical isomorphism between `GrothendieckContra F0` (the mathlib-based
definition using opposite categories) and `GrothendieckContra' F0` (our direct
definition), for a specific functor `F0 : Cᵒᵖ' ⥤ Cat` at the base universe level.

Note: While the objects and morphisms have the same underlying data, the identity
and composition operations involve different `eqToHom` terms, so this requires
proving equations rather than just definitional equality.
-/
def grothendieckContraIso :
    GrothendieckContraCat F' ≅Cat GrothendieckContra' F' where
  hom := grothendieckContraIsoHom.toCatHom
  inv := grothendieckContraIsoInv.toCatHom
  hom_inv_id := Cat.Hom.ext grothendieckContraIsoHomInvId
  inv_hom_id := Cat.Hom.ext grothendieckContraIsoInvHomId

def grothendieckContraEquiv :
  GrothendieckContraCat F' ≌ GrothendieckContra' F' :=
    Cat.equivOfIso grothendieckContraIso

instance gcIsoHomFaithful : (grothendieckContraIsoHom (F' := F')).Faithful := by
  change (grothendieckContraEquiv (F' := F')).functor.Faithful
  infer_instance

instance gcIsoInvFaithful : (grothendieckContraIsoInv (F' := F')).Faithful := by
  change (grothendieckContraEquiv (F' := F')).inverse.Faithful
  infer_instance

def gcDomFuncToGcContra'.{u₃, v₃}
  (D : (Cᵒᵖ' ⥤ Cat.{v₂, u₂}) ⥤ Cat.{v₃, u₃})
  (G :
    (F : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) ->
    (Grothendieck.{u, v, u₂, v₂} (C := Cᵒᵖ') F) ⥤ (D.obj F)ᵒᵖ')
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    (GrothendieckContra'.{u, v, u₂, v₂} (C := C) (CInst := CInst) F' ⥤
     D.obj (Cat.postCompOpFunctor'.obj F')) :=
  grothendieckContraIsoInv (F' := F') ⋙ gcDomFuncToGcContra D G F'

def gcCodFuncToGcContra'.{u₃, v₃}
  (D : (Cᵒᵖ' ⥤ Cat.{v₂, u₂}) ⥤ Cat.{v₃, u₃})
  (G :
    (F : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) ->
    ((D.obj F)ᵒᵖ' ⥤ Grothendieck.{u, v, u₂, v₂} (C := Cᵒᵖ') F))
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    (D.obj (Cat.postCompOpFunctor'.obj F') ⥤
     GrothendieckContra'.{u, v, u₂, v₂} (C := C) (CInst := CInst) F') :=
  gcCodFuncToGcContra D G F' ⋙ grothendieckContraIsoHom (F' := F')

/--
Transfer a functor from mathlib's covariant Grothendieck construction where
Grothendieck categories appear in both domain and codomain, to `GrothendieckContra'`.
-/
def gcDomCodFuncToGcContra'
  (G :
    (F G : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) ->
    (Grothendieck.{u, v, u₂, v₂} (C := Cᵒᵖ') F ⥤
     Grothendieck.{u, v, u₂, v₂} (C := Cᵒᵖ') G))
  (F' G' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    (GrothendieckContra'.{u, v, u₂, v₂} (C := C) (CInst := CInst) F' ⥤
     GrothendieckContra'.{u, v, u₂, v₂} (C := C) (CInst := CInst) G') :=
  grothendieckContraIsoInv (F' := F') ⋙
    gcDomCodFuncToGcContra G F' G' ⋙
    grothendieckContraIsoHom (F' := G')

section Transfer

-- Universe levels for the Transfer section (independent of the outer v₂, u₂)
universe v₃ u₃ v₄ u₄ uₑ vₑ uₑ' vₑ'

def postcompGcIsoHom
    {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {H' : E'ᵒᵖ' ⥤ Cat.{v₄, u₄}} :
    (E ⥤ GrothendieckContraCat H') ⥤ (E ⥤ GrothendieckContra' H') :=
  (Functor.whiskeringRight _ _ _).obj (grothendieckContraIsoHom (F' := H'))

def precompGcIsoInv
    {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {G' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}} :
    (GrothendieckContraCat G' ⥤ E') ⥤ (GrothendieckContra' G' ⥤ E') :=
  (Functor.whiskeringLeft _ _ _).obj (grothendieckContraIsoInv (F' := G'))

def bicompGcIsoHomInv
    {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {G' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}} {H' : E'ᵒᵖ' ⥤ Cat.{v₄, u₄}} :
    (GrothendieckContraCat G' ⥤ GrothendieckContraCat H') ⥤
    (GrothendieckContra' G' ⥤ GrothendieckContra' H') :=
  postcompGcIsoHom
    (E := GrothendieckContraCat G')
    (E' := E')
    (H' := H')
  ⋙ precompGcIsoInv
    (E := E)
    (E' := GrothendieckContra' H')
    (G' := G')

def bicompGcIsoHomInv'
    {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {G' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}} {H' : E'ᵒᵖ' ⥤ Cat.{v₄, u₄}} :
    (GrothendieckContraCat G' ⥤ GrothendieckContraCat H') ⥤
    (GrothendieckContra' G' ⥤ GrothendieckContra' H') :=
  precompGcIsoInv
    (E := E)
    (E' := GrothendieckContraCat H')
    (G' := G')
  ⋙ postcompGcIsoHom
    (E := GrothendieckContra' G')
    (E' := E')
    (H' := H')

def bicompGcIsoEquiv
    {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {G' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}} {H' : E'ᵒᵖ' ⥤ Cat.{v₄, u₄}} :
    bicompGcIsoHomInv (E := E) (E' := E') (G' := G') (H' := H') =
    bicompGcIsoHomInv' (E := E) (E' := E') (G' := G') (H' := H') :=
  rfl

/--
Transfer a functor `F_cov : GrothendieckContra G' ⥤ GrothendieckContra H'`
(defined on the mathlib-derived construction) to a functor
`GrothendieckContra' G' ⥤ GrothendieckContra' H'` (on our direct construction)
by composing with the isomorphisms.

This is the primary mechanism for lifting constructions from mathlib's covariant
Grothendieck construction to our contravariant version.

Note: This version is polymorphic over both universe levels and base categories,
allowing transfer of functors between Grothendieck constructions at different
universe levels and potentially over different base categories E and E'.
-/
def transferFromCov {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {G' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}} {H' : E'ᵒᵖ' ⥤ Cat.{v₄, u₄}}
    (F_cov : GrothendieckContraCat G' ⥤ GrothendieckContraCat H') :
    GrothendieckContra' G' ⥤ GrothendieckContra' H' :=
  (bicompGcIsoHomInv (G' := G') (H' := H')).obj F_cov

/--
Helper function: constructs an object in `GrothendieckContra' H'` from the
result of applying `F_cov` to an object.
-/
def transferredObj {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {G' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}} {H' : E'ᵒᵖ' ⥤ Cat.{v₄, u₄}}
    (F_cov : GrothendieckContraCat G' ⥤ GrothendieckContraCat H')
    (X : GrothendieckContra' G') :
    GrothendieckContra' H' :=
  let Yobj := F_cov.obj (⟨X.base, X.fiber⟩)
  ⟨Yobj.base, Yobj.fiber⟩

/--
Helper function: constructs a morphism in `GrothendieckContra' H'` from the
result of applying `F_cov` to a morphism.
-/
def transferredMap {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {G' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}} {H' : E'ᵒᵖ' ⥤ Cat.{v₄, u₄}}
    (F_cov : GrothendieckContraCat G' ⥤ GrothendieckContraCat H')
    {X Y : GrothendieckContra' G'} (f : X ⟶ Y) :
    transferredObj F_cov X ⟶ transferredObj F_cov Y :=
  let fImg := F_cov.map (⟨f.base, f.fiber⟩ : gcHom G' ⟨X.base, X.fiber⟩ ⟨Y.base, Y.fiber⟩)
  ⟨fImg.base, fImg.fiber⟩

/--
The object function of a transferred functor equals the explicitly constructed
transferred object.
-/
@[simp]
theorem transferFromCov_obj {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {G' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}} {H' : E'ᵒᵖ' ⥤ Cat.{v₄, u₄}}
    (F_cov : GrothendieckContraCat G' ⥤ GrothendieckContraCat H')
    (X : GrothendieckContra' G') :
    (transferFromCov F_cov).obj X = transferredObj F_cov X :=
  rfl

/--
The morphism function of a transferred functor equals the explicitly constructed
transferred morphism.
-/
@[simp]
theorem transferFromCov_map {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {G' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}} {H' : E'ᵒᵖ' ⥤ Cat.{v₄, u₄}}
    (F_cov : GrothendieckContraCat G' ⥤ GrothendieckContraCat H')
    {X Y : GrothendieckContra' G'} (f : X ⟶ Y) :
    (transferFromCov F_cov).map f = transferredMap F_cov f :=
  rfl

/--
Helper function: constructs the identity morphism in `GrothendieckContra' H'` at the
image of an object under `F_cov`.
-/
def transferredId {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {G' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}} {H' : E'ᵒᵖ' ⥤ Cat.{v₄, u₄}}
    (F_cov : GrothendieckContraCat G' ⥤ GrothendieckContraCat H')
    (X : GrothendieckContra' G') :
    transferredObj F_cov X ⟶ transferredObj F_cov X :=
  let Yobj := F_cov.obj (⟨X.base, X.fiber⟩)
  ⟨@CategoryStruct.id E' _ Yobj.base,
   @eqToHom (H'.obj Yobj.base) _ _ _
     (@id_fiber_cod_eq E' _ H' ⟨Yobj.base, Yobj.fiber⟩).symm⟩

/--
Helper function: constructs the composition of two transferred morphisms in
`GrothendieckContra' H'`.
-/
def transferredComp {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {G' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}} {H' : E'ᵒᵖ' ⥤ Cat.{v₄, u₄}}
    (F_cov : GrothendieckContraCat G' ⥤ GrothendieckContraCat H')
    {X Y Z : GrothendieckContra' G'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    transferredObj F_cov X ⟶ transferredObj F_cov Z :=
  -- Map f and g through F_cov to get morphisms in mathlib's Grothendieck
  let fImg := F_cov.map (⟨f.base, f.fiber⟩ : gcHom G' ⟨X.base, X.fiber⟩ ⟨Y.base, Y.fiber⟩)
  let gImg := F_cov.map (⟨g.base, g.fiber⟩ : gcHom G' ⟨Y.base, Y.fiber⟩ ⟨Z.base, Z.fiber⟩)
  -- Convert to morphisms in our GrothendieckContra' H' for use with comp_fiber_cod_eq
  let fImgAsContra : transferredObj F_cov X ⟶ transferredObj F_cov Y :=
    ⟨fImg.base, fImg.fiber⟩
  let gImgAsContra : transferredObj F_cov Y ⟶ transferredObj F_cov Z :=
    ⟨gImg.base, gImg.fiber⟩
  -- Compose them in GrothendieckContra' H'
  ⟨fImg.base ≫ gImg.base,
   fImg.fiber ≫ (H'.map fImg.base).toFunctor.map gImg.fiber ≫
     eqToHom (comp_fiber_cod_eq fImgAsContra gImgAsContra)⟩

/--
The transferred functor maps identity morphisms to the explicitly constructed
identity morphism.
-/
@[simp]
theorem transferFromCov_map_id {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {G' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}} {H' : E'ᵒᵖ' ⥤ Cat.{v₄, u₄}}
    (F_cov : GrothendieckContraCat G' ⥤ GrothendieckContraCat H')
    (X : GrothendieckContra' G') :
    (transferFromCov F_cov).map (𝟙 X) = transferredId F_cov X := by
  exact CategoryTheory.Functor.map_id (transferFromCov F_cov) X

/--
The transferred functor maps composition to the explicitly constructed composition.
-/
theorem transferFromCov_map_comp {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {G' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}} {H' : E'ᵒᵖ' ⥤ Cat.{v₄, u₄}}
    (F_cov : GrothendieckContraCat G' ⥤ GrothendieckContraCat H')
    {X Y Z : GrothendieckContra' G'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (transferFromCov F_cov).map (f ≫ g) = transferredComp F_cov f g := by
  unfold transferFromCov bicompGcIsoHomInv postcompGcIsoHom precompGcIsoInv
  simp only [Functor.whiskeringRight_obj_obj, Functor.whiskeringLeft_obj_obj,
    Functor.comp_obj, Functor.comp_map]
  rw [grothendieckContraIsoInv.map_comp, Functor.map_comp, grothendieckContraIsoHom.map_comp]
  unfold transferredComp
  simp only [grothendieckContraIsoHom, grothendieckContraIsoInv,
    grothendieckContraIsoHomMap, grothendieckContraIsoHomObj,
    grothendieckContraIsoInvMap, grothendieckContraIsoInvObj]
  rfl

def transferFromCovMap
    {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {G' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}} {H' : E'ᵒᵖ' ⥤ Cat.{v₄, u₄}}
    {F_cov G_cov : GrothendieckContraCat G' ⥤ GrothendieckContraCat H'} :
    (F_cov ⟶ G_cov) ⟶ (transferFromCov F_cov ⟶ transferFromCov G_cov) :=
  (bicompGcIsoHomInv (G' := G') (H' := H')).map

end Transfer

end Isomorphism

section Transport

/--
If `F' : Cᵒᵖ' ⥤ Cat` is a contravariant functor and `t : c ⟶ x.base` is a
morphism in `C`, then `transport` maps each `x.base`-based element of
`GrothendieckContra' F'` to a `c`-based element.
-/
@[simps]
def transport (x : GrothendieckContra' F') {c : C} (t : c ⟶ x.base) :
    GrothendieckContra' F' :=
  ⟨c, (F'.map t).toFunctor.obj x.fiber⟩

/--
If `F' : Cᵒᵖ' ⥤ Cat` is a contravariant functor and `t : c ⟶ x.base` is a
morphism in `C`, then `transport` maps each `x.base`-based element `x` of
`GrothendieckContra' F'` to a `c`-based element `x.transport t`.

`fromTransport` is the morphism `x.transport t ⟶ x` induced by `t` and the
identity on fibers.
-/
@[simps!]
def fromTransport (x : GrothendieckContra' F') {c : C} (t : c ⟶ x.base) :
    x.transport t ⟶ x :=
  ⟨t, 𝟙 ((F'.map t).toFunctor.obj x.fiber)⟩

private lemma map_iso_comp_obj_eq {X Y : GrothendieckContra' F'}
    (e₁ : X.base ≅ Y.base) (z : F'.obj Y.base) :
    z = (F'.map e₁.hom ≫ F'.map e₁.inv).toFunctor.obj z := by
  have : F'.map e₁.hom ≫ F'.map e₁.inv = 𝟙 (F'.obj Y.base) := by
    rw [← F'.map_comp, ← F'.map_id]
    congr 1
    exact e₁.inv_hom_id
  simp [this]

@[simps!]
def isoMk_cov_fiber_equiv
    {X Y : GrothendieckContraCat F'} (e₁ : X.base ≅ Y.base)
    (e₂ : X.fiber ≅ (F'.map e₁.inv).toFunctor.obj Y.fiber) :
    ((Cat.postCompOpFunctor'.obj F').map e₁.hom).toFunctor.obj X.fiber ≅ Y.fiber :=
  ((Cat.postCompOpFunctor'.obj F').map e₁.hom).toFunctor.mapIso e₂ ≪≫
    eqToIso (Functor.congr_obj (congrArg Cat.Hom.toFunctor
      ((Cat.postCompOpFunctor'.obj F').mapIso e₁).inv_hom_id) Y.fiber)

-- Lemma: F'.map of a composition of isos
private lemma map_comp_iso {X Y : GrothendieckContraCat F'} (e₁ : X.base ≅ Y.base) :
    F'.map (e₁.inv ≫ e₁.hom) = F'.map e₁.inv ≫ F'.map e₁.hom := by
  rw [F'.map_comp]

private lemma map_inv_hom_eq_id {X Y : GrothendieckContraCat F'} (e₁ : X.base ≅ Y.base) :
    F'.map e₁.inv ≫ F'.map e₁.hom = F'.map (𝟙 Y.base) := by
  rw [← F'.map_comp, e₁.inv_hom_id]

set_option backward.isDefEq.respectTransparency false in
@[simps!]
def isoMk_cov {X Y : GrothendieckContraCat F'} (e₁ : X.base ≅ Y.base)
    (e₂ : X.fiber ≅ (F'.map e₁.inv).toFunctor.obj Y.fiber) :
    X ≅ Y :=
  Grothendieck.isoMk (X := X) (Y := Y)
    e₁
    (isoMk_cov_fiber_equiv e₁ e₂)

/--
Transfer a base isomorphism from `GrothendieckContra'` to `GrothendieckContra`.

In `GrothendieckContra'`, bases live in `C`, but in `GrothendieckContra` (via
`grothendieckContraIsoInv`), they live in `Cᵒᵖ'`. An isomorphism `e₁ : X.base ≅ Y.base`
in `C` becomes an isomorphism in `Cᵒᵖ'` with `.hom` and `.inv` swapped (and composition
reversed).
-/
def baseIsoToCov {X Y : GrothendieckContra' F'} (e₁ : X.base ≅ Y.base) :
    (grothendieckContraIsoInv.obj X).base ≅ (grothendieckContraIsoInv.obj Y).base :=
  opIso (C := C) e₁

/--
Transfer a fiber isomorphism from `GrothendieckContra'` to `GrothendieckContra`.

In `GrothendieckContra'`, fibers live in `F'.obj X.base`. In `GrothendieckContra` (via
`grothendieckContraIsoInv`), fibers live in `(Cat.postCompOpFunctor'.obj F').obj X.base`,
which is `(F'.obj X.base)ᵒᵖ'`. An isomorphism in `F'.obj X.base` becomes an isomorphism
in its opposite category with `.hom` and `.inv` swapped (and composition reversed).

Additionally, `(baseIsoToCov e₁).inv` is definitionally equal to `e₁.hom`, so the
functor application `(F'.map (baseIsoToCov e₁).inv).obj` equals `(F'.map e₁.hom).obj`.
-/
def fiberIsoToCov {X Y : GrothendieckContra' F'} (e₁ : X.base ≅ Y.base)
    (e₂ : X.fiber ≅ (F'.map e₁.hom).toFunctor.obj Y.fiber) :
    (grothendieckContraIsoInv.obj X).fiber ≅
    (F'.map (baseIsoToCov e₁).inv).toFunctor.obj (grothendieckContraIsoInv.obj Y).fiber :=
  -- grothendieckContraIsoInv maps to GrothendieckContra which uses Cat.postCompOpFunctor'.obj F'
  -- This means fibers are in (F'.obj _)ᵒᵖ' instead of F'.obj _
  -- We need to convert e₂ to an iso in the opposite category
  -- baseIsoToCov e₁ has .inv = e₁.hom by definition
  -- In (F'.obj X.base)ᵒᵖ', the iso e₂ becomes an iso with .hom and .inv swapped
  -- and composition is also reversed
  opIso (C := F'.obj X.base) e₂

/--
If we have an isomorphism in `GrothendieckContra` between `grothendieckContraIsoInv.obj X`
and `grothendieckContraIsoInv.obj Y`, we can transfer it to an isomorphism `X ≅ Y`
in `GrothendieckContra'`.
-/
def isoFromCov {X Y : GrothendieckContra' F'}
    (iso_cov : grothendieckContraIsoInv.obj X ≅ grothendieckContraIsoInv.obj Y) :
    X ≅ Y :=
  grothendieckContraIsoHom.mapIso iso_cov

/--
Construct an isomorphism in a contravariant Grothendieck construction from
isomorphisms in its base and fiber.

This is implemented by transferring mathlib's `Grothendieck.isoMk` through
the isomorphism `grothendieckContraIso`.
-/
@[simps!]
def isoMk {X Y : GrothendieckContra' F'} (e₁ : X.base ≅ Y.base)
    (e₂ : X.fiber ≅ (F'.map e₁.hom).toFunctor.obj Y.fiber) :
    X ≅ Y :=
  isoFromCov (isoMk_cov (baseIsoToCov e₁) (fiberIsoToCov e₁ e₂))

/--
Create an isomorphism between a transported element and the original.
-/
@[simps!]
def transportIso (x : GrothendieckContra' F') {c : C} (α : x.base ≅ c) :
    x.transport α.inv ≅ x :=
  isoMk α.symm (Iso.refl _)

end Transport

section

variable (F')

/--
The forgetful functor from `GrothendieckContra' F'` to `C`.
-/
@[simps!]
def forget : GrothendieckContra' F' ⥤ C :=
  precompGcIsoInv (G' := F').obj
  <| Functor.op'
  <| Grothendieck.forget (C := Cᵒᵖ') (Cat.postCompOpFunctor'.obj F')

end

section Functoriality

variable {F' G' H' : Cᵒᵖ' ⥤ Cat}

@[simps!]
def map_cov (α : F' ⟶ G') :
  GrothendieckContraCat F' ⥤ GrothendieckContraCat G' :=
    Functor.op' (Grothendieck.map (Cat.postCompOpFunctor'.map α))

theorem map_cov_obj (α : F' ⟶ G') (X : GrothendieckContra F') :
    (map_cov α).obj X = ⟨X.base, (α.app X.base).toFunctor.obj X.fiber⟩ := by
  unfold map_cov
  simp only [Functor.op', functorOp'Obj]
  rw [Grothendieck.map_obj]
  simp only [Cat.postCompOpFunctor']
  rfl

theorem map_cov_map (α : F' ⟶ G') {X Y : GrothendieckContra F'} (f : gcHom F' X Y) :
    (map_cov α).map f = ⟨f.base,
      (eqToHom (Eq.symm ((Cat.postCompOpFunctor'.map α).naturality f.base))).toNatTrans.app
        Y.fiber ≫
      (Functor.op' (α.app X.base).toFunctor).map f.fiber⟩ := by
  unfold map_cov
  simp only [Functor.op', functorOp'Obj]
  rw [Grothendieck.map_map]
  simp only [Cat.postCompOpFunctor']
  rfl

/--
A natural transformation `α : F' ⟶ G'` induces a functor between the corresponding
contravariant Grothendieck constructions.

This is defined by transferring mathlib's `Grothendieck.map` through our isomorphism.
-/
@[simps!]
def map (α : F' ⟶ G') : GrothendieckContra' F' ⥤ GrothendieckContra' G' :=
  transferFromCov (map_cov α)

@[simp]
theorem map_obj (α : F' ⟶ G') (X : GrothendieckContra' F') :
    (map α).obj X = ⟨X.base, (α.app X.base).toFunctor.obj X.fiber⟩ := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem map_map (α : F' ⟶ G') {X Y : GrothendieckContra' F'} (f : X ⟶ Y) :
    (map α).map f = ⟨f.base, (α.app X.base).toFunctor.map f.fiber ≫
      (eqToHom (α.naturality f.base)).toNatTrans.app Y.fiber⟩ := by
  unfold map
  simp only [transferFromCov_map, transferredMap]
  rw [map_cov_map]
  simp only [transferFromCov_obj, CategoryOp'.eq_1,
    Cat.postCompOpFunctor'.eq_1, Cat.opFunctor'.eq_1,
    Functor.op'.eq_1, functorOp'Obj.eq_1, Functor.whiskeringRight_obj_obj,
    GrothendieckContraCat, GrothendieckContraCatOp, GrothendieckCat, map_cov_obj_base,
    Functor.comp_obj, Functor.comp_map, Functor.toCatHom_toFunctor, map_cov_obj_fiber,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app, Cat.Hom.comp_toFunctor,
    Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
  congr 1
  rw [op_comp_eq]
  congr 1
  apply Cat.eqToHom_op'_eq

theorem functor_comp_forget {α : F' ⟶ G'} :
    GrothendieckContra'.map α ⋙ GrothendieckContra'.forget G' =
    GrothendieckContra'.forget F' :=
  rfl

theorem catHom_comp_forget {α : F' ⟶ G'} :
    (GrothendieckContra'.map α).toCatHom ≫ (GrothendieckContra'.forget G').toCatHom =
    (GrothendieckContra'.forget F').toCatHom :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem map_id_eq : map (𝟙 F') = 𝟭 (GrothendieckContra' F') := by
  fapply _root_.CategoryTheory.Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp [map_map]
    rfl

def mapIdIso : map (𝟙 F') ≅ 𝟭 (GrothendieckContra' F') :=
  eqToIso map_id_eq

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem map_comp_eq (α : F' ⟶ G') (β : G' ⟶ H') :
    map (α ≫ β) = map α ⋙ map β := by
  fapply _root_.CategoryTheory.Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp only [map_map, NatTrans.comp_app, Functor.comp_obj, Functor.comp_map,
      eqToHom_refl, Functor.comp_map, Functor.map_comp, Category.comp_id, Category.id_comp]
    unfold Cat.Hom.toFunctor
    fapply GrothendieckContra'.ext
    · rfl
    · simp

def mapCompIso (α : F' ⟶ G') (β : G' ⟶ H') :
    map (α ≫ β) ≅ map α ⋙ map β :=
  eqToIso (map_comp_eq α β)

section UniverseScaling

variable {F' G' : Cᵒᵖ' ⥤ Cat.{v, u}}

def compAsSmallFunctorEquivalenceFunctor_cov :
    GrothendieckContraCat (F' ⋙ Cat.asSmallFunctor.{w}) ⥤
    GrothendieckContraCat F' :=
  Functor.op'
    (Grothendieck.compAsSmallFunctorEquivalence
      (Cat.postCompOpFunctor'.obj F')).functor

theorem compAsSmallFunctorEquivalenceFunctor_cov_obj
    (X : GrothendieckContra (F' ⋙ Cat.asSmallFunctor.{w})) :
    (compAsSmallFunctorEquivalenceFunctor_cov (F' := F')).obj X =
      ⟨X.base, AsSmall.down.obj X.fiber⟩ := by
  unfold compAsSmallFunctorEquivalenceFunctor_cov
  simp [Functor.op', Grothendieck.compAsSmallFunctorEquivalenceFunctor]

theorem compAsSmallFunctorEquivalenceFunctor_cov_map
    {X Y : GrothendieckContra (F' ⋙ Cat.asSmallFunctor.{w})}
    (f : gcHom (F' ⋙ Cat.asSmallFunctor.{w}) X Y) :
    (compAsSmallFunctorEquivalenceFunctor_cov (F' := F')).map f =
      ⟨f.base, AsSmall.down.map f.fiber⟩ := by
  unfold compAsSmallFunctorEquivalenceFunctor_cov
  simp [Functor.op', Grothendieck.compAsSmallFunctorEquivalenceFunctor]

def compAsSmallFunctorEquivalenceFunctor :
    GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}) ⥤
    GrothendieckContra' F' :=
  transferFromCov compAsSmallFunctorEquivalenceFunctor_cov

theorem compAsSmallFunctorEquivalenceFunctor_obj
    (X : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w})) :
    (compAsSmallFunctorEquivalenceFunctor (F' := F')).obj X =
      ⟨X.base, AsSmall.down.obj X.fiber⟩ := by
  unfold compAsSmallFunctorEquivalenceFunctor
  simp only [transferFromCov_obj, transferredObj]
  rw [compAsSmallFunctorEquivalenceFunctor_cov_obj]
  rfl

theorem compAsSmallFunctorEquivalenceFunctor_map
    {X Y : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w})} (f : X ⟶ Y) :
    (compAsSmallFunctorEquivalenceFunctor (F' := F')).map f =
      ⟨f.base, AsSmall.down.map f.fiber⟩ := by
  unfold compAsSmallFunctorEquivalenceFunctor
  simp only [transferFromCov_map, transferredMap]
  rw [compAsSmallFunctorEquivalenceFunctor_cov_map]
  rfl

def compAsSmallFunctorEquivalenceInverse_cov :
    GrothendieckContraCat F' ⥤ GrothendieckContraCat (F' ⋙ Cat.asSmallFunctor.{w}) :=
  Functor.op'
    (Grothendieck.compAsSmallFunctorEquivalence
      (Cat.postCompOpFunctor'.obj F')).inverse

theorem compAsSmallFunctorEquivalenceInverse_cov_obj
    (X : GrothendieckContra F') :
    (compAsSmallFunctorEquivalenceInverse_cov (F' := F')).obj X =
      ⟨X.base, AsSmall.up.obj X.fiber⟩ := rfl

theorem compAsSmallFunctorEquivalenceInverse_cov_map
    {X Y : GrothendieckContra F'} (f : gcHom F' X Y) :
    (compAsSmallFunctorEquivalenceInverse_cov (F' := F')).map f =
      ⟨f.base, AsSmall.up.map f.fiber⟩ := rfl

def compAsSmallFunctorEquivalenceInverse :
    GrothendieckContra' F' ⥤ GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}) :=
  transferFromCov compAsSmallFunctorEquivalenceInverse_cov

@[simp]
theorem compAsSmallFunctorEquivalenceInverse_obj_fiber (X : GrothendieckContra' F') :
    ((compAsSmallFunctorEquivalenceInverse (F' := F')).obj X).fiber =
      AsSmall.up.obj X.fiber := rfl

@[simp]
theorem compAsSmallFunctorEquivalenceInverse_obj (X : GrothendieckContra' F') :
    (compAsSmallFunctorEquivalenceInverse (F' := F')).obj X =
      ⟨X.base, AsSmall.up.obj X.fiber⟩ := by
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem compAsSmallFunctorEquivalenceInverse_map
    {X Y : GrothendieckContra' F'} (f : X ⟶ Y) :
    (compAsSmallFunctorEquivalenceInverse (F' := F')).map f =
    ⟨f.base,
     eqToHom (compAsSmallFunctorEquivalenceInverse_obj_fiber X) ≫
     AsSmall.up.map f.fiber⟩ := by
  simp only [CategoryOp'.eq_1, Functor.comp_obj,
    Cat.asSmallFunctor_obj, Cat.of_α,
    compAsSmallFunctorEquivalenceInverse_obj_fiber,
    Functor.comp_map, Cat.asSmallFunctor_map,
    Functor.toCatHom_toFunctor, AsSmall.down_obj,
    AsSmall.up_obj_down, eqToHom_refl,
    Category.id_comp]
  unfold compAsSmallFunctorEquivalenceInverse
  simp only [transferFromCov_map, transferredMap,
    compAsSmallFunctorEquivalenceInverse_cov_map]

set_option backward.isDefEq.respectTransparency false in
def compAsSmallFunctorEquivalence :
    GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}) ≌
    GrothendieckContra' F' where
  functor := compAsSmallFunctorEquivalenceFunctor
  inverse := compAsSmallFunctorEquivalenceInverse
  unitIso := Iso.refl _
  counitIso := Iso.refl _

set_option backward.isDefEq.respectTransparency false in
def mapWhiskerRightAsSmallFunctor (α : F' ⟶ G') :
    map (Functor.whiskerRight α Cat.asSmallFunctor.{w}) ≅
    compAsSmallFunctorEquivalenceFunctor ⋙ map α ⋙
      compAsSmallFunctorEquivalenceInverse (F' := G') := by
  unfold map compAsSmallFunctorEquivalenceFunctor compAsSmallFunctorEquivalenceInverse
  calc grothendieckContraIsoInv ⋙ map_cov (Functor.whiskerRight α Cat.asSmallFunctor) ⋙
        grothendieckContraIsoHom
      ≅ grothendieckContraIsoInv ⋙
          (compAsSmallFunctorEquivalenceFunctor_cov ⋙ map_cov α ⋙
            compAsSmallFunctorEquivalenceInverse_cov) ⋙
          grothendieckContraIsoHom := by
        apply Functor.isoWhiskerLeft
        apply Functor.isoWhiskerRight
        unfold map_cov compAsSmallFunctorEquivalenceFunctor_cov
          compAsSmallFunctorEquivalenceInverse_cov
        have mathlib_iso := Grothendieck.mapWhiskerRightAsSmallFunctor
          (Cat.postCompOpFunctor'.map α)
        rw [← Functor.op'_comp, ← Functor.op'_comp]
        exact GebLean.Functor.op'_mapIso mathlib_iso
    _ ≅ grothendieckContraIsoInv ⋙
          compAsSmallFunctorEquivalenceFunctor_cov ⋙
          grothendieckContraIsoHom ⋙
          grothendieckContraIsoInv ⋙
          map_cov α ⋙
          grothendieckContraIsoHom ⋙
          grothendieckContraIsoInv ⋙
          compAsSmallFunctorEquivalenceInverse_cov ⋙
          grothendieckContraIsoHom := by
        refine Iso.refl _

end UniverseScaling

end Functoriality

set_option backward.isDefEq.respectTransparency false in
/--
The contravariant Grothendieck construction as a functor from the functor
category `(Cᵒᵖ' ⥤ Cat)` to the over category over the base category.
-/
def functor {E : Type u} [Category.{v} E] :
    (Eᵒᵖ' ⥤ Cat.{v, u}) ⥤ Over (T := Cat.{v, u}) (Cat.of E) where
  obj F' := Over.mk (X := Cat.of E) (Y := Cat.of (GrothendieckContra' F'))
                    (GrothendieckContra'.forget F').toCatHom
  map {_ _} α := Over.homMk (X := Cat.of E) (GrothendieckContra'.map α).toCatHom
                            GrothendieckContra'.catHom_comp_forget
  map_id F' := by
    ext
    exact GrothendieckContra'.map_id_eq (F' := F')
  map_comp α β := by
    simp [GrothendieckContra'.map_comp_eq α β]
    rfl

section TypeToCategory

variable {F' : Cᵒᵖ' ⥤ Type w}

/--
A morphism in a discrete category implies equality of the underlying elements.
-/
lemma discrete_morphism_eq {X : Type w} {a b : Discrete X} (f : a ⟶ b) : a.as = b.as := by
  cases a using Discrete.recOn
  cases b using Discrete.recOn
  -- Morphisms in Discrete X are eqToHom of equalities
  -- f.down : PLift (a = b)
  exact f.down.down

/--
For a morphism in the Grothendieck construction over discrete categories,
the fiber component witnesses that `F'.map f.base` maps `Y.fiber.as` to `X.fiber.as`.
-/
lemma grothendieck_discrete_fiber_eq (F' : Cᵒᵖ' ⥤ Type w)
    {X Y : GrothendieckContra' (F' ⋙ typeToCat)} (f : X ⟶ Y) :
    F'.map f.base Y.fiber.as = X.fiber.as := by
  -- f.fiber : (F' ⋙ typeToCat).map f.base |>.obj X.fiber ⟶ Y.fiber in the discrete category
  -- (F' ⋙ typeToCat).map f.base is Discrete.functor (Discrete.mk ∘ F'.map f.base)
  -- So (F' ⋙ typeToCat).map f.base |>.obj X.fiber = Discrete.mk ((F'.map f.base) X.fiber.as)
  have h := discrete_morphism_eq f.fiber
  dsimp [typeToCat, Functor.comp] at h
  -- h : ((F'.map f.base) X.fiber.as) = Y.fiber.as
  exact h.symm

/--
The functor from the contravariant Grothendieck construction to the
contravariant category of elements.
-/
def grothendieckTypeToCatFunctor :
    GrothendieckContra' (F' ⋙ typeToCat) ⥤ F'.ElementsContra' where
  obj X := ⟨X.base, X.fiber.as⟩
  map {X Y} f := ⟨f.base, grothendieck_discrete_fiber_eq F' f⟩

/--
Construct a morphism in a discrete category from an equality of the underlying elements.
-/
def discrete_eqToHom_of_eq {X : Type w} {a b : X} (h : a = b) :
    Discrete.mk a ⟶ Discrete.mk b :=
  Discrete.eqToHom (by rw [h])


set_option backward.isDefEq.respectTransparency false in
/--
The inverse functor from the contravariant category of elements to the
contravariant Grothendieck construction.
-/
def grothendieckTypeToCatInverse :
    F'.ElementsContra' ⥤ GrothendieckContra' (F' ⋙ typeToCat) where
  obj p := ⟨p.fst, Discrete.mk p.snd⟩
  map {p q} f := by
    refine ⟨f.val, ?_⟩
    dsimp [typeToCat, Functor.comp]
    -- Need: { as := p.snd } ⟶ { as := F'.map (↑f) q.snd }
    -- f.property : F'.map f.val q.snd = p.snd
    -- So p.snd = F'.map f.val q.snd
    exact discrete_eqToHom_of_eq f.property.symm
  map_comp {X Y Z} f g := by
    refine ext _ _ ?_ ?_
    · rfl
    · dsimp [comp, CategoryStruct.comp, typeToCat, Functor.comp]
      simp only [Category.comp_id]
      apply Subsingleton.elim

set_option backward.isDefEq.respectTransparency false in
/--
Equivalence between the contravariant Grothendieck construction on `F' ⋙ typeToCat`
and the contravariant category of elements of `F'`.

This shows that when target categories are discrete (sets viewed as categories with only
identity morphisms), the Grothendieck construction reduces to the category of elements,
since morphism existence becomes just an equality condition.
-/
def grothendieckTypeToCat :
    GrothendieckContra' (F' ⋙ typeToCat) ≌ F'.ElementsContra' where
  functor := grothendieckTypeToCatFunctor
  inverse := grothendieckTypeToCatInverse
  unitIso := NatIso.ofComponents
    (fun X ↦ Iso.refl _)
    (fun f ↦ by
      refine ext _ _ ?_ ?_
      · simp only [CategoryOp'.eq_1,
          Functor.id_obj, Functor.comp_obj,
          Iso.refl_hom, Functor.comp_map,
          typeToCat_map,
          Functor.toCatHom_toFunctor,
          Discrete.functor_obj_eq_as,
          Function.comp_apply, Functor.id_map,
          Category.comp_id, Category.id_comp,
          grothendieckTypeToCatFunctor,
          grothendieckTypeToCatInverse]
      · simp only [CategoryOp'.eq_1,
          Functor.id_obj, Functor.comp_obj,
          Iso.refl_hom, Functor.comp_map,
          typeToCat_map,
          Functor.toCatHom_toFunctor,
          Discrete.functor_obj_eq_as,
          Function.comp_apply, Functor.id_map]
        apply @Subsingleton.elim _ (Discrete.instSubsingletonDiscreteHom _ _))
  counitIso := NatIso.ofComponents
    (fun p ↦ Iso.refl _)
    (fun f ↦ by
      ext
      simp
      rfl)
  functor_unitIso_comp := by
    intro X
    simp

end TypeToCategory

section Pre

variable {D : Type u₂} [Category.{v₂} D]
variable (F' : Cᵒᵖ' ⥤ Cat.{w, u₁})

def pre_cov (G : D ⥤ C) :
    GrothendieckContraCat (functorOp'Obj G ⋙ F') ⥤ GrothendieckContraCat F' :=
  Functor.op' (Grothendieck.pre (Cat.postCompOpFunctor'.obj F') (functorOp'Obj G))

theorem pre_cov_obj (G : D ⥤ C)
    (X : GrothendieckContra (functorOp'Obj G ⋙ F')) :
    (pre_cov F' G).obj X = ⟨G.obj X.base, X.fiber⟩ := by
  unfold pre_cov
  simp [Functor.op', Grothendieck.pre]

theorem pre_cov_map (G : D ⥤ C)
    {X Y : GrothendieckContra (functorOp'Obj G ⋙ F')}
    (f : gcHom (functorOp'Obj G ⋙ F') X Y) :
    (pre_cov F' G).map f = ⟨G.map f.base, f.fiber⟩ := by
  unfold pre_cov
  simp [Functor.op', Grothendieck.pre]

@[simp]
theorem pre_cov_id : pre_cov F' (𝟭 C) = 𝟭 (GrothendieckContraCat F') :=
  rfl

/--
A functor `G : D ⥤ C` induces a functor between the contravariant Grothendieck
constructions.

Applying a functor `G : D ⥤ C` to the base of the Grothendieck construction
induces a functor `GrothendieckContra' (functorOp'Obj G ⋙ F') ⥤ GrothendieckContra' F'`.
-/
@[simps!]
def pre (G : D ⥤ C) : GrothendieckContra' (functorOp'Obj G ⋙ F') ⥤
    GrothendieckContra' F' :=
  transferFromCov (pre_cov F' G)

@[simp]
theorem pre_obj (G : D ⥤ C) (X : GrothendieckContra' (functorOp'Obj G ⋙ F')) :
    (pre F' G).obj X = ⟨G.obj X.base, X.fiber⟩ := by
  unfold pre
  simp only [transferFromCov_obj, transferredObj]
  rw [pre_cov_obj]

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem pre_map (G : D ⥤ C) {X Y : GrothendieckContra' (functorOp'Obj G ⋙ F')} (f : X ⟶ Y) :
    (pre F' G).map f = ⟨G.map f.base, f.fiber⟩ := by
  unfold pre
  simp only [transferFromCov_map, transferredMap]
  rw [pre_cov_map]

/--
The functor `pre` applied to the identity functor is the identity.
-/
@[simp]
theorem pre_id : pre F' (𝟭 C) = 𝟭 (GrothendieckContra' F') :=
  rfl

def preNatIso_cov {G H : D ⥤ C} (α : G ≅ H) :
    pre_cov F' G ≅ map_cov (Functor.whiskerRight (functorOp'.map α.inv) F') ⋙
      pre_cov F' H := by
  unfold pre_cov map_cov
  simp only [Functor.op']
  have covar_iso := @Grothendieck.preNatIso _ _ _ _ (Cat.postCompOpFunctor'.obj F')
    (functorOp'Obj G) (functorOp'Obj H) (functorOp'.mapIso <| isoToOp' α)
  convert Functor.op'_mapIso covar_iso using 2

/--
Natural isomorphism between `pre` applied to naturally isomorphic functors.

An isomorphism between functors `α : G ≅ H` induces an isomorphism between
`pre G` and `pre H`, up to composition with the `map` induced by whiskering.
-/
def preNatIso {G H : D ⥤ C} (α : G ≅ H) :
    pre F' G ≅ map (Functor.whiskerRight (functorOp'.map α.inv) F') ⋙
      (pre F' H) := by
  unfold pre map
  calc grothendieckContraIsoInv ⋙ pre_cov F' G ⋙ grothendieckContraIsoHom
      ≅ grothendieckContraIsoInv ⋙
          (map_cov (Functor.whiskerRight (functorOp'.map α.inv) F') ⋙ pre_cov F' H) ⋙
          grothendieckContraIsoHom := by
        apply Functor.isoWhiskerLeft
        apply Functor.isoWhiskerRight
        exact preNatIso_cov F' α
    _ ≅ grothendieckContraIsoInv ⋙
          map_cov (Functor.whiskerRight (functorOp'.map α.inv) F') ⋙
          grothendieckContraIsoHom ⋙
          grothendieckContraIsoInv ⋙
          pre_cov F' H ⋙
          grothendieckContraIsoHom := by
        refine Iso.refl _
    _ ≅ grothendieckContraIsoInv ⋙
          map_cov (Functor.whiskerRight (functorOp'.map α.inv) F') ⋙
          grothendieckContraIsoHom ⋙
          (grothendieckContraIsoInv ⋙ pre_cov F' H ⋙ grothendieckContraIsoHom) := by
        refine Iso.refl _

/--
The weak inverse to `pre` when `G` is an equivalence.
-/
def preInv (G : D ≌ C) :
    GrothendieckContra' F' ⥤
    GrothendieckContra' (functorOp'Obj G.functor ⋙ F') :=
  map (Functor.whiskerRight (functorOp'.map G.counitIso.hom) F') ⋙
    pre (functorOp'Obj G.functor ⋙ F') G.inverse

end Pre

section PreWithMorphisms

variable {D : Type u₂} [Category.{v₂} D]
variable {F' : Cᵒᵖ' ⥤ Cat.{w, u₁}}

/--
Composition of `pre` with `map` commutes with whiskering.
-/
lemma pre_comp_map (G : D ⥤ C) {H : Cᵒᵖ' ⥤ Cat} (α : F' ⟶ H) :
    pre F' G ⋙ map α = map (Functor.whiskerLeft (functorOp'Obj G) α) ⋙ pre H G := by
  rfl

/--
Associativity version of `pre_comp_map`.
-/
lemma pre_comp_map_assoc (G : D ⥤ C) {H : Cᵒᵖ' ⥤ Cat} (α : F' ⟶ H) {A : Type*}
    [Category A] (K : GrothendieckContra' H ⥤ A) :
    pre F' G ⋙ map α ⋙ K = map (Functor.whiskerLeft (functorOp'Obj G) α) ⋙
      pre H G ⋙ K := by
  rw [← Functor.assoc, pre_comp_map, Functor.assoc]

end PreWithMorphisms

section PreComp

variable {D : Type u₂} [Category.{v₂} D]
variable (F' : Cᵒᵖ' ⥤ Cat.{w, u₁})

/--
Composition of `pre` functors.

Precomposing with `H ⋙ G` is the same as precomposing with `H` then with `G`.
-/
@[simp]
lemma pre_comp {E : Type*} [Category E] (G : D ⥤ C) (H : E ⥤ D) :
    pre F' (H ⋙ G) = pre (functorOp'Obj G ⋙ F') H ⋙ pre F' G :=
  rfl

/--
Unit isomorphism for `pre` applied to an equivalence.

The functor induced via `pre` by `G.functor ⋙ G.inverse` is naturally isomorphic
to the functor induced via `map` by a whiskered version of `G`'s unit (note:
`unit`, not `unitInv` as in the covariant case, due to the direction reversal
from `functorOp'`).
-/
protected def preUnitIso (G : D ≌ C) :
    map (Functor.whiskerRight (functorOp'.map G.unit) (functorOp'Obj G.functor ⋙ F')) ≅
    pre (functorOp'Obj G.functor ⋙ F') (G.functor ⋙ G.inverse) :=
  preNatIso (functorOp'Obj G.functor ⋙ F') G.unitIso.symm |>.symm

/--
When `G` is an equivalence, `pre G` is also an equivalence.
-/
def preEquivalence (G : D ≌ C) :
    GrothendieckContra' (functorOp'Obj G.functor ⋙ F') ≌
    GrothendieckContra' F' := by
  have mathlib_equiv :=
    Grothendieck.preEquivalence
      (Cat.postCompOpFunctor'.obj F')
      (Equivalence.op' G)
  -- Apply Equivalence.op' to get the equivalence on opposite categories
  have contra_equiv_op := Equivalence.op' mathlib_equiv
  -- Show that functorOp'Obj G.functor and (Equivalence.op' G).functor are naturally isomorphic
  have functor_iso : functorOp'Obj G.functor ≅ (Equivalence.op' G).functor := by
    -- Both equal op'ToOp ⋙ G.op.functor ⋙ opToOp'
    -- functorOp'Obj G.functor = op'ToOp ⋙ G.op ⋙ opToOp' (by functorOp'Obj_eq_comp)
    -- (Equivalence.op' G).functor = opEquivOp'.symm.functor ⋙ G.op.functor ⋙ opEquivOp'.functor
    --                             = op'ToOp ⋙ G.op.functor ⋙ opToOp'
    -- So they should be definitionally equal
    rfl
  -- First, get the equivalence for (Equivalence.op' G).functor
  have equiv1 : GrothendieckContra' ((Equivalence.op' G).functor ⋙ F') ≌ GrothendieckContra' F' :=
    grothendieckContraEquiv.symm.trans (contra_equiv_op.trans grothendieckContraEquiv)
  -- Since functor_iso is rfl, the functors are definitionally equal, so equiv1 is what we need
  exact equiv1

variable {F'} in
/--
Conjugation of `map` by `preEquivalence`.

Left-whiskering `α` by `functorOp'Obj G.functor` and then taking the Grothendieck
construction is, up to isomorphism, the same as taking the Grothendieck construction
of `α` and using the equivalences from `preEquivalence` to match the expected type.
-/
def mapWhiskerLeftIsoConjPreMap {G' : Cᵒᵖ' ⥤ Cat.{w, u₁}} (G : D ≌ C) (α : F' ⟶ G') :
    map (Functor.whiskerLeft (functorOp'Obj G.functor) α) ≅
      (preEquivalence F' G).functor ⋙ map α ⋙ (preEquivalence G' G).inverse := by
  unfold map
  -- Define helper variables for preEquivalence at F' and G'
  let preF := preEquivalence F' G
  let preG := preEquivalence G' G
  calc grothendieckContraIsoInv ⋙
        map_cov (Functor.whiskerLeft (functorOp'Obj G.functor) α) ⋙
        grothendieckContraIsoHom
      ≅ grothendieckContraIsoInv ⋙
          (grothendieckContraIsoHom ⋙ preF.functor ⋙ grothendieckContraIsoInv ⋙
            map_cov α ⋙
            grothendieckContraIsoHom ⋙ preG.inverse ⋙ grothendieckContraIsoInv) ⋙
          grothendieckContraIsoHom := by
        apply Functor.isoWhiskerLeft
        apply Functor.isoWhiskerRight
        -- Strategy: relate our isomorphism to mathlib's through composition
        unfold map_cov
        -- Note: functorOp'Obj G.functor = (Equivalence.op' G).functor by rfl
        -- Get mathlib's isomorphism
        have mathlib_iso :=
          @Grothendieck.mapWhiskerLeftIsoConjPreMap
            Cᵒᵖ' _ Dᵒᵖ' _
            (Cat.postCompOpFunctor'.obj F')
            (Cat.postCompOpFunctor'.obj G')
            (Equivalence.op' G)
            (Cat.postCompOpFunctor'.map α)
        -- Apply Functor.op'_mapIso to transport through opposite
        have iso_transported := GebLean.Functor.op'_mapIso mathlib_iso
        -- Use op'_comp to break up the RHS into a composition of opposites
        rw [Functor.op'_comp, Functor.op'_comp] at iso_transported
        -- Now iso_transported has:
        -- Functor.op' (Grothendieck.map ...) ≅
        --   Functor.op' (Grothendieck.preEquivalence...).functor ⋙
        --   Functor.op' (Grothendieck.map ...) ⋙
        --   Functor.op' (Grothendieck.preEquivalence...).inverse

        -- iso_transported now has Functor.op' of mathlib's preEquivalence.
        -- We need grothendieckContraIsoHom ⋙ preF.functor ⋙ grothendieckContraIsoInv,
        -- which by definition of preF equals the conjugation of Equivalence.op' mathlib_equiv

        -- The goal after Functor.isoWhiskerLeft/Right should match
        -- iso_transported after accounting for the conjugation with grothendieckContraIso
        simp only [preF, preG]
        unfold preEquivalence
        -- Now both sides should be expressed in terms of the underlying equivalences
        exact iso_transported
    _ ≅ grothendieckContraIsoInv ⋙
          grothendieckContraIsoHom ⋙
          preF.functor ⋙
          grothendieckContraIsoInv ⋙
          map_cov α ⋙
          grothendieckContraIsoHom ⋙
          preG.inverse ⋙
          grothendieckContraIsoInv ⋙
          grothendieckContraIsoHom := by
        refine Iso.refl _

end PreComp


section FunctorFrom

variable {F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}}
variable {T : Type u₁} [Category.{v₁} T]

@[reducible]
private def CI : Category.{max v v₂, max u u₂} (GrothendieckContra F') :=
  GrothendieckContraCatInst.{u, v, u₂, v₂} (F' := F')

def gr_ι_flip (c : C) (F : C ⥤ Cat) : ↑(F.obj c) ⥤ Grothendieck F :=
  (Grothendieck.ι (C := C)) F c

/--
The fiber inclusion functor from `F'.obj c` viewed as a
functor to `GrothendieckContra F'`, which is the expression
of `GrothendieckContra' F'` as a covariant Grothendieck construction.
-/
abbrev ι_cov (c : C) : F'.obj c ⥤ GrothendieckContraCat F' :=
  gcCodFuncToGcContra
    (C := C)
    (Cat.postCompOpFunctor' ⋙ (CategoryTheory.evaluation Cᵒᵖ' Cat).obj c)
    (gr_ι_flip (C := Cᵒᵖ') c)
    F'

/--
The fiber inclusion functor from `F'.obj c` to `GrothendieckContra' F'`.
-/
def ι (c : C) : F'.obj c ⥤ GrothendieckContraCat' (F' := F') :=
  gcCodFuncToGcContra'
    (C := C)
    (Cat.postCompOpFunctor' ⋙ (CategoryTheory.evaluation Cᵒᵖ' Cat).obj c)
    (gr_ι_flip (C := Cᵒᵖ') c)
    F'

def ι_obj (c : C) (d : F'.obj c) :
  (ι c).obj d = ⟨c, d⟩ :=
    rfl

def ι_map_fiber (c : C) {d : F'.obj c} :
  d = (F'.map (𝟙 c)).toFunctor.obj ((ι c).obj d).fiber := by
    simp only [CategoryOp'.eq_1, Cat.of_α]
    have map_id_func := congrArg Cat.Hom.toFunctor (F'.map_id c)
    have deq := (congrFun (congrArg Functor.obj map_id_func) d).symm
    simp only [Cat.id_eq_id, Functor.id_obj] at deq
    exact deq

set_option backward.isDefEq.respectTransparency false in
def ι_map (c : C) {d d' : F'.obj c} (f : d ⟶ d') :
  (ι c).map f = ⟨𝟙 c, f ≫ eqToHom (ι_map_fiber c (d := d'))⟩ := by
    simp only [Cat.of_α, CategoryOp'.eq_1]
    unfold ι
    unfold gr_ι_flip
    apply ext
    case w_base =>
      simp only [gcCodFuncToGcContra', gcCodFuncToGcContra, evaluation,
        grothendieckContraIsoHom, grothendieckContraIsoHomMap, Functor.comp_obj,
        Functor.comp_map, Functor.op'.eq_1, functorOp'Obj.eq_1, Grothendieck.ι_map]
      rfl
    case w_fiber =>
      simp only [gcCodFuncToGcContra', gcCodFuncToGcContra, evaluation,
        grothendieckContraIsoHom, grothendieckContraIsoHomMap, Functor.comp_obj,
        Functor.comp_map, Functor.op'.eq_1, functorOp'Obj.eq_1, Grothendieck.ι_map,
        eqToHom_refl', Category.comp_id]
      apply eq_of_heq
      simp only [eqToHom_comp_heq_iff]
      exact (comp_eqToHom_heq f _).symm

/--
The covariant fiber inclusion functor is faithful.
-/
abbrev faithful_ι_cov (c : C) : (ι_cov (F' := F') c).Faithful :=
  op'_faithful (Grothendieck.ι (Cat.postCompOpFunctor'.obj F') c)

set_option backward.isDefEq.respectTransparency false in
/--
The fiber inclusion functor is faithful.
-/
instance faithful_ι (c : C) : (ι (F' := F') c).Faithful := by
  have : (ι_cov (F' := F') c).Faithful := faithful_ι_cov c
  have : (grothendieckContraIsoHom (F' := F')).Faithful := gcIsoHomFaithful
  unfold ι
  unfold gcCodFuncToGcContra'
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Natural transformation induced by a morphism in the base category.
For f : c ⟶ d in C (viewed as d ⟶ c in Cᵒᵖ'), the natural transformation
goes from F'.map f ⋙ ι c to ι d.
-/
def ιNatTrans {c d : C} (f : c ⟶ d) : (F'.map f).toFunctor ⋙ ι c ⟶ ι d where
  app X := { base := f, fiber := 𝟙 _ }
  naturality X Y g := by
    simp only [ι_obj, ι_map, Functor.comp_obj, Functor.comp_map]
    unfold CategoryStruct.comp
    unfold Category.toCategoryStruct
    unfold GrothendieckContraCat'
    unfold Cat.of Cat.str Bundled.of
    simp only [CategoryOp'.eq_1]
    unfold GrothendieckContraInst'
    unfold comp
    apply ext
    case w_base =>
      -- base component: both compositions have base f
      simp
    case w_fiber =>
      -- fiber component: involves eqToHom and functoriality
      simp only [Category.id_comp, CategoryTheory.Functor.map_id, Category.assoc]
      change ((F'.map f).toFunctor.map g ≫ _) ≫ _ ≫ _ =
        (F'.map f).toFunctor.map (g ≫ _) ≫ _
      rw [Functor.map_comp]
      rw [eqToHom_map]
      simp only [Category.assoc]
      simp

variable (fib : ∀ c, F'.obj c ⥤ T)
variable (hom : ∀ {c d : C} (f : c ⟶ d), (F'.map f).toFunctor ⋙ fib c ⟶ fib d)
variable (hom_id : ∀ c,
  hom (𝟙 c) = eqToHom (congrArg (· ⋙ fib c) (congrArg Cat.Hom.toFunctor (F'.map_id c))))

variable (hom_comp : ∀ {c d e : C} (f : c ⟶ d) (g : d ⟶ e),
  hom (f ≫ g) =
    eqToHom (congrArg (· ⋙ fib c) (congrArg Cat.Hom.toFunctor (F'.map_comp g f))) ≫
    Functor.whiskerLeft (F'.map g).toFunctor (hom f) ≫ hom g)

set_option backward.isDefEq.respectTransparency false in
/--
Construct a functor from the contravariant Grothendieck construction given
compatible functors from each fiber.
-/
def functorFrom : GrothendieckContra' F' ⥤ T where
  obj X := (fib X.base).obj X.fiber
  map {X Y} f := (fib X.base).map f.fiber ≫ (hom f.base).app Y.fiber
  map_id := by
    intro X
    change (fib X.base).map (id X).fiber ≫ (hom (id X).base).app X.fiber = _
    unfold id
    simp only []
    rw [hom_id]
    simp
  map_comp := by
    intro X Y Z f g
    -- Need to show: map (f ≫ g) = map f ≫ map g
    simp only [comp, CategoryStruct.comp]
    -- Use Functor.map_comp for fib X.base
    rw [Functor.map_comp, Functor.map_comp]
    -- Use hom_comp to expand hom (f.base ≫ g.base)
    rw [hom_comp]
    simp only [CategoryOp'.eq_1,
      functor_map_eqToHom, Cat.Hom.comp_toFunctor,
      NatTrans.comp_app, Functor.comp_obj,
      eqToHom_app, Functor.whiskerLeft_app,
      Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
    congr 1
    -- The goal is now showing naturality of hom f.base
    -- Recognize (fib X.base).map ∘ (F'.map f.base).map as (F'.map f ⋙ fib X).map
    change (fib X.base).map ((F'.map f.base).toFunctor.map g.fiber) ≫
      (hom f.base).app ((F'.map g.base).toFunctor.obj Z.fiber) ≫ (hom g.base).app Z.fiber =
      (hom f.base).app Y.fiber ≫ (fib Y.base).map g.fiber ≫ (hom g.base).app Z.fiber
    rw [← Functor.comp_map]
    -- Reassociate to separate the naturality square
    rw [← Category.assoc]
    -- Now apply naturality
    rw [NatTrans.naturality (hom f.base) g.fiber]
    simp

set_option backward.isDefEq.respectTransparency false in
/--
The fiber inclusion composed with `functorFrom` recovers the original fiber functor.
-/
def ιCompFunctorFrom (c : C) :
    ι c ⋙ functorFrom fib hom hom_id hom_comp ≅ fib c :=
  NatIso.ofComponents
    (fun _ => Iso.refl _)
    (fun f => by
      simp only [CategoryOp'.eq_1, Cat.of_α,
        Functor.comp_obj, Functor.comp_map,
        Iso.refl_hom, Category.comp_id,
        Category.id_comp, functorFrom, ι_obj]
      rw [ι_map]
      simp only [hom_id, eqToHom_app, Functor.map_comp, Category.assoc]
      simp only [eqToHom_map, eqToHom_trans, eqToHom_refl, Category.comp_id]
    )


set_option backward.isDefEq.respectTransparency false in
/--
Interaction between fiber inclusion and `map`.
-/
def ιCompMap {G' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}} (α : F' ⟶ G') (c : C) :
    ι c ⋙ map α ≅ (α.app c).toFunctor ⋙ ι c :=
  NatIso.ofComponents
    (fun _ => Iso.refl _)
    (fun f => by
      -- Need to show: (ι c ⋙ map α).map f ≫ Iso.refl _ = Iso.refl _ ≫ ((α.app c) ⋙ ι c).map f
      -- Simplify using map_map, ι_obj, and ι_map
      simp [map_map, ι_obj, ι_map]
    )

/-!
### FunctorFromData: Bundled data for functors FROM contravariant Grothendieck constructions

This section provides the dual to `FunctorToData`: a complete characterization of
functors FROM a contravariant Grothendieck construction `GrothendieckContra' F' ⥤ T`.

Every such functor is determined by:
- A family of fiber functors `fib : ∀ c, F'.obj c ⥤ T`
- Natural transformations `hom f : F'.map f ⋙ fib c ⟶ fib d` for each `f : c ⟶ d`
- Coherence conditions for identity and composition

The existing `functorFrom` function takes these components as separate arguments.
`FunctorFromData` bundles them into a single structure.
-/

/--
The type of fiber functors for bundled `FunctorFromData`.
For each `c : C`, a functor `F'.obj c ⥤ T`.
-/
abbrev FunctorFromDataFib := ∀ c, F'.obj c ⥤ T

/--
The type of natural transformations for bundled `FunctorFromData`.
For each `f : c ⟶ d`, a natural transformation `F'.map f ⋙ fib c ⟶ fib d`.
-/
abbrev FunctorFromDataHom (fib : FunctorFromDataFib (F' := F') (T := T)) :=
  ∀ {c d : C} (f : c ⟶ d), (F'.map f).toFunctor ⋙ fib c ⟶ fib d

/--
The identity coherence property for bundled `FunctorFromData`.
States that `hom (𝟙 c)` equals the canonical isomorphism from `F'.map_id`.
-/
abbrev FunctorFromDataHomId (fib : FunctorFromDataFib (F' := F') (T := T))
    (hom : FunctorFromDataHom (F' := F') fib) :=
  ∀ c, hom (𝟙 c) =
    eqToHom (congrArg (· ⋙ fib c) (congrArg Cat.Hom.toFunctor (F'.map_id c)))

/--
The composition coherence property for bundled `FunctorFromData`.
States that `hom (f ≫ g)` decomposes as the composition of whiskered `hom f`,
`hom g`, and the canonical isomorphism from `F'.map_comp`.
-/
abbrev FunctorFromDataHomComp (fib : FunctorFromDataFib (F' := F') (T := T))
    (hom : FunctorFromDataHom (F' := F') fib) :=
  ∀ {c d e : C} (f : c ⟶ d) (g : d ⟶ e), hom (f ≫ g) =
    eqToHom (congrArg (· ⋙ fib c) (congrArg Cat.Hom.toFunctor (F'.map_comp g f))) ≫
    Functor.whiskerLeft (F'.map g).toFunctor (hom f) ≫ hom g

/--
Bundled data for constructing a functor from the contravariant Grothendieck construction.

This structure captures all the data needed to define a functor
`GrothendieckContra' F' ⥤ T`:
- Fiber functors from each `F'.obj c` to `T`
- Natural transformations relating fibers along base morphisms
- Coherence conditions ensuring functoriality
-/
structure FunctorFromData where
  /-- Fiber functors: for each `c : C`, a functor `F'.obj c ⥤ T` -/
  fib' : FunctorFromDataFib (F' := F') (T := T)
  /-- Natural transformations: for each `f : c ⟶ d`, `F'.map f ⋙ fib' c ⟶ fib' d` -/
  hom' : FunctorFromDataHom (F' := F') fib'
  /-- Identity coherence -/
  hom_id' : FunctorFromDataHomId (F' := F') fib' hom'
  /-- Composition coherence -/
  hom_comp' : FunctorFromDataHomComp (F' := F') fib' hom'

variable (data : FunctorFromData (F' := F') (T := T))

set_option backward.isDefEq.respectTransparency false in
/--
Construct a functor from the contravariant Grothendieck construction using bundled data.
This wraps `GrothendieckContra'.functorFrom`.
-/
def functorFromData : GrothendieckContra' F' ⥤ T :=
  functorFrom data.fib' data.hom' data.hom_id' data.hom_comp'

variable (H : GrothendieckContra' F' ⥤ T)

set_option backward.isDefEq.respectTransparency false in
/--
Extract bundled data from a functor `GrothendieckContra' F' ⥤ T`:
- `fib' c := ι c ⋙ H` extracts the fiber functors
- `hom' f := ιNatTrans f ▷ H` constructs the natural transformations using
  the canonical natural transformation for base morphisms
-/
def ofFunctorFrom : FunctorFromData (F' := F') (T := T) where
  fib' c := ι (F' := F') c ⋙ H
  hom' {c d} f := Functor.whiskerRight (ιNatTrans (F' := F') f) H
  hom_id' c := by
    ext x
    simp only [Functor.whiskerRight_app, eqToHom_app, ιNatTrans, ι_obj, Functor.comp_obj]
    have h_fmap_id : (F'.map (𝟙 c)).toFunctor.obj x = x :=
      congrFun (congrArg Functor.obj (congrArg Cat.Hom.toFunctor (F'.map_id c))) x
    have hsrc_eq : (⟨c, (F'.map (𝟙 c)).toFunctor.obj x⟩ : GrothendieckContra' F') = ⟨c, x⟩ := by
      simp only [h_fmap_id]
    rw [← eqToHom_map H hsrc_eq]
    congr 1
    rw [eqToHom_eq]
    apply ext <;> simp
  hom_comp' {c₁ c₂ c₃} (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) := by
    ext (x : ↑(F'.obj c₃))
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      eqToHom_app, ιNatTrans, ι_obj, Functor.comp_obj]
    let fg : c₁ ⟶ c₃ := f ≫ g
    have heq_obj :
        (⟨c₁, (F'.map f).toFunctor.obj ((F'.map g).toFunctor.obj x)⟩ :
          GrothendieckContra' F') =
        ⟨c₁, (F'.map fg).toFunctor.obj x⟩ := by
      congr 1
      exact (congrFun (congrArg Functor.obj
        (congrArg Cat.Hom.toFunctor (F'.map_comp g f))) x).symm
    simp only [← H.map_comp]
    rw [← eqToHom_map H heq_obj.symm, ← H.map_comp]
    congr 1
    -- Prove equality of morphisms in GrothendieckContra' F'
    apply ext
    · simp [base_eqToHom, Category.id_comp]
    · simp [Category.id_comp, eqToHom_refl]

set_option backward.isDefEq.respectTransparency false in
/--
Round-trip: constructing a functor from extracted data gives back the original functor.
-/
theorem functorFromData_ofFunctorFrom : functorFromData (ofFunctorFrom H) = H := by
  fapply _root_.CategoryTheory.Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp only [functorFromData, ofFunctorFrom, functorFrom, Functor.comp_obj,
      Functor.comp_map, Functor.whiskerRight_app, ι_obj, ι_map, Category.id_comp,
      Category.comp_id, eqToHom_refl]
    rw [← H.map_comp]
    congr 1
    have w_base : (({ base := 𝟙 X.base, fiber := f.fiber ≫ eqToHom (ι_map_fiber X.base) } :
        Hom X ((ι X.base).obj ((F'.map f.base).toFunctor.obj Y.fiber))) ≫
        (ιNatTrans f.base).app Y.fiber).base = f.base := by
      unfold CategoryStruct.comp Category.toCategoryStruct GrothendieckContraCat' Cat.of Cat.str
        Bundled.of GrothendieckContraInst' comp ιNatTrans
      simp only [Category.id_comp]
    refine ext _ _ w_base ?_
    simp only [ιNatTrans, cat_comp_fiber,
      Functor.comp_obj, ι_obj]
    simp only [CategoryTheory.Functor.map_id,
      Category.id_comp, Category.assoc,
      eqToHom_trans, eqToHom_refl,
      Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
Round-trip: the fiber functors from extracted data equal the original fiber functors.
-/
theorem ofFunctorFrom_functorFromData_fib :
    (ofFunctorFrom (functorFromData data)).fib' = data.fib' := by
  funext c
  fapply _root_.CategoryTheory.Functor.ext
  · intro x
    simp only [ofFunctorFrom, functorFromData, functorFrom,
      Functor.comp_obj, ι_obj]
  · intro x y f
    simp only [ofFunctorFrom, Functor.comp_map]
    simp only [functorFromData, ι_map]
    simp only [functorFrom, ι_obj]
    have h_hom_id := congrFun (congrArg NatTrans.app (data.hom_id' c)) y
    simp only [eqToHom_app] at h_hom_id
    rw [h_hom_id]
    simp only [Functor.map_comp, eqToHom_map, eqToHom_trans,
      Category.assoc, Category.id_comp, Category.comp_id, eqToHom_refl']

set_option backward.isDefEq.respectTransparency false in
/--
Round-trip: the natural transformations from extracted data equal the original
natural transformations at each component.

The two natural transformations have different types because their fiber functors
differ propositionally. This theorem states that the `.app` components are equal
up to `eqToHom` coercions.
-/
theorem ofFunctorFrom_functorFromData_hom_app {c d : C} (f : c ⟶ d) (x : F'.obj d) :
    ((ofFunctorFrom (functorFromData data)).hom' f).app x =
    eqToHom (congrFun (congrArg Functor.obj
      (congrFun (ofFunctorFrom_functorFromData_fib data) c)) ((F'.map f).toFunctor.obj x)) ≫
    (data.hom' f).app x ≫
    eqToHom (congrFun (congrArg Functor.obj
      (congrFun (ofFunctorFrom_functorFromData_fib data) d)) x).symm := by
  simp only [ofFunctorFrom, Functor.whiskerRight_app, functorFromData, functorFrom,
    ιNatTrans, ι_obj]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [eqToHom_refl', Category.id_comp, Category.comp_id]

section FunctorFromDataCategory

variable (dataG dataH : FunctorFromData (F' := F') (T := T))

/--
The fiber natural transformations for `NatTransFromData` (contravariant case).
For each `c : C`, a natural transformation `dataG.fib' c ⟶ dataH.fib' c`.
-/
abbrev NatTransFromDataFib :=
  ∀ c, dataG.fib' c ⟶ dataH.fib' c

/--
The coherence condition for `NatTransFromData` (contravariant case).
For each `f : c ⟶ d`, the following square commutes:

```
F'.map f ⋙ dataG.fib' c --F'.map f ◁ fibNat c--> F'.map f ⋙ dataH.fib' c
            |                                            |
       dataG.hom' f                                 dataH.hom' f
            |                                            |
            v                                            v
      dataG.fib' d ------fibNat d---------------> dataH.fib' d
```
-/
abbrev NatTransFromDataCoherence (fibNat : NatTransFromDataFib (F' := F') dataG dataH) :=
  ∀ {c d : C} (f : c ⟶ d),
    Functor.whiskerLeft (F'.map f).toFunctor (fibNat c) ≫ dataH.hom' f =
      dataG.hom' f ≫ fibNat d

/--
The data for a natural transformation between functors from the contravariant
Grothendieck construction.

This bundles together:
- Fiber natural transformations for each base object
- Coherence condition ensuring compatibility with the `hom'` structure
-/
@[ext]
structure NatTransFromData where
  /-- Fiber natural transformations: for each `c`, `dataG.fib' c ⟶ dataH.fib' c` -/
  fibNat : NatTransFromDataFib (F' := F') dataG dataH
  /-- Coherence: `(F'.map f ◁ fibNat c) ≫ dataH.hom' f = dataG.hom' f ≫ fibNat d` -/
  coherence : NatTransFromDataCoherence (F' := F') dataG dataH fibNat

variable (natData : NatTransFromData (F' := F') dataG dataH)

set_option backward.isDefEq.respectTransparency false in
/--
Construct a natural transformation between functors from the contravariant
Grothendieck construction from bundled data.
-/
def natTransFromData : functorFromData dataG ⟶ functorFromData dataH where
  app X := (natData.fibNat X.base).app X.fiber
  naturality {X Y} f := by
    simp only [functorFromData, functorFrom]
    have h := congrFun (congrArg NatTrans.app (natData.coherence f.base)) Y.fiber
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
    rw [Category.assoc, ← h, ← Category.assoc, ← Category.assoc,
      (natData.fibNat X.base).naturality f.fiber]

variable {dataG dataH}
variable (α : functorFromData dataG ⟶ functorFromData dataH)

/--
Extract the fiber natural transformations from a natural transformation
between functors from the contravariant Grothendieck construction.
Uses `eqToHom` to cast between `ι c ⋙ functorFromData data` and `data.fib' c`.
-/
def ofNatTransFromDataFibNat : NatTransFromDataFib (F' := F') dataG dataH := fun c =>
  eqToHom (congrFun (ofFunctorFrom_functorFromData_fib dataG) c).symm ≫
  Functor.whiskerLeft (ι (F' := F') c) α ≫
  eqToHom (congrFun (ofFunctorFrom_functorFromData_fib dataH) c)

set_option backward.isDefEq.respectTransparency false in
/--
Extract `NatTransFromData` from a natural transformation between functors
from the contravariant Grothendieck construction.
-/
def ofNatTransFromData : NatTransFromData (F' := F') dataG dataH where
  fibNat := ofNatTransFromDataFibNat (F' := F') α
  coherence {c d} f := by
    ext x
    simp only [ofNatTransFromDataFibNat, NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
    have nat := α.naturality ((ιNatTrans (F' := F') f).app x)
    simp only [functorFromData, functorFrom,
      ιNatTrans, ι_obj, Functor.comp_obj] at nat
    simp only [CategoryTheory.Functor.map_id, Category.id_comp] at nat
    simp only [eqToHom_refl', Category.id_comp, Category.comp_id, ι_obj]
    exact nat.symm

set_option backward.isDefEq.respectTransparency false in
variable (dataG dataH) in
/--
Converting a natural transformation to data and back gives the original
(contravariant case).
-/
theorem natTransFromData_ofNatTransFromData :
    natTransFromData dataG dataH (ofNatTransFromData (F' := F') α) = α := by
  ext X
  simp only [natTransFromData, ofNatTransFromData, ofNatTransFromDataFibNat,
    NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
  simp only [eqToHom_refl', Category.id_comp, Category.comp_id, ι_obj]

set_option backward.isDefEq.respectTransparency false in
variable (dataG dataH) in
/--
Converting data to a natural transformation and back gives the original
(contravariant case).
-/
theorem ofNatTransFromData_natTransFromData :
    ofNatTransFromData (F' := F') (natTransFromData dataG dataH natData) = natData := by
  ext c x
  simp only [ofNatTransFromData, ofNatTransFromDataFibNat,
    NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, natTransFromData]
  simp only [eqToHom_refl', Category.id_comp, Category.comp_id, ι_obj]

/--
Equivalence between `NatTransFromData` and natural transformations between
functors from contravariant Grothendieck categories.
-/
def natTransFromDataEquiv :
    NatTransFromData (F' := F') dataG dataH ≃
    (functorFromData dataG ⟶ functorFromData dataH) where
  toFun := natTransFromData dataG dataH
  invFun := ofNatTransFromData (F' := F')
  left_inv := ofNatTransFromData_natTransFromData dataG dataH
  right_inv := natTransFromData_ofNatTransFromData dataG dataH

variable (data : FunctorFromData (F' := F') (T := T))

/--
The identity `NatTransFromData` on a `FunctorFromData` (contravariant case).
-/
def NatTransFromData.id : NatTransFromData (F' := F') data data where
  fibNat c := 𝟙 (data.fib' c)
  coherence {c d} f := by
    ext x
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app, Category.comp_id]
    exact Category.id_comp _

variable (dataK : FunctorFromData (F' := F') (T := T))

set_option backward.isDefEq.respectTransparency false in
/--
Composition of `NatTransFromData` values (contravariant case).
-/
def NatTransFromData.comp (natDataGH : NatTransFromData (F' := F') dataG dataH)
    (natDataHK : NatTransFromData (F' := F') dataH dataK) :
    NatTransFromData (F' := F') dataG dataK where
  fibNat c := natDataGH.fibNat c ≫ natDataHK.fibNat c
  coherence {c d} f := by
    ext x
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
    have hGH := congrFun (congrArg NatTrans.app (natDataGH.coherence f)) x
    have hHK := congrFun (congrArg NatTrans.app (natDataHK.coherence f)) x
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hGH hHK
    rw [Category.assoc, hHK, ← Category.assoc, hGH, Category.assoc]

/--
`natTransFromData` preserves identity (contravariant case).
-/
theorem natTransFromData_id :
    natTransFromData data data (NatTransFromData.id (F' := F') data) =
    𝟙 (functorFromData data) := by
  ext X
  simp only [natTransFromData, NatTransFromData.id, NatTrans.id_app, functorFromData, functorFrom]

variable (natDataGH : NatTransFromData (F' := F') dataG dataH)
variable (natDataHK : NatTransFromData (F' := F') dataH dataK)

set_option backward.isDefEq.respectTransparency false in
/--
`natTransFromData` preserves composition (contravariant case).
-/
theorem natTransFromData_comp :
    natTransFromData dataG dataK (NatTransFromData.comp (F' := F') dataK natDataGH natDataHK) =
    natTransFromData dataG dataH natDataGH ≫ natTransFromData dataH dataK natDataHK := by
  ext X
  simp only [natTransFromData, NatTransFromData.comp, NatTrans.comp_app]

/--
Category instance on `FunctorFromData F' (T := T)` using `NatTransFromData`
as morphisms (contravariant case).
-/
instance functorFromDataCategory : Category (FunctorFromData (F' := F') (T := T)) where
  Hom X Y := NatTransFromData (F' := F') X Y
  id X := NatTransFromData.id (F' := F') X
  comp {X Y Z} natXY natYZ := NatTransFromData.comp (F' := F') Z natXY natYZ
  id_comp {X Y} nat := by
    apply NatTransFromData.ext
    funext c
    simp only [NatTransFromData.comp, NatTransFromData.id, Category.id_comp]
  comp_id {X Y} nat := by
    apply NatTransFromData.ext
    funext c
    simp only [NatTransFromData.comp, NatTransFromData.id, Category.comp_id]
  assoc {W X Y Z} nat1 nat2 nat3 := by
    apply NatTransFromData.ext
    funext c
    simp only [NatTransFromData.comp, Category.assoc]

/--
Functor from `FunctorFromData F'` to the functor category `GrothendieckContra' F' ⥤ T`.
Sends `data` to `functorFromData data` and morphisms via `natTransFromData`.
-/
def functorFromDataToFunctorCat :
    FunctorFromData (F' := F') (T := T) ⥤ (GrothendieckContra' F' ⥤ T) where
  obj data := functorFromData data
  map {dataX dataY} nat := natTransFromData dataX dataY nat
  map_id data := natTransFromData_id (F' := F') data
  map_comp {dataX dataY dataZ} nat1 nat2 :=
    natTransFromData_comp (F' := F') (dataG := dataX) (dataH := dataY) dataZ nat1 nat2

/--
Composition of natural transformations with `eqToHom` round-trips through intermediate
functors: the middle `eqToHom` terms cancel (contravariant case).
-/
lemma eqToHom_comp_natTrans_comp_app' {A : Type*} [Category A]
    {G' G H H' K K' : A ⥤ T} (pG : G' = G) (pH : H' = H) (pK : K' = K)
    (α : G ⟶ H) (β : H ⟶ K) (X : A) :
    (eqToHom pG ≫ (α ≫ β) ≫ eqToHom pK.symm).app X =
    (eqToHom pG ≫ α ≫ eqToHom pH.symm).app X ≫ (eqToHom pH ≫ β ≫ eqToHom pK.symm).app X := by
  simp only [NatTrans.comp_app, eqToHom_app]
  simp only [Category.assoc]
  congr 2
  simp only [← Category.assoc]
  simp only [eqToHom_trans, eqToHom_refl, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/--
Functor from the functor category `GrothendieckContra' F' ⥤ T` to `FunctorFromData F'`.
Sends `H` to `ofFunctorFrom H` and morphisms via round-trip through `functorFromData`.
-/
def functorCatToFunctorFromData :
    (GrothendieckContra' F' ⥤ T) ⥤ FunctorFromData (F' := F') (T := T) where
  obj := ofFunctorFrom (F' := F') (T := T)
  map {G H} α := ofNatTransFromData (F' := F')
    (eqToHom (functorFromData_ofFunctorFrom G) ≫ α ≫
     eqToHom (functorFromData_ofFunctorFrom H).symm)
  map_id G := by
    simp only [Category.id_comp, eqToHom_trans, eqToHom_refl]
    exact ofNatTransFromData_natTransFromData (F' := F') _ _ (NatTransFromData.id (F' := F')
      (ofFunctorFrom G))
  map_comp {G H K} α β := by
    apply NatTransFromData.ext
    funext c
    ext x
    simp +instances only [
      CategoryStruct.comp,
      NatTransFromData.comp,
      ofNatTransFromData, ofNatTransFromDataFibNat]
    simp only [NatTrans.vcomp_app,
      Functor.whiskerLeft_app, eqToHom_app]
    simp only [eqToHom_refl', Category.id_comp,
      Category.comp_id, ι_obj]

/--
Counit isomorphism for the equivalence: the round-trip through `FunctorFromData` gives
back the original functor up to the canonical equality (contravariant case).
-/
def functorFromDataEquivCounitIso :
    functorCatToFunctorFromData (F' := F') (T := T) ⋙ functorFromDataToFunctorCat (F' := F') ≅
    𝟭 (GrothendieckContra' F' ⥤ T) :=
  NatIso.ofComponents
    (fun G => eqToIso (functorFromData_ofFunctorFrom G))
    (fun {G H} α => by
      simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
      simp only [functorFromDataToFunctorCat, functorCatToFunctorFromData]
      rw [natTransFromData_ofNatTransFromData]
      simp only [eqToIso.hom, Category.assoc]
      simp only [eqToHom_trans, eqToHom_refl, Category.comp_id])

set_option backward.isDefEq.respectTransparency false in
/--
Forward morphism for the unit isomorphism:
`data ⟶ ofFunctorFrom (functorFromData data)` (contravariant case).
Uses the equality `ofFunctorFrom_functorFromData_fib` to build the natural transformation.
-/
def functorFromDataEquivUnitHom (data : FunctorFromData (F' := F') (T := T)) :
    data ⟶ ofFunctorFrom (functorFromData data) where
  fibNat c := eqToHom (congrFun (ofFunctorFrom_functorFromData_fib data) c).symm
  coherence {c c'} f := by
    ext x
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
    simp only [ofFunctorFrom_functorFromData_hom_app, eqToHom_refl', Category.id_comp,
      Category.comp_id]
    simp

set_option backward.isDefEq.respectTransparency false in
/--
Backward morphism for the unit isomorphism:
`ofFunctorFrom (functorFromData data) ⟶ data` (contravariant case).
-/
def functorFromDataEquivUnitInv (data : FunctorFromData (F' := F') (T := T)) :
    ofFunctorFrom (functorFromData data) ⟶ data where
  fibNat c := eqToHom (congrFun (ofFunctorFrom_functorFromData_fib data) c)
  coherence {c c'} f := by
    ext x
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
    simp only [ofFunctorFrom_functorFromData_hom_app, eqToHom_refl', Category.id_comp,
      Category.comp_id]
    simp

/--
Unit isomorphism component for the equivalence (contravariant case).
-/
def functorFromDataEquivUnitComponent (data : FunctorFromData (F' := F') (T := T)) :
    data ≅ (functorFromDataToFunctorCat (F' := F') ⋙
      functorCatToFunctorFromData (F' := F')).obj data := by
  simp only [Functor.comp_obj, functorFromDataToFunctorCat, functorCatToFunctorFromData]
  exact { hom := functorFromDataEquivUnitHom (F' := F') data
          inv := functorFromDataEquivUnitInv (F' := F') data
          hom_inv_id := by
            apply NatTransFromData.ext
            funext c
            unfold CategoryStruct.comp CategoryStruct.id functorFromDataCategory
            simp only [functorFromDataEquivUnitHom, functorFromDataEquivUnitInv,
              NatTransFromData.comp, NatTransFromData.id, eqToHom_trans, eqToHom_refl]
          inv_hom_id := by
            apply NatTransFromData.ext
            funext c
            unfold CategoryStruct.comp CategoryStruct.id functorFromDataCategory
            simp only [functorFromDataEquivUnitHom, functorFromDataEquivUnitInv,
              NatTransFromData.comp, NatTransFromData.id, eqToHom_trans, eqToHom_refl] }

set_option backward.isDefEq.respectTransparency false in
/--
Unit isomorphism for the equivalence (contravariant case).
-/
def functorFromDataEquivUnitIso :
    𝟭 (FunctorFromData (F' := F') (T := T)) ≅
    functorFromDataToFunctorCat (F' := F') ⋙ functorCatToFunctorFromData (F' := F') :=
  NatIso.ofComponents
    (fun data => functorFromDataEquivUnitComponent (F' := F') data)
    (fun {data data'} nat => by
      apply NatTransFromData.ext
      funext c
      ext x
      simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
      unfold CategoryStruct.comp functorFromDataCategory
      simp only [functorFromDataToFunctorCat, functorCatToFunctorFromData,
        functorFromDataEquivUnitComponent, functorFromDataEquivUnitHom,
        NatTransFromData.comp, ofNatTransFromData, ofNatTransFromDataFibNat,
        NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app, natTransFromData, ι_obj]
      simp)

/--
The category of `FunctorFromData F'` is equivalent to the functor category
`GrothendieckContra' F' ⥤ T` (contravariant case).
-/
def functorFromDataEquivCat :
    FunctorFromData (F' := F') (T := T) ≌ (GrothendieckContra' F' ⥤ T) where
  functor := functorFromDataToFunctorCat (F' := F')
  inverse := functorCatToFunctorFromData (F' := F')
  unitIso := functorFromDataEquivUnitIso (F' := F')
  counitIso := functorFromDataEquivCounitIso (F' := F')
  functor_unitIso_comp data := by
    apply NatTrans.ext
    funext X
    simp only [functorFromDataEquivUnitIso, NatIso.ofComponents_hom_app,
      functorFromDataEquivCounitIso, functorFromDataToFunctorCat, functorCatToFunctorFromData,
      functorFromDataEquivUnitComponent, Functor.comp_obj]
    simp only [eqToIso.hom, NatTrans.comp_app, NatTrans.id_app]
    simp only [natTransFromData, functorFromDataEquivUnitHom, eqToHom_app]
    simp only [functorFromData, functorFrom]
    simp

end FunctorFromDataCategory

end FunctorFrom

section FunctorTo

variable {E : Type*} [Category E]

/-! ### Client-Facing Types

These are the types that clients need to understand and provide when constructing
functors into the contravariant Grothendieck construction.
-/

/--
The type of fiber functions for `GrothendieckContra'.functorTo`.
Given a base functor `baseFunc : E ⥤ C`, a fiber function assigns to each
`e : E` an object in the fiber category `F'.obj (baseFunc.obj e)`.
-/
abbrev FunctorToFib (baseFunc : E ⥤ C) := ∀ e, F'.obj (baseFunc.obj e)

/--
The type of morphism functions for `GrothendieckContra'.functorTo`.
Given a fiber function `fib`, a morphism function assigns to each morphism
`g : e ⟶ e'` in `E` a morphism from the source fiber to the transported fiber.
-/
abbrev FunctorToHom (baseFunc : E ⥤ C) (fib : FunctorToFib baseFunc) :=
  ∀ {e e' : E} (g : e ⟶ e'), fib e ⟶ (F'.map (baseFunc.map g)).toFunctor.obj (fib e')


/-! ### Internal Implementation Types

These types are used internally and are derived automatically from functor laws.
Clients do not need to provide these.
-/

/--
The type of identity equality proofs for `GrothendieckContra'.functorTo`.
This equality is derived automatically from `baseFunc.map_id` and `F'.map_id`.
-/
abbrev FunctorToEqId (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (baseFunc : E ⥤ C)
    (fib : FunctorToFib (F' := F') baseFunc) :=
  ∀ e, fib e = (F'.map (baseFunc.map (𝟙 e))).toFunctor.obj (fib e)

/--
Derive the identity equality from functor laws.
-/
lemma functorToEqIdProof (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (baseFunc : E ⥤ C)
    (fib : FunctorToFib (F' := F') baseFunc) : FunctorToEqId F' baseFunc fib := by
  intro e
  have h1 : baseFunc.map (𝟙 e) = 𝟙 (baseFunc.obj e) := baseFunc.map_id e
  have h2 : F'.map (𝟙 (baseFunc.obj e)) = 𝟙 (F'.obj (baseFunc.obj e)) :=
    F'.map_id (baseFunc.obj e)
  calc fib e = (𝟭 (F'.obj (baseFunc.obj e))).obj (fib e) := rfl
    _ = (F'.map (𝟙 (baseFunc.obj e))).toFunctor.obj (fib e) := by
        exact congrArg (·.toFunctor.obj (fib e)) h2.symm
    _ = (F'.map (baseFunc.map (𝟙 e))).toFunctor.obj (fib e) := by
        exact congrArg (fun g => (F'.map g).toFunctor.obj (fib e)) h1.symm

/--
The type of composition equality proofs for `GrothendieckContra'.functorTo`.
This equality is derived automatically from `baseFunc.map_comp` and `F'.map_comp`.
-/
abbrev FunctorToEqComp (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (baseFunc : E ⥤ C)
    (fib : FunctorToFib (F' := F') baseFunc) :=
  ∀ {e e' e'' : E} (g : e ⟶ e') (h : e' ⟶ e''),
    (F'.map (baseFunc.map g)).toFunctor.obj
      ((F'.map (baseFunc.map h)).toFunctor.obj (fib e'')) =
    (F'.map (baseFunc.map (g ≫ h))).toFunctor.obj (fib e'')

/--
Derive the composition equality from functor laws.
-/
lemma functorToEqCompProof (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (baseFunc : E ⥤ C)
    (fib : FunctorToFib (F' := F') baseFunc) : FunctorToEqComp F' baseFunc fib := by
  intro e e' e'' g h
  have h1 : baseFunc.map (g ≫ h) = baseFunc.map g ≫ baseFunc.map h := baseFunc.map_comp g h
  have h2 : F'.map (baseFunc.map h ≫ baseFunc.map g) =
      F'.map (baseFunc.map h) ≫ F'.map (baseFunc.map g) := by
    have := @Functor.map_comp Cᵒᵖ' _ Cat.{v₂, u₂} _ F' (baseFunc.obj e'')
      (baseFunc.obj e') (baseFunc.obj e) (baseFunc.map h) (baseFunc.map g)
    simp only [op_comp_eq] at this
    exact this
  calc (F'.map (baseFunc.map g)).toFunctor.obj
         ((F'.map (baseFunc.map h)).toFunctor.obj (fib e''))
    = ((F'.map (baseFunc.map h) ≫ F'.map (baseFunc.map g))).toFunctor.obj (fib e'') := rfl
    _ = (F'.map (baseFunc.map h ≫ baseFunc.map g)).toFunctor.obj (fib e'') := by
        exact congrArg (·.toFunctor.obj (fib e'')) h2.symm
    _ = (F'.map (baseFunc.map (g ≫ h))).toFunctor.obj (fib e'') := by
        simp only [op_comp_eq, ← baseFunc.map_comp]

/--
The identity coherence property for `GrothendieckContra'.functorTo`.
States that `hom (𝟙 e)` equals the canonical isomorphism from the derived equality.
-/
abbrev FunctorToHomId (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (baseFunc : E ⥤ C)
    (fib : FunctorToFib (F' := F') baseFunc)
    (hom : FunctorToHom baseFunc fib) :=
  ∀ e, hom (𝟙 e) = eqToHom (functorToEqIdProof F' baseFunc fib e)

/--
The composition coherence property for `GrothendieckContra'.functorTo`.
States that `hom (g ≫ h)` decomposes into `hom g`, `hom h`, and transport.
-/
abbrev FunctorToHomComp (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (baseFunc : E ⥤ C)
    (fib : FunctorToFib (F' := F') baseFunc)
    (hom : FunctorToHom baseFunc fib) :=
  ∀ {e e' e'' : E} (g : e ⟶ e') (h : e' ⟶ e''),
    hom (g ≫ h) =
      hom g ≫ (F'.map (baseFunc.map g)).toFunctor.map (hom h) ≫
        eqToHom (functorToEqCompProof F' baseFunc fib g h)

/--
The data required to construct a functor into the contravariant Grothendieck
construction.

This bundles together all the components needed for `functorTo`:
- A base functor `baseFunc : E ⥤ C`
- Fiber objects for each object in `E`
- Fiber morphisms for each morphism in `E`
- Coherence conditions for identity and composition
  (equality proofs are derived automatically)
-/
structure FunctorToData (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) where
  /-- The base functor from `E` to `C` -/
  baseFunc : E ⥤ C
  /-- Fiber objects: for each `e : E`, an object in `F'.obj (baseFunc.obj e)` -/
  fib : FunctorToFib (F' := F') baseFunc
  /-- Fiber morphisms: for each `g : e ⟶ e'`, a morphism between fibers -/
  hom : FunctorToHom baseFunc fib
  /-- Coherence: `hom (𝟙 e) = eqToHom (functorToEqIdProof ...)` -/
  hom_id : FunctorToHomId F' baseFunc fib hom
  /-- Coherence: `hom (g ≫ h)` decomposes correctly -/
  hom_comp : FunctorToHomComp F' baseFunc fib hom

variable (data : FunctorToData F' (E := E))

/--
Construct a functor into the contravariant Grothendieck construction from
bundled data.

This is the contravariant dual of `Grothendieck.functorTo`.
-/
def functorTo : E ⥤ GrothendieckContra' F' where
  obj e := ⟨data.baseFunc.obj e, data.fib e⟩
  map {e e'} g := ⟨data.baseFunc.map g, data.hom g⟩
  map_id e := ext _ _ (data.baseFunc.map_id e) (by
    simp only [data.hom_id]
    cat_disch)
  map_comp {e e' e''} g h := ext _ _ (data.baseFunc.map_comp g h) (by
    simp only [data.hom_comp]
    cat_disch)

/--
The functor `functorTo` composed with `forget` equals `baseFunc`.
-/
theorem functorTo_comp_forget :
    functorTo data ⋙ forget F' = data.baseFunc := rfl

variable (G : E ⥤ GrothendieckContra' F')

/--
Extract `FunctorToData` from a functor into the contravariant Grothendieck
construction.

This is the inverse to `functorTo`, demonstrating that `functorTo` is the
unique introduction rule for functors into contravariant Grothendieck
categories.
-/
def ofFunctor : FunctorToData F' (E := E) where
  baseFunc := G ⋙ forget F'
  fib e := (G.obj e).fiber
  hom g := (G.map g).fiber
  hom_id e := by
    change (G.map (𝟙 e)).fiber = eqToHom _
    have h : G.map (𝟙 e) = id (G.obj e) := G.map_id e
    rw [congr h, id_fiber_val, eqToHom_trans]
  hom_comp g h := by
    change (G.map (g ≫ h)).fiber = _ ≫ _ ≫ eqToHom _
    have hcomp : G.map (g ≫ h) = comp (G.map g) (G.map h) := G.map_comp g h
    rw [congr hcomp, comp_fiber]
    simp only [Functor.comp_map, forget_map]
    cat_disch

/--
Round-trip theorem: `functorTo (ofFunctor G) = G`.

Building a functor from the extracted data recovers the original functor.
-/
theorem functorTo_ofFunctor : functorTo (ofFunctor G) = G := rfl

/--
Round-trip theorem: `ofFunctor (functorTo data) = data`.

Extracting data from a constructed functor recovers the original data.
-/
theorem ofFunctor_functorTo : ofFunctor (functorTo data) = data := rfl

/--
Equivalence between functors into `GrothendieckContra' F'` and `FunctorToData`.

This establishes that `functorTo` is the unique way to construct functors into
contravariant Grothendieck categories: every such functor arises from some
`FunctorToData`, and the correspondence is bijective.
-/
def functorToEquiv :
    (E ⥤ GrothendieckContra' F') ≃ FunctorToData F' (E := E) where
  toFun := ofFunctor
  invFun := functorTo
  left_inv := functorTo_ofFunctor
  right_inv := ofFunctor_functorTo

end FunctorTo

/-!
## Sections of Contravariant Grothendieck Constructions

A section of the forgetful functor `forget F' : GrothendieckContra' F' ⥤ C`
is a functor `s : C ⥤ GrothendieckContra' F'` such that `s ⋙ forget F' = 𝟭 C`.

Such sections correspond to choosing:
- For each `c : C`, an object in the fiber `F'.obj c`
- For each morphism `f : c ⟶ c'`, a compatible fiber morphism

In the contravariant case, fiber morphisms go FROM source TO transported target:
`hom f : fib c ⟶ (F'.map f).obj (fib c')`
-/

section SectionDataContra

variable {C : Type u} [Category.{v} C]
variable (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})

/--
The type of fiber functions for a section of `forget F' : GrothendieckContra' F' ⥤ C`.
-/
abbrev SectionFibContra := ∀ c, F'.obj c

variable {F'}

/--
The type of morphism functions for a contravariant section.
In the contravariant case, morphisms go from source fiber to transported target fiber.
-/
abbrev SectionHomContra (fib : SectionFibContra F') :=
  ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ (F'.map f).toFunctor.obj (fib c')

/--
The identity coherence condition for contravariant sections.
-/
abbrev SectionHomIdContra (fib : SectionFibContra F') (hom : SectionHomContra fib) :=
  ∀ c, hom (𝟙 c) = eqToHom (functorToEqIdProof F' (𝟭 C) fib c)

/--
The composition coherence condition for contravariant sections.
-/
abbrev SectionHomCompContra (fib : SectionFibContra F') (hom : SectionHomContra fib) :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c''),
    hom (f ≫ g) =
      hom f ≫ (F'.map f).toFunctor.map (hom g) ≫
        eqToHom (functorToEqCompProof F' (𝟭 C) fib f g)

variable (F')

/--
The data for a section of `forget F' : GrothendieckContra' F' ⥤ C`.

A section assigns to each object in `C` a fiber element in `F'.obj c`, to each
morphism a compatible fiber morphism, with identity and composition coherence.

Given a section `s : SectionDataContra F'`, the functor
`s.toFunctor : C ⥤ GrothendieckContra' F'` satisfies `s.toFunctor ⋙ forget F' = 𝟭 C`.
-/
structure SectionDataContra where
  /-- Fiber objects for each `c : C` -/
  fib : SectionFibContra F'
  /-- Fiber morphisms for each morphism in `C` -/
  hom : SectionHomContra fib
  /-- Identity coherence -/
  hom_id : SectionHomIdContra fib hom
  /-- Composition coherence -/
  hom_comp : SectionHomCompContra fib hom

variable {F'}
variable (sec : SectionDataContra F')

/--
Construct a functor `C ⥤ GrothendieckContra' F'` from section data.

This functor is a section of `forget F'`: it satisfies
`toFunctor ⋙ forget F' = 𝟭 C`.
-/
def SectionDataContra.toFunctor : C ⥤ GrothendieckContra' F' where
  obj c := ⟨c, sec.fib c⟩
  map {c c'} f := ⟨f, sec.hom f⟩
  map_id c := ext _ _ rfl (by
    simp only [sec.hom_id]
    cat_disch)
  map_comp {c c' c''} f g := ext _ _ rfl (by
    simp only [sec.hom_comp]
    cat_disch)

/--
The section functor composed with forget equals the identity.
-/
theorem SectionDataContra.toFunctor_comp_forget :
    sec.toFunctor ⋙ forget F' = 𝟭 C := rfl

variable {D : Type u₁} [Category.{v₁} D]
variable (F')

/--
The factorization of contravariant `FunctorToData F'` via sections and `pre`.

A `FunctorToData F' (E := D)` decomposes into:
- A base functor `baseFunc : D ⥤ C`
- Section data for `functorOp'Obj baseFunc ⋙ F'`

The original functor is recovered as `sec.toFunctor ⋙ pre F' baseFunc`.
-/
def FunctorToData.toSigmaSectionDataContra (data : FunctorToData F' (E := D)) :
    Σ (baseFunc : D ⥤ C), SectionDataContra (functorOp'Obj baseFunc ⋙ F') :=
  ⟨data.baseFunc, {
    fib := data.fib
    hom := data.hom
    hom_id := data.hom_id
    hom_comp := data.hom_comp
  }⟩

/--
Reconstruct contravariant `FunctorToData F'` from a base functor and section data.
-/
def FunctorToData.ofSigmaSectionDataContra
    (data : Σ (baseFunc : D ⥤ C), SectionDataContra (functorOp'Obj baseFunc ⋙ F')) :
    FunctorToData F' (E := D) :=
  { baseFunc := data.1
    fib := data.2.fib
    hom := data.2.hom
    hom_id := data.2.hom_id
    hom_comp := data.2.hom_comp }

/--
Round-trip: `ofSigmaSectionDataContra (toSigmaSectionDataContra data) = data`
-/
theorem FunctorToData.ofSigmaSectionDataContra_toSigmaSectionDataContra
    (data : FunctorToData F' (E := D)) :
    FunctorToData.ofSigmaSectionDataContra F'
      (FunctorToData.toSigmaSectionDataContra F' data) = data := rfl

/--
Round-trip: `toSigmaSectionDataContra (ofSigmaSectionDataContra data) = data`
-/
theorem FunctorToData.toSigmaSectionDataContra_ofSigmaSectionDataContra
    (data : Σ (baseFunc : D ⥤ C), SectionDataContra (functorOp'Obj baseFunc ⋙ F')) :
    FunctorToData.toSigmaSectionDataContra F'
      (FunctorToData.ofSigmaSectionDataContra F' data) = data := rfl

/--
Equivalence between contravariant `FunctorToData F'` and
`Σ (baseFunc : D ⥤ C), SectionDataContra (functorOp'Obj baseFunc ⋙ F')`.

This establishes that functors into the contravariant Grothendieck construction
decompose into a choice of base functor plus section data for the pulled-back
construction.
-/
def FunctorToData.equivSigmaSectionDataContra :
    FunctorToData F' (E := D) ≃
      Σ (baseFunc : D ⥤ C), SectionDataContra (functorOp'Obj baseFunc ⋙ F') where
  toFun := FunctorToData.toSigmaSectionDataContra F'
  invFun := FunctorToData.ofSigmaSectionDataContra F'
  left_inv := FunctorToData.ofSigmaSectionDataContra_toSigmaSectionDataContra F'
  right_inv := FunctorToData.toSigmaSectionDataContra_ofSigmaSectionDataContra F'

/--
Construct the functor `D ⥤ GrothendieckContra' F'` via the section-pre factorization.

Given a base functor and section data, this constructs the functor as:
`sec.toFunctor ⋙ pre F' baseFunc`

This makes explicit that functors into contravariant Grothendieck constructions
factor through the pullback construction via `pre`.
-/
def FunctorToData.toFunctorViaPreContra
    (baseFunc : D ⥤ C) (sec : SectionDataContra (functorOp'Obj baseFunc ⋙ F')) :
    D ⥤ GrothendieckContra' F' :=
  sec.toFunctor ⋙ pre F' baseFunc

set_option backward.isDefEq.respectTransparency false in
/--
The two ways of constructing a functor from contravariant `FunctorToData` agree.

`functorTo data = sec.toFunctor ⋙ pre F' baseFunc`

where `sec` is the section data extracted from `data`.
-/
theorem FunctorToData.functorTo_eq_toFunctorViaPreContra (data : FunctorToData F' (E := D)) :
    functorTo data =
      FunctorToData.toFunctorViaPreContra F' data.baseFunc
        (FunctorToData.toSigmaSectionDataContra F' data).2 := by
  refine _root_.CategoryTheory.Functor.ext ?h_obj ?h_map
  case h_obj => intro d; rfl
  case h_map =>
    intro d d' f
    simp only [toFunctorViaPreContra, Functor.comp_map,
      SectionDataContra.toFunctor, pre_map, toSigmaSectionDataContra, functorTo,
      eqToHom_refl, Category.id_comp, Category.comp_id]

end SectionDataContra

section NatTransTo

variable {E : Type*} [Category E]

/--
The type of fiber morphism functions for `natTransTo` in the contravariant case.
Given a base natural transformation `baseNat : dataG.baseFunc ⟶ dataH.baseFunc`,
a fiber morphism function assigns to each `e : E` a morphism from the source
fiber to the transported target fiber.
-/
abbrev NatTransToFibMor (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    (dataG dataH : FunctorToData F' (E := E))
    (baseNat : dataG.baseFunc ⟶ dataH.baseFunc) :=
  ∀ e, dataG.fib e ⟶ (F'.map (baseNat.app e)).toFunctor.obj (dataH.fib e)

/--
The type of base equality proofs for `natTransTo` in the contravariant case.
This equality follows from naturality of `baseNat` and functoriality of `F'`.
Clients can provide any proof of this equality.
-/
abbrev NatTransToEqBase (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    (dataG dataH : FunctorToData F' (E := E))
    (baseNat : dataG.baseFunc ⟶ dataH.baseFunc) :=
  ∀ {e e' : E} (f : e ⟶ e'),
    let comp1 : dataG.baseFunc.obj e ⟶ dataH.baseFunc.obj e' :=
      baseNat.app e ≫ dataH.baseFunc.map f
    let comp2 : dataG.baseFunc.obj e ⟶ dataH.baseFunc.obj e' :=
      dataG.baseFunc.map f ≫ baseNat.app e'
    (F'.map comp1).toFunctor.obj (dataH.fib e') = (F'.map comp2).toFunctor.obj (dataH.fib e')

/--
The fiber naturality condition for `natTransTo` in the contravariant case.
This expresses that the two paths from source to target fiber (via composition
in the contravariant Grothendieck category) are equal after accounting for
type transports.
-/
abbrev NatTransToFibNat (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    (dataG dataH : FunctorToData F' (E := E))
    (baseNat : dataG.baseFunc ⟶ dataH.baseFunc)
    (fibMor : NatTransToFibMor F' dataG dataH baseNat)
    (eq_base : NatTransToEqBase F' dataG dataH baseNat) :=
  ∀ {e e' : E} (f : e ⟶ e'),
    dataG.hom f ≫
      (F'.map (dataG.baseFunc.map f)).toFunctor.map (fibMor e') ≫
      eqToHom (Functor.congr_obj
        (congrArg Cat.Hom.toFunctor
          (F'.map_comp (baseNat.app e') (dataG.baseFunc.map f)).symm)
        (dataH.fib e')) =
    fibMor e ≫
      (F'.map (baseNat.app e)).toFunctor.map (dataH.hom f) ≫
      eqToHom ((Functor.congr_obj
        (congrArg Cat.Hom.toFunctor
          (F'.map_comp (dataH.baseFunc.map f) (baseNat.app e)).symm)
        (dataH.fib e')).trans (eq_base f))

/--
The data required to construct a natural transformation between functors
into the contravariant Grothendieck construction.

This bundles together all the components needed for `natTransTo`:
- A base natural transformation between the base functors
- Fiber morphisms for each object
- Equality proof for base naturality (for eqToHom flexibility)
- Fiber naturality condition
-/
structure NatTransToData (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    (dataG dataH : FunctorToData F' (E := E)) where
  /-- Natural transformation between base functors -/
  baseNat : dataG.baseFunc ⟶ dataH.baseFunc
  /-- Fiber morphisms: for each `e`, a morphism between fibers -/
  fibMor : NatTransToFibMor F' dataG dataH baseNat
  /-- Equality proof from base naturality -/
  eq_base : NatTransToEqBase F' dataG dataH baseNat
  /-- Fiber naturality condition -/
  fibNat : NatTransToFibNat F' dataG dataH baseNat fibMor eq_base

variable (dataG dataH : FunctorToData F' (E := E))
variable (nat : NatTransToData F' dataG dataH)

set_option backward.isDefEq.respectTransparency false in
/--
Construct a natural transformation between functors into the contravariant
Grothendieck construction from bundled data.
-/
def natTransTo : functorTo dataG ⟶ functorTo dataH where
  app e := ⟨nat.baseNat.app e, nat.fibMor e⟩
  naturality {e e'} f := by
    have w_base : (dataG.baseFunc.map f ≫ nat.baseNat.app e') =
        (nat.baseNat.app e ≫ dataH.baseFunc.map f) :=
      nat.baseNat.naturality f
    refine ext _ _ w_base ?_
    simp only [functorTo]
    have h := @nat.fibNat e e' f
    cat_disch

variable (α : functorTo dataG ⟶ functorTo dataH)

/--
The base natural transformation extracted from a natural transformation
between functors into the contravariant Grothendieck construction.
-/
def ofNatTransBaseNat : dataG.baseFunc ⟶ dataH.baseFunc where
  app e := (α.app e).base
  naturality {e e'} f := by
    have h := α.naturality f
    simp only [functorTo] at h
    exact congrArg Hom.base h

/--
Extract `NatTransToData` from a natural transformation between functors
into the contravariant Grothendieck construction.
-/
def ofNatTrans : NatTransToData F' dataG dataH where
  baseNat := ofNatTransBaseNat dataG dataH α
  fibMor e := (α.app e).fiber
  eq_base {e e'} f := by
    simp only [ofNatTransBaseNat]
    have h := α.naturality f
    simp only [functorTo] at h
    have hbase := congrArg Hom.base h
    simp only [] at hbase
    exact Functor.congr_obj (congrArg (fun x => (F'.map x).toFunctor) hbase.symm)
      (dataH.fib e')
  fibNat {e e'} f := by
    simp only [ofNatTransBaseNat, functorTo]
    have h := α.naturality f
    simp only [functorTo] at h
    have hfiber := congr h
    simp only [] at hfiber
    calc _ = _ := by cat_disch
      _ = _ := hfiber
      _ = _ := by cat_disch

/--
Converting a natural transformation to data and back gives the original.
-/
theorem natTransTo_ofNatTrans :
    natTransTo dataG dataH (ofNatTrans dataG dataH α) = α := by
  ext e
  rfl

/--
Converting data to a natural transformation and back gives the original.
-/
theorem ofNatTrans_natTransTo :
    ofNatTrans dataG dataH (natTransTo dataG dataH nat) = nat := rfl

/--
Equivalence between `NatTransToData` and natural transformations between
functors into contravariant Grothendieck categories.
-/
def natTransToEquiv :
    NatTransToData F' dataG dataH ≃ (functorTo dataG ⟶ functorTo dataH) where
  toFun := natTransTo dataG dataH
  invFun := ofNatTrans dataG dataH
  left_inv := ofNatTrans_natTransTo dataG dataH
  right_inv := natTransTo_ofNatTrans dataG dataH

end NatTransTo

section FunctorToDataCategory

variable {E : Type*} [Category E]

variable (data : FunctorToData F' (E := E))

/--
The identity `NatTransToData` for a `FunctorToData`, defined via the correspondence
with identity natural transformations.
-/
def NatTransToData.id : NatTransToData F' data data :=
  ofNatTrans data data (𝟙 (functorTo data))

/--
Composition of `NatTransToData`, defined via the correspondence with natural
transformation composition.
-/
def NatTransToData.comp {dataG dataH dataK : FunctorToData F' (E := E)}
    (nat1 : NatTransToData F' dataG dataH)
    (nat2 : NatTransToData F' dataH dataK) : NatTransToData F' dataG dataK :=
  ofNatTrans dataG dataK (natTransTo dataG dataH nat1 ≫ natTransTo dataH dataK nat2)

/--
Category instance on `FunctorToData F' (E := E)` using `NatTransToData` as morphisms.
-/
instance functorToDataCategory : Category (FunctorToData F' (E := E)) where
  Hom := NatTransToData F'
  id data := NatTransToData.id data
  comp {X Y Z} := NatTransToData.comp
  id_comp {_ _} nat := by
    unfold NatTransToData.id NatTransToData.comp
    conv_rhs => rw [← ofNatTrans_natTransTo _ _ nat]
    congr 1
    exact Category.id_comp _
  comp_id {_ _} nat := by
    unfold NatTransToData.id NatTransToData.comp
    conv_rhs => rw [← ofNatTrans_natTransTo _ _ nat]
    congr 1
    exact Category.comp_id _
  assoc {_ _ _ _} nat1 nat2 nat3 := by
    unfold NatTransToData.comp
    congr 1
    exact Category.assoc _ _ _

/--
Functor from `FunctorToData F'` to the functor category `E ⥤ GrothendieckContra' F'`.
Sends `data` to `functorTo data` and morphisms via `natTransTo`.
-/
def functorToDataToFunctorCat :
    FunctorToData F' (E := E) ⥤ (E ⥤ GrothendieckContra' F') where
  obj := functorTo
  map := natTransTo _ _
  map_id _ := rfl
  map_comp _ _ := rfl

/--
Functor from the functor category `E ⥤ GrothendieckContra' F'` to `FunctorToData F'`.
Sends `G` to `ofFunctor G` and morphisms via `ofNatTrans`.
-/
def functorCatToFunctorToData :
    (E ⥤ GrothendieckContra' F') ⥤ FunctorToData F' (E := E) where
  obj := ofFunctor
  map {G H} α := ofNatTrans (ofFunctor G) (ofFunctor H) α
  map_id _ := rfl
  map_comp _ _ := rfl

/--
Categorical isomorphism between `FunctorToData F'` and the functor category
`E ⥤ GrothendieckContra' F'`.
-/
def functorToDataIsoCat :
    FunctorToData F' (E := E) ≅Cat (E ⥤ GrothendieckContra' F') where
  hom := functorToDataToFunctorCat.toCatHom
  inv := functorCatToFunctorToData.toCatHom
  hom_inv_id := rfl
  inv_hom_id := rfl

end FunctorToDataCategory

end GrothendieckContra'

/-!
## Functors Between Grothendieck Constructions (Covariant Case)

This section defines bundled data for functors between two covariant Grothendieck
constructions `Grothendieck G ⥤ Grothendieck F` where `G : C ⥤ Cat` and
`F : D ⥤ Cat`.

A functor between Grothendieck constructions is characterized by:
- A base functor `baseFib : C ⥤ D`
- For each `c : C`, a functor `fibFib c : G.obj c ⥤ F.obj (baseFib.obj c)`
- Coherent fiber morphisms relating these across base morphisms
-/

section FunctorBetween

universe vC vD uC uD

variable {C : Type uC} [Category.{vC} C] (G : C ⥤ Cat.{vC, uC})
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ Cat.{vD, uD})

/--
The base-fiber functor: assigns to each `c : C` a base object in `D`.
-/
abbrev FunctorBetweenBaseFib := C ⥤ D

/--
The fiber-fiber functor: for each `c : C`, a functor from `G.obj c` to
`F.obj (baseFib.obj c)`.
-/
abbrev FunctorBetweenFibFib (baseFib : FunctorBetweenBaseFib (C := C) (D := D)) :=
  ∀ c, G.obj c ⥤ F.obj (baseFib.obj c)

/--
The cross-fiber morphism component: for each `f : c ⟶ c'` and `x : G.obj c`,
a morphism from the transported source fiber to the destination fiber.

For `f : c ⟶ c'` and `x : G.obj c`, the fiber morphism in `Grothendieck F`
goes from `(F.map (baseFib.map f)).obj ((fibFib c).obj x)` in the transported
source fiber to `(fibFib c').obj ((G.map f).obj x)` in the destination fiber.
-/
abbrev FunctorBetweenFibHomCrossApp (baseFib : FunctorBetweenBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenFibFib G F baseFib) :=
  ∀ {c c' : C} (f : c ⟶ c') (x : G.obj c),
    (F.map (baseFib.map f)).toFunctor.obj ((fibFib c).obj x) ⟶
      (fibFib c').obj ((G.map f).toFunctor.obj x)

/--
The naturality condition for cross-fiber morphisms: for each `f : c ⟶ c'` and
`g : x ⟶ y` in `G.obj c`, the appropriate square commutes.
-/
abbrev FunctorBetweenFibHomCrossNat (baseFib : FunctorBetweenBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenFibFib G F baseFib)
    (fibHomCrossApp : FunctorBetweenFibHomCrossApp G F baseFib fibFib) :=
  ∀ {c c' : C} (f : c ⟶ c') {x y : G.obj c} (g : x ⟶ y),
    (F.map (baseFib.map f)).toFunctor.map ((fibFib c).map g) ≫ fibHomCrossApp f y =
    fibHomCrossApp f x ≫ (fibFib c').map ((G.map f).toFunctor.map g)

/--
The equality proof for identity morphisms in the target Grothendieck.
States that `(F.map (baseFib.map (𝟙 c))).obj ((fibFib c).obj x)` equals
`(fibFib c).obj ((G.map (𝟙 c)).obj x)`.
-/
abbrev FunctorBetweenBaseHomEqId (baseFib : FunctorBetweenBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenFibFib G F baseFib) :=
  ∀ (c : C) (x : G.obj c),
    (F.map (baseFib.map (𝟙 c))).toFunctor.obj ((fibFib c).obj x) =
      (fibFib c).obj ((G.map (𝟙 c)).toFunctor.obj x)

/--
Derive the identity equality from functor laws.
-/
lemma functorBetweenBaseHomEqIdProof
    (baseFib : FunctorBetweenBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenFibFib G F baseFib) :
    FunctorBetweenBaseHomEqId G F baseFib fibFib := by
  intro c x
  simp only [baseFib.map_id, F.map_id, G.map_id]
  rfl

/--
The equality proof for composite morphisms in the target Grothendieck.
States that the result of applying the composite is equal to applying
the morphisms sequentially.
-/
abbrev FunctorBetweenBaseHomEqComp (baseFib : FunctorBetweenBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenFibFib G F baseFib) :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'') (x : G.obj c),
    (F.map (baseFib.map (f ≫ g))).toFunctor.obj ((fibFib c).obj x) =
    (F.map (baseFib.map g)).toFunctor.obj
      ((F.map (baseFib.map f)).toFunctor.obj ((fibFib c).obj x))

/--
Derive the composition equality from functor laws.
-/
lemma functorBetweenBaseHomEqCompProof
    (baseFib : FunctorBetweenBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenFibFib G F baseFib) :
    FunctorBetweenBaseHomEqComp G F baseFib fibFib := by
  intro c c' c'' f g x
  simp only [baseFib.map_comp]
  exact congrFun (congrArg Functor.obj
    (congrArg (fun x => x.toFunctor) (F.map_comp (baseFib.map f) (baseFib.map g))))
    ((fibFib c).obj x)

/--
The identity coherence: `fibHomCrossApp (𝟙 c) x` equals the derived eqToHom.
-/
abbrev FunctorBetweenBaseHomId (baseFib : FunctorBetweenBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenFibFib G F baseFib)
    (fibHomCrossApp : FunctorBetweenFibHomCrossApp G F baseFib fibFib) :=
  ∀ (c : C) (x : G.obj c),
    fibHomCrossApp (𝟙 c) x =
      eqToHom (functorBetweenBaseHomEqIdProof G F baseFib fibFib c x)

/--
The equality proof relating `(G.map g).obj ((G.map f).obj x)` to `(G.map (f ≫ g)).obj x`.
This comes from `G.map_comp`.
-/
abbrev FunctorBetweenGMapCompEq (baseFib : FunctorBetweenBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenFibFib G F baseFib) :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'') (x : G.obj c),
    (fibFib c'').obj ((G.map g).toFunctor.obj ((G.map f).toFunctor.obj x)) =
    (fibFib c'').obj ((G.map (f ≫ g)).toFunctor.obj x)

/--
Derive the G.map_comp equality from functor laws.
-/
lemma functorBetweenGMapCompEqProof
    (baseFib : FunctorBetweenBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenFibFib G F baseFib) :
    FunctorBetweenGMapCompEq G F baseFib fibFib := by
  intro c c' c'' f g x
  exact congrArg (fibFib c'').obj
    (congrFun (congrArg Functor.obj
      (congrArg (fun x => x.toFunctor) (G.map_comp f g)).symm) x)

/--
The composition coherence: `fibHomCrossApp (f ≫ g) x` decomposes correctly.
-/
abbrev FunctorBetweenBaseHomComp (baseFib : FunctorBetweenBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenFibFib G F baseFib)
    (fibHomCrossApp : FunctorBetweenFibHomCrossApp G F baseFib fibFib) :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'') (x : G.obj c),
    fibHomCrossApp (f ≫ g) x =
    eqToHom (functorBetweenBaseHomEqCompProof G F baseFib fibFib f g x) ≫
    (F.map (baseFib.map g)).toFunctor.map (fibHomCrossApp f x) ≫
    fibHomCrossApp g ((G.map f).toFunctor.obj x) ≫
    eqToHom (functorBetweenGMapCompEqProof G F baseFib fibFib f g x)

/--
Bundled data for a functor between covariant Grothendieck constructions
`Grothendieck G ⥤ Grothendieck F`.

A functor `H : Grothendieck G ⥤ Grothendieck F` maps:
- Objects: `H.obj (c, x) = (baseFib.obj c, (fibFib c).obj x)`
- Morphisms: `H.map (f, φ) = (baseFib.map f, fibHomCrossApp f x ≫ (fibFib c').map φ)`

The coherence conditions ensure functoriality.
-/
structure FunctorBetweenData where
  /-- The base functor `C ⥤ D` -/
  baseFib : FunctorBetweenBaseFib (C := C) (D := D)
  /-- Fiber functors: for each `c : C`, a functor `G.obj c ⥤ F.obj (baseFib.obj c)` -/
  fibFib : FunctorBetweenFibFib G F baseFib
  /-- Cross-fiber morphisms: for each `f : c ⟶ c'` and `x : G.obj c` -/
  fibHomCrossApp : FunctorBetweenFibHomCrossApp G F baseFib fibFib
  /-- Naturality for cross-fiber morphisms -/
  fibHomCrossNat : FunctorBetweenFibHomCrossNat G F baseFib fibFib fibHomCrossApp
  /-- Identity coherence for cross-fiber morphisms -/
  baseHomId : FunctorBetweenBaseHomId G F baseFib fibFib fibHomCrossApp
  /-- Composition coherence for cross-fiber morphisms -/
  baseHomComp : FunctorBetweenBaseHomComp G F baseFib fibFib fibHomCrossApp

variable (data : FunctorBetweenData G F)

/-! ### Inner construction: fiber functors using FunctorTo

For each `c : C`, we build a functor `G.obj c ⥤ Grothendieck F` using
`FunctorTo`. The base functor is constant at `baseFib.obj c`, so the
coherence conditions become trivial.
-/

/--
The constant base functor for the inner FunctorTo construction.
For each `c : C`, this is the constant functor from `G.obj c` to `D`
at `baseFib.obj c`.
-/
def functorBetweenInnerBaseFunc (c : C) : G.obj c ⥤ D :=
  (Functor.const (G.obj c)).obj (data.baseFib.obj c)

/--
The fiber objects for the inner FunctorTo construction.
For `x : G.obj c`, this is `(fibFib c).obj x`.
-/
def functorBetweenInnerFib (c : C) (x : G.obj c) :
    F.obj ((functorBetweenInnerBaseFunc G F data c).obj x) :=
  (data.fibFib c).obj x

/--
The equality proof for `functorBetweenInnerHom`. Since the base functor is constant
(mapping everything to `𝟙`), `F.map (𝟙 d)` acts as the identity on objects.
-/
lemma functorBetweenInnerHom_eq (c : C) (x : G.obj c) :
    (F.map ((functorBetweenInnerBaseFunc G F data c).map (𝟙 x))).toFunctor.obj
      (functorBetweenInnerFib G F data c x) =
    functorBetweenInnerFib G F data c x := by
  simp only [functorBetweenInnerBaseFunc, functorBetweenInnerFib, Functor.const_obj_map]
  exact congrFun (congrArg Functor.obj (congrArg Cat.Hom.toFunctor (F.map_id _))) _

/--
The fiber morphisms for the inner FunctorTo construction.
Since the base functor is constant, the transport is trivial and
the fiber morphism is just `(fibFib c).map φ`.
-/
def functorBetweenInnerHom (c : C) {x y : G.obj c} (φ : x ⟶ y) :
    (F.map ((functorBetweenInnerBaseFunc G F data c).map φ)).toFunctor.obj
      (functorBetweenInnerFib G F data c x) ⟶
    functorBetweenInnerFib G F data c y :=
  eqToHom (functorBetweenInnerHom_eq G F data c x) ≫
    (data.fibFib c).map φ

set_option backward.isDefEq.respectTransparency false in
/--
Identity coherence for the inner FunctorTo. Trivial since the base is constant.
-/
theorem functorBetweenInnerHom_id (c : C) (x : G.obj c) :
    functorBetweenInnerHom G F data c (𝟙 x) =
      eqToHom (Grothendieck.functorToEqIdProof F
        (functorBetweenInnerBaseFunc G F data c)
        (functorBetweenInnerFib G F data c) x) := by
  simp only [functorBetweenInnerHom, functorBetweenInnerBaseFunc,
    functorBetweenInnerFib, Functor.const_obj_obj, Functor.const_obj_map,
    (data.fibFib c).map_id, Category.comp_id]

/--
When `H : A = 𝟭 C`, then `A.map f = f` (with appropriate `eqToHom` casts).
-/
lemma functor_map_of_eq_id {E : Type*} [Category E] {A : E ⥤ E}
    (H : A = 𝟭 E) {x y : E} (f : x ⟶ y) :
    A.map f = eqToHom (congrFun (congrArg Functor.obj H) x) ≫ f ≫
      eqToHom (congrFun (congrArg Functor.obj H) y).symm := by
  subst H
  simp

set_option backward.isDefEq.respectTransparency false in
/--
Composition coherence for the inner FunctorTo.
-/
theorem functorBetweenInnerHom_comp (c : C) {x y z : G.obj c}
    (φ : x ⟶ y) (ψ : y ⟶ z) :
    functorBetweenInnerHom G F data c (φ ≫ ψ) =
      eqToHom (Grothendieck.functorToEqCompProof F
        (functorBetweenInnerBaseFunc G F data c)
        (functorBetweenInnerFib G F data c) φ ψ) ≫
      (F.map ((functorBetweenInnerBaseFunc G F data c).map ψ)).toFunctor.map
        (functorBetweenInnerHom G F data c φ) ≫
      functorBetweenInnerHom G F data c ψ := by
  simp only [functorBetweenInnerHom, functorBetweenInnerBaseFunc, functorBetweenInnerFib,
    Functor.const_obj_obj, Functor.const_obj_map, (data.fibFib c).map_comp]
  have hFid : (F.map (𝟙 (data.baseFib.obj c))).toFunctor =
      𝟭 (F.obj (data.baseFib.obj c)) := congrArg Cat.Hom.toFunctor (F.map_id _)
  rw [functor_map_of_eq_id hFid]
  cat_disch

set_option backward.isDefEq.respectTransparency false in
/--
The proof term from `functorBetweenInnerHom` can be expressed explicitly.
Since the base functor is constant, `(F.map (𝟙 d)).obj x = x`.
-/
lemma functorBetweenInnerHom_proof (c : C) (x : G.obj c) :
    (F.map ((functorBetweenInnerBaseFunc G F data c).map (𝟙 x))).toFunctor.obj
      (functorBetweenInnerFib G F data c x) =
    functorBetweenInnerFib G F data c x := by
  simp only [functorBetweenInnerBaseFunc, Functor.const_obj_map]
  have hFid : (F.map (𝟙 (data.baseFib.obj c))).toFunctor =
      𝟭 (F.obj (data.baseFib.obj c)) := congrArg Cat.Hom.toFunctor (F.map_id _)
  simp only [hFid, Functor.id_obj]

set_option backward.isDefEq.respectTransparency false in
/--
The `eqToHom` from `functorBetweenInnerHom_eq` is identity on objects after applying `F.map_id`.
This is because `(F.map (𝟙 d)).obj x = (𝟭 _).obj x = x`.
-/
@[simp]
lemma eqToHom_functorBetweenInnerHom_eq (c : C) (x : G.obj c) :
    eqToHom (functorBetweenInnerHom_eq G F data c x) =
    eqToHom (congrFun (congrArg Functor.obj
      (congrArg Cat.Hom.toFunctor (F.map_id (data.baseFib.obj c)))) _) := by
  simp only [functorBetweenInnerBaseFunc, functorBetweenInnerFib, Functor.const_obj_map]

/--
Mapping `eqToHom (functorBetweenInnerHom_eq ...)` through `(F.map g).toFunctor.map`
yields an `eqToHom`.
-/
lemma functor_map_eqToHom_functorBetweenInnerHom_eq {c : C} (x : G.obj c)
    {d : D} (g : data.baseFib.obj c ⟶ d) :
    (F.map g).toFunctor.map (eqToHom (functorBetweenInnerHom_eq G F data c x)) =
    eqToHom (congrArg (F.map g).toFunctor.obj
      (functorBetweenInnerHom_eq G F data c x)) := by
  exact functor_map_eqToHom (F.map g).toFunctor (functorBetweenInnerHom_eq G F data c x)

/--
The equality `functorBetweenInnerHom_eq` becomes reflexive after applying
`(F.map g).toFunctor.obj`.
-/
lemma functorBetweenInnerHom_eq_transport {c : C} (x : G.obj c)
    {d : D} (g : data.baseFib.obj c ⟶ d) :
    (F.map g).toFunctor.obj ((F.map (𝟙 (data.baseFib.obj c))).toFunctor.obj
      ((data.fibFib c).obj x)) =
    (F.map g).toFunctor.obj ((data.fibFib c).obj x) := by
  have h : (F.map (𝟙 (data.baseFib.obj c))).toFunctor = 𝟭 _ :=
    congrArg Cat.Hom.toFunctor (F.map_id _)
  simp only [h, Functor.id_obj]

set_option backward.isDefEq.respectTransparency false in
/--
Transport of `functorBetweenInnerHom` through `(F.map g).toFunctor.map` relates to
the underlying `(data.fibFib c).toFunctor.map φ` via `eqToHom`.
-/
lemma functorBetweenInnerHom_transport {c : C} {x y : G.obj c} (φ : x ⟶ y)
    {d : D} (g : data.baseFib.obj c ⟶ d) :
    (F.map g).toFunctor.map (functorBetweenInnerHom G F data c φ) =
    eqToHom (functorBetweenInnerHom_eq_transport G F data x g) ≫
      (F.map g).toFunctor.map ((data.fibFib c).map φ) := by
  simp only [functorBetweenInnerHom, Functor.map_comp]
  rw [functor_map_eqToHom_functorBetweenInnerHom_eq]

/--
The inner FunctorToData for each `c : C`.
-/
def functorBetweenInnerToData (c : C) :
    Grothendieck.FunctorToData (C := D) (D := G.obj c) F where
  baseFunc := functorBetweenInnerBaseFunc G F data c
  fib := functorBetweenInnerFib G F data c
  hom := functorBetweenInnerHom G F data c
  hom_id := functorBetweenInnerHom_id G F data c
  hom_comp := functorBetweenInnerHom_comp G F data c

/--
The fiber functor for the outer FunctorFrom construction.
For each `c : C`, this gives a functor `G.obj c ⥤ Grothendieck F`.
-/
def functorBetweenFibFunc (c : C) : G.obj c ⥤ Grothendieck F :=
  Grothendieck.functorTo F (functorBetweenInnerToData G F data c)

/-! ### Outer construction: using FunctorFrom

Now we build the natural transformations between fiber functors and
prove the coherence conditions for FunctorFrom.
-/

/--
The natural transformation component for the outer FunctorFrom construction.
For `f : c ⟶ c'` and `x : G.obj c`, this is the morphism
`(functorBetweenFibFunc c).obj x ⟶ (functorBetweenFibFunc c').obj ((G.map f).obj x)`
in `Grothendieck F`.
-/
def functorBetweenHomNatApp {c c' : C} (f : c ⟶ c') (x : G.obj c) :
    (functorBetweenFibFunc G F data c).obj x ⟶
    (functorBetweenFibFunc G F data c').obj ((G.map f).toFunctor.obj x) :=
  ⟨data.baseFib.map f, data.fibHomCrossApp f x⟩

set_option backward.isDefEq.respectTransparency false in
/--
Naturality of `functorBetweenHomNatApp`: for `φ : x ⟶ y` in `G.obj c`,
the square commutes.
-/
theorem functorBetweenHomNat_naturality {c c' : C} (f : c ⟶ c')
    {x y : G.obj c} (φ : x ⟶ y) :
    (functorBetweenFibFunc G F data c).map φ ≫
      functorBetweenHomNatApp G F data f y =
    functorBetweenHomNatApp G F data f x ≫
      (functorBetweenFibFunc G F data c').map ((G.map f).toFunctor.map φ) := by
  refine Grothendieck.ext _ _ ?_ ?_
  · simp only [functorBetweenFibFunc, functorBetweenHomNatApp,
      Grothendieck.functorTo, Grothendieck.comp_base,
      functorBetweenInnerToData, functorBetweenInnerBaseFunc,
      Functor.const_obj_map]
    simp
  · simp only [functorBetweenFibFunc, functorBetweenHomNatApp,
      Grothendieck.functorTo, Grothendieck.comp_fiber,
      functorBetweenInnerToData, functorBetweenInnerBaseFunc,
      functorBetweenInnerFib, Functor.const_obj_obj, Functor.const_obj_map,
      functorBetweenInnerHom]
    simp only [Functor.map_comp, functor_map_eqToHom_functorBetweenInnerHom_eq]
    have hFmapId : (F.map (𝟙 (data.baseFib.obj c'))).toFunctor = 𝟭 _ := by
      simp only [F.map_id, Cat.id_eq_id]
    rw [functor_map_of_eq_id hFmapId]
    have hNat := data.fibHomCrossNat f φ
    cat_disch

/--
The natural transformation `functorBetweenFibFunc c ⟶ G.map f ⋙ functorBetweenFibFunc c'`
for the outer FunctorFrom construction.
-/
def functorBetweenHomNat {c c' : C} (f : c ⟶ c') :
    functorBetweenFibFunc G F data c ⟶
    (G.map f).toFunctor ⋙ functorBetweenFibFunc G F data c' where
  app := functorBetweenHomNatApp G F data f
  naturality _ _ φ := functorBetweenHomNat_naturality G F data f φ

set_option backward.isDefEq.respectTransparency false in
/--
Identity coherence for the outer FunctorFrom construction.
-/
theorem functorBetweenHomNat_id (c : C) :
    functorBetweenHomNat G F data (𝟙 c) =
      eqToHom (by simp only [CategoryTheory.Functor.map_id]; rfl) := by
  ext x
  refine Grothendieck.ext _ _ ?_ ?_
  · simp only [functorBetweenHomNat, functorBetweenHomNatApp, data.baseFib.map_id, eqToHom_app,
      functorBetweenFibFunc, Grothendieck.functorTo, functorBetweenInnerToData,
      functorBetweenInnerBaseFunc, Functor.const_obj_obj]
    simp
  · simp only [functorBetweenHomNat, functorBetweenHomNatApp,
      functorBetweenFibFunc, Grothendieck.functorTo, functorBetweenInnerToData,
      functorBetweenInnerFib]
    simp_rw [data.baseHomId c x]
    simp only [eqToHom_trans, Grothendieck.eqToHom_app_fiber]

/--
When a functor maps the base of an eqToHom between Grothendieck objects with
the same base, the result is the identity functor.
-/
lemma map_base_eqToHom_same_base {d : D} {x y : F.obj d}
    (h : (⟨d, x⟩ : Grothendieck F) = ⟨d, y⟩) :
    (F.map (eqToHom h).base).toFunctor = 𝟭 (F.obj d) := by
  simp only [Grothendieck.base_eqToHom, eqToHom_refl, F.map_id, Cat.id_eq_id]

/--
Composing a morphism with the base of an eqToHom between same-base Grothendieck
objects gives the original morphism.
-/
lemma comp_base_eqToHom_same_base {d d' : D} {x y : F.obj d}
    (f : d' ⟶ d) (h : (⟨d, x⟩ : Grothendieck F) = ⟨d, y⟩) :
    f ≫ (eqToHom h).base = f := by
  simp only [Grothendieck.base_eqToHom, eqToHom_refl, Category.comp_id]

end FunctorBetween

/-!
## Natural Transformations Between Functors of Grothendieck Constructions (Covariant)

For natural transformations `α : H ⟶ K` where `H K : Grothendieck G ⥤ Grothendieck F`,
we require the base functors to be equal (otherwise the codomain objects live in
different fibers). The natural transformation consists of fiber natural transformations
satisfying a coherence condition with the cross-fiber morphisms.
-/

section NatTransBetween

universe vC vD uC uD

variable {C : Type uC} [Category.{vC} C] (G : C ⥤ Cat.{vC, uC})
variable {D : Type uD} [Category.{vD} D] (F : D ⥤ Cat.{vD, uD})
variable (baseFib : FunctorBetweenBaseFib (C := C) (D := D))
variable (dataG dataH : FunctorBetweenData G F)

/--
For a natural transformation between functors with the same base, we need the
base functors to be equal.
-/
abbrev NatTransBetweenBaseFibEq :=
  dataG.baseFib = baseFib ∧ dataH.baseFib = baseFib

/--
The fiber natural transformation component: for each `c : C`, a natural
transformation `dataG.fibFib c ⟶ dataH.fibFib c`.
Since both fibFib functors go from `G.obj c` to `F.obj (baseFib.obj c)` when
the base functors are equal, this is well-typed (up to transport).
-/
abbrev NatTransBetweenFibNatApp
    (fibFibG : FunctorBetweenFibFib G F baseFib)
    (fibFibH : FunctorBetweenFibFib G F baseFib) :=
  ∀ (c : C) (x : G.obj c), (fibFibG c).obj x ⟶ (fibFibH c).obj x

/--
The naturality condition for fiber natural transformations within a single fiber.
For each `g : x ⟶ y` in `G.obj c`:
```
fibFibG c x --fibNatApp c x--> fibFibH c x
    |                              |
(fibFibG c).map g            (fibFibH c).map g
    |                              |
    v                              v
fibFibG c y --fibNatApp c y--> fibFibH c y
```
-/
abbrev NatTransBetweenFibNatNat
    (fibFibG fibFibH : FunctorBetweenFibFib G F baseFib)
    (fibNatApp : NatTransBetweenFibNatApp G F baseFib fibFibG fibFibH) :=
  ∀ (c : C) {x y : G.obj c} (g : x ⟶ y),
    (fibFibG c).map g ≫ fibNatApp c y = fibNatApp c x ≫ (fibFibH c).map g

/--
The coherence condition relating fiber natural transformations to cross-fiber
morphisms. For each `f : c ⟶ c'` and `x : G.obj c`:
```
(F.map (baseFib.map f)).obj (fibFibG c x) --fibHomCrossAppG f x-->
                                               fibFibG c' ((G.map f).obj x)
           |                                              |
(F.map (baseFib.map f)).map (fibNatApp c x)         fibNatApp c' ((G.map f).obj x)
           |                                              |
           v                                              v
(F.map (baseFib.map f)).obj (fibFibH c x) --fibHomCrossAppH f x-->
                                               fibFibH c' ((G.map f).obj x)
```
-/
abbrev NatTransBetweenCoherence
    (fibFibG fibFibH : FunctorBetweenFibFib G F baseFib)
    (fibNatApp : NatTransBetweenFibNatApp G F baseFib fibFibG fibFibH)
    (fibHomCrossAppG : FunctorBetweenFibHomCrossApp G F baseFib fibFibG)
    (fibHomCrossAppH : FunctorBetweenFibHomCrossApp G F baseFib fibFibH) :=
  ∀ {c c' : C} (f : c ⟶ c') (x : G.obj c),
    (F.map (baseFib.map f)).toFunctor.map (fibNatApp c x) ≫ fibHomCrossAppH f x =
    fibHomCrossAppG f x ≫ fibNatApp c' ((G.map f).toFunctor.obj x)

/--
Bundled data for a natural transformation between functors
`Grothendieck G ⥤ Grothendieck F` that share the same base functor.

This structure represents a natural transformation `α : H ⟶ K` where
both `H` and `K` have the same base functor `baseFib : C ⥤ D`.
-/
structure NatTransBetweenData
    (fibFibG fibFibH : FunctorBetweenFibFib G F baseFib)
    (fibHomCrossAppG : FunctorBetweenFibHomCrossApp G F baseFib fibFibG)
    (fibHomCrossAppH : FunctorBetweenFibHomCrossApp G F baseFib fibFibH) where
  /-- Component morphisms: for each `c` and `x`, a morphism between fibers -/
  fibNatApp : NatTransBetweenFibNatApp G F baseFib fibFibG fibFibH
  /-- Naturality within each fiber -/
  fibNatNat : NatTransBetweenFibNatNat G F baseFib fibFibG fibFibH fibNatApp
  /-- Coherence with cross-fiber morphisms -/
  coherence : NatTransBetweenCoherence G F baseFib fibFibG fibFibH fibNatApp
    fibHomCrossAppG fibHomCrossAppH

end NatTransBetween

/-!
## Functors Between Grothendieck Constructions (Contravariant Case)

This section defines bundled data for functors between two contravariant Grothendieck
constructions `GrothendieckContra' G' ⥤ GrothendieckContra' F'` where
`G' : Cᵒᵖ' ⥤ Cat` and `F' : Dᵒᵖ' ⥤ Cat`.
-/

section FunctorBetweenContra

universe vC vD uC uD

variable {C : Type uC} [Category.{vC} C] (G' : Cᵒᵖ' ⥤ Cat.{vC, uC})
variable {D : Type uD} [Category.{vD} D] (F' : Dᵒᵖ' ⥤ Cat.{vD, uD})

/--
The base-fiber functor for contravariant case: assigns to each `c : C` a base
object in `D`.
-/
abbrev FunctorBetweenContraBaseFib := C ⥤ D

/--
The fiber-fiber functor for contravariant case: for each `c : C`, a functor from
`G'.obj c` to `F'.obj (baseFib.obj c)`.
-/
abbrev FunctorBetweenContraFibFib
    (baseFib : FunctorBetweenContraBaseFib (C := C) (D := D)) :=
  ∀ c, G'.obj c ⥤ F'.obj (baseFib.obj c)

/--
The cross-fiber morphism component for contravariant case: for each `f : c ⟶ c'`
and `x' : G'.obj c'`, a morphism relating the transported fibers.

For `G' : Cᵒᵖ' ⥤ Cat`, we have `G'.map f : G'.obj c' ⥤ G'.obj c` (reversed).
So for `f : c ⟶ c'` and `x' : G'.obj c'`:
- `(G'.map f).obj x' : G'.obj c`
- `(fibFib c).obj ((G'.map f).obj x') : F'.obj (baseFib.obj c)`
- `(F'.map (baseFib.map f)).obj ((fibFib c').obj x') : F'.obj (baseFib.obj c)`
-/
abbrev FunctorBetweenContraFibHomCrossApp
    (baseFib : FunctorBetweenContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenContraFibFib G' F' baseFib) :=
  ∀ {c c' : C} (f : c ⟶ c') (x' : G'.obj c'),
    (fibFib c).obj ((G'.map f).toFunctor.obj x') ⟶
    (F'.map (baseFib.map f)).toFunctor.obj ((fibFib c').obj x')

/--
The naturality condition for cross-fiber morphisms in the contravariant case.
For `f : c ⟶ c'` and `g : x' ⟶ y'` in `G'.obj c'`:
- `(G'.map f).map g : (G'.map f).obj x' ⟶ (G'.map f).obj y'`
-/
abbrev FunctorBetweenContraFibHomCrossNat
    (baseFib : FunctorBetweenContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenContraFibFib G' F' baseFib)
    (fibHomCrossApp : FunctorBetweenContraFibHomCrossApp G' F' baseFib fibFib) :=
  ∀ {c c' : C} (f : c ⟶ c') {x' y' : G'.obj c'} (g : x' ⟶ y'),
    (fibFib c).map ((G'.map f).toFunctor.map g) ≫ fibHomCrossApp f y' =
    fibHomCrossApp f x' ≫ (F'.map (baseFib.map f)).toFunctor.map ((fibFib c').map g)

/--
The equality proof for identity morphisms in the contravariant Grothendieck.
For `𝟙 c` and `x : G'.obj c`, the cross-fiber morphism has type:
`(fibFib c).obj ((G'.map (𝟙 c)).obj x) ⟶ (F'.map (baseFib.map (𝟙 c))).obj ((fibFib c).obj x)`
Both sides should equal `(fibFib c).obj x` by functor identity laws.
-/
abbrev FunctorBetweenContraBaseHomEqId
    (baseFib : FunctorBetweenContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenContraFibFib G' F' baseFib) :=
  ∀ (c : C) (x : G'.obj c),
    (fibFib c).obj ((G'.map (𝟙 c)).toFunctor.obj x) =
    (F'.map (baseFib.map (𝟙 c))).toFunctor.obj ((fibFib c).obj x)

/--
Derive the identity equality from functor laws.
-/
lemma functorBetweenContraBaseHomEqIdProof
    (baseFib : FunctorBetweenContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenContraFibFib G' F' baseFib) :
    FunctorBetweenContraBaseHomEqId G' F' baseFib fibFib := by
  intro c x
  simp only [baseFib.map_id]
  have hG : G'.map (𝟙 c) = 𝟙 (G'.obj c) := G'.map_id c
  have hF : F'.map (𝟙 (baseFib.obj c)) = 𝟙 (F'.obj (baseFib.obj c)) :=
    F'.map_id (baseFib.obj c)
  simp only [hG, hF]
  rfl

/--
The equality proof for composite morphisms in the contravariant Grothendieck.
For `f : c ⟶ c'`, `g : c' ⟶ c''`, `x'' : G'.obj c''`:
- The composition path ends at
  `(F'.map (baseFib.map f)).obj ((F'.map (baseFib.map g)).obj ((fibFib c'').obj x''))`
- The composite path uses `(F'.map (baseFib.map (f ≫ g))).obj ((fibFib c'').obj x'')`
These are equal by `F'.map_comp` for contravariant functors.
-/
abbrev FunctorBetweenContraBaseHomEqComp
    (baseFib : FunctorBetweenContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenContraFibFib G' F' baseFib) :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'') (x'' : G'.obj c''),
    (F'.map (baseFib.map f)).toFunctor.obj
      ((F'.map (baseFib.map g)).toFunctor.obj ((fibFib c'').obj x'')) =
    (F'.map (baseFib.map (f ≫ g))).toFunctor.obj ((fibFib c'').obj x'')

/--
Derive the composition equality from functor laws.
For contravariant functors, F'.map_comp g f = F'.map f ⋙ F'.map g.
-/
lemma functorBetweenContraBaseHomEqCompProof
    (baseFib : FunctorBetweenContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenContraFibFib G' F' baseFib) :
    FunctorBetweenContraBaseHomEqComp G' F' baseFib fibFib := by
  intro c c' c'' f g x''
  simp only [baseFib.map_comp]
  have h := congrArg Cat.Hom.toFunctor (F'.map_comp (baseFib.map g) (baseFib.map f))
  exact (congrFun (congrArg Functor.obj h) ((fibFib c'').obj x'')).symm

/--
The equality proof relating `(G'.map f).obj ((G'.map g).obj x'')` to the
composite map applied to `x''` for the contravariant case.
For contravariant functors with `G' : Cᵒᵖ' ⥤ Cat`, and C-morphisms `f : c ⟶ c'`
and `g : c' ⟶ c''`:
- `G'.map f : G'.obj c' ⥤ G'.obj c`
- `G'.map g : G'.obj c'' ⥤ G'.obj c'`
- `G'.map_comp` gives `G'.map (g ≫_{Cᵒᵖ'} f) = G'.map g ⋙ G'.map f`
- Since `Cᵒᵖ'` reverses composition, `g ≫_{Cᵒᵖ'} f = f ≫_C g` when viewed
  as C-morphisms
-/
abbrev FunctorBetweenContraGMapCompEq
    (baseFib : FunctorBetweenContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenContraFibFib G' F' baseFib) :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'') (x'' : G'.obj c''),
    (fibFib c).obj ((G'.map f).toFunctor.obj ((G'.map g).toFunctor.obj x'')) =
    (fibFib c).obj ((G'.map (@CategoryStruct.comp C _ c c' c'' f g)).toFunctor.obj x'')

/--
Derive the G'.map_comp equality from functor laws.
For contravariant functors, G'.map_comp g f = G'.map f ⋙ G'.map g.
-/
lemma functorBetweenContraGMapCompEqProof
    (baseFib : FunctorBetweenContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenContraFibFib G' F' baseFib) :
    FunctorBetweenContraGMapCompEq G' F' baseFib fibFib := by
  intro c c' c'' f g x''
  have h := congrArg Cat.Hom.toFunctor (G'.map_comp g f)
  exact congrArg (fibFib c).obj (congrFun (congrArg Functor.obj h) x'').symm

/--
The identity coherence: `fibHomCrossApp (𝟙 c) x` equals the derived eqToHom.
For `𝟙 c` and `x : G'.obj c`, the cross-fiber morphism `fibHomCrossApp (𝟙 c) x`
should be the identity (via `eqToHom`).
-/
abbrev FunctorBetweenContraBaseHomId
    (baseFib : FunctorBetweenContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenContraFibFib G' F' baseFib)
    (fibHomCrossApp : FunctorBetweenContraFibHomCrossApp G' F' baseFib fibFib) :=
  ∀ (c : C) (x : G'.obj c),
    fibHomCrossApp (𝟙 c) x =
      eqToHom (functorBetweenContraBaseHomEqIdProof G' F' baseFib fibFib c x)

/--
The composition coherence for the contravariant case.
For `f : c ⟶ c'`, `g : c' ⟶ c''`, `x'' : G'.obj c''`:
- The stepwise path goes through:
  1. `fibHomCrossApp f ((G'.map g).obj x'')` to get to `(F'.map (baseFib.map f)).obj (...)`
  2. `(F'.map (baseFib.map f)).map (fibHomCrossApp g x'')` to apply the second cross-fiber
  3. `eqToHom` to relate endpoints
-/
abbrev FunctorBetweenContraBaseHomComp
    (baseFib : FunctorBetweenContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenContraFibFib G' F' baseFib)
    (fibHomCrossApp : FunctorBetweenContraFibHomCrossApp G' F' baseFib fibFib) :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'') (x'' : G'.obj c''),
    eqToHom (functorBetweenContraGMapCompEqProof G' F' baseFib fibFib f g x'') ≫
      fibHomCrossApp (@CategoryStruct.comp C _ c c' c'' f g) x'' =
    fibHomCrossApp f ((G'.map g).toFunctor.obj x'') ≫
    (F'.map (baseFib.map f)).toFunctor.map (fibHomCrossApp g x'') ≫
    eqToHom (functorBetweenContraBaseHomEqCompProof G' F' baseFib fibFib f g x'')

/--
Bundled data for a functor between contravariant Grothendieck constructions
`GrothendieckContra' G' ⥤ GrothendieckContra' F'`.
-/
structure FunctorBetweenContraData where
  /-- The base functor `C ⥤ D` -/
  baseFib : FunctorBetweenContraBaseFib (C := C) (D := D)
  /-- Fiber functors: for each `c : C`, a functor `G'.obj c ⥤ F'.obj (baseFib.obj c)` -/
  fibFib : FunctorBetweenContraFibFib G' F' baseFib
  /-- Cross-fiber morphisms -/
  fibHomCrossApp : FunctorBetweenContraFibHomCrossApp G' F' baseFib fibFib
  /-- Naturality for cross-fiber morphisms -/
  fibHomCrossNat : FunctorBetweenContraFibHomCrossNat G' F' baseFib fibFib fibHomCrossApp
  /-- Identity coherence for cross-fiber morphisms -/
  baseHomId : FunctorBetweenContraBaseHomId G' F' baseFib fibFib fibHomCrossApp
  /-- Composition coherence for cross-fiber morphisms -/
  baseHomComp : FunctorBetweenContraBaseHomComp G' F' baseFib fibFib fibHomCrossApp

end FunctorBetweenContra

/-!
## Natural Transformations Between Functors on Contravariant Grothendieck
Constructions

This section defines bundled data for natural transformations between functors
`GrothendieckContra' G' ⥤ GrothendieckContra' F'` that share the same base
functor.
-/

section NatTransBetweenContra

universe vC vD uC uD

variable {C : Type uC} [Category.{vC} C] (G' : Cᵒᵖ' ⥤ Cat.{vC, uC})
variable {D : Type uD} [Category.{vD} D] (F' : Dᵒᵖ' ⥤ Cat.{vD, uD})
variable (baseFib : FunctorBetweenContraBaseFib (C := C) (D := D))

/--
The component morphisms of a natural transformation between functors on
contravariant Grothendieck constructions. For each `c : C` and `x : G'.obj c`,
a morphism from `fibFibG c x` to `fibFibH c x` in `F'.obj (baseFib.obj c)`.
-/
abbrev NatTransBetweenContraFibNatApp
    (fibFibG fibFibH : FunctorBetweenContraFibFib G' F' baseFib) :=
  ∀ (c : C) (x : G'.obj c), (fibFibG c).obj x ⟶ (fibFibH c).obj x

/--
The naturality condition for the fiber components. For each `c : C` and
morphism `g : x ⟶ y` in `G'.obj c`:
```
fibFibG c x --fibNatApp c x--> fibFibH c x
    |                              |
(fibFibG c).map g           (fibFibH c).map g
    |                              |
    v                              v
fibFibG c y --fibNatApp c y--> fibFibH c y
```
-/
abbrev NatTransBetweenContraFibNatNat
    (fibFibG fibFibH : FunctorBetweenContraFibFib G' F' baseFib)
    (fibNatApp : NatTransBetweenContraFibNatApp G' F' baseFib fibFibG fibFibH) :=
  ∀ (c : C) {x y : G'.obj c} (g : x ⟶ y),
    (fibFibG c).map g ≫ fibNatApp c y = fibNatApp c x ≫ (fibFibH c).map g

/--
The coherence condition relating fiber natural transformations to cross-fiber
morphisms. For each `f : c ⟶ c'` and `x' : G'.obj c'`:
```
(fibFibG c).obj ((G'.map f).obj x') --fibHomCrossAppG f x'-->
                           (F'.map (baseFib.map f)).obj ((fibFibG c').obj x')
           |                                              |
fibNatApp c ((G'.map f).obj x')    (F'.map (baseFib.map f)).map (fibNatApp c' x')
           |                                              |
           v                                              v
(fibFibH c).obj ((G'.map f).obj x') --fibHomCrossAppH f x'-->
                           (F'.map (baseFib.map f)).obj ((fibFibH c').obj x')
```
-/
abbrev NatTransBetweenContraCoherence
    (fibFibG fibFibH : FunctorBetweenContraFibFib G' F' baseFib)
    (fibNatApp : NatTransBetweenContraFibNatApp G' F' baseFib fibFibG fibFibH)
    (fibHomCrossAppG : FunctorBetweenContraFibHomCrossApp G' F' baseFib fibFibG)
    (fibHomCrossAppH : FunctorBetweenContraFibHomCrossApp G' F' baseFib fibFibH) :=
  ∀ {c c' : C} (f : c ⟶ c') (x' : G'.obj c'),
    fibHomCrossAppG f x' ≫ (F'.map (baseFib.map f)).toFunctor.map (fibNatApp c' x') =
    fibNatApp c ((G'.map f).toFunctor.obj x') ≫ fibHomCrossAppH f x'

/--
Bundled data for a natural transformation between functors
`GrothendieckContra' G' ⥤ GrothendieckContra' F'` that share the same base
functor.

This structure represents a natural transformation `α : H ⟶ K` where
both `H` and `K` have the same base functor `baseFib : C ⥤ D`.
-/
structure NatTransBetweenContraData
    (fibFibG fibFibH : FunctorBetweenContraFibFib G' F' baseFib)
    (fibHomCrossAppG : FunctorBetweenContraFibHomCrossApp G' F' baseFib fibFibG)
    (fibHomCrossAppH : FunctorBetweenContraFibHomCrossApp G' F' baseFib fibFibH)
    where
  /-- Component morphisms: for each `c` and `x`, a morphism between fibers -/
  fibNatApp : NatTransBetweenContraFibNatApp G' F' baseFib fibFibG fibFibH
  /-- Naturality within each fiber -/
  fibNatNat : NatTransBetweenContraFibNatNat G' F' baseFib fibFibG fibFibH fibNatApp
  /-- Coherence with cross-fiber morphisms -/
  coherence : NatTransBetweenContraCoherence G' F' baseFib fibFibG fibFibH fibNatApp
    fibHomCrossAppG fibHomCrossAppH

end NatTransBetweenContra

/-!
## Lax Natural Transformations and the Lax Functor Category

This section defines lax natural transformations between Cat-valued functors
and shows that they form a category. The Grothendieck construction is then
shown to be functorial with respect to this category.

A lax natural transformation `α : G ⟹ F` between `G F : C ⥤ Cat` consists of:
- Component functors `α.app c : G.obj c ⥤ F.obj c` for each `c : C`
- Laxity morphisms `α.lax f x : (F.map f).obj ((α.app c).obj x) ⟶
  (α.app c').obj ((G.map f).obj x)` for each `f : c ⟶ c'` and `x : G.obj c`
- Naturality and coherence conditions

These correspond exactly to functors `Grothendieck G ⥤ Grothendieck F` that
act as the identity on the base category.
-/

section LaxNatTrans

universe vC uC vF uF

variable {C : Type uC} [Category.{vC} C]
variable (G F : C ⥤ Cat.{vF, uF})

/--
Component functors for a lax natural transformation.
For each `c : C`, a functor from `G.obj c` to `F.obj c`.
-/
abbrev LaxNatTransApp := ∀ c, G.obj c ⥤ F.obj c

variable {G F}
variable (app : LaxNatTransApp G F)

/--
Laxity morphism components for a lax natural transformation `α : G ⟹ F`.

Given a morphism `f : c ⟶ c'` in `C` and an element `x` in the fiber `G.obj c`,
there are two ways to obtain an element of `F.obj c'`:

1. **Apply α first, then transport via F**: Apply the component functor
   `app c : G.obj c ⥤ F.obj c` to get `(app c).obj x` in `F.obj c`, then
   transport along f using F to get `(F.map f).obj ((app c).obj x)` in
   `F.obj c'`.

2. **Transport via G first, then apply α**: Transport x along f using G
   to get `(G.map f).obj x` in `G.obj c'`, then apply the component functor
   `app c' : G.obj c' ⥤ F.obj c'` to get `(app c').obj ((G.map f).obj x)`
   in `F.obj c'`.

The laxity morphism goes from (1) to (2):

  `(F.map f).obj ((app c).obj x) ⟶ (app c').obj ((G.map f).obj x)`

This matches the nLab convention for lax natural transformations: for
`α : F ⇒ G`, the 2-cell `α_f : G(f) ∘ α_A ⇒ α_B ∘ F(f)` goes from the
"target-functor-then-transport" composite to the "transport-then-target-functor"
composite. (Our notation `G ⟹ F` reverses the roles of F and G relative
to nLab's `F ⇒ G`.)
-/
abbrev LaxNatTransLaxApp :=
  ∀ {c c' : C} (f : c ⟶ c') (x : G.obj c),
    (F.map f).toFunctor.obj ((app c).obj x) ⟶
    (app c').obj ((G.map f).toFunctor.obj x)

variable (laxApp : LaxNatTransLaxApp app)

/--
Naturality of laxity morphisms: for each `f : c ⟶ c'` and `φ : x ⟶ y`,
the appropriate square commutes.
-/
abbrev LaxNatTransLaxNat :=
  ∀ {c c' : C} (f : c ⟶ c') {x y : G.obj c} (φ : x ⟶ y),
    (F.map f).toFunctor.map ((app c).map φ) ≫ laxApp f y =
    laxApp f x ≫ (app c').map ((G.map f).toFunctor.map φ)

/--
Equality proof for identity laxity. States that
`(F.map (𝟙 c)).obj ((app c).obj x) = (app c).obj ((G.map (𝟙 c)).obj x)`.
-/
abbrev LaxNatTransIdEq :=
  ∀ (c : C) (x : G.obj c),
    (F.map (𝟙 c)).toFunctor.obj ((app c).obj x) =
    (app c).obj ((G.map (𝟙 c)).toFunctor.obj x)

/--
Derive the identity equality from functor laws.
-/
lemma laxNatTransIdEqProof : LaxNatTransIdEq app := by
  intro c x
  have hF : (F.map (𝟙 c)).toFunctor = 𝟭 _ :=
    congrArg Cat.Hom.toFunctor (F.map_id c) |>.trans (Cat.id_eq_id (F.obj c))
  have hG : (G.map (𝟙 c)).toFunctor = 𝟭 _ :=
    congrArg Cat.Hom.toFunctor (G.map_id c) |>.trans (Cat.id_eq_id (G.obj c))
  simp only [hF, hG, Functor.id_obj]

/--
Identity coherence: `laxApp (𝟙 c) x` equals the canonical eqToHom.
-/
abbrev LaxNatTransLaxId :=
  ∀ (c : C) (x : G.obj c),
    laxApp (𝟙 c) x = eqToHom (laxNatTransIdEqProof app c x)

/--
Equality proof for composition laxity.
-/
abbrev LaxNatTransCompEq :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'') (x : G.obj c),
    (F.map (f ≫ g)).toFunctor.obj ((app c).obj x) =
    (F.map g).toFunctor.obj ((F.map f).toFunctor.obj ((app c).obj x))

/--
Derive the composition equality from functor laws.
-/
lemma laxNatTransCompEqProof : LaxNatTransCompEq app := by
  intro c c' c'' f g x
  have h := congrArg Cat.Hom.toFunctor (F.map_comp f g)
  exact congrFun (congrArg Functor.obj h) ((app c).obj x)

/--
Equality for the right side of composition coherence.
-/
abbrev LaxNatTransCompEqRight :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'') (x : G.obj c),
    (app c'').obj ((G.map g).toFunctor.obj ((G.map f).toFunctor.obj x)) =
    (app c'').obj ((G.map (f ≫ g)).toFunctor.obj x)

/--
Derive the right composition equality from functor laws.
-/
lemma laxNatTransCompEqRightProof : LaxNatTransCompEqRight app := by
  intro c c' c'' f g x
  have h := congrArg Cat.Hom.toFunctor (G.map_comp f g)
  exact congrArg (app c'').obj (congrFun (congrArg Functor.obj h.symm) x)

/--
Composition coherence: `laxApp (f ≫ g) x` decomposes as eqToHom,
transported `laxApp f`, then `laxApp g`, then eqToHom.
-/
abbrev LaxNatTransLaxComp :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'') (x : G.obj c),
    laxApp (f ≫ g) x =
    eqToHom (laxNatTransCompEqProof app f g x) ≫
    (F.map g).toFunctor.map (laxApp f x) ≫
    laxApp g ((G.map f).toFunctor.obj x) ≫
    eqToHom (laxNatTransCompEqRightProof app f g x)

/--
Bundled data for a lax natural transformation `G ⟹ F` between Cat-valued
functors `G F : C ⥤ Cat`.

A lax natural transformation consists of:
- Component functors for each object
- Laxity morphisms for each morphism
- Naturality and coherence conditions

These correspond to functors `Grothendieck G ⥤ Grothendieck F` that are
identity on the base category.
-/
structure LaxNatTransData (G F : C ⥤ Cat.{vF, uF}) where
  /-- Component functors: for each `c`, a functor `G.obj c ⥤ F.obj c` -/
  app : LaxNatTransApp G F
  /-- Laxity morphisms: for each `f` and `x`, a morphism between fibers -/
  laxApp : LaxNatTransLaxApp app
  /-- Naturality of laxity morphisms -/
  laxNat : LaxNatTransLaxNat app laxApp
  /-- Identity coherence -/
  laxId : LaxNatTransLaxId app laxApp
  /-- Composition coherence -/
  laxComp : LaxNatTransLaxComp app laxApp

variable (α : LaxNatTransData G F)

/--
Construct a functor `Grothendieck G ⥤ Grothendieck F` from a lax natural
transformation. This functor is the identity on base objects.
-/
def LaxNatTransData.toFunctor : Grothendieck G ⥤ Grothendieck F where
  obj X := ⟨X.base, (α.app X.base).obj X.fiber⟩
  map {X Y} f := ⟨f.base, α.laxApp f.base X.fiber ≫ (α.app Y.base).map f.fiber⟩
  map_id X := by
    refine Grothendieck.ext _ _ ?_ ?_
    · simp only [Grothendieck.id_base]
    · simp only [Grothendieck.id_fiber, Grothendieck.id_base, α.laxId, eqToHom_map,
        eqToHom_trans]
  map_comp {X Y Z} f g := by
    refine Grothendieck.ext _ _ ?_ ?_
    · simp only [Grothendieck.comp_base]
    · simp only [Grothendieck.comp_fiber, Grothendieck.comp_base]
      simp only [α.laxComp f.base g.base X.fiber]
      simp only [(α.app Z.base).map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc,
        eqToHom_refl, Category.id_comp]
      unfold Cat.Hom.toFunctor
      simp only [Functor.map_comp, Category.assoc]
      have h : (F.map g.base).toFunctor.map ((α.app Y.base).map f.fiber) ≫
          α.laxApp g.base Y.fiber =
          α.laxApp g.base ((G.map f.base).toFunctor.obj X.fiber) ≫
          (α.app Z.base).map ((G.map g.base).toFunctor.map f.fiber) := α.laxNat g.base f.fiber
      unfold Cat.Hom.toFunctor at h
      simp only [← Category.assoc]
      congr 1
      simp only [Category.assoc]
      congr 1
      congr 1
      exact h.symm

/--
The functor from a lax nat trans is identity on base.
-/
theorem LaxNatTransData.toFunctor_base (X : Grothendieck G) :
    (α.toFunctor.obj X).base = X.base := rfl

/--
The functor from a lax nat trans is identity on base morphisms.
-/
theorem LaxNatTransData.toFunctor_map_base {X Y : Grothendieck G} (f : X ⟶ Y) :
    (α.toFunctor.map f).base = f.base := rfl

/--
The identity lax natural transformation.
-/
def LaxNatTransData.id (G : C ⥤ Cat.{vF, uF}) : LaxNatTransData G G where
  app c := 𝟭 (G.obj c)
  laxApp f x := eqToHom (by simp only [Functor.id_obj])
  laxNat {c c'} f {x y} φ := by
    simp only [Functor.id_obj, Functor.id_map, eqToHom_refl, Category.id_comp, Category.comp_id]
  laxId c x := rfl
  laxComp {c c' c''} f g x := by
    unfold Cat.Hom.toFunctor
    simp only [Functor.id_obj, eqToHom_refl, Category.id_comp, CategoryTheory.Functor.map_id,
      eqToHom_trans]

set_option backward.isDefEq.respectTransparency false in
/--
Composition of lax natural transformations.

Given `α : G ⟹ H` and `β : H ⟹ K`, their composition `α ⋙ β : G ⟹ K` has:
- Component functors: `(α ⋙ β).app c = α.app c ⋙ β.app c`
- Laxity: `β.laxApp f (α.app c x) ≫ β.app c'.map (α.laxApp f x)`
-/
def LaxNatTransData.comp {G H K : C ⥤ Cat.{vF, uF}}
    (α : LaxNatTransData G H) (β : LaxNatTransData H K) :
    LaxNatTransData G K where
  app c := α.app c ⋙ β.app c
  laxApp {c c'} f x :=
    β.laxApp f ((α.app c).obj x) ≫ (β.app c').map (α.laxApp f x)
  laxNat {c c'} f {x y} φ := by
    simp only [Functor.comp_obj, Functor.comp_map, Category.assoc]
    have hα : (H.map f).toFunctor.map ((α.app c).map φ) ≫ α.laxApp f y =
        α.laxApp f x ≫ (α.app c').map ((G.map f).toFunctor.map φ) := α.laxNat f φ
    have hβ : (K.map f).toFunctor.map ((β.app c).map ((α.app c).map φ)) ≫
        β.laxApp f ((α.app c).obj y) =
        β.laxApp f ((α.app c).obj x) ≫
        (β.app c').map ((H.map f).toFunctor.map ((α.app c).map φ)) :=
        β.laxNat f ((α.app c).map φ)
    rw [← Category.assoc ((K.map f).toFunctor.map _) _ _, hβ, Category.assoc,
        ← Functor.map_comp, hα, Functor.map_comp]
  laxId c x := by
    simp only [Functor.comp_obj, α.laxId, eqToHom_map, β.laxId, eqToHom_trans]
  laxComp {c c' c''} f g x := by
    simp only [α.laxComp f g x, β.laxComp f g ((α.app c).obj x)]
    simp only [Functor.map_comp, (β.app c'').map_comp, eqToHom_map, Category.assoc,
      eqToHom_trans_assoc]
    have hβ : (K.map g).toFunctor.map ((β.app c').map (α.laxApp f x)) ≫
            β.laxApp g ((α.app c').obj ((G.map f).toFunctor.obj x)) =
          β.laxApp g ((H.map f).toFunctor.obj ((α.app c).obj x)) ≫
            (β.app c'').map ((H.map g).toFunctor.map (α.laxApp f x)) :=
        β.laxNat g (α.laxApp f x)
    congr 1
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc, eqToHom_refl, Category.id_comp]
    congr 1
    simp only [← Category.assoc]
    congr 1
    exact hβ.symm

/-!
### Whiskering Operations for Lax Natural Transformations

These operations compose lax natural transformations with functors, analogous
to `whiskerLeft` and `whiskerRight` for ordinary natural transformations.
-/

variable {D : Type uC} [Category.{vC} D]

set_option backward.isDefEq.respectTransparency false in
/--
Left whiskering: precompose a lax natural transformation with a functor.

Given `H : D ⥤ C` and `α : LaxNatTransData G F` where `G F : C ⥤ Cat`,
produces `LaxNatTransData (H ⋙ G) (H ⋙ F)`.

The component at `d : D` is `α.app (H.obj d)`, and the laxity morphism for
`f : d ⟶ d'` is `α.laxApp (H.map f)`.
-/
def LaxNatTransData.whiskerLeft (H : D ⥤ C) (α : LaxNatTransData G F) :
    LaxNatTransData (H ⋙ G) (H ⋙ F) where
  app d := α.app (H.obj d)
  laxApp f x := α.laxApp (H.map f) x
  laxNat {d d'} f {x y} φ := α.laxNat (H.map f) φ
  laxId d x := by
    simp only [Functor.comp_obj, Functor.comp_map]
    convert α.laxId (H.obj d) x using 2 <;> simp [H.map_id]
  laxComp {d d' d''} f g x := by
    simp only [Functor.comp_obj, Functor.comp_map]
    have h := α.laxComp (H.map f) (H.map g) x
    simp only at h ⊢
    grind

/--
Left whiskering respects identity lax natural transformations.
-/
theorem LaxNatTransData.whiskerLeft_id (H : D ⥤ C) :
    (LaxNatTransData.id G).whiskerLeft H = LaxNatTransData.id (H ⋙ G) := by
  simp only [whiskerLeft, LaxNatTransData.id]
  congr

/--
Left whiskering respects composition of lax natural transformations.
-/
theorem LaxNatTransData.whiskerLeft_comp (H : D ⥤ C)
    {K : C ⥤ Cat.{vF, uF}}
    (α : LaxNatTransData G F) (β : LaxNatTransData F K) :
    (α.comp β).whiskerLeft H = (α.whiskerLeft H).comp (β.whiskerLeft H) := rfl

/-!
### Grothendieck Functor from Lax Natural Transformation to Constant Target

Given a lax natural transformation `α : LaxNatTransData G ((Functor.const C).obj D)` where
the target is a constant functor at `D : Cat`, and a functor `H : ↑D ⥤ Cat`, we construct
a functor `C ⥤ Cat` whose fiber at `c` is `Grothendieck (α.app c ⋙ H)`.

The construction uses:
- `α.laxApp f x` to transport fiber elements along `f : c ⟶ c'`
- `α.laxNat f φ` for naturality of the transition functor
- `α.laxId` and `α.laxComp` for the functor identity and composition laws
-/

variable (D : Cat.{vF, uF})
variable (α : LaxNatTransData G ((Functor.const C).obj D))
variable (H : ↑D ⥤ Cat.{vF, uF})

/--
Applying `eqToHom h : A ⥤ B` in `Cat` to an object `x : A` gives heterogeneous
equality with the original object. This uses `cases` to eliminate the equality.
-/
lemma eqToHom_obj_heq (A B : Cat) (h : A = B) (x : A.α) :
    HEq ((eqToHom h).toFunctor.obj x) x := by
  cases h
  rfl

/--
For a functor `eqToHom h : C ⥤ D` in `Cat` where `h : C = D`, applying it to
a morphism gives something HEq to the original morphism.
-/
lemma eqToHom_map_heq' {C D : Cat} (h : C = D) {x y : C} (f : x ⟶ y) :
    (eqToHom h).toFunctor.map f ≍ f := by
  subst h
  rfl

/--
Version of `eqToHom_map_heq'` where the functor is only propositionally equal
to `eqToHom`.
-/
lemma functor_map_heq_of_eq_eqToHom' {C D : Cat} (h : C = D)
    (G : ↑C ⥤ ↑D) (hG : G = (eqToHom h).toFunctor) {x y : ↑C} (f : x ⟶ y) :
    G.map f ≍ f := by
  subst hG
  exact eqToHom_map_heq' h f

set_option backward.isDefEq.respectTransparency false in
/--
When `G.map (𝟙 c) = 𝟭 (G.obj c)` (via functor identity law and Cat.id_eq_id),
the `.map` of `G.map (𝟙 c)` is HEq to identity on morphisms.
-/
lemma functor_map_id_heq {C : Type*} [Category C] (G : C ⥤ Cat) (c : C)
    {X Y : (G.obj c).α} (f : X ⟶ Y) :
    HEq ((G.map (𝟙 c)).toFunctor.map f) f := by
  have hG : (G.map (𝟙 c)).toFunctor = 𝟭 (G.obj c) := by
    rw [G.map_id]
    exact Cat.id_eq_id (G.obj c)
  unfold Cat.Hom.toFunctor at hG ⊢
  rw [hG, Functor.id_map]

set_option backward.isDefEq.respectTransparency false in
/--
When `G.map (f ≫ g) = G.map f ⋙ G.map g` (functor composition law), the `.map`
of `G.map (f ≫ g)` on a morphism `h` is HEq to composing the maps.
-/
lemma functor_map_comp_heq {C : Type*} [Category C] (G : C ⥤ Cat) {c c' c'' : C}
    (f : c ⟶ c') (g : c' ⟶ c'') {X Y : (G.obj c).α} (h : X ⟶ Y) :
    HEq ((G.map (f ≫ g)).toFunctor.map h)
      ((G.map g).toFunctor.map ((G.map f).toFunctor.map h)) := by
  have hComp : (G.map (f ≫ g)).toFunctor = (G.map f).toFunctor ⋙ (G.map g).toFunctor := by
    have := congrArg Cat.Hom.toFunctor (G.map_comp f g)
    simp only [Cat.comp_eq_comp] at this
    exact this
  unfold Cat.Hom.toFunctor at hComp ⊢
  rw [hComp, Functor.comp_map]

/--
When two functors `F G : C ⥤ D` are equal, their maps on a morphism are HEq.
-/
lemma functor_eq_map_heq {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} (h : F = G) {X Y : C} (f : X ⟶ Y) :
    HEq (F.map f) (G.map f) := by
  cases h
  rfl

/--
Lifting HEq through function application.

If `f : α → β` and `g : α' → β'` are HEq (via source/target equalities), then
`f x` and `g y` are HEq when x and y are HEq.
-/
lemma function_app_heq.{uα, uβ} {α α' : Type uα} {β β' : Type uβ}
    {f : α → β} {g : α' → β'}
    (hαα' : α = α') (hββ' : β = β') (hfg : HEq f g) {x : α} {y : α'} (hxy : HEq x y) :
    HEq (f x) (g y) := by
  cases hαα'
  cases hββ'
  cases hfg
  cases hxy
  rfl

/--
Lifting HEq through functor map.

If morphisms `f` and `g` are HEq and the domain/codomain equalities hold,
applying `F.map` to both preserves HEq.
-/
lemma functor_map_arg_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (hX : X = X') (hY : Y = Y') (hfg : HEq f g) :
    HEq (F.map f) (F.map g) := by
  cases hX
  cases hY
  cases hfg
  rfl

/--
Simplified lax morphism for constant target.

When `F = (Functor.const C).obj D`, we have `F.map f = 𝟙 D`, so
`α.laxApp f x : (α.app c).obj x ⟶ (α.app c').obj ((G.map f).obj x)` in `↑D`.
-/
abbrev LaxNatTransData.laxAppConst {c c' : C} (f : c ⟶ c') (x : G.obj c) :
    (α.app c).obj x ⟶ (α.app c').obj ((G.map f).toFunctor.obj x) :=
  α.laxApp f x

/--
Object map for the Grothendieck transition functor.
Maps `(x, e) : Grothendieck (α.app c ⋙ H)` to `Grothendieck (α.app c' ⋙ H)`.
-/
def LaxNatTransData.grothendieckTransitionObj {c c' : C} (f : c ⟶ c')
    (X : Grothendieck (α.app c ⋙ H)) : Grothendieck (α.app c' ⋙ H) :=
  ⟨(G.map f).toFunctor.obj X.base,
   (H.map (α.laxAppConst D f X.base)).toFunctor.obj X.fiber⟩

set_option backward.isDefEq.respectTransparency false in
/--
Fiber coherence equation for the Grothendieck transition morphism.

Uses the lax naturality condition to show that applying the transition morphism
and then the base map is equal to applying the base map and then the transition.
-/
theorem LaxNatTransData.grothendieckTransition_fiber_eq {c c' : C} (f : c ⟶ c')
    {X Y : Grothendieck (α.app c ⋙ H)} (g : X ⟶ Y) :
    ((α.app c' ⋙ H).map ((G.map f).toFunctor.map g.base)).toFunctor.obj
      ((H.map (α.laxAppConst D f X.base)).toFunctor.obj X.fiber) =
    (H.map (α.laxAppConst D f Y.base)).toFunctor.obj
      (((α.app c ⋙ H).map g.base).toFunctor.obj X.fiber) := by
  simp only [Functor.comp_obj, Functor.comp_map]
  have laxNat := α.laxNat f g.base
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Cat.id_eq_id,
    Functor.id_map] at laxNat
  have h := congrArg (H.map ·) laxNat
  simp only [H.map_comp] at h
  have h' := congrFun (congrArg (Cat.Hom.toFunctor · |>.obj) h) X.fiber
  exact h'.symm

/--
Morphism map for the Grothendieck transition functor.
-/
def LaxNatTransData.grothendieckTransitionHom {c c' : C} (f : c ⟶ c')
    {X Y : Grothendieck (α.app c ⋙ H)} (g : X ⟶ Y) :
    α.grothendieckTransitionObj D H f X ⟶ α.grothendieckTransitionObj D H f Y where
  base := (G.map f).toFunctor.map g.base
  fiber :=
    eqToHom (α.grothendieckTransition_fiber_eq D H f g) ≫
    (H.map (α.laxAppConst D f Y.base)).toFunctor.map g.fiber

set_option backward.isDefEq.respectTransparency false in
/--
The transition functor for the Grothendieck construction along `f : c ⟶ c'`.
-/
def LaxNatTransData.grothendieckTransition {c c' : C} (f : c ⟶ c') :
    Grothendieck (α.app c ⋙ H) ⥤ Grothendieck (α.app c' ⋙ H) where
  obj := α.grothendieckTransitionObj D H f
  map := α.grothendieckTransitionHom D H f
  map_id X := by
    refine Grothendieck.ext _ _ ?_ ?_
    · simp only [grothendieckTransitionHom, grothendieckTransitionObj, Grothendieck.id_base,
        CategoryTheory.Functor.map_id]
    · simp only [grothendieckTransitionHom, grothendieckTransitionObj, Grothendieck.id_fiber,
        Functor.comp_obj, eqToHom_map, eqToHom_trans]
  map_comp {X Y Z} g h := by
    refine Grothendieck.ext _ _ ?_ ?_
    · simp only [grothendieckTransitionHom, grothendieckTransitionObj, Grothendieck.comp_base,
        Functor.map_comp]
    · simp only [grothendieckTransitionHom, grothendieckTransitionObj,
          Grothendieck.comp_fiber, Functor.comp_obj, Functor.comp_map,
          Functor.map_comp, eqToHom_map, eqToHom_trans_assoc,
          Category.assoc, laxAppConst]
      -- Use lax naturality to relate the two paths for g.fiber
      have laxNat := α.laxNat f h.base
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Cat.id_eq_id] at laxNat
      -- The two functor compositions are equal by lax naturality
      -- In Cat, ⋙ is the same as ≫ (composition of morphisms)
      have hFunEqCat : H.map ((α.app c).map h.base) ≫ H.map (α.laxApp f Z.base) =
                       H.map (α.laxApp f Y.base) ≫
                       H.map ((α.app c').map ((G.map f).toFunctor.map h.base)) := by
        rw [← H.map_comp, ← H.map_comp]
        simp only [Functor.id_map] at laxNat
        exact congrArg H.map laxNat
      have hFunEq : (H.map ((α.app c).map h.base)).toFunctor ⋙
                    (H.map (α.laxApp f Z.base)).toFunctor =
                    (H.map (α.laxApp f Y.base)).toFunctor ⋙
                    (H.map ((α.app c').map ((G.map f).toFunctor.map h.base))).toFunctor := by
        have := congrArg Cat.Hom.toFunctor hFunEqCat
        simp only [Cat.comp_eq_comp] at this
        unfold Cat.Hom.toFunctor at this
        exact this
      -- Use naturality of eqToHom hFunEq to relate the two functor maps
      have hNat := (eqToHom hFunEq).naturality g.fiber
      simp only [eqToHom_app, Functor.comp_obj, Functor.comp_map] at hNat
      -- hNat: F2.map (F1.map g.fiber) ≫ eqToHom _ = eqToHom _ ≫ G2.map (G1.map g.fiber)
      -- hNat relates the two paths for g.fiber modulo eqToHom
      -- Insert identity as (... ≫ 𝟙) then rewrite 𝟙 to eqToHom ≫ eqToHom.symm
      rw [← Category.comp_id ((H.map (α.laxApp f Z.base)).toFunctor.map
            ((H.map ((α.app c).map h.base)).toFunctor.map g.fiber))]
      -- The object equality at codomain of g.fiber
      -- (F ⋙ G).obj X is defeq to G.obj (F.obj X)
      have hObjEq :
          (H.map (α.laxApp f Z.base)).toFunctor.obj
            ((H.map ((α.app c).map h.base)).toFunctor.obj Y.fiber) =
          (H.map ((α.app c').map ((G.map f).toFunctor.map h.base))).toFunctor.obj
            ((H.map (α.laxApp f Y.base)).toFunctor.obj Y.fiber) := by
        simp only [← Functor.comp_obj]
        exact Functor.congr_obj hFunEq Y.fiber
      rw [show (𝟙 _ : _ ⟶ (H.map (α.laxApp f Z.base)).toFunctor.obj
            ((H.map ((α.app c).map h.base)).toFunctor.obj Y.fiber)) =
          eqToHom hObjEq ≫ eqToHom hObjEq.symm
          by simp only [eqToHom_trans, eqToHom_refl]]
      simp only [Category.assoc]
      -- Now match hNat's eqToHom with our hObjEq
      -- hNat: F.map ≫ eqToHom(congr_obj) = eqToHom(congr_obj) ≫ G.map
      -- We need to show the eqToHom proofs are equal
      -- Domain equality for the domain of g.fiber
      have hObjEq_dom :
          (H.map (α.laxApp f Z.base)).toFunctor.obj
            ((H.map ((α.app c).map h.base)).toFunctor.obj
              (((α.app c ⋙ H).map g.base).toFunctor.obj X.fiber)) =
          (H.map ((α.app c').map ((G.map f).toFunctor.map h.base))).toFunctor.obj
            ((H.map (α.laxApp f Y.base)).toFunctor.obj
              (((α.app c ⋙ H).map g.base).toFunctor.obj X.fiber)) := by
        simp only [← Functor.comp_obj]
        exact Functor.congr_obj hFunEq (((α.app c ⋙ H).map g.base).toFunctor.obj X.fiber)
      have hNat' :
          (H.map (α.laxApp f Z.base)).toFunctor.map
            ((H.map ((α.app c).map h.base)).toFunctor.map g.fiber) ≫
          eqToHom hObjEq =
          eqToHom hObjEq_dom ≫
          (H.map ((α.app c').map ((G.map f).toFunctor.map h.base))).toFunctor.map
            ((H.map (α.laxApp f Y.base)).toFunctor.map g.fiber) := by
        simp only [← Functor.comp_obj, ← Functor.comp_map]
        exact hNat
      -- Reassociate to match hNat' pattern
      rw [← Category.assoc ((H.map (α.laxApp f Z.base)).toFunctor.map
            ((H.map ((α.app c).map h.base)).toFunctor.map g.fiber)) (eqToHom hObjEq)]
      rw [hNat']
      -- Simplify eqToHom chains
      simp only [Category.assoc, eqToHom_trans_assoc]

set_option backward.isDefEq.respectTransparency false in
/--
Object equality for `grothendieckFunctor.map_comp`.

The transition functor for a composite morphism `f ≫ g` agrees on objects with
the composition of individual transition functors.
-/
lemma LaxNatTransData.grothendieckFunctor_map_comp_obj {c c' c'' : C}
    (f : c ⟶ c') (g : c' ⟶ c'')
    (X : Grothendieck (α.app c ⋙ H)) :
    (α.grothendieckTransition D H (f ≫ g)).obj X =
    (α.grothendieckTransition D H g).obj
      ((α.grothendieckTransition D H f).obj X) := by
  simp only [grothendieckTransition, grothendieckTransitionObj]
  rw [Grothendieck.mk.injEq]
  constructor
  · simp only [G.map_comp]; rfl
  · simp only [laxAppConst]
    have h := α.laxComp f g X.base
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Cat.id_eq_id] at h
    rw [h, H.map_comp, H.map_comp, H.map_comp, eqToHom_map, eqToHom_map]
    simp only [Functor.id_map, Functor.comp_obj]
    apply HEq.trans (eqToHom_obj_heq _ _ _ _)
    apply heq_of_eq
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
Morphism mapping equality for `grothendieckFunctor.map_comp`.

The transition functor for a composite morphism `f ≫ g` agrees on morphisms
(up to eqToHom conjugation) with the composition of individual transition
functors.
-/
lemma LaxNatTransData.grothendieckFunctor_map_comp_map {c c' c'' : C}
    (f : c ⟶ c') (g : c' ⟶ c'')
    (X Y : Grothendieck (α.app c ⋙ H)) (h : X ⟶ Y) :
    (α.grothendieckTransition D H (f ≫ g)).map h =
    eqToHom (α.grothendieckFunctor_map_comp_obj D H f g X) ≫
    (α.grothendieckTransition D H f ⋙ α.grothendieckTransition D H g).map h ≫
    eqToHom (α.grothendieckFunctor_map_comp_obj D H f g Y).symm := by
  simp only [grothendieckTransition, grothendieckTransitionHom, Functor.comp_map]
  refine Grothendieck.ext _ _ ?_ ?_
  · simp only [Grothendieck.comp_base, Grothendieck.base_eqToHom]
    apply eq_of_heq
    apply HEq.trans (functor_map_comp_heq G f g h.base)
    apply HEq.symm
    apply HEq.trans (eqToHom_comp_heq _ _)
    exact comp_eqToHom_heq _ _
  · simp only [laxAppConst, Grothendieck.comp_fiber, grothendieckTransitionObj,
        Functor.comp_obj, Functor.comp_map, Functor.map_comp, eqToHom_map,
        eqToHom_trans_assoc, Category.assoc]
    have laxComp := α.laxComp f g Y.base
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Cat.id_eq_id,
        Functor.id_map] at laxComp
    have hFunEq : H.map (α.laxApp (f ≫ g) Y.base) =
        H.map (eqToHom _ ≫ α.laxApp f Y.base ≫
          α.laxApp g ((G.map f).toFunctor.obj Y.base) ≫ eqToHom _) :=
      congrArg H.map laxComp
    simp only [H.map_comp, eqToHom_map] at hFunEq
    have hFunEq' := congrArg Cat.Hom.toFunctor hFunEq
    simp only [Cat.comp_eq_comp] at hFunEq'
    unfold Cat.Hom.toFunctor at hFunEq'
    simp only [Grothendieck.comp_base,
        Grothendieck.fiber_eqToHom,
        Functor.comp_obj, Functor.comp_map,
        eqToHom_map, eqToHom_trans_assoc]
    apply eq_of_heq
    apply HEq.trans (eqToHom_comp_heq _ _)
    apply HEq.symm
    apply HEq.trans (eqToHom_comp_heq _ _)
    apply HEq.trans (comp_eqToHom_heq _ _)
    apply HEq.symm
    -- Goal: LHS ≍ RHS where
    -- LHS = (H.map (α.laxApp (f ≫ g) Y.base)).map h.fiber
    -- RHS = outer.map (g_fun.map (f_fun.map h.fiber))
    -- with outer = H.map ((α.app c'').map (eqToHom _).base)
    --
    -- Use hFunEq' to expand LHS
    apply HEq.trans (functor_eq_map_heq hFunEq' h.fiber)
    -- Now: (eqToHom ≫ Hf ≫ Hg ≫ eqToHom).map h.fiber ≍ outer.map (...)
    simp only [Functor.comp_map]
    -- Expanded: outer_eq.map (Hg.map (Hf.map (inner_eq.map h.fiber)))
    -- The inner eqToHom gives (inner_eq.map h.fiber) ≍ h.fiber
    -- The outer eqToHom gives outer_eq.map x ≍ x
    -- So LHS ≍ Hg.map (Hf.map h.fiber)
    apply HEq.trans (eqToHom_map_heq' _ _)
    -- Now: Hg.map (Hf.map (inner_eq.map h.fiber)) ≍ outer.map (Hg.map (Hf.map h.fiber))
    -- Show the outers match by showing both reduce to Hg.map (Hf.map h.fiber)
    -- First, show outer is eqToHom
    have hOuterIsEqToHom : H.map ((α.app c'').map
        (Grothendieck.Hom.base
          (eqToHom (α.grothendieckFunctor_map_comp_obj D H f g Y).symm))) =
        eqToHom (congrArg (fun x => H.obj ((α.app c'').obj x.base))
          (α.grothendieckFunctor_map_comp_obj D H f g Y).symm) := by
      simp only [Grothendieck.base_eqToHom, eqToHom_map]
    have hOuterIsEqToHom' := congrArg Cat.Hom.toFunctor hOuterIsEqToHom
    unfold Cat.Hom.toFunctor at hOuterIsEqToHom'
    -- Strip the outer eqToHom from RHS
    apply HEq.symm
    apply HEq.trans (functor_map_heq_of_eq_eqToHom' _ _ hOuterIsEqToHom' _)
    -- Now both sides are: Hg.map (Hf.map (some form of h.fiber))
    -- Need to show inner_eq.map h.fiber vs h.fiber lift through Hf and Hg
    apply HEq.symm
    -- Goal: Hg.map (Hf.map h.fiber) ≍ Hg.map (Hf.map (eqToHom.map h.fiber))
    -- Since both must typecheck as morphisms in the same category for Hf.map,
    -- the eqToHom must be eqToHom rfl, so this is rfl
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
The Grothendieck functor for a lax natural transformation `α : G ⟹ᵢₐₓ const D`
composed with a functor `H : D ⥤ Cat`.

This maps each object `c : C` to the Grothendieck category `Grothendieck (α.app c ⋙ H)`
and each morphism `f : c ⟶ c'` to the transition functor `grothendieckTransition f`.
-/
def LaxNatTransData.grothendieckFunctor : C ⥤ Cat.{vF, uF} where
  obj c := Cat.of (Grothendieck (α.app c ⋙ H))
  map f := (α.grothendieckTransition D H f).toCatHom
  map_id c := by
    apply Cat.Hom.ext
    simp only [Functor.toCatHom_toFunctor, Cat.id_eq_id]
    apply _root_.CategoryTheory.Functor.ext
    case h_obj =>
      intro X
      simp only [grothendieckTransition, grothendieckTransitionObj, Functor.id_obj]
      rw [Grothendieck.mk.injEq]
      refine ⟨?_, ?_⟩
      · simp only [G.map_id, Cat.id_eq_id, Functor.id_obj]
      · simp only [laxAppConst]
        have h := α.laxId c X.base
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Cat.id_eq_id] at h
        rw [h, eqToHom_map]
        exact eqToHom_obj_heq _ _ _ _
    case h_map =>
      intro X Y f
      simp only [grothendieckTransition, grothendieckTransitionHom, Functor.id_map]
      refine Grothendieck.ext _ _ ?_ ?_
      · apply eq_of_heq
        apply HEq.trans (functor_map_id_heq G c f.base)
        apply HEq.symm
        simp only [Grothendieck.comp_base, Grothendieck.base_eqToHom]
        apply HEq.trans (eqToHom_comp_heq _ _)
        exact comp_eqToHom_heq _ _
      · simp only [laxAppConst, grothendieckTransitionObj, Functor.comp_obj]
        have hId := α.laxId c Y.base
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Cat.id_eq_id] at hId
        apply eq_of_heq
        apply HEq.trans (eqToHom_comp_heq _ _)
        apply HEq.trans (eqToHom_comp_heq _ _)
        have h1 : HEq ((H.map (α.laxApp (𝟙 c) Y.base)).toFunctor.map f.fiber)
            f.fiber := by
          rw [hId, eqToHom_map]
          exact eqToHom_map_heq' _ _
        apply HEq.trans h1
        exact HEq.symm (@Grothendieck.conj_eqToHom_fiber_heq _ _ (α.app c ⋙ H) _ _ _ _ _ _ _)
  map_comp {c c' c''} f g := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Functor.toCatHom_toFunctor]
    apply _root_.CategoryTheory.Functor.ext
    case h_obj => exact α.grothendieckFunctor_map_comp_obj D H f g
    case h_map => exact α.grothendieckFunctor_map_comp_map D H f g

end LaxNatTrans

/-!
## The Category of Cat-Valued Functors with Lax Natural Transformations

This section defines `LaxFunctorCat`, a wrapper type around `C ⥤ Cat` where
morphisms are lax natural transformations rather than natural transformations.
-/

section LaxFunctorCat

universe vC uC

variable (C : Type uC) [Category.{vC} C]

/--
A wrapper type for `C ⥤ Cat` where morphisms are lax natural transformations.

This is needed because mathlib already defines a category structure on `C ⥤ Cat`
using natural transformations as morphisms. By wrapping the functor in a new
type, we can define a different category structure using lax natural
transformations.
-/
@[ext]
structure LaxFunctorCat where
  /-- The underlying functor to Cat. -/
  toFunctor : C ⥤ Cat.{vC, uC}

variable {C}

/-- Coercion from `LaxFunctorCat` to functor. -/
instance : CoeOut (LaxFunctorCat C) (C ⥤ Cat.{vC, uC}) where
  coe := LaxFunctorCat.toFunctor

/-- Wrap a functor as a `LaxFunctorCat`. -/
abbrev LaxFunctorCat.of (F : C ⥤ Cat.{vC, uC}) : LaxFunctorCat C := ⟨F⟩

/-- Associativity of lax natural transformation composition. -/
theorem LaxNatTransData.comp_assoc {G H K L : C ⥤ Cat.{vC, uC}}
    (α : LaxNatTransData G H) (β : LaxNatTransData H K)
    (γ : LaxNatTransData K L) :
    (α.comp β).comp γ = α.comp (β.comp γ) := by
  cases α; cases β; cases γ
  simp only [LaxNatTransData.comp, Functor.assoc]
  congr 1
  funext c x
  simp only [Functor.comp_obj, Functor.comp_map, Category.assoc, Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Left identity for lax natural transformation composition. -/
theorem LaxNatTransData.id_comp {G H : C ⥤ Cat.{vC, uC}}
    (α : LaxNatTransData G H) :
    (LaxNatTransData.id G).comp α = α := by
  cases α with | mk app laxApp _ _ _ =>
  simp only [LaxNatTransData.comp, LaxNatTransData.id]
  congr 1
  funext c f g y
  simp only [Functor.id_obj, eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id]

/-- Right identity for lax natural transformation composition. -/
theorem LaxNatTransData.comp_id {G H : C ⥤ Cat.{vC, uC}}
    (α : LaxNatTransData G H) :
    α.comp (LaxNatTransData.id H) = α := by
  cases α with | mk app laxApp _ _ _ =>
  simp only [LaxNatTransData.comp, LaxNatTransData.id]
  congr 1
  funext c f g y
  simp [Functor.id_obj, Functor.id_map]

/-- The category structure on `LaxFunctorCat C` with lax natural transformations
as morphisms. -/
instance : Category (LaxFunctorCat C) where
  Hom G H := LaxNatTransData G.toFunctor H.toFunctor
  id G := LaxNatTransData.id G.toFunctor
  comp := LaxNatTransData.comp
  id_comp := LaxNatTransData.id_comp
  comp_id := LaxNatTransData.comp_id
  assoc := LaxNatTransData.comp_assoc

set_option backward.isDefEq.respectTransparency false in
/--
Convert a natural transformation to a lax natural transformation.

A natural transformation `α : F ⟹ G` satisfies the strict naturality condition
`α.app c ⋙ G.map f = F.map f ⋙ α.app c'`. This implies that the laxity morphisms
are all identities (up to `eqToHom`).
-/
def LaxNatTransData.ofNatTrans {G H : C ⥤ Cat.{vC, uC}} (α : NatTrans G H) :
    LaxNatTransData G H where
  app c := (α.app c).toFunctor
  laxApp {c c'} f x := eqToHom (by
    simp only [← Functor.comp_obj]
    have nat := congrArg Cat.Hom.toFunctor (α.naturality f)
    simp only [Cat.Hom.comp_toFunctor] at nat
    exact (congrArg (·.obj x) nat).symm)
  laxNat {c c'} f {x y} φ := by
    have nat := congrArg Cat.Hom.toFunctor (α.naturality f)
    simp only [Cat.Hom.comp_toFunctor] at nat
    have h := Functor.congr_hom nat.symm φ
    change (H.map f).toFunctor.map ((α.app c).toFunctor.map φ) ≫ _ =
      _ ≫ (α.app c').toFunctor.map ((G.map f).toFunctor.map φ)
    conv_lhs => rw [show (H.map f).toFunctor.map ((α.app c).toFunctor.map φ) =
        ((α.app c).toFunctor ⋙ (H.map f).toFunctor).map φ from rfl]
    rw [h]
    conv_lhs => rw [show ((G.map f).toFunctor ⋙ (α.app c').toFunctor).map φ =
        (α.app c').toFunctor.map ((G.map f).toFunctor.map φ) from rfl]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  laxId c x := by
    simp
  laxComp {c c' c''} f g x := by
    simp

/--
The embedding of natural transformations into lax natural transformations
respects identity.
-/
theorem LaxNatTransData.ofNatTrans_id (G : C ⥤ Cat.{vC, uC}) :
    LaxNatTransData.ofNatTrans (𝟙 G) = LaxNatTransData.id G := by
  simp only [LaxNatTransData.ofNatTrans, LaxNatTransData.id, NatTrans.id_app]
  congr 1

/--
The embedding of natural transformations into lax natural transformations
respects composition.
-/
theorem LaxNatTransData.ofNatTrans_comp {G H K : C ⥤ Cat.{vC, uC}}
    (α : NatTrans G H) (β : NatTrans H K) :
    LaxNatTransData.ofNatTrans (α ≫ β : G ⟶ K) =
      (LaxNatTransData.ofNatTrans α).comp (LaxNatTransData.ofNatTrans β) := by
  simp only [LaxNatTransData.ofNatTrans, LaxNatTransData.comp, NatTrans.comp_app]
  congr 1
  funext c f x
  simp [Functor.comp_obj]

/--
The functor embedding the natural transformation category into the lax natural
transformation category.

This is faithful: natural transformations embed as lax natural transformations
where all laxity morphisms are identities (via `eqToHom`).
-/
def natToLaxFunctor : (C ⥤ Cat.{vC, uC}) ⥤ LaxFunctorCat C where
  obj F := LaxFunctorCat.of F
  map α := LaxNatTransData.ofNatTrans α
  map_id G := LaxNatTransData.ofNatTrans_id G
  map_comp α β := LaxNatTransData.ofNatTrans_comp α β

end LaxFunctorCat

open CategoryTheory

/-!
## Decomposition of FunctorBetweenData via Lax Natural Transformations

This section shows that `FunctorBetweenData G F` decomposes as a base functor
`baseFib : C ⥤ D` together with a lax natural transformation
`G ⟹ baseFib ⋙ F`.

For this to work, we require the Cat-valued functors to have matching
universe levels.
-/

section FunctorBetweenDecomposition

universe vC uC

variable {C : Type uC} [Category.{vC} C] (G : C ⥤ Cat.{vC, uC})
variable {D : Type uC} [Category.{vC} D] (F : D ⥤ Cat.{vC, uC})

/--
Extract a lax natural transformation from FunctorBetweenData.

Given `data : FunctorBetweenData G F`, we get a lax natural transformation
`G ⟹ data.baseFib ⋙ F`.
-/
def FunctorBetweenData.toLaxNatTrans (data : FunctorBetweenData G F) :
    LaxNatTransData G (data.baseFib ⋙ F) where
  app c := data.fibFib c
  laxApp {c c'} f x := data.fibHomCrossApp f x
  laxNat {c c'} f {x y} φ := data.fibHomCrossNat f φ
  laxId c x := data.baseHomId c x
  laxComp {c c' c''} f g x := by
    simp only [Functor.comp_obj, Functor.comp_map]
    exact data.baseHomComp f g x

/--
Construct FunctorBetweenData from a base functor and lax natural transformation.

Given `baseFib : C ⥤ D` and `α : LaxNatTransData G (baseFib ⋙ F)`, we get
`FunctorBetweenData G F`.
-/
def FunctorBetweenData.ofLaxNatTrans (baseFib : C ⥤ D)
    (α : LaxNatTransData G (baseFib ⋙ F)) : FunctorBetweenData G F where
  baseFib := baseFib
  fibFib c := α.app c
  fibHomCrossApp {_ _} f x := α.laxApp f x
  fibHomCrossNat {_ _} f {_ _} φ := α.laxNat f φ
  baseHomId c x := α.laxId c x
  baseHomComp {_ _ _} f g x := α.laxComp f g x

/--
Round-trip: `toLaxNatTrans` followed by `ofLaxNatTrans` is identity.
-/
theorem FunctorBetweenData.ofLaxNatTrans_toLaxNatTrans
    (data : FunctorBetweenData G F) :
    ofLaxNatTrans G F data.baseFib (toLaxNatTrans G F data) = data := by
  rfl

/--
Round-trip: `ofLaxNatTrans` followed by `toLaxNatTrans` is identity.
-/
theorem FunctorBetweenData.toLaxNatTrans_ofLaxNatTrans (baseFib : C ⥤ D)
    (α : LaxNatTransData G (baseFib ⋙ F)) :
    toLaxNatTrans G F (ofLaxNatTrans G F baseFib α) = α := by
  rfl

/--
The type of FunctorBetweenData decomposes as a sigma type.

`FunctorBetweenData G F ≃ Σ (baseFib : C ⥤ D), LaxNatTransData G (baseFib ⋙ F)`
-/
def FunctorBetweenData.equivSigmaLaxNatTrans :
    FunctorBetweenData G F ≃
      Σ (baseFib : C ⥤ D), LaxNatTransData G (baseFib ⋙ F) where
  toFun data := ⟨data.baseFib, data.toLaxNatTrans G F⟩
  invFun p := ofLaxNatTrans G F p.1 p.2
  left_inv := ofLaxNatTrans_toLaxNatTrans G F
  right_inv _ := rfl

/--
Construct the functor `Grothendieck G ⥤ Grothendieck F` via the lax-nat-trans-pre
factorization.

Given `data : FunctorBetweenData G F`, this constructs the functor as:
`(data.toLaxNatTrans G F).toFunctor ⋙ Grothendieck.pre F data.baseFib`

This makes explicit that functors between Grothendieck constructions factor through
the pullback construction via `pre`.
-/
def FunctorBetweenData.toFunctorViaPre (data : FunctorBetweenData G F) :
    Grothendieck G ⥤ Grothendieck F :=
  (data.toLaxNatTrans G F).toFunctor ⋙ Grothendieck.pre F data.baseFib

/--
The object map of `toFunctorViaPre`.
-/
theorem FunctorBetweenData.toFunctorViaPre_obj (data : FunctorBetweenData G F)
    (X : Grothendieck G) :
    (data.toFunctorViaPre).obj X = ⟨data.baseFib.obj X.base, (data.fibFib X.base).obj X.fiber⟩ :=
  rfl

/--
The morphism map of `toFunctorViaPre`.
-/
theorem FunctorBetweenData.toFunctorViaPre_map (data : FunctorBetweenData G F)
    {X Y : Grothendieck G} (f : X ⟶ Y) :
    (data.toFunctorViaPre).map f =
      ⟨data.baseFib.map f.base,
       data.fibHomCrossApp f.base X.fiber ≫ (data.fibFib Y.base).map f.fiber⟩ := rfl

/--
The factored functor agrees with `functorBetweenFibFunc` on objects within fibers.
-/
theorem FunctorBetweenData.toFunctorViaPre_eq_functorBetweenFibFunc_obj
    (data : FunctorBetweenData G F) (c : C) (x : G.obj c) :
    (data.toFunctorViaPre).obj ⟨c, x⟩ = (functorBetweenFibFunc G F data c).obj x := rfl

end FunctorBetweenDecomposition

/-!
## Oplax Natural Transformations for Contravariant Cat-Valued Functors

This section defines oplax natural transformations between contravariant
Cat-valued functors `G' F' : Cᵒᵖ' ⥤ Cat`.

For contravariant functors, oplax natural transformations have component
functors `app c : G'.obj c ⥤ F'.obj c` and oplax morphisms:

```
oplaxApp f x' : (app c).obj ((G'.map f).obj x') ⟶ (F'.map f).obj ((app c').obj x')
```

for `f : c ⟶ c'` and `x' : G'.obj c'`.

Note: For covariant functors, "lax" has morphisms going from F-transported to
G-transported. For contravariant functors, the analogous direction is what we
call "oplax" here, reflecting the reversal of morphism direction.
-/

section OplaxNatTrans

universe vC uC vF uF

variable {C : Type uC} [Category.{vC} C]
variable (G' F' : Cᵒᵖ' ⥤ Cat.{vF, uF})

/--
Component functors for an oplax natural transformation between contravariant
Cat-valued functors.
-/
abbrev OplaxNatTransApp :=
  ∀ c : C, G'.obj c ⥤ F'.obj c

variable {G' F'}
variable (app : OplaxNatTransApp G' F')

/--
Oplax morphism components for an oplax natural transformation `α : G' ⟹ F'`
between contravariant Cat-valued functors `G' F' : Cᵒᵖ' ⥤ Cat`.

Given a morphism `f : c' ⟶ c` in `C` and an element `x` in the fiber `G'.obj c`,
there are two ways to obtain an element of `F'.obj c'`.

Note on contravariance: For `G' : Cᵒᵖ' ⥤ Cat`, the morphism `f : c' ⟶ c` in `C`
corresponds to a morphism from `c` to `c'` in `Cᵒᵖ'`. Thus `G'.map f` acts as
a functor `G'.obj c ⥤ G'.obj c'` (going from `c` to `c'` in the fiber categories).
Similarly, `F'.map f : F'.obj c ⥤ F'.obj c'`. This convention makes `c` the
"source" and `c'` the "target" from the functor's perspective, matching the
natural direction of transport.

1. **Transport via G' first, then apply α**: Transport x along f using G'
   to get `(G'.map f).obj x` in `G'.obj c'`, then apply the component functor
   `app c' : G'.obj c' ⥤ F'.obj c'` to get `(app c').obj ((G'.map f).obj x)` in
   `F'.obj c'`.

2. **Apply α first, then transport via F'**: Apply the component functor
   `app c : G'.obj c ⥤ F'.obj c` to get `(app c).obj x` in `F'.obj c`,
   then transport along f using F' to get `(F'.map f).obj ((app c).obj x)`
   in `F'.obj c'`.

The oplax morphism goes from (1) to (2):

  `(app c').obj ((G'.map f).obj x) ⟶ (F'.map f).obj ((app c).obj x)`

This is consistent with nLab's convention: if we view G', F' as covariant
functors on Cᵒᵖ, then a lax transformation would have the arrow going in the
opposite direction. Since "oplax" means reversing the 2-cell direction from
"lax", our oplax for contravariant functors has the direction shown above:
from (G'-transport-then-α) to (α-then-F'-transport).
-/
abbrev OplaxNatTransOplaxApp :=
  ∀ {c c' : C} (f : c' ⟶ c) (x : G'.obj c),
    (app c').obj ((G'.map f).toFunctor.obj x) ⟶
    (F'.map f).toFunctor.obj ((app c).obj x)

variable (oplaxApp : OplaxNatTransOplaxApp app)

/--
Naturality of oplax morphisms.
For `f : c' ⟶ c` and `φ : x ⟶ y` in `G'.obj c`, both sides of the equation
have domain `(app c').obj ((G'.map f).obj x)` and codomain
`(F'.map f).obj ((app c).obj y)`.
-/
abbrev OplaxNatTransOplaxNat :=
  ∀ {c c' : C} (f : c' ⟶ c) {x y : G'.obj c} (φ : x ⟶ y),
    (app c').map ((G'.map f).toFunctor.map φ) ≫ oplaxApp f y =
    oplaxApp f x ≫ (F'.map f).toFunctor.map ((app c).map φ)

/--
Equality proof for identity oplax coherence.
-/
abbrev OplaxNatTransIdEq :=
  ∀ (c : C) (x : G'.obj c),
    (app c).obj ((G'.map (𝟙 c)).toFunctor.obj x) =
    (F'.map (𝟙 c)).toFunctor.obj ((app c).obj x)

/--
Derive the identity equality from functor laws.
-/
lemma oplaxNatTransIdEqProof : OplaxNatTransIdEq app := by
  intro c x
  have hG : (G'.map (𝟙 c)).toFunctor = 𝟭 _ :=
    congrArg Cat.Hom.toFunctor (G'.map_id c) |>.trans (Cat.id_eq_id (G'.obj c))
  have hF : (F'.map (𝟙 c)).toFunctor = 𝟭 _ :=
    congrArg Cat.Hom.toFunctor (F'.map_id c) |>.trans (Cat.id_eq_id (F'.obj c))
  simp only [hG, hF, Functor.id_obj]

/--
Identity coherence: `oplaxApp (𝟙 c) x` equals the canonical eqToHom.
-/
abbrev OplaxNatTransOplaxId :=
  ∀ (c : C) (x : G'.obj c),
    oplaxApp (𝟙 c) x = eqToHom (oplaxNatTransIdEqProof app c x)

/--
Equality proof for composition oplax coherence (left side).
For `f : c' ⟶ c` and `g : c'' ⟶ c'` in C, the C-composition is `g ≫ f : c'' ⟶ c`.
By contravariant functoriality: `G'.map (g ≫ f) = G'.map f ⋙ G'.map g`.
-/
abbrev OplaxNatTransCompEqLeft :=
  ∀ {c c' c'' : C} (f : c' ⟶ c) (g : c'' ⟶ c') (x : G'.obj c),
    (app c'').obj ((G'.map (@CategoryStruct.comp C _ c'' c' c g f)).toFunctor.obj x) =
    (app c'').obj ((G'.map g).toFunctor.obj ((G'.map f).toFunctor.obj x))

/--
Derive the left composition equality from functor laws.
-/
lemma oplaxNatTransCompEqLeftProof : OplaxNatTransCompEqLeft app := by
  intro c c' c'' f g x
  exact congrArg (app c'').obj (congrFun (congrArg Functor.obj
    (congrArg (fun x => x.toFunctor) (G'.map_comp f g))) x)

/--
Equality proof for composition oplax coherence (right side).
For `f : c' ⟶ c` and `g : c'' ⟶ c'` in C, the C-composition is `g ≫ f : c'' ⟶ c`.
By contravariant functoriality: `F'.map (g ≫ f) = F'.map f ⋙ F'.map g`.
-/
abbrev OplaxNatTransCompEqRight :=
  ∀ {c c' c'' : C} (f : c' ⟶ c) (g : c'' ⟶ c') (x : G'.obj c),
    (F'.map g).toFunctor.obj ((F'.map f).toFunctor.obj ((app c).obj x)) =
    (F'.map (@CategoryStruct.comp C _ c'' c' c g f)).toFunctor.obj ((app c).obj x)

/--
Derive the right composition equality from functor laws.
-/
lemma oplaxNatTransCompEqRightProof : OplaxNatTransCompEqRight app := by
  intro c c' c'' f g x
  exact (congrFun (congrArg Functor.obj
    (congrArg (fun x => x.toFunctor) (F'.map_comp f g))) ((app c).obj x)).symm

/--
Composition coherence: `oplaxApp (g ≫ f) x` decomposes stepwise.
For `f : c' ⟶ c` and `g : c'' ⟶ c'` in C, the composed morphism is `g ≫ f : c'' ⟶ c`.
The decomposition first applies the `f` step (c ⟶ c' in Cᵒᵖ'), then the `g` step
(c' ⟶ c'' in Cᵒᵖ').
-/
abbrev OplaxNatTransOplaxComp :=
  ∀ {c c' c'' : C} (f : c' ⟶ c) (g : c'' ⟶ c') (x : G'.obj c),
    oplaxApp (@CategoryStruct.comp C _ c'' c' c g f) x =
    eqToHom (oplaxNatTransCompEqLeftProof app f g x) ≫
    oplaxApp g ((G'.map f).toFunctor.obj x) ≫
    (F'.map g).toFunctor.map (oplaxApp f x) ≫
    eqToHom (oplaxNatTransCompEqRightProof app f g x)

/--
Bundled data for an oplax natural transformation `G' ⟹ F'` between contravariant
Cat-valued functors `G' F' : Cᵒᵖ' ⥤ Cat`.

An oplax natural transformation consists of:
- Component functors for each object
- Oplax morphisms for each morphism
- Naturality and coherence conditions

These correspond to functors `GrothendieckContra' G' ⥤ GrothendieckContra' F'`
that are identity on the base category.
-/
structure OplaxNatTransData (G' F' : Cᵒᵖ' ⥤ Cat.{vF, uF}) where
  /-- Component functors: for each `c`, a functor `G'.obj c ⥤ F'.obj c` -/
  app : OplaxNatTransApp G' F'
  /-- Oplax morphisms: for each `f` and `x'`, a morphism between fibers -/
  oplaxApp : OplaxNatTransOplaxApp app
  /-- Naturality of oplax morphisms -/
  oplaxNat : OplaxNatTransOplaxNat app oplaxApp
  /-- Identity coherence -/
  oplaxId : OplaxNatTransOplaxId app oplaxApp
  /-- Composition coherence -/
  oplaxComp : OplaxNatTransOplaxComp app oplaxApp

set_option backward.isDefEq.respectTransparency false in
/--
Identity oplax natural transformation.
-/
def OplaxNatTransData.id (G' : Cᵒᵖ' ⥤ Cat.{vF, uF}) : OplaxNatTransData G' G' where
  app c := 𝟭 (G'.obj c)
  oplaxApp f x := eqToHom (by simp only [Functor.id_obj])
  oplaxNat f φ := by
    intro y φ'
    simp only [Functor.id_map, eqToHom_naturality]
  oplaxId c x := rfl
  oplaxComp f g x := by
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]

set_option backward.isDefEq.respectTransparency false in
/--
Composition of oplax natural transformations.

Given `α : G' ⟹ H'` and `β : H' ⟹ K'`, their composition `α ⋙ β : G' ⟹ K'` has:
- Component functors: `(α ⋙ β).app c = α.app c ⋙ β.app c`
- Oplax: For `f : c' ⟶ c` and `x : G'.obj c`,
  `(β.app c').map (α.oplaxApp f x) ≫ β.oplaxApp f ((α.app c).obj x)`
-/
def OplaxNatTransData.comp {G' H' K' : Cᵒᵖ' ⥤ Cat.{vF, uF}}
    (α : OplaxNatTransData G' H') (β : OplaxNatTransData H' K') :
    OplaxNatTransData G' K' where
  app c := α.app c ⋙ β.app c
  oplaxApp {c c'} f x :=
    (β.app c').map (α.oplaxApp f x) ≫ β.oplaxApp f ((α.app c).obj x)
  oplaxNat {c c'} f {x y} φ := by
    simp only [Functor.comp_obj, Functor.comp_map]
    have hα : (α.app c').map ((G'.map f).toFunctor.map φ) ≫ α.oplaxApp f y =
        α.oplaxApp f x ≫ (H'.map f).toFunctor.map ((α.app c).map φ) := α.oplaxNat f φ
    have hβ : (β.app c').map ((H'.map f).toFunctor.map ((α.app c).map φ)) ≫
            β.oplaxApp f ((α.app c).obj y) =
        β.oplaxApp f ((α.app c).obj x) ≫
            (K'.map f).toFunctor.map ((β.app c).map ((α.app c).map φ)) :=
        β.oplaxNat f ((α.app c).map φ)
    calc
      _ = ((β.app c').map ((α.app c').map ((G'.map f).toFunctor.map φ)) ≫
          (β.app c').map (α.oplaxApp f y)) ≫ β.oplaxApp f ((α.app c).obj y) := by
        simp only [Category.assoc]
      _ = (β.app c').map ((α.app c').map ((G'.map f).toFunctor.map φ) ≫ α.oplaxApp f y) ≫
          β.oplaxApp f ((α.app c).obj y) := by rw [← (β.app c').map_comp]
      _ = (β.app c').map (α.oplaxApp f x ≫ (H'.map f).toFunctor.map ((α.app c).map φ)) ≫
          β.oplaxApp f ((α.app c).obj y) := by rw [hα]
      _ = ((β.app c').map (α.oplaxApp f x) ≫
          (β.app c').map ((H'.map f).toFunctor.map ((α.app c).map φ))) ≫
          β.oplaxApp f ((α.app c).obj y) := by rw [(β.app c').map_comp]
      _ = (β.app c').map (α.oplaxApp f x) ≫
          (β.app c').map ((H'.map f).toFunctor.map ((α.app c).map φ)) ≫
          β.oplaxApp f ((α.app c).obj y) := by simp only [Category.assoc]
      _ = (β.app c').map (α.oplaxApp f x) ≫
          (β.oplaxApp f ((α.app c).obj x) ≫
          (K'.map f).toFunctor.map ((β.app c).map ((α.app c).map φ))) := by rw [hβ]
      _ = _ := by simp only [Category.assoc]
  oplaxId c x := by
    simp only [Functor.comp_obj, α.oplaxId, eqToHom_map, β.oplaxId, eqToHom_trans]
  oplaxComp {c c' c''} f g x := by
    simp only [α.oplaxComp f g x, β.oplaxComp f g ((α.app c).obj x)]
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans_assoc]
    congr 1
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc, eqToHom_refl, Category.id_comp]
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc]
    congr 1
    exact β.oplaxNat g (α.oplaxApp f x)

/--
Construct a functor `GrothendieckContra' G' ⥤ GrothendieckContra' F'` from an oplax
natural transformation. This functor is the identity on base objects.
-/
def OplaxNatTransData.toFunctor (α : OplaxNatTransData G' F') :
    GrothendieckContra' G' ⥤ GrothendieckContra' F' where
  obj X := ⟨X.base, (α.app X.base).obj X.fiber⟩
  map {X Y} f := ⟨f.base, (α.app X.base).map f.fiber ≫ α.oplaxApp f.base Y.fiber⟩
  map_id X := by
    refine GrothendieckContra'.ext _ _ ?_ ?_
    · rfl
    · change ((α.app X.base).map (GrothendieckContra'.id (F' := G') X).fiber ≫
        α.oplaxApp (GrothendieckContra'.id (F' := G') X).base X.fiber) ≫ eqToHom _ =
        (GrothendieckContra'.id (F' := F') ⟨X.base, (α.app X.base).obj X.fiber⟩).fiber
      simp only [GrothendieckContra'.id_fiber_val, GrothendieckContra'.id_base,
        α.oplaxId, eqToHom_map, eqToHom_trans]
  map_comp {X Y Z} f g := by
    refine GrothendieckContra'.ext _ _ ?_ ?_
    · rfl
    · change ((α.app X.base).map (GrothendieckContra'.comp f g).fiber ≫
        α.oplaxApp (GrothendieckContra'.comp f g).base Z.fiber) ≫ eqToHom _ =
        (GrothendieckContra'.comp
          (⟨f.base, (α.app X.base).map f.fiber ≫ α.oplaxApp f.base Y.fiber⟩ :
            GrothendieckContra'.Hom
              ⟨X.base, (α.app X.base).obj X.fiber⟩ ⟨Y.base, (α.app Y.base).obj Y.fiber⟩)
          (⟨g.base, (α.app Y.base).map g.fiber ≫ α.oplaxApp g.base Z.fiber⟩ :
            GrothendieckContra'.Hom
              ⟨Y.base, (α.app Y.base).obj Y.fiber⟩ ⟨Z.base, (α.app Z.base).obj Z.fiber⟩)).fiber
      simp only [GrothendieckContra'.comp_fiber, GrothendieckContra'.comp_base]
      -- OplaxComp takes f : c' ⟶ c and g : c'' ⟶ c' with composition g ≫ f.
      -- Here f.base : X.base ⟶ Y.base and g.base : Y.base ⟶ Z.base, so f.base ≫ g.base.
      -- We apply oplaxComp with arguments swapped: g.base plays role of f, f.base plays role of g.
      simp only [α.oplaxComp g.base f.base Z.fiber]
      simp only [(α.app X.base).map_comp, (F'.map f.base).toFunctor.map_comp, eqToHom_map,
        Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      slice_lhs 2 3 => rw [α.oplaxNat f.base g.fiber]
      simp only [Category.assoc, Category.comp_id]

/--
The functor from an oplax nat trans is identity on base.
-/
@[simp]
theorem OplaxNatTransData.toFunctor_obj_base (α : OplaxNatTransData G' F')
    (X : GrothendieckContra' G') :
    (α.toFunctor.obj X).base = X.base := by
  unfold OplaxNatTransData.toFunctor
  rfl

/--
The functor from an oplax nat trans is identity on base morphisms.
-/
@[simp]
theorem OplaxNatTransData.toFunctor_map_base (α : OplaxNatTransData G' F')
    {X Y : GrothendieckContra' G'} (f : X ⟶ Y) :
    (α.toFunctor.map f).base = f.base := by
  unfold OplaxNatTransData.toFunctor
  rfl

variable {D : Type uC} [Category.{vC} D]

set_option backward.isDefEq.respectTransparency false in
/--
Left whiskering: precompose an oplax natural transformation with a functor.

Given `H : D ⥤ C` and `α : OplaxNatTransData G' F'` where `G' F' : Cᵒᵖ' ⥤ Cat`,
produces `OplaxNatTransData (H.op' ⋙ G') (H.op' ⋙ F')`.

The component at `d : D` is `α.app (H.obj d)`, and the oplax morphism for
`f : d ⟶ d'` in `Dᵒᵖ'` is `α.oplaxApp (H.map f)` where `H.map f : H.obj d ⟶ H.obj d'`
in `Cᵒᵖ'`.
-/
def OplaxNatTransData.whiskerLeft (H : D ⥤ C) (α : OplaxNatTransData G' F') :
    OplaxNatTransData (Functor.op' H ⋙ G') (Functor.op' H ⋙ F') where
  app d := α.app (H.obj d)
  oplaxApp f x := α.oplaxApp (H.map f) x
  oplaxNat {d d'} f {x y} φ := α.oplaxNat (H.map f) φ
  oplaxId d x := by
    simp only [Functor.comp_obj, Functor.comp_map, Functor.op']
    convert α.oplaxId (H.obj d) x using 2 <;> simp [H.map_id]
  oplaxComp {d d' d''} f g x := by
    simp only [Functor.comp_obj, Functor.comp_map, Functor.op', functorOp'Obj]
    have h := α.oplaxComp (H.map f) (H.map g) x
    simp only at h ⊢
    grind

/--
Left whiskering respects identity oplax natural transformations.
-/
theorem OplaxNatTransData.whiskerLeft_id (H : D ⥤ C) :
    (OplaxNatTransData.id G').whiskerLeft H = OplaxNatTransData.id (Functor.op' H ⋙ G') := by
  simp only [whiskerLeft, OplaxNatTransData.id, Functor.op']
  congr

/--
Left whiskering respects composition of oplax natural transformations.
-/
theorem OplaxNatTransData.whiskerLeft_comp (H : D ⥤ C)
    {K' : Cᵒᵖ' ⥤ Cat.{vF, uF}}
    (α : OplaxNatTransData G' F') (β : OplaxNatTransData F' K') :
    (α.comp β).whiskerLeft H = (α.whiskerLeft H).comp (β.whiskerLeft H) := rfl

end OplaxNatTrans

/-!
## Contravariant FunctorBetween Decomposition via Pre

This section shows that `FunctorBetweenContraData` decomposes via oplax natural
transformations and the `pre` functor.
-/

section FunctorBetweenContraDecomposition

universe vC' uC'

variable {C : Type uC'} [Category.{vC'} C] (G' : Cᵒᵖ' ⥤ Cat.{vC', uC'})
variable {D : Type uC'} [Category.{vC'} D] (F' : Dᵒᵖ' ⥤ Cat.{vC', uC'})

set_option backward.isDefEq.respectTransparency false in
/--
Convert a `FunctorBetweenContraData` to an `OplaxNatTransData` for the composite
functor `functorOp'Obj baseFib ⋙ F'`.

This shows that functor data between contravariant Grothendieck constructions
decomposes into a base functor and an oplax natural transformation.

Note: `FunctorBetweenContraData` uses composition `f ≫ g` for `f : c ⟶ c'` and
`g : c' ⟶ c''`, while `OplaxNatTransData` uses composition `g ≫ f` for
`f : c' ⟶ c` and `g : c'' ⟶ c'`. We adapt by swapping the arguments when
converting.
-/
def FunctorBetweenContraData.toOplaxNatTrans (data : FunctorBetweenContraData G' F') :
    OplaxNatTransData G' (functorOp'Obj data.baseFib ⋙ F') where
  app c := data.fibFib c
  oplaxApp {c c'} f x := data.fibHomCrossApp f x
  oplaxNat {c c'} f {x y} φ := data.fibHomCrossNat f φ
  oplaxId c x := data.baseHomId c x
  oplaxComp {c c' c''} f g x := by
    -- OplaxComp: f : c' ⟶ c, g : c'' ⟶ c', x : G'.obj c, composition g ≫ f : c'' ⟶ c
    -- data.baseHomComp expects: f' : c ⟶ c', g' : c' ⟶ c'', composition f' ≫ g'
    -- We use data.baseHomComp g f x to match: g : c'' ⟶ c', f : c' ⟶ c, composition g ≫ f
    simp only [Functor.comp_obj, Functor.comp_map]
    have h := data.baseHomComp g f x
    simp only [functorOp'Obj] at h ⊢
    rw [← h]
    simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/--
Construct the functor `GrothendieckContra' G' ⥤ GrothendieckContra' F'` via the
oplax-pre factorization.

Given `FunctorBetweenContraData G' F'`, we factor the functor as:
`toOplaxNatTrans.toFunctor ⋙ GrothendieckContra'.pre F' baseFib`

This makes the `pre` functor central to the decomposition of functors between
contravariant Grothendieck constructions.
-/
def FunctorBetweenContraData.toFunctorViaPre (data : FunctorBetweenContraData G' F') :
    GrothendieckContra' G' ⥤ GrothendieckContra' F' :=
  (data.toOplaxNatTrans G' F').toFunctor ⋙ GrothendieckContra'.pre F' data.baseFib

/--
The object map of `toFunctorViaPre`.
-/
theorem FunctorBetweenContraData.toFunctorViaPre_obj (data : FunctorBetweenContraData G' F')
    (X : GrothendieckContra' G') :
    (data.toFunctorViaPre G' F').obj X =
      ⟨data.baseFib.obj X.base, (data.fibFib X.base).obj X.fiber⟩ := rfl

/--
The morphism map of `toFunctorViaPre`.
-/
theorem FunctorBetweenContraData.toFunctorViaPre_map (data : FunctorBetweenContraData G' F')
    {X Y : GrothendieckContra' G'} (f : X ⟶ Y) :
    (data.toFunctorViaPre G' F').map f =
      ⟨data.baseFib.map f.base,
       (data.fibFib X.base).map f.fiber ≫ data.fibHomCrossApp f.base Y.fiber⟩ := rfl

end FunctorBetweenContraDecomposition

/-!
## The Category of Contravariant Cat-Valued Functors with Oplax Natural Transformations

This section defines `OplaxFunctorCat`, a wrapper type around `Cᵒᵖ' ⥤ Cat` where
morphisms are oplax natural transformations rather than natural transformations.
-/

section OplaxFunctorCat

universe vC uC

variable (C : Type uC) [Category.{vC} C]

/--
A wrapper type for `Cᵒᵖ' ⥤ Cat` where morphisms are oplax natural transformations.
-/
@[ext]
structure OplaxFunctorCat where
  /-- The underlying functor to Cat. -/
  toFunctor : Cᵒᵖ' ⥤ Cat.{vC, uC}

variable {C}

/-- Coercion from `OplaxFunctorCat` to functor. -/
instance : CoeOut (OplaxFunctorCat C) (Cᵒᵖ' ⥤ Cat.{vC, uC}) where
  coe := OplaxFunctorCat.toFunctor

/-- Wrap a functor as an `OplaxFunctorCat`. -/
abbrev OplaxFunctorCat.of (F' : Cᵒᵖ' ⥤ Cat.{vC, uC}) : OplaxFunctorCat C := ⟨F'⟩

/-- Associativity of oplax natural transformation composition. -/
theorem OplaxNatTransData.comp_assoc {G' H' K' L' : Cᵒᵖ' ⥤ Cat.{vC, uC}}
    (α : OplaxNatTransData G' H') (β : OplaxNatTransData H' K')
    (γ : OplaxNatTransData K' L') :
    (α.comp β).comp γ = α.comp (β.comp γ) := by
  cases α; cases β; cases γ
  simp only [OplaxNatTransData.comp, Functor.assoc]
  congr 1
  funext c x'
  simp only [Functor.comp_obj, Functor.comp_map, Category.assoc, Functor.map_comp]

/-- Left identity for oplax natural transformation composition. -/
theorem OplaxNatTransData.id_comp {G' H' : Cᵒᵖ' ⥤ Cat.{vC, uC}}
    (α : OplaxNatTransData G' H') :
    (OplaxNatTransData.id G').comp α = α := by
  cases α with | mk app oplaxApp _ _ _ =>
  simp only [OplaxNatTransData.comp, OplaxNatTransData.id]
  congr 1
  funext c f g y'
  simp only [Functor.id_obj, eqToHom_refl, CategoryTheory.Functor.map_id]
  exact Category.id_comp _

/-- Right identity for oplax natural transformation composition. -/
theorem OplaxNatTransData.comp_id {G' H' : Cᵒᵖ' ⥤ Cat.{vC, uC}}
    (α : OplaxNatTransData G' H') :
    α.comp (OplaxNatTransData.id H') = α := by
  cases α with | mk app oplaxApp _ _ _ =>
  simp only [OplaxNatTransData.comp, OplaxNatTransData.id]
  congr 1
  funext c f g y'
  simp [Functor.id_obj, Functor.id_map]

/-- The category structure on `OplaxFunctorCat C` with oplax natural transformations
as morphisms. -/
instance : Category (OplaxFunctorCat C) where
  Hom G' H' := OplaxNatTransData G'.toFunctor H'.toFunctor
  id G' := OplaxNatTransData.id G'.toFunctor
  comp := OplaxNatTransData.comp
  id_comp := OplaxNatTransData.id_comp
  comp_id := OplaxNatTransData.comp_id
  assoc := OplaxNatTransData.comp_assoc

end OplaxFunctorCat

/-!
## Double Grothendieck Constructions

Polynomial functors arise as double Grothendieck constructions. Given a span
`I ← E → X` defining a polynomial functor:
- First layer: position functor `p : E → I` gives `∫ᵖ E`
- Second layer: direction functor `d : E → X` gives `∫ᵈ (∫ᵖ E)`

This section provides infrastructure for working with such composed
Grothendieck constructions.
-/

section DoubleGrothendieck

variable {C : Type*} [Category C]

/--
Given functors `F : C ⥤ Cat` and `G : ∫F ⥤ Cat`, the double Grothendieck
construction `∫∫(F,G)` is defined as `∫G`, the Grothendieck construction of `G`
over the already-constructed `∫F`.

This represents families indexed by the total space of `F`, which themselves
vary over the base `C`.
-/
abbrev DoubleGrothendieck (F : C ⥤ Cat) (G : Grothendieck F ⥤ Cat) : Type _ :=
  Grothendieck G

/--
Objects in the double Grothendieck construction consist of:
- A base object `c : C`
- A first-layer fiber `x : F.obj c`
- A second-layer fiber `y : G.obj ⟨c, x⟩`
-/
def DoubleGrothendieck.mk {F : C ⥤ Cat} {G : Grothendieck F ⥤ Cat}
    (c : C) (x : F.obj c) (y : G.obj ⟨c, x⟩) :
    DoubleGrothendieck F G :=
  ⟨⟨c, x⟩, y⟩

/--
Extract the base component from a double Grothendieck object.
-/
def DoubleGrothendieck.baseObj {F : C ⥤ Cat} {G : Grothendieck F ⥤ Cat}
    (obj : DoubleGrothendieck F G) : C :=
  obj.base.1

/--
Extract the first fiber from a double Grothendieck object.
-/
def DoubleGrothendieck.fib1 {F : C ⥤ Cat} {G : Grothendieck F ⥤ Cat}
    (obj : DoubleGrothendieck F G) : F.obj (baseObj obj) :=
  obj.base.2

/--
Extract the second fiber from a double Grothendieck object.
-/
def DoubleGrothendieck.fib2 {F : C ⥤ Cat} {G : Grothendieck F ⥤ Cat}
    (obj : DoubleGrothendieck F G) : G.obj obj.base :=
  obj.2

/--
Forgetful functor from double Grothendieck to single Grothendieck,
forgetting the second layer.
-/
def DoubleGrothendieck.forgetSecond {F : C ⥤ Cat} (G : Grothendieck F ⥤ Cat) :
    DoubleGrothendieck F G ⥤ Grothendieck F :=
  Grothendieck.forget G

/--
Forgetful functor from double Grothendieck to base, forgetting both layers.
-/
def DoubleGrothendieck.forgetBoth {F : C ⥤ Cat} (G : Grothendieck F ⥤ Cat) :
    DoubleGrothendieck F G ⥤ C :=
  forgetSecond G ⋙ Grothendieck.forget F

/--
The composition of double Grothendieck forgetful functors.
-/
theorem DoubleGrothendieck.forgetBoth_eq_comp {F : C ⥤ Cat}
    (G : Grothendieck F ⥤ Cat) :
    forgetBoth G = forgetSecond G ⋙ Grothendieck.forget F :=
  rfl

/--
Inclusion of the second-layer fiber at a point in `Grothendieck F`.
Given `obj : Grothendieck F`, this includes `G.obj obj` into the double
Grothendieck construction over `obj`.
-/
def DoubleGrothendieck.ιSecond {F : C ⥤ Cat} (G : Grothendieck F ⥤ Cat)
    (obj : Grothendieck F) : G.obj obj ⥤ DoubleGrothendieck F G :=
  Grothendieck.ι G obj

/--
Objects in the second-layer fiber at `obj` map to objects in the double
Grothendieck with `obj` as their first-layer component.
-/
@[simp]
theorem DoubleGrothendieck.ιSecond_obj {F : C ⥤ Cat} (G : Grothendieck F ⥤ Cat)
    (obj : Grothendieck F) (y : G.obj obj) :
    (ιSecond G obj).obj y = ⟨obj, y⟩ :=
  rfl

/--
The composition of ιSecond with forgetSecond gives back the base object.
-/
theorem DoubleGrothendieck.ιSecond_comp_forgetSecond {F : C ⥤ Cat}
    (G : Grothendieck F ⥤ Cat) (obj : Grothendieck F) (y : G.obj obj) :
    (forgetSecond G).obj ((ιSecond G obj).obj y) = obj :=
  rfl

/--
The nested fiber at a point in the double Grothendieck construction.
Given `c : C`, `x : F.obj c`, this gives a functor from `G.obj ⟨c, x⟩`
into the double Grothendieck.
-/
def DoubleGrothendieck.ιNested {F : C ⥤ Cat} (G : Grothendieck F ⥤ Cat)
    (c : C) (x : F.obj c) : G.obj ⟨c, x⟩ ⥤ DoubleGrothendieck F G :=
  ιSecond G ⟨c, x⟩

/--
Objects via ιNested are triples with the given base and first fiber.
-/
@[simp]
theorem DoubleGrothendieck.ιNested_obj {F : C ⥤ Cat} (G : Grothendieck F ⥤ Cat)
    (c : C) (x : F.obj c) (y : G.obj ⟨c, x⟩) :
    (ιNested G c x).obj y = mk c x y :=
  rfl

/--
The forgetBoth functor factors through forgetSecond then forget.
This is the definitional equality exposed as a functor isomorphism.
-/
def DoubleGrothendieck.forgetBothIso {F : C ⥤ Cat} (G : Grothendieck F ⥤ Cat) :
    forgetBoth G ≅ forgetSecond G ⋙ Grothendieck.forget F :=
  Iso.refl _

/--
The two components of a double Grothendieck object's base.
-/
theorem DoubleGrothendieck.forgetSecond_base_eq {F : C ⥤ Cat}
    {G : Grothendieck F ⥤ Cat} (obj : DoubleGrothendieck F G) :
    ((forgetSecond G).obj obj).base = baseObj obj :=
  rfl

/--
The two components of a double Grothendieck object's first fiber.
-/
theorem DoubleGrothendieck.forgetSecond_fiber_eq {F : C ⥤ Cat}
    {G : Grothendieck F ⥤ Cat} (obj : DoubleGrothendieck F G) :
    ((forgetSecond G).obj obj).fiber = fib1 obj :=
  rfl

/--
Functors into double Grothendieck factor as: first into single Grothendieck,
then lifted to double. This states that composing with forgetSecond recovers
the intermediate functor.
-/
theorem DoubleGrothendieck.functor_factors_forgetSecond {D : Type*} [Category D]
    {F : C ⥤ Cat} {G : Grothendieck F ⥤ Cat}
    (H : D ⥤ DoubleGrothendieck F G) :
    ∃ (H₁ : D ⥤ Grothendieck F), H ⋙ forgetSecond G = H₁ :=
  ⟨H ⋙ forgetSecond G, rfl⟩

/--
Functors from double Grothendieck compose naturally: a functor from
Grothendieck G composed with a functor from each G-fiber gives a functor
from the double construction.
-/
theorem DoubleGrothendieck.functor_from_factors {E : Type*} [Category E]
    {F : C ⥤ Cat} {G : Grothendieck F ⥤ Cat}
    (H : DoubleGrothendieck F G ⥤ E) :
    ∃ (fibFunctors : ∀ obj : Grothendieck F, G.obj obj ⥤ E),
      ∀ obj y, H.obj ⟨obj, y⟩ = (fibFunctors obj).obj y :=
  ⟨fun obj => ιSecond G obj ⋙ H, fun _ _ => rfl⟩

/-!
### Layered Construction of Functors into Double Grothendieck

A functor `D ⥤ DoubleGrothendieck F G` factors through the layered structure:
the outer layer uses `functorTo G`, whose base functor is itself a functor
`D ⥤ Grothendieck F` arising from `functorTo F`.

Pattern for constructing functors into double Grothendieck:
1. Define first-layer FunctorToData F to get `firstLayer : D ⥤ Grothendieck F`
2. Define second-layer FunctorToData G with `baseFunc := firstLayer`
3. Apply `functorTo G` to get `D ⥤ DoubleGrothendieck F G`

The double Grothendieck universal property composes the two single-layer
universal properties. See FunctorToData and functorTo in the FunctorTo section
for the single-layer construction.
-/

end DoubleGrothendieck

/-! ## Grothendieck Construction as a Functor -/

section GrothendieckFunctor

universe v₃ u₃ v₄ u₄

/--
The Grothendieck construction as a functor: sends a functor
`F : C ⥤ Cat` to `Grothendieck F`, and a natural
transformation `α : F ⟶ G` to `Grothendieck.map α`.
-/
def grothendieckFunctor
    (C : Type u₄) [Category.{v₄} C] :
    (C ⥤ Cat.{v₃, u₃}) ⥤
      Cat.{max v₄ v₃, max u₄ u₃} where
  obj F := Cat.of (Grothendieck F)
  map α := (Grothendieck.map α).toCatHom
  map_id F := by
    apply Cat.Hom.ext
    exact Grothendieck.map_id_eq
  map_comp α β := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor,
      Functor.toCatHom_toFunctor]
    exact Grothendieck.map_comp_eq α β

end GrothendieckFunctor

/-! ## Slice-Refined Grothendieck Functor -/

section GrothendieckFunctorOver

universe v₁₀ u₁₀

/--
The slice-refined version of `grothendieckFunctor`, landing in the
`Over` category of `Cat` over `E`.  Each functor `F : E ⥤ Cat` is
sent to `(Grothendieck F, Grothendieck.forget F)` as an object of
`Over E`; morphisms use `grothendieckFunctor.map` together with the
commutativity `Grothendieck.map α ⋙ Grothendieck.forget _
= Grothendieck.forget _`.

When the universe levels match, this is definitionally equal to
mathlib's `Grothendieck.functor`.  The point of this factoring is
to make explicit that mathlib's slice-refined construction
`Grothendieck.functor` decomposes into two orthogonal pieces:

1. Our `grothendieckFunctor`, which is universe-polymorphic in four
   levels (base and fibre `Cat` may live at independent universes).
2. `Grothendieck.forget` + the slice packaging, which requires the
   base and fibre to live at the same `Cat` level.

Thus the universe restriction in mathlib's `Grothendieck.functor`
can be attributed to the slice packaging alone, not to the
Grothendieck construction itself.
-/
def grothendieckFunctorOver {E : Cat.{v₁₀, u₁₀}} :
    (E ⥤ Cat.{v₁₀, u₁₀}) ⥤ Over (T := Cat.{v₁₀, u₁₀}) E where
  obj F := Over.mk (Grothendieck.forget F).toCatHom
  map {_ _} α := Over.homMk ((grothendieckFunctor E).map α)
    congr($(Grothendieck.functor_comp_forget).toCatHom)
  map_id F := by
    ext
    exact Grothendieck.map_id_eq (F := F)
  map_comp α β := by
    ext
    exact Grothendieck.map_comp_eq α β

/--
`grothendieckFunctorOver` equals mathlib's `Grothendieck.functor`
definitionally.  This confirms the factoring: mathlib's
`Grothendieck.functor` is `grothendieckFunctor` plus the slice
packaging, with no hidden data.
-/
theorem grothendieckFunctorOver_eq_functor {E : Cat.{v₁₀, u₁₀}} :
    (grothendieckFunctorOver : (E ⥤ Cat.{v₁₀, u₁₀}) ⥤ _) =
      Grothendieck.functor := rfl

/--
Forgetting the slice recovers `grothendieckFunctor`.  Together with
`grothendieckFunctorOver_eq_functor`, this expresses the identity
`grothendieckFunctor = Grothendieck.functor ⋙ Over.forget _` at
matched universes.
-/
theorem grothendieckFunctorOver_comp_forget {E : Cat.{v₁₀, u₁₀}} :
    grothendieckFunctorOver (E := E) ⋙ Over.forget _ =
      grothendieckFunctor E := rfl

end GrothendieckFunctorOver

/-! ## Grothendieck Pre as a Natural Transformation -/

section GrothendieckPre

universe v₅ u₅ v₆ u₆

/--
Given a functor `G : C ⥤ D` (with `C` and `D` in the same
universes), `Grothendieck.pre` at each `F : D ⥤ Cat` assembles
into a natural transformation from the composite
`(Functor.whiskeringLeft C D Cat).obj G ⋙ grothendieckFunctor C`
to `grothendieckFunctor D`.
-/
def grothendieckPre
    {C : Type u₅} [Category.{v₅} C]
    {D : Type u₅} [Category.{v₅} D]
    (G : C ⥤ D) :
    (Functor.whiskeringLeft C D Cat.{v₆, u₆}).obj G ⋙
      grothendieckFunctor C ⟶
      grothendieckFunctor D where
  app F := (Grothendieck.pre F G).toCatHom
  naturality F H α := by
    apply Cat.Hom.ext
    simp only [Functor.comp_map,
      Cat.Hom.comp_toFunctor]
    exact (Grothendieck.pre_comp_map G α).symm

end GrothendieckPre

/-! ## Contravariant Grothendieck Construction as a Functor -/

section GrothendieckContraFunctor

universe v₇ u₇ v₈ u₈

/--
The contravariant Grothendieck construction as a functor.
Sends `F : Cᵒᵖ ⥤ Cat` to the category with objects
`(c : C, x : F.obj c.op)` and morphisms `(c, x) ⟶ (c', x')`
given by `(f : c ⟶ c', φ : x ⟶ (F.map f.op).obj x')`.

Defined as the composite of three steps:
1. Post-compose `F` with `Cat.opFunctor`, replacing each fibre
   category with its opposite.
2. Apply the covariant `grothendieckFunctor`.
3. Post-compose with `Cat.opFunctor`, taking the opposite of the
   resulting total category.

This realizes the strict 1-categorical straightening of a presheaf of
categories into its associated fibration; the resulting total category
admits a canonical forgetful functor to `C` whose fibres over `c : C`
are the categories `F.obj c.op`.  See
https://ncatlab.org/nlab/show/Grothendieck+construction
for a description.
-/
def grothendieckContraFunctor
    (C : Type u₈) [Category.{v₈} C] :
    (Cᵒᵖ ⥤ Cat.{v₇, u₇}) ⥤
      Cat.{max v₈ v₇, max u₈ u₇} :=
  (Functor.whiskeringRight _ _ _).obj Cat.opFunctor.{v₇, u₇} ⋙
    grothendieckFunctor Cᵒᵖ ⋙
    Cat.opFunctor.{max v₈ v₇, max u₈ u₇}

namespace GrothendieckContraFunctor

variable {C : Type u₈} [Category.{v₈} C] {F : Cᵒᵖ ⥤ Cat.{v₇, u₇}}

/--
Construct an object of `(grothendieckContraFunctor C).obj F`
from a base `c : C` and a fibre `x : F.obj (op c)`.
-/
def mkObj (c : C) (x : F.obj (Opposite.op c)) :
    (grothendieckContraFunctor C).obj F :=
  Opposite.op (⟨Opposite.op c, Opposite.op x⟩ :
    Grothendieck (F ⋙ Cat.opFunctor.{v₇, u₇}))

/--
The base of an object of `(grothendieckContraFunctor C).obj F`.
-/
def objBase (X : (grothendieckContraFunctor C).obj F) : C :=
  X.unop.base.unop

/--
The fibre of an object of `(grothendieckContraFunctor C).obj F`.
-/
def objFiber (X : (grothendieckContraFunctor C).obj F) :
    F.obj (Opposite.op (objBase X)) :=
  X.unop.fiber.unop

@[simp]
theorem objBase_mkObj (c : C) (x : F.obj (Opposite.op c)) :
    objBase (mkObj c x) = c := rfl

@[simp]
theorem objFiber_mkObj (c : C) (x : F.obj (Opposite.op c)) :
    objFiber (mkObj c x) = x := rfl

/--
Construct a morphism in `(grothendieckContraFunctor C).obj F`
from a base morphism `h : objBase X ⟶ objBase Y` and a fibre
morphism `ψ : objFiber X ⟶ (F.map h.op).toFunctor.obj (objFiber Y)`.
-/
def mkHom
    {X Y : (grothendieckContraFunctor C).obj F}
    (h : objBase X ⟶ objBase Y)
    (ψ : objFiber X ⟶ (F.map h.op).toFunctor.obj (objFiber Y)) :
    X ⟶ Y :=
  Quiver.Hom.op
    (⟨h.op, ψ.op⟩ : Grothendieck.Hom Y.unop X.unop)

/--
The base of a morphism in `(grothendieckContraFunctor C).obj F`.
-/
def homBase {X Y : (grothendieckContraFunctor C).obj F}
    (f : X ⟶ Y) : objBase X ⟶ objBase Y :=
  f.unop.base.unop

/--
The fibre of a morphism in `(grothendieckContraFunctor C).obj F`.
-/
def homFiber
    {X Y : (grothendieckContraFunctor C).obj F} (f : X ⟶ Y) :
    objFiber X ⟶ (F.map (homBase f).op).toFunctor.obj (objFiber Y) :=
  f.unop.fiber.unop

@[simp]
theorem homBase_mkHom
    {X Y : (grothendieckContraFunctor C).obj F}
    (h : objBase X ⟶ objBase Y)
    (ψ : objFiber X ⟶ (F.map h.op).toFunctor.obj (objFiber Y)) :
    homBase (mkHom h ψ) = h := rfl

@[simp]
theorem homFiber_mkHom
    {X Y : (grothendieckContraFunctor C).obj F}
    (h : objBase X ⟶ objBase Y)
    (ψ : objFiber X ⟶ (F.map h.op).toFunctor.obj (objFiber Y)) :
    homFiber (mkHom h ψ) = ψ := rfl

end GrothendieckContraFunctor

end GrothendieckContraFunctor

/-! ## Slice-Refined Contravariant Grothendieck Functor -/

section GrothendieckContraFunctorOver

universe v₁₁ u₁₁

set_option backward.isDefEq.respectTransparency false in
/--
Slice-level left-oppotization on `Cat`: given `X : Cat`, the functor
`Over (Cat.opFunctor.obj X) ⥤ Over X` sending `(Y, f : Y ⟶ Xᵒᵖ)` to
`(Cat.opFunctor.obj Y, f.toFunctor.leftOp.toCatHom)`.

This is the natural slice-level version of `Functor.leftOp`: it acts
on the underlying Cat by `Cat.opFunctor` and on the over-projection
by `Functor.leftOp`, reinterpreting a slice over `Xᵒᵖ` as a slice
over `X`.
-/
def Cat.Over.leftOp {X : Cat.{v₁₁, u₁₁}} :
    Over (T := Cat.{v₁₁, u₁₁}) (Cat.opFunctor.obj X) ⥤
      Over (T := Cat.{v₁₁, u₁₁}) X where
  obj Y := Over.mk Y.hom.toFunctor.leftOp.toCatHom
  map {Y Y'} f := Over.homMk (Cat.opFunctor.map f.left) (by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Cat.opFunctor_map,
      Functor.toCatHom_toFunctor]
    have hw : f.left.toFunctor ⋙ Y'.hom.toFunctor = Y.hom.toFunctor := by
      rw [← Cat.Hom.comp_toFunctor]; exact congrArg _ (Over.w f)
    calc f.left.toFunctor.op ⋙ Y'.hom.toFunctor.leftOp
        = (f.left.toFunctor ⋙ Y'.hom.toFunctor).leftOp := rfl
      _ = Y.hom.toFunctor.leftOp := by rw [hw])
  map_id Y := by
    ext
    simp; rfl
  map_comp f g := by
    ext
    simp; rfl

/--
The slice-refined version of `grothendieckContraFunctor`, landing
in the `Over` category of `Cat` over `E`.  Each `F : Eᵒᵖ ⥤ Cat` is
sent to its contravariant Grothendieck total paired with the
canonical forgetful to `E`.

Constructed compositionally as:
1. Post-compose with `Cat.opFunctor` on fibres (`whiskeringRight`).
2. Apply the slice-refined covariant Grothendieck construction
   (mathlib's `Grothendieck.functor`) at base `Eᵒᵖ`, landing in
   `Over Eᵒᵖ`.
3. Apply slice-level left-oppotization `Cat.Over.leftOp`, landing
   in `Over E`.

When universe levels match, composition with `Over.forget` recovers
our `grothendieckContraFunctor` — demonstrating that the slice
restriction (same universe for base and fibres) comes entirely from
step 3's `Over` packaging, not from the underlying Grothendieck
construction.
-/
def grothendieckContraFunctorOver {E : Cat.{v₁₁, u₁₁}} :
    (Eᵒᵖ ⥤ Cat.{v₁₁, u₁₁}) ⥤ Over (T := Cat.{v₁₁, u₁₁}) E :=
  (Functor.whiskeringRight _ _ _).obj Cat.opFunctor.{v₁₁, u₁₁} ⋙
    @Grothendieck.functor (Cat.opFunctor.obj E) ⋙
    Cat.Over.leftOp

/--
Forgetting the slice recovers `grothendieckContraFunctor` (at
matched universes).  Analogue of `grothendieckFunctorOver_comp_forget`.
-/
theorem grothendieckContraFunctorOver_comp_forget
    {E : Cat.{v₁₁, u₁₁}} :
    grothendieckContraFunctorOver (E := E) ⋙ Over.forget _ =
      grothendieckContraFunctor E := rfl

end GrothendieckContraFunctorOver

/-! ## Strict Two-Sided Grothendieck Construction

This section implements the strict two-sided Grothendieck
construction for bifunctors `H : Dᵒᵖ ⥤ C ⥤ Cat` (Lucyshyn-Wright
Def. 7.1 / Stefanich arXiv:2011.03027), landing in
`Over (Cat.of (C × D))` so that the commutativity conditions of
the two-sided construction are encoded by slice morphisms.

Built from two reusable slice-preserving Grothendieck primitives:
`sliceContraFunctor` (contravariant outer) and `sliceCovFunctor`
(covariant outer).  The two-sided construction is then realized
compositionally in two equivalent orderings, related by a natural
isomorphism.
-/

section StrictTwoSidedGrothendieck

universe v_sp u_sp

variable {C D : Cat.{v_sp, u_sp}}

set_option backward.isDefEq.respectTransparency false in
/--
Projection from the covariant Grothendieck of a constant-`Cat`-valued
functor `(Functor.const D).obj X` to the fibre `X`.  On objects, sends
`⟨d, x⟩ ↦ x`; on morphisms, sends `⟨f, φ⟩ ↦ φ`.

This is the "second projection" in the canonical equivalence
`Grothendieck ((Functor.const D).obj X) ≃ D × X`.
-/
def grothOfConstProj
    (D : Cat.{v_sp, u_sp}) (X : Cat.{v_sp, u_sp}) :
    (Cat.of (Grothendieck ((Functor.const D).obj X))) ⥤
      (X : Cat.{v_sp, u_sp}) where
  obj g := g.fiber
  map {g₁ _} f :=
    eqToHom (rfl : g₁.fiber =
      (((Functor.const D).obj X).map f.base).toFunctor.obj g₁.fiber)
      ≫ f.fiber
  map_id g := by
    rw [Grothendieck.id_fiber]
    simp
  map_comp {_ _ _} f g := by
    rw [Grothendieck.comp_fiber]
    simp

set_option backward.isDefEq.respectTransparency false in
/--
Projection from the contravariant Grothendieck of a constant-
`Cat`-valued functor `(Functor.const Dᵒᵖ).obj X` to the fibre `X`.
Dual of `grothOfConstProj`.
-/
def grothContraOfConstProj
    (D : Cat.{v_sp, u_sp}) (X : Cat.{v_sp, u_sp}) :
    ((grothendieckContraFunctor D).obj
        ((Functor.const Dᵒᵖ).obj X)).α ⥤
      (X : Cat.{v_sp, u_sp}) where
  obj opg := opg.unop.fiber.unop
  map {_ _} f := f.unop.fiber.unop
  map_id opg := by
    change (𝟙 opg).unop.fiber.unop = _
    rw [show (𝟙 opg).unop = 𝟙 opg.unop from rfl,
      Grothendieck.id_fiber]
    simp
  map_comp {_ _ _} f g := by
    rw [show (f ≫ g) =
        Quiver.Hom.op (g.unop ≫ f.unop) from rfl]
    dsimp only [Quiver.Hom.unop_op]
    rw [Grothendieck.comp_fiber]
    simp

/--
Given `G : Dᵒᵖ ⥤ Over C`, the natural transformation from
`G ⋙ Over.forget _` to the constant functor at `C` whose component
at each `d : Dᵒᵖ` is the slice projection `(G.obj d).hom`.
-/
def sliceCoverNatTrans
    (G : Dᵒᵖ ⥤ Over (T := Cat.{v_sp, u_sp}) C) :
    G ⋙ Over.forget _ ⟶ (Functor.const Dᵒᵖ).obj C where
  app d := (G.obj d).hom
  naturality {d₁ d₂} f := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map,
      Over.forget_map]
    change (G.map f).left.toFunctor ⋙ (G.obj d₂).hom.toFunctor =
        (G.obj d₁).hom.toFunctor ⋙ 𝟭 _
    rw [Functor.comp_id, ← Cat.Hom.comp_toFunctor]
    exact congrArg _ (Over.w (G.map f))

/--
Given `F : C ⥤ Over D`, the natural transformation from
`F ⋙ Over.forget _` to the constant functor at `D` whose component
at each `c : C` is the slice projection `(F.obj c).hom`.  Dual of
`sliceCoverNatTrans`.
-/
def sliceUnderNatTrans
    (F : C ⥤ Over (T := Cat.{v_sp, u_sp}) D) :
    F ⋙ Over.forget _ ⟶ (Functor.const C).obj D where
  app c := (F.obj c).hom
  naturality {c₁ c₂} f := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map,
      Over.forget_map]
    change (F.map f).left.toFunctor ⋙ (F.obj c₂).hom.toFunctor =
        (F.obj c₁).hom.toFunctor ⋙ 𝟭 _
    rw [Functor.comp_id, ← Cat.Hom.comp_toFunctor]
    exact congrArg _ (Over.w (F.map f))

/--
The `C`-direction projection of the slice-preserving contravariant
Grothendieck construction.  Given `G : Dᵒᵖ ⥤ Over C`, maps the
total category of the contravariant Grothendieck of
`G ⋙ Over.forget` to `C` by applying each fibre's slice
projection `(G.obj (op d)).hom` at the appropriate object.

Expressed as the composition of the contravariant-Grothendieck map
along `sliceCoverNatTrans G` (assembling the fibrewise slice
projections into a natural transformation to the constant functor
at `C`) with `grothContraOfConstProj`.
-/
def sliceContraFunctor.projC
    (G : Dᵒᵖ ⥤ Over (T := Cat.{v_sp, u_sp}) C) :
    ((grothendieckContraFunctor D).obj (G ⋙ Over.forget _)).α ⥤
      (C : Cat.{v_sp, u_sp}) :=
  ((grothendieckContraFunctor D).map (sliceCoverNatTrans G)).toFunctor
    ⋙ grothContraOfConstProj D C

/--
Naturality of `sliceContraFunctor.projC` along a morphism
`ν : G ⟶ G'` in `Dᵒᵖ ⥤ Over C`:  the contravariant-Grothendieck
map along the forgetful whiskering of `ν` composes with the
slice projection of `G'` to give the slice projection of `G`.

Derives from functoriality of `grothendieckContraFunctor D` together
with the factoring identity
`whiskerRight ν (Over.forget _) ≫ sliceCoverNatTrans G'
  = sliceCoverNatTrans G`.
-/
theorem sliceContraFunctor.projC_naturality
    {G G' : Dᵒᵖ ⥤ Over (T := Cat.{v_sp, u_sp}) C}
    (ν : G ⟶ G') :
    ((grothendieckContraFunctor D).map
        (Functor.whiskerRight ν (Over.forget _))).toFunctor ⋙
      sliceContraFunctor.projC G' =
      sliceContraFunctor.projC G := by
  unfold sliceContraFunctor.projC
  rw [← Functor.assoc, ← Cat.Hom.comp_toFunctor,
    ← (grothendieckContraFunctor D).map_comp]
  congr 3
  apply NatTrans.ext
  funext d
  exact Over.w (ν.app d)

/--
The slice-preserving contravariant Grothendieck construction.
Given `G : Dᵒᵖ ⥤ Over C`, produces an `Over (Cat.of (C × D))` object
whose underlying category is the contravariant Grothendieck of
`G ⋙ Over.forget` and whose projection is the pair of
`sliceContraFunctor.projC` (to `C`) and the standard contra-
Grothendieck forgetful (to `D`).
-/
def sliceContraFunctor :
    (Dᵒᵖ ⥤ Over (T := Cat.{v_sp, u_sp}) C) ⥤
      Over (T := Cat.{v_sp, u_sp}) (Cat.of (C × D)) where
  obj G :=
    Over.mk (T := Cat.{v_sp, u_sp})
      ((sliceContraFunctor.projC G).prod'
        ((grothendieckContraFunctorOver (E := D)).obj
          (G ⋙ Over.forget _)).hom.toFunctor).toCatHom
  map {G G'} ν :=
    Over.homMk
      ((grothendieckContraFunctor D).map
        (Functor.whiskerRight ν (Over.forget _)))
      (by
        apply Cat.Hom.ext
        change ((grothendieckContraFunctor D).map
              (Functor.whiskerRight ν
                (Over.forget _))).toFunctor ⋙
            (sliceContraFunctor.projC G').prod'
              ((grothendieckContraFunctorOver (E := D)).obj
                (G' ⋙ Over.forget _)).hom.toFunctor =
            (sliceContraFunctor.projC G).prod'
              ((grothendieckContraFunctorOver (E := D)).obj
                (G ⋙ Over.forget _)).hom.toFunctor
        rw [show ∀ {A B K : Cat.{v_sp, u_sp}}
              (F : A ⥤ B) (G : A ⥤ K)
              {A' : Cat.{v_sp, u_sp}} (H : A' ⥤ A),
              H ⋙ F.prod' G = (H ⋙ F).prod' (H ⋙ G)
            from fun _ _ _ _ => rfl]
        congr 1
        exact sliceContraFunctor.projC_naturality ν)
  map_id G := by
    apply Over.OverMorphism.ext
    change (grothendieckContraFunctor D).map
        (Functor.whiskerRight (𝟙 G) (Over.forget _)) = _
    rw [Functor.whiskerRight_id']
    simp
  map_comp {G G' G''} ν₁ ν₂ := by
    apply Over.OverMorphism.ext
    change (grothendieckContraFunctor D).map
        (Functor.whiskerRight (ν₁ ≫ ν₂) (Over.forget _)) = _
    rw [Functor.whiskerRight_comp]
    simp

/--
The `D`-direction projection of the slice-preserving covariant
Grothendieck construction.  Given `F : C ⥤ Over D`, maps the total
category of the covariant Grothendieck of `F ⋙ Over.forget` to `D`
by applying each fibre's slice projection `(F.obj c).hom` at the
appropriate object.
-/
def sliceCovFunctor.projD
    (F : C ⥤ Over (T := Cat.{v_sp, u_sp}) D) :
    ((grothendieckFunctor C).obj (F ⋙ Over.forget _)).α ⥤
      (D : Cat.{v_sp, u_sp}) :=
  ((grothendieckFunctor C).map (sliceUnderNatTrans F)).toFunctor
    ⋙ grothOfConstProj C D

/--
Naturality of `sliceCovFunctor.projD` along a morphism
`ν : F ⟶ F'` in `C ⥤ Over D`:  the covariant-Grothendieck map
along the forgetful whiskering of `ν` composes with the slice
projection of `F'` to give the slice projection of `F`.

Derives from functoriality of `grothendieckFunctor C` together
with the factoring identity
`whiskerRight ν (Over.forget _) ≫ sliceUnderNatTrans F'
  = sliceUnderNatTrans F`.
-/
theorem sliceCovFunctor.projD_naturality
    {F F' : C ⥤ Over (T := Cat.{v_sp, u_sp}) D}
    (ν : F ⟶ F') :
    ((grothendieckFunctor C).map
        (Functor.whiskerRight ν (Over.forget _))).toFunctor ⋙
      sliceCovFunctor.projD F' =
      sliceCovFunctor.projD F := by
  unfold sliceCovFunctor.projD
  rw [← Functor.assoc, ← Cat.Hom.comp_toFunctor,
    ← (grothendieckFunctor C).map_comp]
  congr 3
  apply NatTrans.ext
  funext c
  exact Over.w (ν.app c)

set_option backward.isDefEq.respectTransparency false in
/--
The slice-preserving covariant Grothendieck construction.
Given `F : C ⥤ Over D`, produces an `Over (Cat.of (C × D))` object
whose underlying category is the covariant Grothendieck of
`F ⋙ Over.forget` and whose projection is the pair of the standard
covariant-Grothendieck forgetful (to `C`) and
`sliceCovFunctor.projD` (to `D`).
-/
def sliceCovFunctor :
    (C ⥤ Over (T := Cat.{v_sp, u_sp}) D) ⥤
      Over (T := Cat.{v_sp, u_sp}) (Cat.of (C × D)) where
  obj F :=
    Over.mk (T := Cat.{v_sp, u_sp})
      (((grothendieckFunctorOver (E := C)).obj
          (F ⋙ Over.forget _)).hom.toFunctor.prod'
        (sliceCovFunctor.projD F)).toCatHom
  map {F F'} ν :=
    Over.homMk
      ((grothendieckFunctor C).map
        (Functor.whiskerRight ν (Over.forget _)))
      (by
        apply Cat.Hom.ext
        change ((grothendieckFunctor C).map
              (Functor.whiskerRight ν
                (Over.forget _))).toFunctor ⋙
            ((grothendieckFunctorOver (E := C)).obj
                (F' ⋙ Over.forget _)).hom.toFunctor.prod'
              (sliceCovFunctor.projD F') =
            ((grothendieckFunctorOver (E := C)).obj
                (F ⋙ Over.forget _)).hom.toFunctor.prod'
              (sliceCovFunctor.projD F)
        rw [show ∀ {A B K : Cat.{v_sp, u_sp}}
              (F : A ⥤ B) (G : A ⥤ K)
              {A' : Cat.{v_sp, u_sp}} (H : A' ⥤ A),
              H ⋙ F.prod' G = (H ⋙ F).prod' (H ⋙ G)
            from fun _ _ _ _ => rfl]
        congr 1
        exact sliceCovFunctor.projD_naturality ν)
  map_id F := by
    apply Over.OverMorphism.ext
    change (grothendieckFunctor C).map
        (Functor.whiskerRight (𝟙 F) (Over.forget _)) = _
    rw [Functor.whiskerRight_id']
    simp
    rfl
  map_comp {F F' F''} ν₁ ν₂ := by
    apply Over.OverMorphism.ext
    change (grothendieckFunctor C).map
        (Functor.whiskerRight (ν₁ ≫ ν₂) (Over.forget _)) = _
    rw [Functor.whiskerRight_comp]
    simp

/--
Strict two-sided Grothendieck construction, covariant-then-
contravariant order.  For `H : Dᵒᵖ ⥤ C ⥤ Cat`, first apply
mathlib's slice-refined `Grothendieck.functor` pointwise in `D` to
get `Dᵒᵖ ⥤ Over C`, then apply `sliceContraFunctor` to land in
`Over (Cat.of (C × D))`.

Objects are triples `(c, d, x : H(d, c))` with a strict
commutativity condition on morphisms expressed by the slice
structure over `C × D`.
-/
def twoSidedGrothendieckCovContra :
    (Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}) ⥤
      Over (T := Cat.{v_sp, u_sp}) (Cat.of (C × D)) :=
  (Functor.whiskeringRight _ _ _).obj Grothendieck.functor ⋙
    sliceContraFunctor

/--
Strict two-sided Grothendieck construction, contravariant-then-
covariant order.  For `H : Dᵒᵖ ⥤ C ⥤ Cat`, first flip to
`C ⥤ Dᵒᵖ ⥤ Cat`, then apply `grothendieckContraFunctorOver`
pointwise in `C` to get `C ⥤ Over D`, then apply `sliceCovFunctor`
to land in `Over (Cat.of (C × D))`.

Agrees with `twoSidedGrothendieckCovContra` at the level of object
data: `twoSidedGrothendieckObjEquiv` provides a type equivalence
between their underlying object types at each `H`, confirming both
orderings encode the same Lucyshyn-Wright triples `(d, c, y)`
modulo nested `Opposite` presentation.
-/
def twoSidedGrothendieckContraCov :
    (Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}) ⥤
      Over (T := Cat.{v_sp, u_sp}) (Cat.of (C × D)) :=
  flipFunctor Dᵒᵖ C Cat.{v_sp, u_sp} ⋙
    (Functor.whiskeringRight _ _ _).obj grothendieckContraFunctorOver ⋙
    sliceCovFunctor

namespace TwoSidedGrothendieckCovContra

variable {H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}}

/--
Construct an object of `(twoSidedGrothendieckCovContra.obj H).left`
from a `D`-base `d`, a `C`-base `c`, and a fibre element
`y : (H.obj (op d)).obj c`.
-/
def mkObj (d : D) (c : C)
    (y : ((H.obj (Opposite.op d)).obj c).α) :
    ((twoSidedGrothendieckCovContra.obj H).left : Cat) :=
  Opposite.op ⟨Opposite.op d, Opposite.op ⟨c, y⟩⟩

/--
The `D`-coordinate of an object of
`(twoSidedGrothendieckCovContra.obj H).left`.
-/
def objD (x : ((twoSidedGrothendieckCovContra.obj H).left : Cat)) : D :=
  x.unop.base.unop

/--
The `C`-coordinate of an object of
`(twoSidedGrothendieckCovContra.obj H).left`.
-/
def objC (x : ((twoSidedGrothendieckCovContra.obj H).left : Cat)) : C :=
  x.unop.fiber.unop.base

/--
The fibre element of an object of
`(twoSidedGrothendieckCovContra.obj H).left`.
-/
def objFiber (x : ((twoSidedGrothendieckCovContra.obj H).left : Cat)) :
    ((H.obj (Opposite.op (objD x))).obj (objC x)).α :=
  x.unop.fiber.unop.fiber

@[simp]
theorem objD_mkObj (d : D) (c : C)
    (y : ((H.obj (Opposite.op d)).obj c).α) :
    objD (mkObj (H := H) d c y) = d := rfl

@[simp]
theorem objC_mkObj (d : D) (c : C)
    (y : ((H.obj (Opposite.op d)).obj c).α) :
    objC (mkObj (H := H) d c y) = c := rfl

@[simp]
theorem objFiber_mkObj (d : D) (c : C)
    (y : ((H.obj (Opposite.op d)).obj c).α) :
    objFiber (mkObj (H := H) d c y) = y := rfl

/--
Construct a morphism in `(twoSidedGrothendieckCovContra.obj H).left`
from a `D`-base morphism `β`, a `C`-base morphism `α`, and a fibre
morphism `φ` in `(H.obj (op (objD X))).obj (objC Y)`.
-/
def mkHom
    {X Y : ((twoSidedGrothendieckCovContra.obj H).left : Cat)}
    (β : objD X ⟶ objD Y) (α : objC X ⟶ objC Y)
    (φ : ((H.obj (Opposite.op (objD X))).map α).toFunctor.obj
            (objFiber X) ⟶
          ((H.map β.op).app (objC Y)).toFunctor.obj (objFiber Y)) :
    X ⟶ Y :=
  Quiver.Hom.op ⟨β.op, Quiver.Hom.op ⟨α, φ⟩⟩

/--
The `D`-base of a morphism in
`(twoSidedGrothendieckCovContra.obj H).left`.
-/
def homD {X Y : ((twoSidedGrothendieckCovContra.obj H).left : Cat)}
    (f : X ⟶ Y) : objD X ⟶ objD Y :=
  f.unop.base.unop

/--
The `C`-base of a morphism in
`(twoSidedGrothendieckCovContra.obj H).left`.
-/
def homC {X Y : ((twoSidedGrothendieckCovContra.obj H).left : Cat)}
    (f : X ⟶ Y) : objC X ⟶ objC Y :=
  f.unop.fiber.unop.base

/--
The fibre morphism of a morphism in
`(twoSidedGrothendieckCovContra.obj H).left`.
-/
def homFiber
    {X Y : ((twoSidedGrothendieckCovContra.obj H).left : Cat)}
    (f : X ⟶ Y) :
    ((H.obj (Opposite.op (objD X))).map (homC f)).toFunctor.obj
        (objFiber X) ⟶
      ((H.map (homD f).op).app (objC Y)).toFunctor.obj (objFiber Y) :=
  f.unop.fiber.unop.fiber

@[simp]
theorem homD_mkHom
    {X Y : ((twoSidedGrothendieckCovContra.obj H).left : Cat)}
    (β : objD X ⟶ objD Y) (α : objC X ⟶ objC Y)
    (φ : ((H.obj (Opposite.op (objD X))).map α).toFunctor.obj
            (objFiber X) ⟶
          ((H.map β.op).app (objC Y)).toFunctor.obj (objFiber Y)) :
    homD (mkHom β α φ) = β := rfl

@[simp]
theorem homC_mkHom
    {X Y : ((twoSidedGrothendieckCovContra.obj H).left : Cat)}
    (β : objD X ⟶ objD Y) (α : objC X ⟶ objC Y)
    (φ : ((H.obj (Opposite.op (objD X))).map α).toFunctor.obj
            (objFiber X) ⟶
          ((H.map β.op).app (objC Y)).toFunctor.obj (objFiber Y)) :
    homC (mkHom β α φ) = α := rfl

@[simp]
theorem homFiber_mkHom
    {X Y : ((twoSidedGrothendieckCovContra.obj H).left : Cat)}
    (β : objD X ⟶ objD Y) (α : objC X ⟶ objC Y)
    (φ : ((H.obj (Opposite.op (objD X))).map α).toFunctor.obj
            (objFiber X) ⟶
          ((H.map β.op).app (objC Y)).toFunctor.obj (objFiber Y)) :
    homFiber (mkHom β α φ) = φ := rfl

@[simp]
theorem homD_id (x : ((twoSidedGrothendieckCovContra.obj H).left : Cat)) :
    homD (𝟙 x) = 𝟙 (objD x) := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem homC_id (x : ((twoSidedGrothendieckCovContra.obj H).left : Cat)) :
    homC (𝟙 x) = 𝟙 (objC x) := by
  change ((𝟙 x).unop.fiber.unop).base = _
  rw [show (𝟙 x).unop = 𝟙 x.unop from rfl,
      Grothendieck.id_fiber, eqToHom_unop, Grothendieck.base_eqToHom]
  rfl

@[simp]
theorem homD_comp
    {X Y Z : ((twoSidedGrothendieckCovContra.obj H).left : Cat)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homD (f ≫ g) = homD f ≫ homD g := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem homC_comp
    {X Y Z : ((twoSidedGrothendieckCovContra.obj H).left : Cat)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homC (f ≫ g) = homC f ≫ homC g := by
  change ((f ≫ g).unop.fiber.unop).base = _
  rw [show (f ≫ g).unop = g.unop ≫ f.unop from rfl,
      Grothendieck.comp_fiber]
  simp [Grothendieck.comp_base, eqToHom_unop, homC,
      Grothendieck.functor]

set_option backward.isDefEq.respectTransparency false in
/--
The fibre component of the identity morphism is a canonical
`eqToHom`.  Property of the two-layer nested Grothendieck encoding.
-/
@[simp]
theorem homFiber_id
    (x : ((twoSidedGrothendieckCovContra.obj H).left : Cat)) :
    homFiber (𝟙 x) = eqToHom (by
      simp [homD_id, homC_id,
        CategoryTheory.Functor.map_id]) := by
  apply eq_of_heq
  refine HEq.trans ?_ (eqToHom_heq_id_dom _ _ _).symm
  dsimp only [homFiber]
  change HEq
    (Grothendieck.Hom.fiber (Grothendieck.Hom.fiber
      ((𝟙 x.unop) : x.unop ⟶ x.unop)).unop) _
  rw [Grothendieck.id_fiber, eqToHom_unop, Grothendieck.fiber_eqToHom]
  apply (eqToHom_heq_id_dom _ _ _).trans
  congr 1
  simp
  rfl

/--
The fibre of a composition is the composition of the fibres in the
inner Grothendieck structure.  Exposed for later use in constructing
the two-sided Grothendieck equivalence.
-/
theorem homFiber_comp
    {X Y Z : ((twoSidedGrothendieckCovContra.obj H).left : Cat)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    HEq (homFiber (f ≫ g))
      ((g.unop ≫ f.unop).fiber.unop.fiber) := by
  dsimp only [homFiber]
  rfl

/-- Identity morphisms in the covariant-then-contravariant two-
sided Grothendieck expressed via `mkHom`. -/
theorem mkHom_id
    (x : ((twoSidedGrothendieckCovContra.obj H).left : Cat)) :
    𝟙 x = mkHom (𝟙 (objD x)) (𝟙 (objC x))
      (eqToHom (by
        simp [CategoryTheory.Functor.map_id])) := by
  rw [show 𝟙 x =
    mkHom (homD (𝟙 x)) (homC (𝟙 x)) (homFiber (𝟙 x)) from rfl]
  apply eq_of_heq
  congr 1
  · exact homC_id x
  · have hC : homC (𝟙 x) = 𝟙 (objC x) := homC_id x
    refine HEq.trans (heq_of_eq (homFiber_id x)) ?_
    refine HEq.trans (eqToHom_heq_id_dom _ _ ?_) ?_
    · simp [CategoryTheory.Functor.map_id]
    · refine HEq.trans ?_
        (eqToHom_heq_id_dom _ _ (by
          simp [CategoryTheory.Functor.map_id])).symm
      congr 1
      simp [hC]

/-- Composition of `mkHom`-constructed morphisms in the covariant-
then-contravariant two-sided Grothendieck.  The fibre component is
the destructured `homFiber` of the underlying composition; together
with the simp lemmas `homD_comp`, `homC_comp`, `homD_mkHom`,
`homC_mkHom`, this exposes the Lucyshyn-Wright composition formula
`(c ⋅ a, d ⋅ b, a*(y) ⋅ d!(x))` for downstream use. -/
theorem mkHom_comp
    {x y z : ((twoSidedGrothendieckCovContra.obj H).left : Cat)}
    (β₁ : objD x ⟶ objD y) (α₁ : objC x ⟶ objC y)
    (φ₁ : ((H.obj (Opposite.op (objD x))).map α₁).toFunctor.obj
            (objFiber x) ⟶
          ((H.map β₁.op).app (objC y)).toFunctor.obj (objFiber y))
    (β₂ : objD y ⟶ objD z) (α₂ : objC y ⟶ objC z)
    (φ₂ : ((H.obj (Opposite.op (objD y))).map α₂).toFunctor.obj
            (objFiber y) ⟶
          ((H.map β₂.op).app (objC z)).toFunctor.obj (objFiber z)) :
    mkHom β₁ α₁ φ₁ ≫ mkHom β₂ α₂ φ₂ =
      mkHom (β₁ ≫ β₂) (α₁ ≫ α₂)
        (eqToHom (by
            simp [homC_comp, homC_mkHom]) ≫
          homFiber (mkHom β₁ α₁ φ₁ ≫ mkHom β₂ α₂ φ₂) ≫
          eqToHom (by
            change ((H.map (homD (mkHom β₁ α₁ φ₁ ≫
                  mkHom β₂ α₂ φ₂)).op).app (objC z)).toFunctor.obj
                (objFiber z) =
              ((H.map (β₁ ≫ β₂).op).app (objC z)).toFunctor.obj
                (objFiber z)
            rfl)) := by
  conv_lhs => rw [show (mkHom β₁ α₁ φ₁ ≫ mkHom β₂ α₂ φ₂ :
    _ ⟶ _) =
    mkHom (homD (mkHom β₁ α₁ φ₁ ≫ mkHom β₂ α₂ φ₂))
      (homC (mkHom β₁ α₁ φ₁ ≫ mkHom β₂ α₂ φ₂))
      (homFiber (mkHom β₁ α₁ φ₁ ≫ mkHom β₂ α₂ φ₂)) from rfl]
  congr 1
  · simp
  · refine HEq.symm ?_
    refine (eqToHom_comp_heq _ _).trans ?_
    refine (comp_eqToHom_heq _ _).trans ?_
    rfl

end TwoSidedGrothendieckCovContra

namespace TwoSidedGrothendieckContraCov

variable {H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}}

/--
Construct an object of `(twoSidedGrothendieckContraCov.obj H).left`
from a `D`-base `d`, a `C`-base `c`, and a fibre element
`y : (H.obj (op d)).obj c`.
-/
def mkObj (d : D) (c : C)
    (y : ((H.obj (Opposite.op d)).obj c).α) :
    ((twoSidedGrothendieckContraCov.obj H).left : Cat) :=
  ⟨c, Opposite.op ⟨Opposite.op d, Opposite.op y⟩⟩

/--
The `D`-coordinate of an object of
`(twoSidedGrothendieckContraCov.obj H).left`.
-/
def objD (x : ((twoSidedGrothendieckContraCov.obj H).left : Cat)) : D :=
  x.fiber.unop.base.unop

/--
The `C`-coordinate of an object of
`(twoSidedGrothendieckContraCov.obj H).left`.
-/
def objC (x : ((twoSidedGrothendieckContraCov.obj H).left : Cat)) : C :=
  x.base

/--
The fibre element of an object of
`(twoSidedGrothendieckContraCov.obj H).left`.
-/
def objFiber (x : ((twoSidedGrothendieckContraCov.obj H).left : Cat)) :
    ((H.obj (Opposite.op (objD x))).obj (objC x)).α :=
  x.fiber.unop.fiber.unop

@[simp]
theorem objD_mkObj (d : D) (c : C)
    (y : ((H.obj (Opposite.op d)).obj c).α) :
    objD (mkObj (H := H) d c y) = d := rfl

@[simp]
theorem objC_mkObj (d : D) (c : C)
    (y : ((H.obj (Opposite.op d)).obj c).α) :
    objC (mkObj (H := H) d c y) = c := rfl

@[simp]
theorem objFiber_mkObj (d : D) (c : C)
    (y : ((H.obj (Opposite.op d)).obj c).α) :
    objFiber (mkObj (H := H) d c y) = y := rfl

/--
Construct a morphism in `(twoSidedGrothendieckContraCov.obj H).left`
from a `D`-base morphism `β`, a `C`-base morphism `α`, and a fibre
morphism `φ` in `(H.obj (op (objD X))).obj (objC Y)`.
-/
def mkHom
    {X Y : ((twoSidedGrothendieckContraCov.obj H).left : Cat)}
    (β : objD X ⟶ objD Y) (α : objC X ⟶ objC Y)
    (φ : ((H.obj (Opposite.op (objD X))).map α).toFunctor.obj
            (objFiber X) ⟶
          ((H.map β.op).app (objC Y)).toFunctor.obj (objFiber Y)) :
    X ⟶ Y :=
  ⟨α, Quiver.Hom.op ⟨β.op, Quiver.Hom.op φ⟩⟩

/--
The `D`-base of a morphism in
`(twoSidedGrothendieckContraCov.obj H).left`.
-/
def homD {X Y : ((twoSidedGrothendieckContraCov.obj H).left : Cat)}
    (f : X ⟶ Y) : objD X ⟶ objD Y :=
  f.fiber.unop.base.unop

/--
The `C`-base of a morphism in
`(twoSidedGrothendieckContraCov.obj H).left`.
-/
def homC {X Y : ((twoSidedGrothendieckContraCov.obj H).left : Cat)}
    (f : X ⟶ Y) : objC X ⟶ objC Y :=
  f.base

/--
The fibre morphism of a morphism in
`(twoSidedGrothendieckContraCov.obj H).left`.
-/
def homFiber
    {X Y : ((twoSidedGrothendieckContraCov.obj H).left : Cat)}
    (f : X ⟶ Y) :
    ((H.obj (Opposite.op (objD X))).map (homC f)).toFunctor.obj
        (objFiber X) ⟶
      ((H.map (homD f).op).app (objC Y)).toFunctor.obj (objFiber Y) :=
  f.fiber.unop.fiber.unop

@[simp]
theorem homD_mkHom
    {X Y : ((twoSidedGrothendieckContraCov.obj H).left : Cat)}
    (β : objD X ⟶ objD Y) (α : objC X ⟶ objC Y)
    (φ : ((H.obj (Opposite.op (objD X))).map α).toFunctor.obj
            (objFiber X) ⟶
          ((H.map β.op).app (objC Y)).toFunctor.obj (objFiber Y)) :
    homD (mkHom β α φ) = β := rfl

@[simp]
theorem homC_mkHom
    {X Y : ((twoSidedGrothendieckContraCov.obj H).left : Cat)}
    (β : objD X ⟶ objD Y) (α : objC X ⟶ objC Y)
    (φ : ((H.obj (Opposite.op (objD X))).map α).toFunctor.obj
            (objFiber X) ⟶
          ((H.map β.op).app (objC Y)).toFunctor.obj (objFiber Y)) :
    homC (mkHom β α φ) = α := rfl

@[simp]
theorem homFiber_mkHom
    {X Y : ((twoSidedGrothendieckContraCov.obj H).left : Cat)}
    (β : objD X ⟶ objD Y) (α : objC X ⟶ objC Y)
    (φ : ((H.obj (Opposite.op (objD X))).map α).toFunctor.obj
            (objFiber X) ⟶
          ((H.map β.op).app (objC Y)).toFunctor.obj (objFiber Y)) :
    homFiber (mkHom β α φ) = φ := rfl

@[simp]
theorem homC_id (x : ((twoSidedGrothendieckContraCov.obj H).left : Cat)) :
    homC (𝟙 x) = 𝟙 (objC x) := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem homD_id (x : ((twoSidedGrothendieckContraCov.obj H).left : Cat)) :
    homD (𝟙 x) = 𝟙 (objD x) := by
  dsimp only [homD]
  rw [Grothendieck.id_fiber, eqToHom_unop, Grothendieck.base_eqToHom,
      eqToHom_unop]
  rfl

@[simp]
theorem homC_comp
    {X Y Z : ((twoSidedGrothendieckContraCov.obj H).left : Cat)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homC (f ≫ g) = homC f ≫ homC g := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem homD_comp
    {X Y Z : ((twoSidedGrothendieckContraCov.obj H).left : Cat)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    homD (f ≫ g) = homD f ≫ homD g := by
  change ((f ≫ g).fiber.unop.base.unop) = _
  rw [Grothendieck.comp_fiber]
  simp [Grothendieck.comp_base, homD, Grothendieck.functor,
      grothendieckContraFunctorOver, Cat.Over.leftOp]

set_option backward.isDefEq.respectTransparency false in
/--
The fibre component of the identity morphism is a canonical
`eqToHom`.  Property of the two-layer nested Grothendieck encoding
in the contravariant-covariant ordering.
-/
@[simp]
theorem homFiber_id
    (x : ((twoSidedGrothendieckContraCov.obj H).left : Cat)) :
    homFiber (𝟙 x) = eqToHom (by
      simp [homD_id, homC_id,
        CategoryTheory.Functor.map_id]) := by
  apply eq_of_heq
  refine HEq.trans ?_ (eqToHom_heq_id_dom _ _ _).symm
  dsimp only [homFiber]
  change HEq
    (Grothendieck.Hom.fiber ((𝟙 x : x ⟶ x)).fiber.unop).unop _
  rw [Grothendieck.id_fiber, eqToHom_unop, Grothendieck.fiber_eqToHom,
      eqToHom_unop]
  apply (eqToHom_heq_id_dom _ _ _).trans
  congr 1

/--
The fibre of a composition is the composition of the fibres in the
inner Grothendieck structure.  Exposed for later use in constructing
the two-sided Grothendieck equivalence.
-/
theorem homFiber_comp
    {X Y Z : ((twoSidedGrothendieckContraCov.obj H).left : Cat)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    HEq (homFiber (f ≫ g))
      ((f ≫ g).fiber.unop.fiber.unop) := by
  dsimp only [homFiber]
  rfl

/-- Identity morphisms in the contravariant-then-covariant two-
sided Grothendieck expressed via `mkHom`. -/
theorem mkHom_id
    (x : ((twoSidedGrothendieckContraCov.obj H).left : Cat)) :
    𝟙 x = mkHom (𝟙 (objD x)) (𝟙 (objC x))
      (eqToHom (by
        simp [CategoryTheory.Functor.map_id])) := by
  rw [show 𝟙 x =
    mkHom (homD (𝟙 x)) (homC (𝟙 x)) (homFiber (𝟙 x)) from rfl]
  apply eq_of_heq
  congr 1
  · exact homD_id x
  · refine HEq.trans (heq_of_eq (homFiber_id x)) ?_
    refine HEq.trans (eqToHom_heq_id_dom _ _ ?_) ?_
    · simp [CategoryTheory.Functor.map_id]
    · refine HEq.trans ?_
        (eqToHom_heq_id_dom _ _ (by
          simp [CategoryTheory.Functor.map_id])).symm
      congr 1

/-- Composition of `mkHom`-constructed morphisms in the contra-
variant-then-covariant two-sided Grothendieck.  The fibre component
is the destructured `homFiber` of the underlying composition;
together with the simp lemmas `homD_comp`, `homC_comp`,
`homD_mkHom`, `homC_mkHom`, this exposes the Lucyshyn-Wright
composition formula `(c ⋅ a, d ⋅ b, a*(y) ⋅ d!(x))` for downstream
use. -/
theorem mkHom_comp
    {x y z : ((twoSidedGrothendieckContraCov.obj H).left : Cat)}
    (β₁ : objD x ⟶ objD y) (α₁ : objC x ⟶ objC y)
    (φ₁ : ((H.obj (Opposite.op (objD x))).map α₁).toFunctor.obj
            (objFiber x) ⟶
          ((H.map β₁.op).app (objC y)).toFunctor.obj (objFiber y))
    (β₂ : objD y ⟶ objD z) (α₂ : objC y ⟶ objC z)
    (φ₂ : ((H.obj (Opposite.op (objD y))).map α₂).toFunctor.obj
            (objFiber y) ⟶
          ((H.map β₂.op).app (objC z)).toFunctor.obj (objFiber z)) :
    mkHom β₁ α₁ φ₁ ≫ mkHom β₂ α₂ φ₂ =
      mkHom (β₁ ≫ β₂) (α₁ ≫ α₂)
        (eqToHom (by
            simp [homC_comp, homC_mkHom]) ≫
          homFiber (mkHom β₁ α₁ φ₁ ≫ mkHom β₂ α₂ φ₂) ≫
          eqToHom (by
            simp [homD_comp, homD_mkHom])) := by
  conv_lhs => rw [show (mkHom β₁ α₁ φ₁ ≫ mkHom β₂ α₂ φ₂ :
    _ ⟶ _) =
    mkHom (homD (mkHom β₁ α₁ φ₁ ≫ mkHom β₂ α₂ φ₂))
      (homC (mkHom β₁ α₁ φ₁ ≫ mkHom β₂ α₂ φ₂))
      (homFiber (mkHom β₁ α₁ φ₁ ≫ mkHom β₂ α₂ φ₂)) from rfl]
  congr 1
  · simp
  · refine HEq.symm ?_
    refine (eqToHom_comp_heq _ _).trans ?_
    refine (comp_eqToHom_heq _ _).trans ?_
    rfl

end TwoSidedGrothendieckContraCov

/--
Forward object map of the pointwise two-sided Grothendieck object
equivalence.  Reassociates the nested `Opposite`-wrapped triple
`(d, c, y)` from the covariant-then-contravariant presentation to
the contravariant-then-covariant presentation.
-/
def twoSidedGrothendieckObjEquiv.toFun
    (H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp})
    (x : ((twoSidedGrothendieckCovContra.obj H).left : Type _)) :
    ((twoSidedGrothendieckContraCov.obj H).left : Type _) :=
  ⟨x.unop.fiber.unop.base,
    Opposite.op ⟨x.unop.base, Opposite.op x.unop.fiber.unop.fiber⟩⟩

/--
Backward object map of the pointwise two-sided Grothendieck object
equivalence.  Inverse of `twoSidedGrothendieckObjEquiv.toFun`.
-/
def twoSidedGrothendieckObjEquiv.invFun
    (H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp})
    (y : ((twoSidedGrothendieckContraCov.obj H).left : Type _)) :
    ((twoSidedGrothendieckCovContra.obj H).left : Type _) :=
  Opposite.op
    ⟨y.fiber.unop.base,
      Opposite.op ⟨y.base, y.fiber.unop.fiber.unop⟩⟩

/--
Pointwise type equivalence between the object types underlying the
two orderings of the strict two-sided Grothendieck construction.
Both orderings encode the same triple data `(d, c, y)` (with
`d : D`, `c : C`, and `y : (H.obj (op d)).obj c`), differing only in
the nested `Opposite` presentation.  A full equivalence of
categories is not provided here.
-/
def twoSidedGrothendieckObjEquiv
    (H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}) :
    ((twoSidedGrothendieckCovContra.obj H).left : Type _) ≃
      ((twoSidedGrothendieckContraCov.obj H).left : Type _) where
  toFun := twoSidedGrothendieckObjEquiv.toFun H
  invFun := twoSidedGrothendieckObjEquiv.invFun H
  left_inv _ := rfl
  right_inv _ := rfl

namespace twoSidedGrothendieckEquiv

variable {H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}}

/--
Object map of the forward Cat functor of the two-sided Grothendieck
equivalence.
-/
def forwardObj
    (X : ((twoSidedGrothendieckCovContra.obj H).left : Cat)) :
    ((twoSidedGrothendieckContraCov.obj H).left : Cat) :=
  TwoSidedGrothendieckContraCov.mkObj
    (TwoSidedGrothendieckCovContra.objD X)
    (TwoSidedGrothendieckCovContra.objC X)
    (TwoSidedGrothendieckCovContra.objFiber X)

/--
Morphism map of the forward Cat functor of the two-sided Grothendieck
equivalence.
-/
def forwardMap
    {X Y : ((twoSidedGrothendieckCovContra.obj H).left : Cat)}
    (f : X ⟶ Y) :
    forwardObj (H := H) X ⟶ forwardObj (H := H) Y :=
  TwoSidedGrothendieckContraCov.mkHom
    (X := forwardObj X) (Y := forwardObj Y)
    (TwoSidedGrothendieckCovContra.homD (X := X) (Y := Y) f)
    (TwoSidedGrothendieckCovContra.homC (X := X) (Y := Y) f)
    (TwoSidedGrothendieckCovContra.homFiber (X := X) (Y := Y) f)

/--
Object map of the backward Cat functor of the two-sided Grothendieck
equivalence.
-/
def backwardObj
    (Y : ((twoSidedGrothendieckContraCov.obj H).left : Cat)) :
    ((twoSidedGrothendieckCovContra.obj H).left : Cat) :=
  TwoSidedGrothendieckCovContra.mkObj
    (TwoSidedGrothendieckContraCov.objD Y)
    (TwoSidedGrothendieckContraCov.objC Y)
    (TwoSidedGrothendieckContraCov.objFiber Y)

/--
Morphism map of the backward Cat functor of the two-sided Grothendieck
equivalence.
-/
def backwardMap
    {X Y : ((twoSidedGrothendieckContraCov.obj H).left : Cat)}
    (f : X ⟶ Y) :
    backwardObj (H := H) X ⟶ backwardObj (H := H) Y :=
  TwoSidedGrothendieckCovContra.mkHom
    (X := backwardObj X) (Y := backwardObj Y)
    (TwoSidedGrothendieckContraCov.homD (X := X) (Y := Y) f)
    (TwoSidedGrothendieckContraCov.homC (X := X) (Y := Y) f)
    (TwoSidedGrothendieckContraCov.homFiber (X := X) (Y := Y) f)

/--
Hom-set bijection between the covariant-then-contravariant and
contravariant-then-covariant orderings of the strict two-sided
Grothendieck, at fixed objects `X` and `Y` of the covariant-then-
contravariant side.

This is weaker than a full `CategoryTheory.Equivalence` (which would
require preservation of identities and composition), but captures the
correspondence between the two orderings at the level of morphism data.
-/
def homEquivForward
    (X Y : ((twoSidedGrothendieckCovContra.obj H).left : Cat)) :
    (X ⟶ Y) ≃
      ((forwardObj (H := H) X : ((twoSidedGrothendieckContraCov.obj H).left
          : Cat)) ⟶ forwardObj (H := H) Y) where
  toFun := forwardMap (H := H) (X := X) (Y := Y)
  invFun := backwardMap (H := H) (X := forwardObj X) (Y := forwardObj Y)
  left_inv _ := rfl
  right_inv _ := rfl

/--
Hom-set bijection between the two orderings, at fixed objects `X` and
`Y` of the contravariant-then-covariant side.  Symmetric counterpart
of `homEquivForward`.
-/
def homEquivBackward
    (X Y : ((twoSidedGrothendieckContraCov.obj H).left : Cat)) :
    (X ⟶ Y) ≃
      ((backwardObj (H := H) X : ((twoSidedGrothendieckCovContra.obj H).left
          : Cat)) ⟶ backwardObj (H := H) Y) where
  toFun := backwardMap (H := H) (X := X) (Y := Y)
  invFun := forwardMap (H := H) (X := backwardObj X) (Y := backwardObj Y)
  left_inv _ := rfl
  right_inv _ := rfl

end twoSidedGrothendieckEquiv

end StrictTwoSidedGrothendieck

/-! ## Total Category of Functors into `Cat` -/

section CatOverCat

universe v₉ u₉

/--
The functor sending a category `D` to the category of small
categories equipped with a functor into `D`.  That is, on objects
`D ↦ {(E : Cat, G : E ⥤ D)}`, on morphisms `α : D ⥤ D'` by
post-composing `G` with `α`.

Defined as the unstraightening over `Cat` of the `Cat`-valued
hom profunctor (`catHomProfunctor.flip`).
-/
abbrev catOverCatFunctor :=
  catHomProfunctor.{v₉, u₉, max v₉ u₉, max (v₉+1) (u₉+1)}.flip ⋙
    grothendieckContraFunctor Cat.{v₉, u₉}

/--
The total category of all (small) categories equipped with a
functor into `Cat`.  Objects are pairs `(E : Cat, G : E ⥤ Cat)`;
morphisms `(E, G) ⟶ (E', G')` are pairs `(f : E ⥤ E', φ : G ⟶ f ⋙ G')`.

Recovered as the fibre of `catOverCatFunctor` at `Cat`.
-/
abbrev catOverCat :=
  catOverCatFunctor.{v₉, u₉}.obj (Cat.of Cat.{v₉, u₉})

/--
The total category obtained by applying the covariant Grothendieck
construction to `catOverCatFunctor`.  Objects are triples
`(D : Cat, E : Cat, G : E ⥤ D)`; morphisms
`(D, E, G) ⟶ (D', E', G')` are triples
`(α : D ⥤ D', k : E ⥤ E', φ : G ⋙ α ⟶ k ⋙ G')` — commutative
squares of functors that commute up to a (not necessarily
invertible) natural transformation.

The previously-defined `catOverCat` is the fibre of this total
category over the object `Cat.of Cat`; i.e. when we restrict `D`
to be `Cat` itself.
-/
abbrev catOverCatTotal :=
  (grothendieckFunctor
    Cat.{max v₉ u₉, max (v₉+1) (u₉+1)}).obj
    catOverCatFunctor.{v₉, u₉}

set_option backward.isDefEq.respectTransparency false in
/--
The unstraightening functor from `catOverCat` to `Cat`, sending
each pair `(E : Cat, G : E ⥤ Cat)` to `Grothendieck G`, and a
morphism `(f : E ⥤ E', φ : G ⟶ f ⋙ G')` to the composite
`Grothendieck.map φ ⋙ (grothendieckPre f).app G'`.

This is the 1-categorical strict unstraightening, realizing each
`(E, G)` as its total category and each base-change + natural
transformation pair as a functor between the corresponding totals.
-/
def unstraighten : catOverCat.{v₉, u₉} ⥤ Cat.{v₉, u₉} where
  obj T := (grothendieckFunctor
      (GrothendieckContraFunctor.objBase
        (C := Cat.{v₉, u₉}) T)).obj
    (GrothendieckContraFunctor.objFiber
      (C := Cat.{v₉, u₉}) T)
  map {T T'} m :=
    (Grothendieck.map
      (GrothendieckContraFunctor.homFiber
        (C := Cat.{v₉, u₉}) m)).toCatHom ≫
    (grothendieckPre
      (GrothendieckContraFunctor.homBase
        (C := Cat.{v₉, u₉}) m).toFunctor).app
      (GrothendieckContraFunctor.objFiber
        (C := Cat.{v₉, u₉}) T')
  map_id T := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor,
      Functor.toCatHom_toFunctor,
      Cat.Hom.id_toFunctor]
    change Grothendieck.map
        (GrothendieckContraFunctor.homFiber
          (C := Cat.{v₉, u₉}) (𝟙 T)) ⋙
        ((grothendieckPre
            (Functor.id (GrothendieckContraFunctor.objBase
              (C := Cat.{v₉, u₉}) T))).app
          (GrothendieckContraFunctor.objFiber
            (C := Cat.{v₉, u₉}) T)).toFunctor = Functor.id _
    have hPre :
        ((grothendieckPre
            (Functor.id (GrothendieckContraFunctor.objBase
              (C := Cat.{v₉, u₉}) T))).app
          (GrothendieckContraFunctor.objFiber
            (C := Cat.{v₉, u₉}) T)).toFunctor =
          Functor.id _ :=
      Grothendieck.pre_id _
    rw [hPre]
    change Grothendieck.map
        (GrothendieckContraFunctor.homFiber
          (C := Cat.{v₉, u₉}) (𝟙 T)) ⋙ Functor.id _ =
          Functor.id _
    rw [Functor.comp_id]
    exact Grothendieck.map_id_eq
  map_comp {T T' T''} m n := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor,
      Functor.toCatHom_toFunctor]
    change Grothendieck.map
        (GrothendieckContraFunctor.homFiber
          (C := Cat.{v₉, u₉}) m ≫
          (GrothendieckContraFunctor.homBase
              (C := Cat.{v₉, u₉}) m).toFunctor.whiskerLeft
            (GrothendieckContraFunctor.homFiber
              (C := Cat.{v₉, u₉}) n)) ⋙
        Grothendieck.pre
          (GrothendieckContraFunctor.objFiber
            (C := Cat.{v₉, u₉}) T'')
          ((GrothendieckContraFunctor.homBase
              (C := Cat.{v₉, u₉}) m).toFunctor ⋙
            (GrothendieckContraFunctor.homBase
              (C := Cat.{v₉, u₉}) n).toFunctor) =
      (Grothendieck.map
          (GrothendieckContraFunctor.homFiber
            (C := Cat.{v₉, u₉}) m) ⋙
          Grothendieck.pre
            (GrothendieckContraFunctor.objFiber
              (C := Cat.{v₉, u₉}) T')
            (GrothendieckContraFunctor.homBase
              (C := Cat.{v₉, u₉}) m).toFunctor) ⋙
        Grothendieck.map
            (GrothendieckContraFunctor.homFiber
              (C := Cat.{v₉, u₉}) n) ⋙
          Grothendieck.pre
            (GrothendieckContraFunctor.objFiber
              (C := Cat.{v₉, u₉}) T'')
            (GrothendieckContraFunctor.homBase
              (C := Cat.{v₉, u₉}) n).toFunctor
    rw [Grothendieck.map_comp_eq,
      Grothendieck.pre_comp
        (GrothendieckContraFunctor.objFiber
          (C := Cat.{v₉, u₉}) T'')
        (GrothendieckContraFunctor.homBase
          (C := Cat.{v₉, u₉}) n).toFunctor
        (GrothendieckContraFunctor.homBase
          (C := Cat.{v₉, u₉}) m).toFunctor]
    rw [Functor.assoc (Grothendieck.map
        (GrothendieckContraFunctor.homFiber
          (C := Cat.{v₉, u₉}) m))]
    change Grothendieck.map
        (GrothendieckContraFunctor.homFiber
          (C := Cat.{v₉, u₉}) m) ⋙
        (Grothendieck.map
          ((GrothendieckContraFunctor.homBase
              (C := Cat.{v₉, u₉}) m).toFunctor.whiskerLeft
            (GrothendieckContraFunctor.homFiber
              (C := Cat.{v₉, u₉}) n))) ⋙
        Grothendieck.pre
            (((catHomProfunctor.flip.obj
                  (Cat.of Cat.{v₉, u₉})).map
              (GrothendieckContraFunctor.homBase
                (C := Cat.{v₉, u₉}) n).op).toFunctor.obj
              (GrothendieckContraFunctor.objFiber
                (C := Cat.{v₉, u₉}) T''))
            (GrothendieckContraFunctor.homBase
              (C := Cat.{v₉, u₉}) m).toFunctor ⋙
          Grothendieck.pre
            (GrothendieckContraFunctor.objFiber
              (C := Cat.{v₉, u₉}) T'')
            (GrothendieckContraFunctor.homBase
              (C := Cat.{v₉, u₉}) n).toFunctor = _
    rw [← Grothendieck.pre_comp_map_assoc
        (GrothendieckContraFunctor.homBase
          (C := Cat.{v₉, u₉}) m).toFunctor
        (GrothendieckContraFunctor.homFiber
          (C := Cat.{v₉, u₉}) n)]
    rw [Functor.assoc]

end CatOverCat

end GebLean
