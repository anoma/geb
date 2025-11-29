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

@[simp]
def GrothendieckContraCatInst.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    Category.{max v v₂, max u u₂}
      (GrothendieckContra.{u, v, u₂, v₂} (C := C) (CI := CI) F') :=
  (GrothendieckContraCat.{u, v, u₂, v₂} (C := C) (CI := CI) F').str

@[simp]
def GrothendieckContraCatStructInst.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    CategoryStruct.{max v v₂, max u u₂}
      (GrothendieckContra.{u, v, u₂, v₂} (C := C) (CI := CI) F') :=
  (GrothendieckContraCatInst.{u, v, u₂, v₂} (C := C) (CI := CI) F').toCategoryStruct

@[simp]
def GrothendieckContraQuivInst.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) :
    Quiver.{max v v₂ + 1, max u u₂}
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
    ((Cat.postCompOpFunctor'.obj F').map f.base).obj Y.fiber ⟶
    ((Cat.postCompOpFunctor'.obj F').map g.base).obj Y.fiber :=
      eqToHom (by rw [w_base])

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
    ((Cat.postCompOpFunctor'.obj F').map (gcId F' X).base).obj X.fiber = X.fiber :=
  of_eq_true
    (Eq.trans
      (congrArg (fun x ↦ x.obj X.fiber = X.fiber) (F'.map_id X.base))
      (eq_self X.fiber))

@[simp]
theorem gcf_id_fiber.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
  (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (X : GrothendieckContra F') :
    (gcId F' X).fiber = eqToHom (gcf_id_base_eq F' X) :=
      rfl

@[simp]
theorem gcf_id_fiber_cod_eq.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
    (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (X : GrothendieckContra F') :
  (F'.map  (𝟙 X.base)).obj X.fiber = X.fiber :=
    (Functor.congr_obj (F'.map_id X.base).symm X.fiber).symm

@[simp]
theorem gcf_id_fiber_eq.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
    (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (X : GrothendieckContra F') :
  (X.fiber ⟶ (F'.map  (𝟙 X.base)).obj X.fiber) = (X.fiber ⟶ X.fiber) :=
    (congrArg (Quiver.Hom X.fiber) (gcf_id_fiber_cod_eq F' X).symm).symm

@[simp]
theorem gcf_id_fiber_eq_op.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
    (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (X : GrothendieckContra F') :
  ((F'.map  (𝟙 X.base)).obj X.fiber ⟶ X.fiber) = (X.fiber ⟶ X.fiber) :=
    (congrFun (congrArg Quiver.Hom (gcf_id_fiber_cod_eq F' X).symm)
      X.fiber).symm

@[simp]
theorem gcf_id_fiber_eq_rev.{u, v, u₂, v₂} {C : Type u} [CI : Category.{v, u} C]
    (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (X : GrothendieckContra F') :
  ((F'.map  (𝟙 X.base)).obj X.fiber ⟶ X.fiber) =
  (X.fiber ⟶ (F'.map  (𝟙 X.base)).obj X.fiber) :=
    Eq.trans (gcf_id_fiber_eq_op F' X) (gcf_id_fiber_eq F' X).symm

@[simp]
theorem gcf_comp_fiber_cod_eq.{u, v, u₂, v₂} {C : Type u}
    [CI : Category.{v, u} C] (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    {X Y Z : GrothendieckContra F'} (f : gcHom F' X Y) (g : gcHom F' Y Z) :
  (F'.map f.base).obj ((F'.map g.base).obj Z.fiber) =
  (F'.map (g.base ≫ f.base)).obj Z.fiber :=
    (symm <| Functor.congr_obj (F'.map_comp g.base f.base) Z.fiber)

@[simp]
theorem gcf_comp_fiber_eq.{u, v, u₂, v₂} {C : Type u}
    [CI : Category.{v, u} C] (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    {X Y Z : GrothendieckContra F'} (f : gcHom F' X Y) (g : gcHom F' Y Z) :
  ((F'.map f.base).obj Y.fiber ⟶
    (F'.map f.base).obj ((F'.map g.base).obj Z.fiber)) =
  ((F'.map f.base).obj Y.fiber ⟶
    (F'.map (g.base ≫ f.base)).obj Z.fiber) :=
  (congrArg
    (Quiver.Hom ((F'.map f.base).obj Y.fiber))
    (gcf_comp_fiber_cod_eq F' f g).symm).symm

@[simp]
theorem gcf_comp_fiber_eq_op.{u, v, u₂, v₂} {C : Type u}
    [CI : Category.{v, u} C] (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    {X Y Z : GrothendieckContra F'} (f : gcHom F' X Y) (g : gcHom F' Y Z) :
  ((F'.map f.base).obj ((F'.map g.base).obj Z.fiber) ⟶
    (F'.map f.base).obj Y.fiber) =
  ((F'.map (g.base ≫ f.base)).obj Z.fiber ⟶
    (F'.map f.base).obj Y.fiber) :=
  (congrFun
    (congrArg Quiver.Hom (gcf_comp_fiber_cod_eq F' f g).symm)
    ((F'.map f.base).obj Y.fiber)).symm

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
 ((Cat.postCompOpFunctor'.obj F').map (g.base ≫ f.base)).obj Z.fiber =
  ((Cat.postCompOpFunctor'.obj F').map f.base).obj
    (((Cat.postCompOpFunctor'.obj F').map g.base).obj Z.fiber) :=
  of_eq_true
    (Eq.trans
      (congrArg
        (fun x ↦ x.obj Z.fiber = (F'.map f.base).obj ((F'.map g.base).obj Z.fiber))
        (F'.map_comp g.base f.base))
      (eq_self ((F'.map f.base).obj ((F'.map g.base).obj Z.fiber))))

@[simp]
theorem gcf_comp_fiber.{u, v, u₂, v₂} {C : Type u}
    [CI : Category.{v, u} C] (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    {X Y Z : GrothendieckContra F'} (f : gcHom F' X Y) (g : gcHom F' Y Z) :
  (gcComp F' f g).fiber =
    eqToHom (gcf_comp_fiber_precomp F' f g) ≫
    ((Cat.postCompOpFunctor'.obj F').map f.base).map g.fiber ≫
    f.fiber
      := rfl

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
  ∀ {d d' : D} (g : d ⟶ d'), (F.map (baseFunc.map g)).obj (fib d) ⟶ fib d'

/-! ### Internal Implementation Types

These types are used internally and are derived automatically from functor laws.
Clients do not need to provide these.
-/

/--
The type of identity equality proofs for `functorTo`.
This equality is derived automatically from `baseFunc.map_id` and `F.map_id`.
-/
abbrev FunctorToEqId (baseFunc : D ⥤ C) (fib : FunctorToFib F baseFunc) :=
  ∀ d, (F.map (baseFunc.map (𝟙 d))).obj (fib d) = fib d

/--
Derive the identity equality from functor laws.
-/
lemma functorToEqIdProof (baseFunc : D ⥤ C) (fib : FunctorToFib F baseFunc) :
    FunctorToEqId F baseFunc fib := by
  intro d
  simp only [baseFunc.map_id]
  exact congrFun (congrArg Functor.obj (F.map_id (baseFunc.obj d))) (fib d)

/--
The type of composition equality proofs for `functorTo`.
This equality is derived automatically from `baseFunc.map_comp` and `F.map_comp`.
-/
abbrev FunctorToEqComp (baseFunc : D ⥤ C) (fib : FunctorToFib F baseFunc) :=
  ∀ {d d' d'' : D} (g : d ⟶ d') (h : d' ⟶ d''),
    (F.map (baseFunc.map (g ≫ h))).obj (fib d) =
    (F.map (baseFunc.map h)).obj ((F.map (baseFunc.map g)).obj (fib d))

/--
Derive the composition equality from functor laws.
-/
lemma functorToEqCompProof (baseFunc : D ⥤ C) (fib : FunctorToFib F baseFunc) :
    FunctorToEqComp F baseFunc fib := by
  intro d d' d'' g h
  simp only [baseFunc.map_comp]
  exact congrFun (congrArg Functor.obj (F.map_comp (baseFunc.map g) (baseFunc.map h)))
    (fib d)

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
      (F.map (baseFunc.map h)).map (hom g) ≫ hom h

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

section NatTransTo

/--
The type of fiber morphism functions for `natTransTo`.
Given a base natural transformation `baseNat : dataG.baseFunc ⟶ dataH.baseFunc`,
a fiber morphism function assigns to each `d : D` a morphism from the transported
source fiber to the target fiber.
-/
abbrev NatTransToFibMor (dataG dataH : FunctorToData F (D := D))
    (baseNat : dataG.baseFunc ⟶ dataH.baseFunc) :=
  ∀ d, (F.map (baseNat.app d)).obj (dataG.fib d) ⟶ dataH.fib d

/--
The type of base equality proofs for `natTransTo`.
This equality follows from naturality of `baseNat` and functoriality of `F`.
Clients can provide any proof of this equality.
-/
abbrev NatTransToEqBase (dataG dataH : FunctorToData F (D := D))
    (baseNat : dataG.baseFunc ⟶ dataH.baseFunc) :=
  ∀ {d d' : D} (f : d ⟶ d'),
    (F.map (dataG.baseFunc.map f ≫ baseNat.app d')).obj (dataG.fib d) =
    (F.map (baseNat.app d ≫ dataH.baseFunc.map f)).obj (dataG.fib d)

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
    eqToHom (Functor.congr_obj
        (F.map_comp (dataG.baseFunc.map f) (baseNat.app d')) (dataG.fib d)) ≫
      (F.map (baseNat.app d')).map (dataG.hom f) ≫
      fibMor d' =
    eqToHom ((eq_base f).trans (Functor.congr_obj
        (F.map_comp (baseNat.app d) (dataH.baseFunc.map f)) (dataG.fib d))) ≫
      (F.map (dataH.baseFunc.map f)).map (fibMor d) ≫
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
    exact Functor.congr_obj (congrArg F.map hbase) (dataG.fib d)
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
  hom := functorToDataToFunctorCat F (D := D)
  inv := functorCatToFunctorToData F (D := D)
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
  ∀ {c c' : C} (f : c ⟶ c'), fib c ⟶ F.map f ⋙ fib c'

/--
The identity coherence property for `Grothendieck.functorFrom`.
States that `hom (𝟙 c)` equals the canonical isomorphism from `F.map_id`.
-/
abbrev FunctorFromHomId (fib : FunctorFromFib F (E := E))
    (hom : FunctorFromHom F fib) :=
  ∀ c, hom (𝟙 c) = eqToHom (by simp only [Functor.map_id]; rfl)

/--
The composition coherence property for `Grothendieck.functorFrom`.
States that `hom (f ≫ g)` decomposes as the composition of `hom f`, whiskered `hom g`,
and the canonical isomorphism from `F.map_comp`.
-/
abbrev FunctorFromHomComp (fib : FunctorFromFib F (E := E))
    (hom : FunctorFromHom F fib) :=
  ∀ c₁ c₂ c₃ (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃), hom (f ≫ g) =
    hom f ≫ Functor.whiskerLeft (F.map f) (hom g) ≫
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
    have heq : (⟨c, x⟩ : Grothendieck F) = ⟨c, (F.map (𝟙 c)).obj x⟩ := by
      simp only [Functor.map_id]
      rfl
    have h : (Grothendieck.Hom.mk (base := 𝟙 c)
        (fiber := 𝟙 ((F.map (𝟙 c)).obj x)) :
        Grothendieck.Hom (F := F) ⟨c, x⟩ ⟨c, (F.map (𝟙 c)).obj x⟩) = eqToHom heq := by
      rw [Grothendieck.eqToHom_eq]
      simp
    rw [h, eqToHom_map]
  hom_comp c₁ c₂ c₃ f g := by
    ext x
    simp only [Functor.comp_obj, Grothendieck.ι_obj, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, eqToHom_app,
      Grothendieck.ιNatTrans]
    rw [← Category.assoc, ← H.map_comp]
    have heq_obj : (⟨c₃, (F.map g).obj ((F.map f).obj x)⟩ : Grothendieck F) =
        ⟨c₃, (F.map (f ≫ g)).obj x⟩ := by
      congr 1
      exact (congrFun (congrArg Functor.obj (F.map_comp f g)) x).symm
    rw [← eqToHom_map H heq_obj, ← H.map_comp]
    congr 1
    apply Grothendieck.ext <;> simp

/--
Round-trip: constructing a functor from extracted data gives back the original functor.
-/
theorem functorFromData_ofFunctorFrom : functorFromData F (ofFunctorFrom H) = H := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp only [functorFromData, ofFunctorFrom, Grothendieck.functorFrom_map,
      Functor.comp_obj, Functor.comp_map, Grothendieck.ι_obj, Grothendieck.ι_map,
      Functor.whiskerRight_app, Category.id_comp, Category.comp_id, eqToHom_refl]
    rw [← H.map_comp]
    congr 1
    apply Grothendieck.ext <;> simp

/--
Round-trip: the fiber functors from extracted data equal the original fiber functors.
-/
theorem ofFunctorFrom_functorFromData_fib :
    (ofFunctorFrom (functorFromData F data)).fib = data.fib := by
  funext c
  fapply Functor.ext
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
      (congrFun (ofFunctorFrom_functorFromData_fib data) c')) ((F.map f).obj x)).symm := by
  simp only [ofFunctorFrom, Functor.whiskerRight_app, functorFromData,
    Grothendieck.ιNatTrans, Grothendieck.ι_obj, Grothendieck.functorFrom_map]
  simp only [Functor.map_id, Category.id_comp, Category.comp_id, eqToHom_refl]
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
    dataG.hom f ≫ Functor.whiskerLeft (F.map f) (fibNat c') = fibNat c ≫ dataH.hom f

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
    simp only [Functor.map_id, Category.comp_id] at nat
    simp only [eqToHom_refl', Category.id_comp, Category.comp_id, Grothendieck.ι_obj]
    exact nat

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
    unfold CategoryStruct.comp
    simp only [functorFromDataCategory, NatTransFromData.comp, ofNatTransFrom, ofNatTransFromFibNat]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
    simp only [eqToHom_refl', Category.id_comp, Category.comp_id, Grothendieck.ι_obj]
    exact eqToHom_comp_natTrans_comp_app
      (functorFromData_ofFunctorFrom G)
      (functorFromData_ofFunctorFrom H)
      (functorFromData_ofFunctorFrom K)
      α β ⟨c, x⟩

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

/-- A morphism in the contravariant Grothendieck category `F' : Cᵒᵖ' ⥤ Cat` consists of
`base : X.base ⟶ Y.base` and `f.fiber : X.fiber ⟶ (F'.map base).obj Y.fiber`.
-/
structure Hom (X Y : GrothendieckContra' F') where
  /-- The morphism between base objects. -/
  base : X.base ⟶ Y.base
  /-- The morphism from the source fiber object to the pullback of the target fiber object. -/
  fiber : X.fiber ⟶ (F'.map base).obj Y.fiber

@[ext (iff := false)]
theorem ext {X Y : GrothendieckContra' F'} (f g : Hom X Y) (w_base : f.base = g.base)
    (w_fiber : f.fiber ≫ eqToHom (by rw [w_base]) = g.fiber) : f = g := by
  cases f; cases g
  congr
  dsimp at w_base
  cat_disch

@[simp]
theorem id_fiber_cod_eq (X : GrothendieckContra' F') :
  (F'.map  (𝟙 X.base)).obj X.fiber = X.fiber :=
    (Functor.congr_obj (F'.map_id X.base).symm X.fiber).symm

@[simp]
theorem id_fiber_eq (X : GrothendieckContra' F') :
  (X.fiber ⟶ (F'.map  (𝟙 X.base)).obj X.fiber) = (X.fiber ⟶ X.fiber) :=
    (congrArg (Quiver.Hom X.fiber) (id_fiber_cod_eq X).symm).symm

@[simp]
theorem id_fiber_eq_op (X : GrothendieckContra' F') :
  ((F'.map  (𝟙 X.base)).obj X.fiber ⟶ X.fiber) = (X.fiber ⟶ X.fiber) :=
    (congrFun (congrArg Quiver.Hom (id_fiber_cod_eq X).symm) X.fiber).symm

@[simp]
theorem id_fiber_eq_rev (X : GrothendieckContra' F') :
  ((F'.map  (𝟙 X.base)).obj X.fiber ⟶ X.fiber) =
  (X.fiber ⟶ (F'.map  (𝟙 X.base)).obj X.fiber) :=
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
    (F'.map f.base).obj ((F'.map g.base).obj Z.fiber) =
    (F'.map (g.base ≫ f.base)).obj Z.fiber :=
      (symm <| Functor.congr_obj (F'.map_comp g.base f.base) Z.fiber)

@[simp]
theorem comp_fiber_eq {X Y Z : GrothendieckContra' F'}
  (f : Hom X Y) (g : Hom Y Z) :
  ((F'.map f.base).obj Y.fiber ⟶
    (F'.map f.base).obj ((F'.map g.base).obj Z.fiber)) =
  ((F'.map f.base).obj Y.fiber ⟶
    (F'.map (g.base ≫ f.base)).obj Z.fiber) :=
  (congrArg
    (Quiver.Hom ((F'.map f.base).obj Y.fiber))
    (comp_fiber_cod_eq f g ).symm).symm

@[simp]
theorem comp_fiber_eq_op {X Y Z : GrothendieckContra' F'}
  (f : Hom X Y) (g : Hom Y Z) :
  ((F'.map f.base).obj ((F'.map g.base).obj Z.fiber) ⟶
    (F'.map f.base).obj Y.fiber) =
  ((F'.map (g.base ≫ f.base)).obj Z.fiber ⟶
    (F'.map f.base).obj Y.fiber) :=
  (congrFun
    (congrArg Quiver.Hom (comp_fiber_cod_eq f g).symm)
    ((F'.map f.base).obj Y.fiber)).symm

/-- Composition of morphisms in the contravariant Grothendieck category.
-/
def comp {X Y Z : GrothendieckContra' F'} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber := f.fiber ≫ (F'.map f.base).map g.fiber ≫
    eqToHom (comp_fiber_cod_eq f g)

attribute [local simp] eqToHom_map Functor.map_id

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
      slice_lhs 1 3 => erw [Functor.congr_hom (F'.map_id X.base) f.fiber]
      simp
  assoc f g h := by
    ext
    · simp [comp]
    · dsimp [comp]
      slice_lhs 2 4 => erw [Functor.congr_hom (F'.map_comp g.base f.base) h.fiber]
      simp

abbrev GrothendieckContraCat' : Cat := Cat.of (GrothendieckContra' F')

@[simp]
theorem id_base (X : GrothendieckContra' F') : (id X).base = 𝟙 X.base := rfl

@[simp]
theorem id_base_eq (X : GrothendieckContra' F') :
  (F'.map X.id.base).obj X.fiber = X.fiber :=
    (Functor.congr_obj (F'.map_id X.base).symm X.fiber).symm

@[simp]
theorem id_fiber (X : GrothendieckContra' F') :
    (id X).fiber = eqToHom (id_base_eq X).symm := rfl

@[simp]
theorem comp_base {X Y Z : GrothendieckContra' F'} (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).base = f.base ≫ g.base := rfl

@[simp]
theorem comp_fiber {X Y Z : GrothendieckContra' F'} (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).fiber = f.fiber ≫ (F'.map f.base).map g.fiber ≫
      eqToHom (comp_fiber_cod_eq f g) :=
        rfl

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

lemma eqToHom_eq {X Y : GrothendieckContra' F'} (hF : X = Y) :
    eqToHom hF = { base := eqToHom (by subst hF; rfl)
                   fiber := eqToHom (by subst hF; exact (id_fiber_cod_eq X).symm) } := by
  subst hF
  rfl

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
  simp only [grothendieckContraIsoHomMap, gcf_id_fiber, id_fiber]
  exact Cat.eqToHom_postCompOp_eq F' base
    (gcf_id_base_eq F' ⟨base, fiber⟩)
    (id_base_eq ⟨base, fiber⟩).symm

theorem grothendieckContraIsoHomMapId
    (X : GrothendieckContra F') :
    grothendieckContraIsoHomMap (gcId F' X) = 𝟙 (grothendieckContraIsoHomObj X) := by
  cases X with | mk base fiber =>
  have h_base := @grothendieckContraIsoHomMapId_base_components _ CInst F' base fiber
  have h_fiber := @grothendieckContraIsoHomMapId_fiber_components _ CInst F' base fiber
  refine GrothendieckContra'.ext _ _ h_base ?_
  rw [h_fiber]
  simp
  rfl

theorem grothendieckContraIsoHomMapComp_base_components
    {X Y Z : GrothendieckContra F'}
    (f : gcHom F' X Y)
    (g : gcHom F' Y Z) :
    (grothendieckContraIsoHomMap (gcComp F' f g)).base =
    (grothendieckContraIsoHomMap f ≫ grothendieckContraIsoHomMap g).base := by
  simp only [grothendieckContraIsoHomMap, grothendieckContraIsoHomObj]
  rw [gcf_comp_base]
  simp
  rfl

theorem grothendieckContraIsoHomMapComp_fiber_eq
    {X Y Z : GrothendieckContra F'} (f : gcHom F' X Y) (g : gcHom F' Y Z) :
    eqToHom (gcf_comp_fiber_precomp F' f g) ≫
      ((Cat.postCompOpFunctor'.obj F').map f.base).map g.fiber ≫ f.fiber =
    (grothendieckContraIsoHomMap f ≫ grothendieckContraIsoHomMap g).fiber := by
  simp
    [ grothendieckContraIsoHomMap, grothendieckContraIsoHomObj,
      Cat.postCompOpFunctor', GrothendieckContraInst', CategoryStruct.comp,
      Cat.opFunctorObj', Cat.of, Cat.str, Bundled.of, CategoryOp'Inst]
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
  simp only [Cat.str]
  exact grothendieckContraIsoHomMapComp_fiber_eq f g

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
  simp
    [grothendieckContraIsoInvMap, grothendieckContraIsoInvObj,
     Cat.opFunctorObj', Cat.of, Cat.str, Bundled.of]
  exact Eq.trans (id_fiber _)
    (by simp ; exact (Cat.eqToHom_postCompOp_eq F' base _ _).symm)

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
  simp only [grothendieckContraIsoInvMap, grothendieckContraIsoInvObj]
  unfold GrothendieckContraInst'
  unfold CategoryStruct.comp
  simp only []
  rw [comp_base]
  rw [gcf_comp_base]
  simp

theorem grothendieckContraIsoInvMapComp_fiber_eq
    {X Y Z : GrothendieckContra' F'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f.fiber ≫ (F'.map f.base).map g.fiber ≫ eqToHom (comp_fiber_cod_eq f g) =
    eqToHom (gcf_comp_fiber_precomp F' (grothendieckContraIsoInvMap f)
      (grothendieckContraIsoInvMap g)) ≫
    ((Cat.postCompOpFunctor'.obj F').map (grothendieckContraIsoInvMap f).base).map
      (grothendieckContraIsoInvMap g).fiber ≫
    (grothendieckContraIsoInvMap f).fiber := by
  simp
    [ grothendieckContraIsoInvMap, grothendieckContraIsoInvObj,
      Cat.postCompOpFunctor', CategoryStruct.comp,
      Cat.opFunctorObj', Cat.of, Cat.str, Bundled.of, CategoryOp'Inst]
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

theorem grothendieckContraIsoHomInvId :
    grothendieckContraIsoHom ⋙ grothendieckContraIsoInv = 𝟭 (GrothendieckContraCat F') := by
  fapply Functor.ext
  · intro X
    cases X
    rfl
  · intro X Y f
    cases f
    simp
    rfl

theorem grothendieckContraIsoInvHomId :
    grothendieckContraIsoInv ⋙ grothendieckContraIsoHom = 𝟭 (GrothendieckContra' F') := by
  fapply Functor.ext
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
  hom := grothendieckContraIsoHom
  inv := grothendieckContraIsoInv
  hom_inv_id := grothendieckContraIsoHomInvId
  inv_hom_id := grothendieckContraIsoInvHomId

def grothendieckContraEquiv :
  GrothendieckContraCat F' ≌ GrothendieckContra' F' :=
    Cat.equivOfIso grothendieckContraIso

instance gcIsoHomFaithful : (grothendieckContraIsoHom (F' := F')).Faithful := by
  change (grothendieckContraEquiv (F' := F')).functor.Faithful
  infer_instance

instance gcIsoInvFaithful : (grothendieckContraIsoInv (F' := F')).Faithful := by
  change (grothendieckContraEquiv (F' := F')).symm.functor.Faithful
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
   fImg.fiber ≫ (H'.map fImg.base).map gImg.fiber ≫
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
  exact Functor.map_id (transferFromCov F_cov) X

/--
The transferred functor maps composition to the explicitly constructed composition.
-/
@[simp]
theorem transferFromCov_map_comp {E : Type uₑ} [Category.{vₑ} E] {E' : Type uₑ'} [Category.{vₑ'} E']
    {G' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}} {H' : E'ᵒᵖ' ⥤ Cat.{v₄, u₄}}
    (F_cov : GrothendieckContraCat G' ⥤ GrothendieckContraCat H')
    {X Y Z : GrothendieckContra' G'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (transferFromCov F_cov).map (f ≫ g) = transferredComp F_cov f g := by
  exact Functor.map_comp (transferFromCov F_cov) f g

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
  ⟨c, (F'.map t).obj x.fiber⟩

/--
If `F' : Cᵒᵖ' ⥤ Cat` is a contravariant functor and `t : c ⟶ x.base` is a
morphism in `C`, then `transport` maps each `x.base`-based element `x` of
`GrothendieckContra' F'` to a `c`-based element `x.transport t`.

`fromTransport` is the morphism `x.transport t ⟶ x` induced by `t` and the
identity on fibers.
-/
@[simps]
def fromTransport (x : GrothendieckContra' F') {c : C} (t : c ⟶ x.base) :
    x.transport t ⟶ x :=
  ⟨t, 𝟙 _⟩

private lemma map_iso_comp_obj_eq {X Y : GrothendieckContra' F'}
    (e₁ : X.base ≅ Y.base) (z : F'.obj Y.base) :
    z = (F'.map e₁.hom ≫ F'.map e₁.inv).obj z := by
  have : F'.map e₁.hom ≫ F'.map e₁.inv = 𝟙 (F'.obj Y.base) := by
    rw [← F'.map_comp, ← F'.map_id]
    congr 1
    exact e₁.inv_hom_id
  simp [this]

@[simps!]
def isoMk_cov_fiber_equiv
    {X Y : GrothendieckContraCat F'} (e₁ : X.base ≅ Y.base)
    (e₂ : X.fiber ≅ (F'.map e₁.inv).obj Y.fiber) :
    ((Cat.postCompOpFunctor'.obj F').map e₁.hom).obj X.fiber ≅ Y.fiber :=
  ((Cat.postCompOpFunctor'.obj F').map e₁.hom).mapIso e₂ ≪≫
    eqToIso (Functor.congr_obj ((Cat.postCompOpFunctor'.obj F').mapIso e₁).inv_hom_id Y.fiber)

-- Lemma: F'.map of a composition of isos
private lemma map_comp_iso {X Y : GrothendieckContraCat F'} (e₁ : X.base ≅ Y.base) :
    F'.map (e₁.inv ≫ e₁.hom) = F'.map e₁.inv ≫ F'.map e₁.hom := by
  rw [F'.map_comp]

private lemma map_inv_hom_eq_id {X Y : GrothendieckContraCat F'} (e₁ : X.base ≅ Y.base) :
    F'.map e₁.inv ≫ F'.map e₁.hom = F'.map (𝟙 Y.base) := by
  rw [← F'.map_comp, e₁.inv_hom_id]

@[simps!]
def isoMk_cov {X Y : GrothendieckContraCat F'} (e₁ : X.base ≅ Y.base)
    (e₂ : X.fiber ≅ (F'.map e₁.inv).obj Y.fiber) :
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
    (e₂ : X.fiber ≅ (F'.map e₁.hom).obj Y.fiber) :
    (grothendieckContraIsoInv.obj X).fiber ≅
    (F'.map (baseIsoToCov e₁).inv).obj (grothendieckContraIsoInv.obj Y).fiber :=
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
    (e₂ : X.fiber ≅ (F'.map e₁.hom).obj Y.fiber) :
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
    (map_cov α).obj X = ⟨X.base, (α.app X.base).obj X.fiber⟩ := by
  unfold map_cov
  simp only [Functor.op', functorOp'Obj]
  rw [Grothendieck.map_obj]
  simp only [Cat.postCompOpFunctor']
  rfl

theorem map_cov_map (α : F' ⟶ G') {X Y : GrothendieckContra F'} (f : gcHom F' X Y) :
    (map_cov α).map f = ⟨f.base,
      (eqToHom (Eq.symm ((Cat.postCompOpFunctor'.map α).naturality f.base))).app Y.fiber ≫
      (Functor.op' (α.app X.base)).map f.fiber⟩ := by
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
    (map α).obj X = ⟨X.base, (α.app X.base).obj X.fiber⟩ := rfl

@[simp]
theorem map_map (α : F' ⟶ G') {X Y : GrothendieckContra' F'} (f : X ⟶ Y) :
    (map α).map f = ⟨f.base, (α.app X.base).map f.fiber ≫
      (eqToHom (α.naturality f.base)).app Y.fiber⟩ := by
  unfold map
  simp only [transferFromCov_map, transferredMap]
  rw [map_cov_map]
  simp
  congr 1
  rw [op_comp_eq]
  congr 1
  apply Cat.eqToHom_op'_eq

theorem functor_comp_forget {α : F' ⟶ G'} :
    GrothendieckContra'.map α ⋙ GrothendieckContra'.forget G' =
    GrothendieckContra'.forget F' :=
  rfl

@[simp]
theorem map_id_eq : map (𝟙 F') = 𝟙 (Cat.of <| GrothendieckContra' F') := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp [map_map]
    rfl

def mapIdIso : map (𝟙 F') ≅ 𝟙 (Cat.of <| GrothendieckContra' F') :=
  eqToIso map_id_eq

@[simp]
theorem map_comp_eq (α : F' ⟶ G') (β : G' ⟶ H') :
    map (α ≫ β) = map α ⋙ map β := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp only [map_map, NatTrans.comp_app, Cat.comp_obj, Cat.comp_map,
      eqToHom_refl, Functor.comp_map, Functor.map_comp, Category.comp_id, Category.id_comp]
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

theorem compAsSmallFunctorEquivalenceInverse_map
    {X Y : GrothendieckContra' F'} (f : X ⟶ Y) :
    (compAsSmallFunctorEquivalenceInverse (F' := F')).map f =
    ⟨f.base,
     eqToHom (compAsSmallFunctorEquivalenceInverse_obj_fiber X) ≫
     AsSmall.up.map f.fiber⟩ := by
  simp
  unfold compAsSmallFunctorEquivalenceInverse
  simp only
    [transferFromCov_map, transferredMap,
     compAsSmallFunctorEquivalenceInverse_cov_map]

def compAsSmallFunctorEquivalence :
    GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}) ≌
    GrothendieckContra' F' where
  functor := compAsSmallFunctorEquivalenceFunctor
  inverse := compAsSmallFunctorEquivalenceInverse
  unitIso := Iso.refl _
  counitIso := Iso.refl _

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

/--
The contravariant Grothendieck construction as a functor from the functor
category `(Cᵒᵖ' ⥤ Cat)` to the over category over the base category.
-/
def functor {E : Type u} [Category.{v} E] :
    (Eᵒᵖ' ⥤ Cat.{v, u}) ⥤ Over (T := Cat.{v, u}) (Cat.of E) where
  obj F' := Over.mk (X := Cat.of E) (Y := Cat.of (GrothendieckContra' F'))
                    (GrothendieckContra'.forget F')
  map {_ _} α := Over.homMk (X := Cat.of E) (GrothendieckContra'.map α)
                            GrothendieckContra'.functor_comp_forget
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
      · simp; rfl
      · simp; apply Subsingleton.elim)
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
  d = (F'.map (𝟙 c)).obj ((ι c).obj d).fiber := by
    simp [ι_obj]
    have deq := (congrFun (congrArg Functor.obj <| F'.map_id c) d).symm
    simp at deq
    exact deq

def ι_map (c : C) {d d' : F'.obj c} (f : d ⟶ d') :
  (ι c).map f = ⟨𝟙 c, f ≫ eqToHom (ι_map_fiber c (d := d'))⟩ := by
    simp [ι_obj]
    unfold ι
    unfold gr_ι_flip
    apply ext
    all_goals simp
      [gcCodFuncToGcContra', gcCodFuncToGcContra, evaluation,
       grothendieckContraIsoHom, grothendieckContraIsoHomMap]
    -- The base goal is now solved, only fiber remains
    rw [op_comp_eq]
    apply congrArg
    rw [Cat.eqToHom_op'_eq]

/--
The covariant fiber inclusion functor is faithful.
-/
abbrev faithful_ι_cov (c : C) : (ι_cov (F' := F') c).Faithful :=
  op'_faithful (Grothendieck.ι (Cat.postCompOpFunctor'.obj F') c)

/--
The fiber inclusion functor is faithful.
-/
instance faithful_ι (c : C) : (ι (F' := F') c).Faithful := by
  have : (ι_cov (F' := F') c).Faithful := faithful_ι_cov c
  have : (grothendieckContraIsoHom (F' := F')).Faithful := gcIsoHomFaithful
  unfold ι
  unfold gcCodFuncToGcContra'
  infer_instance

/--
Natural transformation induced by a morphism in the base category.
For f : c ⟶ d in C (viewed as d ⟶ c in Cᵒᵖ'), the natural transformation
goes from F'.map f ⋙ ι c to ι d.
-/
def ιNatTrans {c d : C} (f : c ⟶ d) : F'.map f ⋙ ι c ⟶ ι d where
  app X := { base := f, fiber := 𝟙 _ }
  naturality X Y g := by
    simp only [ι_obj, ι_map, Functor.comp_obj, Functor.comp_map]
    unfold CategoryStruct.comp
    unfold Category.toCategoryStruct
    unfold GrothendieckContraCat'
    unfold Cat.of Cat.str Bundled.of
    simp
    unfold GrothendieckContraInst'
    unfold comp
    apply ext
    case w_base =>
      -- base component: both compositions have base f
      simp
    case w_fiber =>
      -- fiber component: involves eqToHom and functoriality
      simp only [Category.id_comp, Functor.map_id, Category.assoc]
      change ((F'.map f).map g ≫ _) ≫ _ ≫ _ = (F'.map f).map (g ≫ _) ≫ _
      rw [Functor.map_comp]
      rw [eqToHom_map]
      simp only [Category.assoc]
      simp

variable (fib : ∀ c, F'.obj c ⥤ T)
variable (hom : ∀ {c d : C} (f : c ⟶ d), F'.map f ⋙ fib c ⟶ fib d)
variable (hom_id : ∀ c, hom (𝟙 c) = eqToHom (congrArg (· ⋙ fib c) (F'.map_id c)))

variable (hom_comp : ∀ {c d e : C} (f : c ⟶ d) (g : d ⟶ e),
  hom (f ≫ g) = eqToHom (congrArg (· ⋙ fib c) (F'.map_comp g f)) ≫
    Functor.whiskerLeft (F'.map g) (hom f) ≫ hom g)

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
    -- Simplify whiskerLeft - this eliminates the eqToHom terms
    simp [Functor.whiskerLeft]
    -- Cancel common prefix
    congr 1
    -- The goal is now showing naturality of hom f.base
    -- Recognize (fib X.base).map ∘ (F'.map f.base).map as (F'.map f ⋙ fib X).map
    change (fib X.base).map ((F'.map f.base).map g.fiber) ≫
      (hom f.base).app ((F'.map g.base).obj Z.fiber) ≫ (hom g.base).app Z.fiber =
      (hom f.base).app Y.fiber ≫ (fib Y.base).map g.fiber ≫ (hom g.base).app Z.fiber
    rw [← Functor.comp_map]
    -- Reassociate to separate the naturality square
    rw [← Category.assoc]
    -- Now apply naturality
    rw [NatTrans.naturality (hom f.base) g.fiber]
    simp

/--
The fiber inclusion composed with `functorFrom` recovers the original fiber functor.
-/
def ιCompFunctorFrom (c : C) :
    ι c ⋙ functorFrom fib hom hom_id hom_comp ≅ fib c :=
  NatIso.ofComponents
    (fun _ => Iso.refl _)
    (fun f => by
      -- Need to show: (ι c ⋙ functorFrom).map f ≫ Iso.refl _ = Iso.refl _ ≫ (fib c).map f
      -- which simplifies to: (functorFrom).map (ι c).map f = (fib c).map f
      simp [functorFrom, ι_obj]
      -- Use ι_map to rewrite (ι c).map f
      rw [ι_map]
      -- Now we have (fib c).map (f ≫ eqToHom ...) ≫ (hom (𝟙 c)).app _
      simp only [Functor.map_comp, ι_obj]
      -- Use hom_id to simplify hom (𝟙 c)
      rw [hom_id]
      -- Simplify the eqToHom terms
      simp
    )


/--
Interaction between fiber inclusion and `map`.
-/
def ιCompMap {G' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}} (α : F' ⟶ G') (c : C) :
    ι c ⋙ map α ≅ (α.app c) ⋙ ι c :=
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
  ∀ {c d : C} (f : c ⟶ d), F'.map f ⋙ fib c ⟶ fib d

/--
The identity coherence property for bundled `FunctorFromData`.
States that `hom (𝟙 c)` equals the canonical isomorphism from `F'.map_id`.
-/
abbrev FunctorFromDataHomId (fib : FunctorFromDataFib (F' := F') (T := T))
    (hom : FunctorFromDataHom (F' := F') fib) :=
  ∀ c, hom (𝟙 c) = eqToHom (congrArg (· ⋙ fib c) (F'.map_id c))

/--
The composition coherence property for bundled `FunctorFromData`.
States that `hom (f ≫ g)` decomposes as the composition of whiskered `hom f`,
`hom g`, and the canonical isomorphism from `F'.map_comp`.
-/
abbrev FunctorFromDataHomComp (fib : FunctorFromDataFib (F' := F') (T := T))
    (hom : FunctorFromDataHom (F' := F') fib) :=
  ∀ {c d e : C} (f : c ⟶ d) (g : d ⟶ e), hom (f ≫ g) =
    eqToHom (congrArg (· ⋙ fib c) (F'.map_comp g f)) ≫
    Functor.whiskerLeft (F'.map g) (hom f) ≫ hom g

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

/--
Construct a functor from the contravariant Grothendieck construction using bundled data.
This wraps `GrothendieckContra'.functorFrom`.
-/
def functorFromData : GrothendieckContra' F' ⥤ T :=
  functorFrom data.fib' data.hom' data.hom_id' data.hom_comp'

variable (H : GrothendieckContra' F' ⥤ T)

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
    have h_fmap_id : (F'.map (𝟙 c)).obj x = x :=
      congrFun (congrArg Functor.obj (F'.map_id c)) x
    have hsrc_eq : (⟨c, (F'.map (𝟙 c)).obj x⟩ : GrothendieckContra' F') = ⟨c, x⟩ := by
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
    have heq_obj : (⟨c₁, (F'.map f).obj ((F'.map g).obj x)⟩ : GrothendieckContra' F') =
        ⟨c₁, (F'.map fg).obj x⟩ := by
      simp only [fg]
      congr 1
      exact (congrFun (congrArg Functor.obj (F'.map_comp g f)) x).symm
    simp only [← H.map_comp]
    rw [← eqToHom_map H heq_obj.symm, ← H.map_comp]
    congr 1
    -- Prove equality of morphisms in GrothendieckContra' F'
    apply ext
    · simp [GrothendieckContraInst', comp_base, base_eqToHom, Category.id_comp]
    · simp [GrothendieckContraInst', Category.id_comp, eqToHom_refl]

/--
Round-trip: constructing a functor from extracted data gives back the original functor.
-/
theorem functorFromData_ofFunctorFrom : functorFromData (ofFunctorFrom H) = H := by
  fapply Functor.ext
  · intro X
    rfl
  · intro X Y f
    simp only [functorFromData, ofFunctorFrom, functorFrom, Functor.comp_obj,
      Functor.comp_map, Functor.whiskerRight_app, ι_obj, ι_map, Category.id_comp,
      Category.comp_id, eqToHom_refl]
    rw [← H.map_comp]
    congr 1
    have w_base : (({ base := 𝟙 X.base, fiber := f.fiber ≫ eqToHom (ι_map_fiber X.base) } :
        Hom X ((ι X.base).obj ((F'.map f.base).obj Y.fiber))) ≫
        (ιNatTrans f.base).app Y.fiber).base = f.base := by
      unfold CategoryStruct.comp Category.toCategoryStruct GrothendieckContraCat' Cat.of Cat.str
        Bundled.of GrothendieckContraInst' comp ιNatTrans
      simp only [Category.id_comp]
    refine ext _ _ w_base ?_
    simp only [GrothendieckContraInst', comp_fiber, ιNatTrans, Category.assoc]
    -- Goal: f.fiber ≫ eqToHom _ ≫ (F'.map (𝟙 X.base)).map (𝟙 _) ≫ eqToHom _ ≫ eqToHom _ = f.fiber
    -- Use the fact that (F'.map (𝟙 X.base)).map (𝟙 _) = 𝟙 _
    have h_map_id : (F'.map (𝟙 X.base)).map
        (𝟙 ((F'.map f.base ⋙ ι X.base).obj Y.fiber).fiber) =
        𝟙 ((F'.map (𝟙 X.base)).obj ((F'.map f.base ⋙ ι X.base).obj Y.fiber).fiber) :=
      (F'.map (𝟙 X.base)).map_id _
    rw [h_map_id]
    -- Goal: f.fiber ≫ eqToHom A ≫ 𝟙 X ≫ eqToHom B = f.fiber
    -- Use convert to get: ... = f.fiber ≫ 𝟙 _
    convert Category.comp_id f.fiber using 1
    -- Now: f.fiber ≫ eqToHom A ≫ 𝟙 X ≫ eqToHom B = f.fiber ≫ 𝟙 _
    congr 1
    simp only [eqToHom_trans]
    exact eqToHom_comp_id_comp_eqToHom _ _

/--
Round-trip: the fiber functors from extracted data equal the original fiber functors.
-/
theorem ofFunctorFrom_functorFromData_fib :
    (ofFunctorFrom (functorFromData data)).fib' = data.fib' := by
  funext c
  fapply Functor.ext
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
      (congrFun (ofFunctorFrom_functorFromData_fib data) c)) ((F'.map f).obj x)) ≫
    (data.hom' f).app x ≫
    eqToHom (congrFun (congrArg Functor.obj
      (congrFun (ofFunctorFrom_functorFromData_fib data) d)) x).symm := by
  simp only [ofFunctorFrom, Functor.whiskerRight_app, functorFromData, functorFrom,
    ιNatTrans, ι_obj]
  simp only [Functor.map_id, Category.id_comp]
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
    Functor.whiskerLeft (F'.map f) (fibNat c) ≫ dataH.hom' f = dataG.hom' f ≫ fibNat d

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
    simp only [Functor.map_id, Category.id_comp] at nat
    simp only [eqToHom_refl', Category.id_comp, Category.comp_id, ι_obj]
    exact nat.symm

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
    unfold CategoryStruct.comp
    simp only [functorFromDataCategory, NatTransFromData.comp,
      ofNatTransFromData, ofNatTransFromDataFibNat]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
    simp only [eqToHom_refl', Category.id_comp, Category.comp_id, ι_obj]
    exact eqToHom_comp_natTrans_comp_app'
      (functorFromData_ofFunctorFrom G)
      (functorFromData_ofFunctorFrom H)
      (functorFromData_ofFunctorFrom K)
      α β ⟨c, x⟩

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
  ∀ {e e' : E} (g : e ⟶ e'), fib e ⟶ (F'.map (baseFunc.map g)).obj (fib e')


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
  ∀ e, fib e = (F'.map (baseFunc.map (𝟙 e))).obj (fib e)

/--
Derive the identity equality from functor laws.
-/
lemma functorToEqIdProof (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (baseFunc : E ⥤ C)
    (fib : FunctorToFib (F' := F') baseFunc) : FunctorToEqId F' baseFunc fib := by
  intro e
  simp only [baseFunc.map_id]
  exact (congrFun (congrArg Functor.obj (F'.map_id (baseFunc.obj e))) (fib e)).symm

/--
The type of composition equality proofs for `GrothendieckContra'.functorTo`.
This equality is derived automatically from `baseFunc.map_comp` and `F'.map_comp`.
-/
abbrev FunctorToEqComp (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (baseFunc : E ⥤ C)
    (fib : FunctorToFib (F' := F') baseFunc) :=
  ∀ {e e' e'' : E} (g : e ⟶ e') (h : e' ⟶ e''),
    (F'.map (baseFunc.map g)).obj ((F'.map (baseFunc.map h)).obj (fib e'')) =
    (F'.map (baseFunc.map (g ≫ h))).obj (fib e'')

/--
Derive the composition equality from functor laws.
-/
lemma functorToEqCompProof (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) (baseFunc : E ⥤ C)
    (fib : FunctorToFib (F' := F') baseFunc) : FunctorToEqComp F' baseFunc fib := by
  intro e e' e'' g h
  simp only [baseFunc.map_comp]
  exact (congrFun (congrArg Functor.obj
    (F'.map_comp (baseFunc.map h) (baseFunc.map g))) (fib e'')).symm

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
      hom g ≫ (F'.map (baseFunc.map g)).map (hom h) ≫
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
    rw [congr h, id_fiber, eqToHom_trans]
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
  ∀ e, dataG.fib e ⟶ (F'.map (baseNat.app e)).obj (dataH.fib e)

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
    (F'.map comp1).obj (dataH.fib e') = (F'.map comp2).obj (dataH.fib e')

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
      (F'.map (dataG.baseFunc.map f)).map (fibMor e') ≫
      eqToHom (Functor.congr_obj
        (F'.map_comp (baseNat.app e') (dataG.baseFunc.map f)).symm (dataH.fib e')) =
    fibMor e ≫
      (F'.map (baseNat.app e)).map (dataH.hom f) ≫
      eqToHom ((Functor.congr_obj
        (F'.map_comp (dataH.baseFunc.map f) (baseNat.app e)).symm (dataH.fib e')).trans
        (eq_base f))

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
    simp only [GrothendieckContraInst', comp_fiber, functorTo]
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
    simp only [GrothendieckContraInst', comp_base] at hbase
    exact Functor.congr_obj (congrArg F'.map hbase.symm) (dataH.fib e')
  fibNat {e e'} f := by
    simp only [ofNatTransBaseNat, functorTo]
    have h := α.naturality f
    simp only [functorTo] at h
    have hfiber := congr h
    simp only [GrothendieckContraInst', comp_fiber] at hfiber
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
  hom := functorToDataToFunctorCat
  inv := functorCatToFunctorToData
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
    (F.map (baseFib.map f)).obj ((fibFib c).obj x) ⟶ (fibFib c').obj ((G.map f).obj x)

/--
The naturality condition for cross-fiber morphisms: for each `f : c ⟶ c'` and
`g : x ⟶ y` in `G.obj c`, the appropriate square commutes.
-/
abbrev FunctorBetweenFibHomCrossNat (baseFib : FunctorBetweenBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenFibFib G F baseFib)
    (fibHomCrossApp : FunctorBetweenFibHomCrossApp G F baseFib fibFib) :=
  ∀ {c c' : C} (f : c ⟶ c') {x y : G.obj c} (g : x ⟶ y),
    (F.map (baseFib.map f)).map ((fibFib c).map g) ≫ fibHomCrossApp f y =
    fibHomCrossApp f x ≫ (fibFib c').map ((G.map f).map g)

/--
The equality proof for identity morphisms in the target Grothendieck.
States that `(F.map (baseFib.map (𝟙 c))).obj ((fibFib c).obj x)` equals
`(fibFib c).obj ((G.map (𝟙 c)).obj x)`.
-/
abbrev FunctorBetweenBaseHomEqId (baseFib : FunctorBetweenBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenFibFib G F baseFib) :=
  ∀ (c : C) (x : G.obj c),
    (F.map (baseFib.map (𝟙 c))).obj ((fibFib c).obj x) =
      (fibFib c).obj ((G.map (𝟙 c)).obj x)

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
    (F.map (baseFib.map (f ≫ g))).obj ((fibFib c).obj x) =
    (F.map (baseFib.map g)).obj
      ((F.map (baseFib.map f)).obj ((fibFib c).obj x))

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
    (F.map_comp (baseFib.map f) (baseFib.map g))) ((fibFib c).obj x)

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
    (fibFib c'').obj ((G.map g).obj ((G.map f).obj x)) =
    (fibFib c'').obj ((G.map (f ≫ g)).obj x)

/--
Derive the G.map_comp equality from functor laws.
-/
lemma functorBetweenGMapCompEqProof
    (baseFib : FunctorBetweenBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenFibFib G F baseFib) :
    FunctorBetweenGMapCompEq G F baseFib fibFib := by
  intro c c' c'' f g x
  exact congrArg (fibFib c'').obj
    (congrFun (congrArg Functor.obj (G.map_comp f g).symm) x)

/--
The composition coherence: `fibHomCrossApp (f ≫ g) x` decomposes correctly.
-/
abbrev FunctorBetweenBaseHomComp (baseFib : FunctorBetweenBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenFibFib G F baseFib)
    (fibHomCrossApp : FunctorBetweenFibHomCrossApp G F baseFib fibFib) :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'') (x : G.obj c),
    fibHomCrossApp (f ≫ g) x =
    eqToHom (functorBetweenBaseHomEqCompProof G F baseFib fibFib f g x) ≫
    (F.map (baseFib.map g)).map (fibHomCrossApp f x) ≫
    fibHomCrossApp g ((G.map f).obj x) ≫
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
    (F.map ((functorBetweenInnerBaseFunc G F data c).map (𝟙 x))).obj
      (functorBetweenInnerFib G F data c x) =
    functorBetweenInnerFib G F data c x := by
  simp only [functorBetweenInnerBaseFunc, functorBetweenInnerFib, Functor.const_obj_map]
  exact congrFun (congrArg Functor.obj (F.map_id _)) _

/--
The fiber morphisms for the inner FunctorTo construction.
Since the base functor is constant, the transport is trivial and
the fiber morphism is just `(fibFib c).map φ`.
-/
def functorBetweenInnerHom (c : C) {x y : G.obj c} (φ : x ⟶ y) :
    (F.map ((functorBetweenInnerBaseFunc G F data c).map φ)).obj
      (functorBetweenInnerFib G F data c x) ⟶
    functorBetweenInnerFib G F data c y :=
  eqToHom (functorBetweenInnerHom_eq G F data c x) ≫
    (data.fibFib c).map φ

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

/--
Composition coherence for the inner FunctorTo.
-/
theorem functorBetweenInnerHom_comp (c : C) {x y z : G.obj c}
    (φ : x ⟶ y) (ψ : y ⟶ z) :
    functorBetweenInnerHom G F data c (φ ≫ ψ) =
      eqToHom (Grothendieck.functorToEqCompProof F
        (functorBetweenInnerBaseFunc G F data c)
        (functorBetweenInnerFib G F data c) φ ψ) ≫
      (F.map ((functorBetweenInnerBaseFunc G F data c).map ψ)).map
        (functorBetweenInnerHom G F data c φ) ≫
      functorBetweenInnerHom G F data c ψ := by
  simp only [functorBetweenInnerHom, functorBetweenInnerBaseFunc, functorBetweenInnerFib,
    Functor.const_obj_obj, Functor.const_obj_map, (data.fibFib c).map_comp]
  have hFid : F.map (𝟙 (data.baseFib.obj c)) = 𝟭 (F.obj (data.baseFib.obj c)) := F.map_id _
  rw [functor_map_of_eq_id hFid]
  cat_disch

/--
The proof term from `functorBetweenInnerHom` can be expressed explicitly.
Since the base functor is constant, `(F.map (𝟙 d)).obj x = x`.
-/
lemma functorBetweenInnerHom_proof (c : C) (x : G.obj c) :
    (F.map ((functorBetweenInnerBaseFunc G F data c).map (𝟙 x))).obj
      (functorBetweenInnerFib G F data c x) =
    functorBetweenInnerFib G F data c x := by
  simp only [functorBetweenInnerBaseFunc, Functor.const_obj_map]
  have hFid : F.map (𝟙 (data.baseFib.obj c)) = 𝟭 (F.obj (data.baseFib.obj c)) := F.map_id _
  simp only [hFid, Functor.id_obj]

/--
The `eqToHom` from `functorBetweenInnerHom_eq` is identity on objects after applying `F.map_id`.
This is because `(F.map (𝟙 d)).obj x = (𝟭 _).obj x = x`.
-/
@[simp]
lemma eqToHom_functorBetweenInnerHom_eq (c : C) (x : G.obj c) :
    eqToHom (functorBetweenInnerHom_eq G F data c x) =
    eqToHom (congrFun (congrArg Functor.obj (F.map_id (data.baseFib.obj c))) _) := by
  simp only [functorBetweenInnerBaseFunc, functorBetweenInnerFib, Functor.const_obj_map]

/--
Mapping `eqToHom (functorBetweenInnerHom_eq ...)` through `(F.map g).map` yields an `eqToHom`.
-/
lemma functor_map_eqToHom_functorBetweenInnerHom_eq {c : C} (x : G.obj c)
    {d : D} (g : data.baseFib.obj c ⟶ d) :
    (F.map g).map (eqToHom (functorBetweenInnerHom_eq G F data c x)) =
    eqToHom (congrArg (F.map g).obj (functorBetweenInnerHom_eq G F data c x)) := by
  exact functor_map_eqToHom (F.map g) (functorBetweenInnerHom_eq G F data c x)

/--
The equality `functorBetweenInnerHom_eq` becomes reflexive after applying `(F.map g).obj`.
-/
lemma functorBetweenInnerHom_eq_transport {c : C} (x : G.obj c)
    {d : D} (g : data.baseFib.obj c ⟶ d) :
    (F.map g).obj ((F.map (𝟙 (data.baseFib.obj c))).obj ((data.fibFib c).obj x)) =
    (F.map g).obj ((data.fibFib c).obj x) := by
  rw [F.map_id]
  rfl

/--
Transport of `functorBetweenInnerHom` through `(F.map g).map` relates to
the underlying `(data.fibFib c).map φ` via `eqToHom`.
-/
lemma functorBetweenInnerHom_transport {c : C} {x y : G.obj c} (φ : x ⟶ y)
    {d : D} (g : data.baseFib.obj c ⟶ d) :
    (F.map g).map (functorBetweenInnerHom G F data c φ) =
    eqToHom (functorBetweenInnerHom_eq_transport G F data x g) ≫
      (F.map g).map ((data.fibFib c).map φ) := by
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
    (functorBetweenFibFunc G F data c').obj ((G.map f).obj x) :=
  ⟨data.baseFib.map f, data.fibHomCrossApp f x⟩

/--
Naturality of `functorBetweenHomNatApp`: for `φ : x ⟶ y` in `G.obj c`,
the square commutes.
-/
theorem functorBetweenHomNat_naturality {c c' : C} (f : c ⟶ c')
    {x y : G.obj c} (φ : x ⟶ y) :
    (functorBetweenFibFunc G F data c).map φ ≫
      functorBetweenHomNatApp G F data f y =
    functorBetweenHomNatApp G F data f x ≫
      (functorBetweenFibFunc G F data c').map ((G.map f).map φ) := by
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
    have hFmapId : F.map (𝟙 (data.baseFib.obj c')) = 𝟭 _ := F.map_id _
    rw [functor_map_of_eq_id hFmapId]
    have hNat := data.fibHomCrossNat f φ
    cat_disch

/--
The natural transformation `functorBetweenFibFunc c ⟶ G.map f ⋙ functorBetweenFibFunc c'`
for the outer FunctorFrom construction.
-/
def functorBetweenHomNat {c c' : C} (f : c ⟶ c') :
    functorBetweenFibFunc G F data c ⟶
    G.map f ⋙ functorBetweenFibFunc G F data c' where
  app := functorBetweenHomNatApp G F data f
  naturality _ _ φ := functorBetweenHomNat_naturality G F data f φ

/--
Identity coherence for the outer FunctorFrom construction.
-/
theorem functorBetweenHomNat_id (c : C) :
    functorBetweenHomNat G F data (𝟙 c) =
      eqToHom (by simp only [Functor.map_id]; rfl) := by
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
    F.map (eqToHom h).base = 𝟭 (F.obj d) := by
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
    (F.map (baseFib.map f)).map (fibNatApp c x) ≫ fibHomCrossAppH f x =
    fibHomCrossAppG f x ≫ fibNatApp c' ((G.map f).obj x)

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
    (fibFib c).obj ((G'.map f).obj x') ⟶
    (F'.map (baseFib.map f)).obj ((fibFib c').obj x')

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
    (fibFib c).map ((G'.map f).map g) ≫ fibHomCrossApp f y' =
    fibHomCrossApp f x' ≫ (F'.map (baseFib.map f)).map ((fibFib c').map g)

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
    (fibFib c).obj ((G'.map (𝟙 c)).obj x) =
    (F'.map (baseFib.map (𝟙 c))).obj ((fibFib c).obj x)

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
    (F'.map (baseFib.map f)).obj
      ((F'.map (baseFib.map g)).obj ((fibFib c'').obj x'')) =
    (F'.map (baseFib.map (f ≫ g))).obj ((fibFib c'').obj x'')

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
  exact (congrFun (congrArg Functor.obj
    (F'.map_comp (baseFib.map g) (baseFib.map f))) ((fibFib c'').obj x'')).symm

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
    (fibFib c).obj ((G'.map f).obj ((G'.map g).obj x'')) =
    (fibFib c).obj ((G'.map (@CategoryStruct.comp C _ c c' c'' f g)).obj x'')

/--
Derive the G'.map_comp equality from functor laws.
For contravariant functors, G'.map_comp g f = G'.map f ⋙ G'.map g.
-/
lemma functorBetweenContraGMapCompEqProof
    (baseFib : FunctorBetweenContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenContraFibFib G' F' baseFib) :
    FunctorBetweenContraGMapCompEq G' F' baseFib fibFib := by
  intro c c' c'' f g x''
  exact congrArg (fibFib c).obj
    (congrFun (congrArg Functor.obj (G'.map_comp g f)) x'').symm

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
    fibHomCrossApp f ((G'.map g).obj x'') ≫
    (F'.map (baseFib.map f)).map (fibHomCrossApp g x'') ≫
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
    fibHomCrossAppG f x' ≫ (F'.map (baseFib.map f)).map (fibNatApp c' x') =
    fibNatApp c ((G'.map f).obj x') ≫ fibHomCrossAppH f x'

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

end GebLean
