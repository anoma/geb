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
  grothendieckContraIsoInv (F' := G') ⋙ F_cov ⋙ grothendieckContraIsoHom (F' := H')

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

/--
Helper function that wraps a mathlib Grothendieck function that takes a natural
transformation.

Takes a natural transformation `α` between our contravariant functors, applies
`Cat.postCompOpFunctor'.map` to convert it to mathlib's format, passes it to a mathlib
Grothendieck function, and wraps the result in `Functor.op'`.
-/
abbrev transferCovFunctorOnMap {E : Type uₑ} [Category.{vₑ} E]
    {G' H' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}}
    (α : G' ⟶ H')
    (mathlibFunc : (Cat.postCompOpFunctor'.obj G' ⟶ Cat.postCompOpFunctor'.obj H') →
                   (Grothendieck (Cat.postCompOpFunctor'.obj G') ⥤
                    Grothendieck (Cat.postCompOpFunctor'.obj H'))) :
    GrothendieckContraCat G' ⥤ GrothendieckContraCat H' :=
  Functor.op' (mathlibFunc (Cat.postCompOpFunctor'.map α))

/--
Computation lemma: the object function of `transferCovFunctorOnMap` in terms of the
mathlib function's object function.
-/
theorem transferCovFunctorOnMap_obj {E : Type uₑ} [Category.{vₑ} E]
    {G' H' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}}
    (α : G' ⟶ H')
    (mathlibFunc : (Cat.postCompOpFunctor'.obj G' ⟶ Cat.postCompOpFunctor'.obj H') →
                   (Grothendieck (Cat.postCompOpFunctor'.obj G') ⥤
                    Grothendieck (Cat.postCompOpFunctor'.obj H')))
    (X : GrothendieckContra G') :
    (transferCovFunctorOnMap α mathlibFunc).obj X =
      (mathlibFunc (Cat.postCompOpFunctor'.map α)).obj X := rfl

/--
Computation lemma: the morphism function of `transferCovFunctorOnMap` in terms of the
mathlib function's morphism function.
-/
theorem transferCovFunctorOnMap_map {E : Type uₑ} [Category.{vₑ} E]
    {G' H' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}}
    (α : G' ⟶ H')
    (mathlibFunc : (Cat.postCompOpFunctor'.obj G' ⟶ Cat.postCompOpFunctor'.obj H') →
                   (Grothendieck (Cat.postCompOpFunctor'.obj G') ⥤
                    Grothendieck (Cat.postCompOpFunctor'.obj H')))
    {X Y : GrothendieckContra G'} (f : gcHom G' X Y) :
    (transferCovFunctorOnMap α mathlibFunc).map f =
      (mathlibFunc (Cat.postCompOpFunctor'.map α)).map f := rfl

/--
Specialized computation for `transferCovFunctorOnMap` when used with `Grothendieck.map`.
This computes all the way down to the components of `α`, removing all the `Cat.postCompOpFunctor'`
wrappers.
-/
theorem transferCovFunctorOnMap_grothendieckMap_obj {E : Type uₑ} [Category.{vₑ} E]
    {G' H' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}}
    (α : G' ⟶ H')
    (X : GrothendieckContra G') :
    (transferCovFunctorOnMap α Grothendieck.map).obj X =
      ⟨X.base, (α.app X.base).obj X.fiber⟩ := by
  rw [transferCovFunctorOnMap_obj]
  simp [Functor.op', Grothendieck.map, Cat.postCompOpFunctor']

/--
Specialized computation for `transferCovFunctorOnMap` when used with `Grothendieck.map`.
This computes all the way down to the components of `α`, removing all the `Cat.postCompOpFunctor'`
wrappers.

Note: The morphism still contains `(Cat.postCompOpFunctor'.map α).naturality` which is the
naturality of `whiskerRight α opFunctor'`. This can be further expanded if needed, but is
left in this form as it's a standard naturality condition.
-/
theorem transferCovFunctorOnMap_grothendieckMap_map {E : Type uₑ} [Category.{vₑ} E]
    {G' H' : Eᵒᵖ' ⥤ Cat.{v₃, u₃}}
    (α : G' ⟶ H')
    {X Y : GrothendieckContra G'} (f : gcHom G' X Y) :
    (transferCovFunctorOnMap α Grothendieck.map).map f =
      ⟨f.base,
        (eqToHom (Eq.symm ((Cat.postCompOpFunctor'.map α).naturality f.base))).app Y.fiber ≫
        (Functor.op' (α.app X.base)).map f.fiber⟩ := by
  rw [transferCovFunctorOnMap_map]
  simp [Functor.op', Grothendieck.map, Cat.postCompOpFunctor']

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

/--
Construct an isomorphism in a contravariant Grothendieck construction from
isomorphisms in its base and fiber.
-/
@[simps!]
def isoMk {X Y : GrothendieckContra' F'} (e₁ : X.base ≅ Y.base)
    (e₂ : X.fiber ≅ (F'.map e₁.hom).obj Y.fiber) :
    X ≅ Y where
  hom := ⟨e₁.hom, e₂.hom⟩
  inv := ⟨e₁.inv, eqToHom (map_iso_comp_obj_eq e₁ Y.fiber) ≫
    (F'.map e₁.inv).map e₂.inv⟩
  hom_inv_id := ext _ _ (by
      change (comp (Hom.mk e₁.hom e₂.hom)
        (Hom.mk e₁.inv (eqToHom (map_iso_comp_obj_eq e₁ Y.fiber) ≫
        (F'.map e₁.inv).map e₂.inv))).base = (id X).base
      rw [comp_base, id_base]
      exact e₁.hom_inv_id) (by
      let e₁op : @Iso Cᵒᵖ' _ X.base Y.base := {
        hom := e₁.inv
        inv := e₁.hom
        hom_inv_id := e₁.hom_inv_id
        inv_hom_id := e₁.inv_hom_id
      }
      have h := Functor.congr_hom (F'.mapIso e₁op).hom_inv_id e₂.inv
      dsimp at h
      change (comp (Hom.mk e₁.hom e₂.hom)
        (Hom.mk e₁.inv (eqToHom (map_iso_comp_obj_eq e₁ Y.fiber) ≫
        (F'.map e₁.inv).map e₂.inv))).fiber ≫ eqToHom _ = (id X).fiber
      rw [comp_fiber, id_fiber]
      simp only [Functor.map_comp, eqToHom_map]
      rw [h]
      simp)
  inv_hom_id := ext _ _ (by
      change (comp (Hom.mk e₁.inv (eqToHom (map_iso_comp_obj_eq e₁ Y.fiber) ≫
        (F'.map e₁.inv).map e₂.inv)) (Hom.mk e₁.hom e₂.hom)).base = (id Y).base
      rw [comp_base, id_base]
      exact e₁.inv_hom_id) (by
      change (comp (Hom.mk e₁.inv (eqToHom (map_iso_comp_obj_eq e₁ Y.fiber) ≫
        (F'.map e₁.inv).map e₂.inv)) (Hom.mk e₁.hom e₂.hom)).fiber ≫
        eqToHom _ = (id Y).fiber
      rw [comp_fiber, id_fiber]
      simp)

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
  gcDomFuncToGcContra'
    ((Functor.const (Cᵒᵖ' ⥤ Cat.{v₂, u₂})).obj (Cat.of C))
    Grothendieck.forget
    F'

end

section Functoriality

variable {F' G' H' : Cᵒᵖ' ⥤ Cat}

@[simps!]
def map_cov (α : F' ⟶ G') : GrothendieckContraCat F' ⥤ GrothendieckContraCat G' :=
    transferCovFunctorOnMap α Grothendieck.map

theorem map_cov_obj (α : F' ⟶ G') (X : GrothendieckContra F') :
    (map_cov α).obj X = ⟨X.base, (α.app X.base).obj X.fiber⟩ := by
  unfold map_cov
  simp only [Functor.op']
  rw [Grothendieck.map_obj]
  simp only [Cat.postCompOpFunctor']
  rfl

theorem map_cov_map (α : F' ⟶ G') {X Y : GrothendieckContra F'} (f : gcHom F' X Y) :
    (map_cov α).map f = ⟨f.base,
      (eqToHom (Eq.symm ((Cat.postCompOpFunctor'.map α).naturality f.base))).app Y.fiber ≫
      (Functor.op' (α.app X.base)).map f.fiber⟩ := by
  unfold map_cov
  simp only [Functor.op']
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
    GrothendieckContraCat (F' ⋙ Cat.asSmallFunctor.{w}) ⥤ GrothendieckContraCat F' :=
  Functor.op'
    (Grothendieck.compAsSmallFunctorEquivalence (Cat.postCompOpFunctor'.obj F')).functor

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
    GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}) ⥤ GrothendieckContra' F' :=
  transferFromCov compAsSmallFunctorEquivalenceFunctor_cov

theorem compAsSmallFunctorEquivalenceFunctor_obj
    (X : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w})) :
    (compAsSmallFunctorEquivalenceFunctor (F' := F')).obj X =
      ⟨X.base, AsSmall.down.obj X.fiber⟩ := by
  unfold compAsSmallFunctorEquivalenceFunctor
  simp only [transferFromCov_obj, transferredObj]
  rw [compAsSmallFunctorEquivalenceFunctor_cov_obj]
  simp

theorem compAsSmallFunctorEquivalenceFunctor_map
    {X Y : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w})} (f : X ⟶ Y) :
    (compAsSmallFunctorEquivalenceFunctor (F' := F')).map f =
      ⟨f.base, AsSmall.down.map f.fiber⟩ := by
  unfold compAsSmallFunctorEquivalenceFunctor
  simp only [transferFromCov_map, transferredMap]
  rw [compAsSmallFunctorEquivalenceFunctor_cov_map]
  simp

def compAsSmallFunctorEquivalenceInverse_cov :
    GrothendieckContraCat F' ⥤ GrothendieckContraCat (F' ⋙ Cat.asSmallFunctor.{w}) :=
  Functor.op'
    (Grothendieck.compAsSmallFunctorEquivalence (Cat.postCompOpFunctor'.obj F')).inverse

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

theorem compAsSmallFunctorEquivalenceInverse_obj (X : GrothendieckContra' F') :
    (compAsSmallFunctorEquivalenceInverse (F' := F')).obj X =
      ⟨X.base, AsSmall.up.obj X.fiber⟩ := by
  unfold compAsSmallFunctorEquivalenceInverse
  simp only [transferFromCov_obj, transferredObj]
  rw [compAsSmallFunctorEquivalenceInverse_cov_obj]

-- Note: This lemma has type class synthesis issues and is omitted
-- theorem compAsSmallFunctorEquivalenceInverse_map
--     {X Y : GrothendieckContra' F'} (f : X ⟶ Y) :
--     (compAsSmallFunctorEquivalenceInverse (F' := F')).map f =
--       ⟨f.base, AsSmall.up.map f.fiber⟩ := by
--   unfold compAsSmallFunctorEquivalenceInverse
--   simp only [transferFromCov_map, transferredMap]
--   rw [compAsSmallFunctorEquivalenceInverse_cov_map]

def compAsSmallFunctorEquivalence :
    GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}) ≌ GrothendieckContra' F' where
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
        rw [← op'_comp, ← op'_comp]
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
        rw [op'_comp, op'_comp] at iso_transported
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

end FunctorFrom

end GrothendieckContra'

end GebLean
