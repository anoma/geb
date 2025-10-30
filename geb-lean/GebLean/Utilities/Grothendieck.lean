import Mathlib.CategoryTheory.Category.Cat.AsSmall
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Grothendieck
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
theorem gcf_comp_fiber.{u, v, u₂, v₂} {C : Type u}
    [CI : Category.{v, u} C] (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂})
    {X Y Z : GrothendieckContra F'} (f : gcHom F' X Y) (g : gcHom F' Y Z) :
  (gcComp F' f g).fiber =
    eqToHom (Grothendieck.comp._proof_1 g f) ≫
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
  fun X => ⟨X.base, X.fiber⟩

def grothendieckContraIsoHomMap
    {X Y : GrothendieckContra F'} :
    gcHom F' X Y →
    (grothendieckContraIsoHomObj X ⟶ grothendieckContraIsoHomObj Y) :=
  fun f => ⟨f.base, f.fiber⟩

theorem grothendieckContraIsoHomMapId
    (X : GrothendieckContra F') :
    grothendieckContraIsoHomMap (gcId F' X) = 𝟙 (grothendieckContraIsoHomObj X) :=
  GrothendieckContra'.ext (F' := F')
    (X := grothendieckContraIsoHomObj X)
    (Y := grothendieckContraIsoHomObj X)
    (grothendieckContraIsoHomMap (gcId F' X))
    (𝟙 (grothendieckContraIsoHomObj X))
    rfl
    (by
      unfold grothendieckContraIsoHomMap grothendieckContraIsoHomObj
      simp
      unfold Cat.opFunctorObj'
      unfold Cat.of
      unfold Cat.str
      unfold Bundled.of
      unfold GrothendieckContraInst'
      simp
      let idfeq := id_fiber_eq (grothendieckContraIsoHomObj X)
      unfold grothendieckContraIsoHomMap grothendieckContraIsoHomObj at idfeq
      simp at idfeq
      let idfeq_op := id_fiber_eq_op (grothendieckContraIsoHomObj X)
      unfold grothendieckContraIsoHomMap grothendieckContraIsoHomObj at idfeq_op
      simp at idfeq_op
      let idfcodeq := (id_fiber_cod_eq <| grothendieckContraIsoHomObj X).symm
      unfold grothendieckContraIsoHomMap grothendieckContraIsoHomObj at idfcodeq
      simp at idfcodeq
      let idfeq_rev := id_fiber_eq_rev <| grothendieckContraIsoHomObj X
      unfold grothendieckContraIsoHomMap grothendieckContraIsoHomObj at idfeq_rev
      simp at idfeq_rev
      sorry
      )

theorem grothendieckContraIsoHomMapComp
    {X Y Z : GrothendieckContra F'}
    (f : gcHom F' X Y)
    (g : gcHom F' Y Z) :
    grothendieckContraIsoHomMap (gcComp F' f g) =
    grothendieckContraIsoHomMap f ≫ grothendieckContraIsoHomMap g := by
  cases f
  cases g
  simp [grothendieckContraIsoHomMap]
  sorry

def grothendieckContraIsoHom :
    GrothendieckContraCat F' ⥤ GrothendieckContra' F' where
  obj := grothendieckContraIsoHomObj
  map := grothendieckContraIsoHomMap
  map_id := grothendieckContraIsoHomMapId
  map_comp := grothendieckContraIsoHomMapComp

def grothendieckContraIsoInvObj :
    GrothendieckContra' F' → GrothendieckContra F' :=
  fun X => ⟨X.base, X.fiber⟩

def grothendieckContraIsoInvMap
    {X Y : GrothendieckContra' F'} :
    (X ⟶ Y) → gcHom F' (grothendieckContraIsoInvObj X) (grothendieckContraIsoInvObj Y) :=
  fun f => ⟨f.base, f.fiber⟩

theorem grothendieckContraIsoInvMapId
    (X : GrothendieckContra' F') :
    grothendieckContraIsoInvMap (𝟙 X) = gcId F' (grothendieckContraIsoInvObj X) := by
  simp [grothendieckContraIsoInvMap, grothendieckContraIsoInvObj]
  sorry

theorem grothendieckContraIsoInvMapComp
    {X Y Z : GrothendieckContra' F'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    grothendieckContraIsoInvMap (f ≫ g) =
    gcComp F' (grothendieckContraIsoInvMap f) (grothendieckContraIsoInvMap g) := by
  cases f
  cases g
  simp [grothendieckContraIsoInvObj,grothendieckContraIsoInvMap, Category.toCategoryStruct]
  sorry

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
@[simps]
def forget : GrothendieckContra' F' ⥤ C where
  obj X := X.base
  map f := f.base

end

section Functoriality

variable {F' G' H' : Cᵒᵖ' ⥤ Cat}

/--
A natural transformation `α : F' ⟶ G'` induces a functor between the corresponding
contravariant Grothendieck constructions.
-/
@[simps!]
def map (α : F' ⟶ G') : GrothendieckContra' F' ⥤ GrothendieckContra' G' where
  obj X := ⟨X.base, (α.app X.base).obj X.fiber⟩
  map {X Y} f := ⟨f.base, (α.app X.base).map f.fiber ≫
    (eqToHom (α.naturality f.base)).app Y.fiber⟩
  map_id X := by
    refine ext _ _ ?_ ?_
    · rfl
    · dsimp [CategoryStruct.id]
      simp only [Cat.eqToHom_app, eqToHom_map, eqToHom_trans]
      rw [Category.comp_id]
  map_comp {X Y Z} f g := by
    refine ext _ _ ?_ ?_
    · dsimp
      rfl
    · dsimp [comp, CategoryStruct.comp]
      simp only [Functor.map_comp, Category.assoc]
      simp only [Cat.eqToHom_app, eqToHom_map, eqToHom_trans, Category.comp_id]
      congr 1
      simp only [← Cat.comp_map]
      rw [Functor.congr_hom (α.naturality f.base) g.fiber]
      simp only [Category.assoc, eqToHom_trans]

@[simp]
theorem map_obj (α : F' ⟶ G') (X : GrothendieckContra' F') :
    (map α).obj X = ⟨X.base, (α.app X.base).obj X.fiber⟩ := rfl

@[simp]
theorem map_map (α : F' ⟶ G') {X Y : GrothendieckContra' F'} (f : X ⟶ Y) :
    (map α).map f = ⟨f.base, (α.app X.base).map f.fiber ≫
      (eqToHom (α.naturality f.base)).app Y.fiber⟩ := rfl

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
    simp only [map_map, map_obj, NatTrans.comp_app, Cat.comp_obj, Cat.comp_map,
      eqToHom_refl, Functor.comp_map, Functor.map_comp, Category.comp_id, Category.id_comp]
    fapply ext
    · rfl
    · simp

def mapCompIso (α : F' ⟶ G') (β : G' ⟶ H') :
    map (α ≫ β) ≅ map α ⋙ map β :=
  eqToIso (map_comp_eq α β)

section UniverseScaling

variable {F' G' : Cᵒᵖ' ⥤ Cat.{v, u}}


/--
Proof that mapping identity through compAsSmallFunctorEquivalenceInverse preserves identity.
-/
lemma compAsSmallFunctorEquivalenceInverse_map_id
    (X : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w})) :
    let idX : X ⟶ X := 𝟙 X
    (⟨idX.base, AsSmall.down.map idX.fiber⟩ :
      (⟨X.base, AsSmall.down.obj X.fiber⟩ : GrothendieckContra' F') ⟶
      (⟨X.base, AsSmall.down.obj X.fiber⟩ : GrothendieckContra' F')) =
    𝟙 (⟨X.base, AsSmall.down.obj X.fiber⟩ : GrothendieckContra' F') := by
  apply GrothendieckContra'.ext
  · simp [CategoryStruct.id]
  · simp [CategoryStruct.id]

/--
Proof that mapping composition through compAsSmallFunctorEquivalenceInverse preserves composition.
-/
lemma compAsSmallFunctorEquivalenceInverse_map_comp
    {X Y Z : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w})}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (⟨(f ≫ g).base, AsSmall.down.map (f ≫ g).fiber⟩ :
      (⟨X.base, AsSmall.down.obj X.fiber⟩ : GrothendieckContra' F') ⟶
      (⟨Z.base, AsSmall.down.obj Z.fiber⟩ : GrothendieckContra' F')) =
    ((⟨f.base, AsSmall.down.map f.fiber⟩ :
      (⟨X.base, AsSmall.down.obj X.fiber⟩ : GrothendieckContra' F') ⟶
      (⟨Y.base, AsSmall.down.obj Y.fiber⟩ : GrothendieckContra' F')) ≫
    (⟨g.base, AsSmall.down.map g.fiber⟩ :
      (⟨Y.base, AsSmall.down.obj Y.fiber⟩ : GrothendieckContra' F') ⟶
      (⟨Z.base, AsSmall.down.obj Z.fiber⟩ : GrothendieckContra' F')) :
      (⟨X.base, AsSmall.down.obj X.fiber⟩ : GrothendieckContra' F') ⟶
      (⟨Z.base, AsSmall.down.obj Z.fiber⟩ : GrothendieckContra' F')) := by
  apply GrothendieckContra'.ext <;> simp [CategoryStruct.comp, down_comp]

/--
Inverse of the equivalence relating Grothendieck constructions across universes.
-/
@[simps]
def compAsSmallFunctorEquivalenceInverse :
    GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}) ⥤ GrothendieckContra' F' where
  obj X := ⟨X.base, AsSmall.down.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.down.map f.fiber⟩
  map_id := compAsSmallFunctorEquivalenceInverse_map_id
  map_comp := compAsSmallFunctorEquivalenceInverse_map_comp

/--
Proof that mapping identity through compAsSmallFunctorEquivalenceFunctor preserves identity.
-/
lemma compAsSmallFunctorEquivalenceFunctor_map_id (X : GrothendieckContra' F') :
    let idX : X ⟶ X := 𝟙 X
    (⟨idX.base, AsSmall.up.map idX.fiber⟩ :
      (⟨X.base, AsSmall.up.obj X.fiber⟩ : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w})) ⟶
      (⟨X.base, AsSmall.up.obj X.fiber⟩ : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}))) =
    𝟙 (⟨X.base, AsSmall.up.obj X.fiber⟩ : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w})) := by
  apply GrothendieckContra'.ext
  · simp [CategoryStruct.id]
  · simp [CategoryStruct.id]

/--
Proof that mapping composition through compAsSmallFunctorEquivalenceFunctor preserves composition.
-/
lemma compAsSmallFunctorEquivalenceFunctor_map_comp
    {X Y Z : GrothendieckContra' F'} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (⟨(f ≫ g).base, AsSmall.up.map (f ≫ g).fiber⟩ :
      (⟨X.base, AsSmall.up.obj X.fiber⟩ : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w})) ⟶
      (⟨Z.base, AsSmall.up.obj Z.fiber⟩ : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}))) =
    ((⟨f.base, AsSmall.up.map f.fiber⟩ :
      (⟨X.base, AsSmall.up.obj X.fiber⟩ : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w})) ⟶
      (⟨Y.base, AsSmall.up.obj Y.fiber⟩ : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}))) ≫
    (⟨g.base, AsSmall.up.map g.fiber⟩ :
      (⟨Y.base, AsSmall.up.obj Y.fiber⟩ : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w})) ⟶
      (⟨Z.base, AsSmall.up.obj Z.fiber⟩ : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}))) :
      (⟨X.base, AsSmall.up.obj X.fiber⟩ : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w})) ⟶
      (⟨Z.base, AsSmall.up.obj Z.fiber⟩ : GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}))) := by
  apply GrothendieckContra'.ext <;> simp [CategoryStruct.comp, Functor.map_comp]
  apply ULift.ext
  simp [down_comp, AsSmall.up_map_down]

/--
The functor part of the equivalence relating Grothendieck constructions
across universes.
-/
@[simps!]
def compAsSmallFunctorEquivalenceFunctor :
    GrothendieckContra' F' ⥤ GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}) where
  obj X := ⟨X.base, AsSmall.up.obj X.fiber⟩
  map f := ⟨f.base, AsSmall.up.map f.fiber⟩
  map_id := compAsSmallFunctorEquivalenceFunctor_map_id
  map_comp := compAsSmallFunctorEquivalenceFunctor_map_comp

/--
Equivalence relating Grothendieck constructions across universes, showing that
the construction respects universe scaling.
-/
def compAsSmallFunctorEquivalence :
    GrothendieckContra' F' ≌ GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}) where
  functor := compAsSmallFunctorEquivalenceFunctor
  inverse := compAsSmallFunctorEquivalenceInverse
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/--
Natural isomorphism for whiskering with universe-scaling functor.
-/
def mapWhiskerRightAsSmallFunctor (α : F' ⟶ G') :
    map (Functor.whiskerRight α Cat.asSmallFunctor.{w}) ≅
    compAsSmallFunctorEquivalenceInverse (F' := F') ⋙ map α ⋙
      compAsSmallFunctorEquivalenceFunctor (F' := G') :=
  NatIso.ofComponents
    (fun _ => Iso.refl _)
    (fun _ => by
      apply GrothendieckContra'.ext
      · simp [compAsSmallFunctorEquivalenceInverse, compAsSmallFunctorEquivalenceFunctor]
      · simp [compAsSmallFunctorEquivalenceInverse, compAsSmallFunctorEquivalenceFunctor])

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
    (fun X => Iso.refl _)
    (fun f => by
      refine ext _ _ ?_ ?_
      · simp; rfl
      · simp; apply Subsingleton.elim)
  counitIso := NatIso.ofComponents
    (fun p => Iso.refl _)
    (fun f => by
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

/--
A functor `G : D ⥤ C` induces a functor between the contravariant Grothendieck
constructions.

Applying a functor `G : D ⥤ C` to the base of the Grothendieck construction
induces a functor `GrothendieckContra' (functorOp'Obj G ⋙ F') ⥤ GrothendieckContra' F'`.
-/
@[simps!]
def pre (G : D ⥤ C) : GrothendieckContra' (functorOp'Obj G ⋙ F') ⥤
    GrothendieckContra' F' where
  obj X := ⟨G.obj X.base, X.fiber⟩
  map f := ⟨G.map f.base, f.fiber⟩
  map_id X := ext _ _ (G.map_id _) (by simp [CategoryStruct.id])
  map_comp f g := ext _ _ (G.map_comp _ _) (by
    simp [comp, CategoryStruct.comp])

/--
The functor `pre` applied to the identity functor is the identity.
-/
@[simp]
theorem pre_id : pre F' (𝟭 C) = 𝟭 (GrothendieckContra' F') :=
  rfl

/--
Natural isomorphism between `pre` applied to naturally isomorphic functors.

An isomorphism between functors `α : G ≅ H` induces an isomorphism between
`pre G` and `pre H`, up to composition with the `map` induced by whiskering.
-/
def preNatIso {G H : D ⥤ C} (α : G ≅ H) :
    pre F' G ≅ map (Functor.whiskerRight (functorOp'.map α.inv) F') ⋙
      (pre F' H) :=
  NatIso.ofComponents
    (fun X => (transportIso ⟨G.obj X.base, X.fiber⟩ (α.app X.base)).symm)
    (fun f => by sorry)

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
    GrothendieckContra' F' where
  functor := pre F' G.functor
  inverse := preInv F' G
  unitIso := sorry
  counitIso := preNatIso F' G.counitIso.symm |>.symm
  functor_unitIso_comp := sorry

variable {F'} in
/--
Conjugation of `map` by `preEquivalence`.

Left-whiskering `α` by `functorOp'Obj G.functor` and then taking the Grothendieck
construction is, up to isomorphism, the same as taking the Grothendieck construction
of `α` and using the equivalences from `preEquivalence` to match the expected type.
-/
def mapWhiskerLeftIsoConjPreMap {G' : Cᵒᵖ' ⥤ Cat.{w, u₁}} (G : D ≌ C) (α : F' ⟶ G') :
    map (Functor.whiskerLeft (functorOp'Obj G.functor) α) ≅
      (preEquivalence F' G).functor ⋙ map α ⋙ (preEquivalence G' G).inverse :=
  sorry

end PreComp


section FunctorFrom

variable {F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}}
variable {T : Type u₁} [Category.{v₁} T]

/--
The fiber inclusion functor from `F'.obj c` to `GrothendieckContra' F'`.
-/
def ι (c : C) : F'.obj c ⥤ GrothendieckContra' F' where
  obj f := ⟨c, f⟩
  map φ := ⟨𝟙 c, eqToHom (Functor.congr_obj (F'.map_id c).symm _) ≫
    (F'.map (𝟙 c)).map φ⟩
  map_id f := by
    fapply ext
    · rfl
    · sorry
  map_comp φ ψ := sorry

/--
The fiber inclusion functor is faithful.
-/
instance faithful_ι (c : C) : (ι c : F'.obj c ⥤ GrothendieckContra' F').Faithful where
  map_injective f := sorry

/--
Natural transformation induced by a morphism in the base category.
-/
@[simps]
def ιNatTrans {c d : C} (f : c ⟶ d) : F'.map f ⋙ ι c ⟶ ι d where
  app := fun X => ⟨f, 𝟙 _⟩
  naturality := sorry

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
    sorry

/--
The fiber inclusion composed with `functorFrom` recovers the original fiber functor.
-/
theorem ιCompFunctorFrom (c : C) :
    ι c ⋙ functorFrom fib hom hom_id = fib c := by
  sorry

/--
Interaction between fiber inclusion and `map`.
-/
theorem ιCompMap {G' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}} (α : F' ⟶ G') (c : C) :
    ι c ⋙ map α = (α.app c) ⋙ ι c :=
  sorry

end FunctorFrom

end GrothendieckContra'

end GebLean
