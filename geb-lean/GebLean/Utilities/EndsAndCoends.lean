import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Types.Basic
import GebLean.Utilities.PowersAndCopowers

/-!
# Explicit Ends and Coends in Type

Mathlib's `end_`, `coend`, `endFunctor`, `coendFunctor` are not
computable.  This module provides computable versions for
`Type v` by giving explicit constructions as subtypes (ends) and
quotients (coends).

## Main definitions

* `typeEnd F` -- The end of `F : Jᵒᵖ ⥤ J ⥤ Type v`, given as the
  subtype of compatible families satisfying the wedge condition.
* `typeCoend F` -- The coend of `F : Jᵒᵖ ⥤ J ⥤ Type v`, given as
  a quotient of the sigma type by the cowedge relation.
* `typeEndFunctor` -- Computable end functor `(Jᵒᵖ ⥤ J ⥤ Type v) ⥤ Type v`.
* `typeCoendFunctor` -- Computable coend functor.
-/

namespace GebLean

open CategoryTheory
open CategoryTheory.Limits

universe v u

variable {J : Type u} [Category.{v} J]

/-- The end of a profunctor `F : Jᵒᵖ ⥤ J ⥤ Type v` in `Type v`,
constructed as the subtype of families `(j : J) → (F.obj (op j)).obj j`
satisfying the wedge condition: for every morphism `f : i ⟶ j`,
`(F.obj (op i)).map f (x i) = (F.map f.op).app j (x j)`. -/
def typeEnd (F : Jᵒᵖ ⥤ J ⥤ Type v) : Type (max u v) :=
  { x : (j : J) → (F.obj (Opposite.op j)).obj j //
    ∀ {i j : J} (f : i ⟶ j),
      (F.obj (Opposite.op i)).map f (x i) =
        (F.map f.op).app j (x j) }

/-- Projection from `typeEnd F` to the component at `j`. -/
def typeEnd.proj (F : Jᵒᵖ ⥤ J ⥤ Type v) (j : J) :
    typeEnd F → (F.obj (Opposite.op j)).obj j :=
  fun x => x.val j

section TypeEndWedge

variable {J : Type v} [Category.{v} J]

/-- The wedge with apex `typeEnd F` in `Type v`.
The projections are `typeEnd.proj` and the wedge condition
follows from the subtype predicate of `typeEnd`. -/
def typeEndWedge (F : Jᵒᵖ ⥤ J ⥤ Type v) : Wedge F :=
  Wedge.mk (typeEnd F) (fun j => typeEnd.proj F j)
    (fun {i j} f => by
      ext x
      exact x.property f)

/-- `typeEndWedge F` is a limit wedge (i.e., the end
of `F` in `Type v`).  Given any other wedge `s`, the
unique morphism `s.pt → typeEnd F` packages the wedge
projections into a compatible family. -/
def typeEndWedge_isLimit (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    IsLimit (typeEndWedge F) :=
  Multifork.IsLimit.mk (typeEndWedge F)
    (fun s => fun x => ⟨fun j => s.ι j x,
      fun {_ _} f =>
        congr_fun (Wedge.condition s f) x⟩)
    (fun _ _ => rfl)
    (fun _ _ hm => funext (fun x =>
      Subtype.ext (funext (fun j =>
        congr_fun (hm j) x))))

/-- `typeEndWedge F` is a terminal wedge. -/
def typeEndWedge_isTerminal (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    IsTerminal (typeEndWedge F) :=
  (Cone.isLimitEquivIsTerminal _)
    (typeEndWedge_isLimit F)

end TypeEndWedge

/-!
## Coends in Type
-/

section TypeCoend

variable {J : Type u} [Category.{v} J]

/-- The cowedge relation on `Σ (j : J), (F.obj (op j)).obj j`.
For a morphism `f : i ⟶ j` and element
`x : (F.obj (op j)).obj i`, identifies
`⟨i, (F.map f.op).app i x⟩` with
`⟨j, (F.obj (op j)).map f x⟩`. -/
inductive typeCoendRel (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    (Σ (j : J), (F.obj (Opposite.op j)).obj j) →
    (Σ (j : J), (F.obj (Opposite.op j)).obj j) → Prop
  | intro {i j : J} (f : i ⟶ j)
      (x : (F.obj (Opposite.op j)).obj i) :
      typeCoendRel F
        ⟨i, (F.map f.op).app i x⟩
        ⟨j, (F.obj (Opposite.op j)).map f x⟩

/-- The coend of a profunctor `F : Jᵒᵖ ⥤ J ⥤ Type v` in `Type`,
constructed as a quotient of `Σ (j : J), (F.obj (op j)).obj j`
by the cowedge relation `typeCoendRel`. -/
def typeCoend (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    Type (max u v) :=
  Quot (typeCoendRel F)

/-- Injection from the `j`-th component into `typeCoend F`. -/
def typeCoend.inj (F : Jᵒᵖ ⥤ J ⥤ Type v) (j : J) :
    (F.obj (Opposite.op j)).obj j → typeCoend F :=
  fun x => Quot.mk _ ⟨j, x⟩

end TypeCoend

section TypeCoendCowedge

variable {J : Type v} [Category.{v} J]

/-- The cowedge with apex `typeCoend F` in `Type v`.
The injections are `typeCoend.inj` and the cowedge condition
follows from `Quot.sound` applied to `typeCoendRel`. -/
def typeCoendCowedge (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    Cowedge F :=
  Cowedge.mk (typeCoend F) (fun j => typeCoend.inj F j)
    (fun {i j} f => by
      ext x
      exact Quot.sound (typeCoendRel.intro f x))

/-- `typeCoendCowedge F` is a colimit cowedge (i.e., the
coend of `F` in `Type v`). -/
def typeCoendCowedge_isColimit
    (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    IsColimit (typeCoendCowedge F) :=
  Multicofork.IsColimit.mk (typeCoendCowedge F)
    (fun s => Quot.lift (fun ⟨j, x⟩ => s.π j x)
      (fun _ _ r => by
        cases r with
        | intro f x =>
          exact congr_fun
            (Cowedge.condition s f) x))
    (fun _ _ => rfl)
    (fun _ m hm => by
      ext ⟨j, x⟩
      exact congr_fun (hm j) x)

/-- `typeCoendCowedge F` is an initial cowedge. -/
def typeCoendCowedge_isInitial
    (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    IsInitial (typeCoendCowedge F) :=
  (Cocone.isColimitEquivIsInitial _)
    (typeCoendCowedge_isColimit F)

end TypeCoendCowedge

/-!
## End and Coend Functors
-/

section Functors

variable (J : Type v) [Category.{v} J]

/-- The action of a natural transformation `α : F ⟶ G` on
`typeEnd`: maps a compatible family for `F` to one for `G`
by applying `α` componentwise. -/
def typeEnd.map {F G : Jᵒᵖ ⥤ J ⥤ Type v} (α : F ⟶ G) :
    typeEnd F → typeEnd G :=
  fun ⟨x, hx⟩ => ⟨fun j => (α.app (Opposite.op j)).app j (x j),
    fun {i j} f => by
      have h1 := congr_fun
        ((α.app (Opposite.op i)).naturality f) (x i)
      simp only [types_comp_apply] at h1
      rw [hx f] at h1
      have h2 := congr_fun
        (congr_app (α.naturality f.op) j) (x j)
      simp only [NatTrans.comp_app,
        types_comp_apply] at h2
      exact h1.symm.trans h2⟩

/-- The computable end functor
`(Jᵒᵖ ⥤ J ⥤ Type v) ⥤ Type v`. -/
def typeEndFunctor : (Jᵒᵖ ⥤ J ⥤ Type v) ⥤ Type v where
  obj := typeEnd
  map := typeEnd.map J
  map_id := fun _ => by
    ext ⟨_, _⟩
    rfl
  map_comp := fun _ _ => by
    ext ⟨_, _⟩
    rfl

/-- The action of a natural transformation `α : F ⟶ G` on
`typeCoend`: maps the quotient for `F` to the quotient for
`G` by applying `α` componentwise on representatives. -/
def typeCoend.map {F G : Jᵒᵖ ⥤ J ⥤ Type v}
    (α : F ⟶ G) : typeCoend F → typeCoend G :=
  Quot.map
    (fun ⟨j, x⟩ =>
      ⟨j, (α.app (Opposite.op j)).app j x⟩)
    (fun _ _ r => by
      cases r with
      | @intro i j f x =>
        dsimp only
        have h1 := congr_fun
          (congr_app (α.naturality f.op) i) x
        simp only [NatTrans.comp_app,
          types_comp_apply] at h1
        have h2 := congr_fun
          ((α.app (Opposite.op j)).naturality f) x
        simp only [types_comp_apply] at h2
        rw [h1, h2]
        exact typeCoendRel.intro f
          ((α.app (Opposite.op j)).app i x))

/-- The computable coend functor
`(Jᵒᵖ ⥤ J ⥤ Type v) ⥤ Type v`. -/
def typeCoendFunctor :
    (Jᵒᵖ ⥤ J ⥤ Type v) ⥤ Type v where
  obj := typeCoend
  map := typeCoend.map J
  map_id := fun _ => by
    ext ⟨_, _⟩
    rfl
  map_comp := fun _ _ => by
    ext ⟨_, _⟩
    rfl

end Functors

/-!
## Adjunctions for End and Coend

The end functor `typeEndFunctor` is right adjoint to the
functor sending `Y : Type v` to the profunctor
`(a, b) ↦ (a.unop ⟶ b) × Y`.

Dually, the coend functor `typeCoendFunctor` is left adjoint
to the functor sending `Y : Type v` to the profunctor
`(a, b) ↦ (b ⟶ a.unop) → Y`.
-/

section EndAdjunction

variable (J : Type v) [Category.{v} J]

/-- For fixed `Y : Type v` and `a : Jᵒᵖ`, the functor
`J ⥤ Type v` sending `b ↦ (a.unop ⟶ b) × Y`. -/
def typeEndLAdj.innerObj (Y : Type v)
    (a : Jᵒᵖ) : J ⥤ Type v where
  obj b := (a.unop ⟶ b) × Y
  map g := fun ⟨h, y⟩ => ⟨h ≫ g, y⟩
  map_id := by
    intro X; ext ⟨h, y⟩ : 1
    exact Prod.ext (Category.comp_id h) rfl
  map_comp := by
    intro _ _ _ f g; ext ⟨h, y⟩ : 1
    exact Prod.ext
      (Category.assoc h f g).symm rfl

/-- For fixed `Y : Type v`, the profunctor
`Jᵒᵖ ⥤ J ⥤ Type v` sending `(a, b)` to
`(a.unop ⟶ b) × Y`. -/
def typeEndLAdj.obj (Y : Type v) :
    Jᵒᵖ ⥤ J ⥤ Type v where
  obj a := typeEndLAdj.innerObj J Y a
  map f :=
    { app := fun _ ⟨h, y⟩ => ⟨f.unop ≫ h, y⟩
      naturality := by
        intro _ _ g; ext ⟨h, y⟩
        simp only [types_comp_apply]
        exact Prod.ext
          (Category.assoc _ h g).symm rfl
    }
  map_id := by
    intro a; ext b ⟨h, y⟩
    exact Prod.ext (Category.id_comp h) rfl
  map_comp := by
    intro _ _ _ f₁ f₂; ext b ⟨h, y⟩
    simp only [NatTrans.comp_app,
      types_comp_apply]
    exact Prod.ext
      (Category.assoc _ _ h) rfl

/-- The nat trans induced by `φ : Y → Z` between
profunctors `typeEndLAdj.obj Y ⟶ typeEndLAdj.obj Z`,
applying `φ` to the second component. -/
def typeEndLAdj.mapNatTrans
    {Y Z : Type v} (φ : Y → Z) :
    typeEndLAdj.obj J Y ⟶ typeEndLAdj.obj J Z where
  app a :=
    { app := fun _ ⟨h, y⟩ => ⟨h, φ y⟩
      naturality := by intros; ext ⟨_, _⟩; rfl }
  naturality := by intros; ext _ ⟨_, _⟩; rfl

/-- The functor `Type v ⥤ (Jᵒᵖ ⥤ J ⥤ Type v)`
sending `Y` to the profunctor
`(a, b) ↦ (a.unop ⟶ b) × Y`. This is the left
adjoint of `typeEndFunctor`. -/
def typeEndLAdjFunctor :
    Type v ⥤ (Jᵒᵖ ⥤ J ⥤ Type v) where
  obj := typeEndLAdj.obj J
  map := typeEndLAdj.mapNatTrans J
  map_id := by intros; ext _ _ ⟨_, _⟩; rfl
  map_comp := by intros; ext _ _ ⟨_, _⟩; rfl

/-- Forward direction of the hom-set bijection:
given a nat trans `typeEndLAdj.obj Y ⟶ P`, produce
a function `Y → typeEnd P` by evaluating at
identity morphisms. -/
def typeEndAdj.homEquivToFun
    (Y : Type v) (P : Jᵒᵖ ⥤ J ⥤ Type v)
    (α : typeEndLAdj.obj J Y ⟶ P) :
    Y → typeEnd P :=
  fun y => ⟨
    fun j => (α.app (Opposite.op j)).app j
      (𝟙 j, y),
    fun {i j} f => by
      have h1 := congr_fun
        ((α.app (Opposite.op i)).naturality f)
        (𝟙 i, y)
      simp only [types_comp_apply] at h1
      dsimp only [typeEndLAdj.innerObj,
        typeEndLAdj.obj] at h1
      rw [Category.id_comp] at h1
      have h2 := congr_fun
        (congr_app (α.naturality f.op) j)
        (𝟙 j, y)
      simp only [NatTrans.comp_app,
        types_comp_apply] at h2
      dsimp only [typeEndLAdj.obj] at h2
      rw [Category.comp_id] at h2
      exact h1.symm.trans h2⟩

/-- Backward direction of the hom-set bijection:
given a function `Y → typeEnd P`, produce a nat trans
`typeEndLAdj.obj Y ⟶ P` by applying the covariant
action of `P` to morphisms from the compatible
family. -/
def typeEndAdj.homEquivInvFun
    (Y : Type v) (P : Jᵒᵖ ⥤ J ⥤ Type v)
    (f : Y → typeEnd P) :
    typeEndLAdj.obj J Y ⟶ P where
  app a :=
    { app := fun b ⟨h, y⟩ =>
        (P.obj a).map h ((f y).val a.unop)
      naturality := by
        intro b b' g; ext ⟨h, y⟩
        simp only [types_comp_apply]
        dsimp only [typeEndLAdj.innerObj,
          typeEndLAdj.obj]
        simp only [Functor.map_comp,
          types_comp_apply]
    }
  naturality := by
    intro a a' g; ext b ⟨h, y⟩
    simp only [NatTrans.comp_app,
      types_comp_apply]
    dsimp only [typeEndLAdj.obj]
    simp only [Functor.map_comp, types_comp_apply]
    rw [(f y).property g.unop]
    have := congr_fun
      ((P.map g).naturality h) ((f y).val a.unop)
    simp only [types_comp_apply] at this
    exact this.symm

/-- The hom-set equivalence for the end adjunction:
nat trans from `typeEndLAdj.obj Y` to `P` correspond
to functions `Y → typeEnd P`. -/
def typeEndAdj.homEquiv
    (Y : Type v) (P : Jᵒᵖ ⥤ J ⥤ Type v) :
    (typeEndLAdj.obj J Y ⟶ P) ≃ (Y → typeEnd P) where
  toFun := typeEndAdj.homEquivToFun J Y P
  invFun := typeEndAdj.homEquivInvFun J Y P
  left_inv := by
    intro α
    ext a b ⟨h, y⟩
    dsimp only [typeEndAdj.homEquivToFun,
      typeEndAdj.homEquivInvFun]
    have := congr_fun
      ((α.app a).naturality h) (𝟙 (a.unop), y)
    simp only [types_comp_apply] at this
    dsimp only [typeEndLAdj.innerObj,
      typeEndLAdj.obj] at this
    rw [Category.id_comp] at this
    exact this.symm
  right_inv := by
    intro f; ext y
    apply Subtype.ext; ext j
    dsimp only [typeEndAdj.homEquivToFun,
      typeEndAdj.homEquivInvFun]
    simp

/-- The end functor is right adjoint to the
functor sending `Y` to the profunctor
`(a, b) ↦ (a.unop ⟶ b) × Y`. -/
def typeEndAdj :
    typeEndLAdjFunctor J ⊣ typeEndFunctor J :=
  Adjunction.mkOfHomEquiv
    { homEquiv := typeEndAdj.homEquiv J }

end EndAdjunction

/-!
## Coend Adjunction

The coend functor `typeCoendFunctor` is left adjoint
to the functor sending `Y : Type v` to the profunctor
`(a, b) ↦ (b ⟶ a.unop) → Y`.
-/

section CoendAdjunction

variable (J : Type v) [Category.{v} J]

/-- For fixed `Y : Type v` and `a : Jᵒᵖ`, the functor
`J ⥤ Type v` sending `b ↦ (b ⟶ a.unop) → Y`. -/
def typeCoendRAdj.innerObj (Y : Type v)
    (a : Jᵒᵖ) : J ⥤ Type v where
  obj b := (b ⟶ a.unop) → Y
  map g := fun k h => k (g ≫ h)
  map_id := by
    intro X; funext k h
    simp only [types_id_apply, Category.id_comp]
  map_comp := by
    intro _ _ _ f g; funext k h
    simp only [types_comp_apply, Category.assoc]

/-- For fixed `Y : Type v`, the profunctor
`Jᵒᵖ ⥤ J ⥤ Type v` sending `(a, b)` to
`(b ⟶ a.unop) → Y`. -/
def typeCoendRAdj.obj (Y : Type v) :
    Jᵒᵖ ⥤ J ⥤ Type v where
  obj a := typeCoendRAdj.innerObj J Y a
  map f :=
    { app := fun _ k h => k (h ≫ f.unop)
      naturality := by
        intro _ _ g; ext k; funext h
        simp only [types_comp_apply]
        dsimp only [typeCoendRAdj.innerObj]
        rw [Category.assoc]
    }
  map_id := by
    intro a; ext b k; funext h
    simp only [NatTrans.id_app, types_id_apply,
      unop_id, Category.comp_id]
  map_comp := by
    intro _ _ _ f₁ f₂; ext b k; funext h
    simp only [NatTrans.comp_app,
      types_comp_apply, unop_comp, Category.assoc]

/-- The nat trans induced by `φ : Y → Z` between
profunctors `typeCoendRAdj.obj Y ⟶ typeCoendRAdj.obj Z`,
applying `φ` to the output. -/
def typeCoendRAdj.mapNatTrans
    {Y Z : Type v} (φ : Y → Z) :
    typeCoendRAdj.obj J Y ⟶
      typeCoendRAdj.obj J Z where
  app a :=
    { app := fun _ k h => φ (k h)
      naturality := by intros; rfl }
  naturality := by intros; rfl

/-- The functor `Type v ⥤ (Jᵒᵖ ⥤ J ⥤ Type v)`
sending `Y` to the profunctor
`(a, b) ↦ (b ⟶ a.unop) → Y`. This is the right
adjoint of `typeCoendFunctor`. -/
def typeCoendRAdjFunctor :
    Type v ⥤ (Jᵒᵖ ⥤ J ⥤ Type v) where
  obj := typeCoendRAdj.obj J
  map := typeCoendRAdj.mapNatTrans J
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- Forward direction of the hom-set bijection:
given `f : typeCoend P → Y`, produce a nat trans
`P ⟶ typeCoendRAdj.obj J Y` by composing `f` with
injections into the coend. -/
def typeCoendAdj.homEquivToFun
    (P : Jᵒᵖ ⥤ J ⥤ Type v) (Y : Type v)
    (f : typeCoend P → Y) :
    P ⟶ typeCoendRAdj.obj J Y where
  app a :=
    { app := fun b x h =>
        f (Quot.mk _ ⟨a.unop,
          (P.obj a).map h x⟩)
      naturality := by
        intro b b' g; ext x; funext h
        simp only [types_comp_apply]
        change f (Quot.mk _ ⟨a.unop,
          (P.obj a).map h ((P.obj a).map g x)⟩) =
          f (Quot.mk _ ⟨a.unop,
            (P.obj a).map (g ≫ h) x⟩)
        simp only [Functor.map_comp,
          types_comp_apply]
    }
  naturality := by
    intro a a' g; ext b x; funext h
    simp only [NatTrans.comp_app,
      types_comp_apply]
    change f (Quot.mk _ ⟨a'.unop,
      (P.obj a').map h
        ((P.map g).app b x)⟩) =
      f (Quot.mk _ ⟨a.unop,
        (P.obj a).map (h ≫ g.unop) x⟩)
    have h_nat := congr_fun
      ((P.map g).naturality h) x
    simp only [types_comp_apply] at h_nat
    have h_comp := congr_fun
      ((P.obj a).map_comp h g.unop) x
    simp only [types_comp_apply] at h_comp
    rw [← h_nat, h_comp]
    exact congr_arg f (Quot.sound
      (typeCoendRel.intro g.unop
        ((P.obj a).map h x)))

/-- Backward direction of the hom-set bijection:
given a nat trans `P ⟶ typeCoendRAdj.obj J Y`,
produce `typeCoend P → Y` via the universal property
of quotients. -/
def typeCoendAdj.homEquivInvFun
    (P : Jᵒᵖ ⥤ J ⥤ Type v) (Y : Type v)
    (α : P ⟶ typeCoendRAdj.obj J Y) :
    typeCoend P → Y :=
  Quot.lift
    (fun ⟨j, x⟩ =>
      (α.app (Opposite.op j)).app j x (𝟙 j))
    (by
      intro ⟨_, _⟩ ⟨_, _⟩ r
      cases r with
      | intro f z =>
        dsimp only []
        rename_i i j
        trans (α.app (Opposite.op j)).app i z f
        · have h1 := congr_fun
            (congr_fun
              (congr_app (α.naturality f.op) i)
              z)
            (𝟙 i)
          simp only [NatTrans.comp_app,
            types_comp_apply] at h1
          rw [h1]
          change (α.app (Opposite.op j)).app i
            z (𝟙 i ≫ f.op.unop) =
            (α.app (Opposite.op j)).app i z f
          simp only [Category.id_comp,
            Quiver.Hom.unop_op]
        · symm
          have h2 := congr_fun
            (congr_fun
              ((α.app (Opposite.op j)).naturality
                f)
              z)
            (𝟙 j)
          simp only [types_comp_apply] at h2
          rw [h2]
          change (α.app (Opposite.op j)).app i
            z (f ≫ 𝟙 j) =
            (α.app (Opposite.op j)).app i z f
          simp only [Category.comp_id])

/-- The hom-set equivalence for the coend
adjunction: functions `typeCoend P → Y` correspond
to nat trans `P ⟶ typeCoendRAdj.obj J Y`. -/
def typeCoendAdj.homEquiv
    (P : Jᵒᵖ ⥤ J ⥤ Type v) (Y : Type v) :
    (typeCoend P → Y) ≃
      (P ⟶ typeCoendRAdj.obj J Y) where
  toFun := typeCoendAdj.homEquivToFun J P Y
  invFun := typeCoendAdj.homEquivInvFun J P Y
  left_inv := by
    intro f; ext ⟨j, x⟩
    dsimp only [typeCoendAdj.homEquivToFun,
      typeCoendAdj.homEquivInvFun]
    change f (Quot.mk _ ⟨j,
      (P.obj (Opposite.op j)).map (𝟙 j) x⟩) =
      f (Quot.mk _ ⟨j, x⟩)
    simp
  right_inv := by
    intro α; ext a b x; funext h
    dsimp only [typeCoendAdj.homEquivToFun,
      typeCoendAdj.homEquivInvFun]
    change (α.app a).app a.unop
      ((P.obj a).map h x) (𝟙 a.unop) =
      (α.app a).app b x h
    have := congr_fun
      (congr_fun
        ((α.app a).naturality h) x)
      (𝟙 a.unop)
    simp only [types_comp_apply] at this
    rw [this]
    change (α.app a).app b x
      (h ≫ 𝟙 a.unop) =
      (α.app a).app b x h
    simp only [Category.comp_id]

/-- The coend functor is left adjoint to the
functor sending `Y` to the profunctor
`(a, b) ↦ (b ⟶ a.unop) → Y`. -/
def typeCoendAdj :
    typeCoendFunctor J ⊣ typeCoendRAdjFunctor J :=
  Adjunction.mkOfHomEquiv
    { homEquiv := typeCoendAdj.homEquiv J
      homEquiv_naturality_left_symm := by
        intro _ _ _ f g
        ext ⟨j, x⟩; rfl
      homEquiv_naturality_right := by
        intro _ _ _ f g
        ext _ _ _; funext _; rfl }

end CoendAdjunction

/-!
## Terminal Wedges and Initial Cowedges in Type

Every profunctor `F : Jᵒᵖ ⥤ J ⥤ Type v` has a terminal wedge
(given by `typeEndWedge`) and an initial cowedge (given by
`typeCoendCowedge`).
-/

section TypeInstances

variable {J : Type v} [Category.{v} J]

instance typeHasTerminalWedge
    (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    HasTerminal (Wedge F) :=
  (typeEndWedge_isTerminal F).hasTerminal

instance typeHasInitialCowedge
    (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    HasInitial (Cowedge F) :=
  (typeCoendCowedge_isInitial F).hasInitial

end TypeInstances

/-!
## Type-Valued Weighted (Co)Limits via (Co)Ends

A weighted limit in `Type v` is computed by the formula
`{W, F} = end_j F(j)^{W(j)}` (end of the power profunctor),
and a weighted colimit by `W * F = coend^j W(j) . F(j)`
(coend of the copower profunctor).
-/

section TypeWeightedLimits

variable {J : Type v} [Category.{v} J]

/-- The weighted limit of `F : J ⥤ Type v` weighted by
`W : J ⥤ Type v`, computed as the end of the power
profunctor `(op j₁, j₂) ↦ W(j₁) → F(j₂)`. -/
def typeWeightedLimit
    (W : J ⥤ Type v) (F : J ⥤ Type v) : Type v :=
  typeEnd (powerProfunctor (C := Type v) W F)

/-- The weighted colimit of `F : J ⥤ Type v` weighted by
`W : Jᵒᵖ ⥤ Type v`, computed as the coend of the copower
profunctor `(op j₁, j₂) ↦ W(j₁) × F(j₂)`. -/
def typeWeightedColimit
    (W : Jᵒᵖ ⥤ Type v) (F : J ⥤ Type v) : Type v :=
  typeCoend (copowerProfunctor (C := Type v) W F)

/-- The weighted cone over `F` with weight `W` whose apex is
`typeWeightedLimit W F`, obtained by transporting the terminal
end wedge through the cone-wedge equivalence. -/
def typeWeightedLimitCone
    (W : J ⥤ Type v) (F : J ⥤ Type v) :
    WeightedCone (C := Type v) W F :=
  (weightedConeWedgeEquiv W F).inverse.obj
    (typeEndWedge (powerProfunctor (C := Type v) W F))

/-- The weighted cone `typeWeightedLimitCone W F` is a
weighted limit. -/
def typeWeightedLimitCone_isWeightedLimit
    (W : J ⥤ Type v) (F : J ⥤ Type v) :
    IsWeightedLimit (typeWeightedLimitCone W F) :=
  isWeightedLimitOfIsTerminalPowerWedge W F
    (typeEndWedge_isTerminal
      (powerProfunctor (C := Type v) W F))

/-- The weighted cocone over `F` with weight `W` whose apex
is `typeWeightedColimit W F`, obtained by transporting the
initial coend cowedge through the cocone-cowedge
equivalence. -/
def typeWeightedColimitCocone
    (W : Jᵒᵖ ⥤ Type v) (F : J ⥤ Type v) :
    WeightedCocone (C := Type v) W F :=
  (weightedCoconeCowedgeEquiv W F).inverse.obj
    (typeCoendCowedge
      (copowerProfunctor (C := Type v) W F))

/-- The weighted cocone `typeWeightedColimitCocone W F` is
a weighted colimit. -/
def typeWeightedColimitCocone_isWeightedColimit
    (W : Jᵒᵖ ⥤ Type v) (F : J ⥤ Type v) :
    IsWeightedColimit
      (typeWeightedColimitCocone W F) :=
  isWeightedColimitOfIsInitialCopowerCowedge W F
    (typeCoendCowedge_isInitial
      (copowerProfunctor (C := Type v) W F))

/-- The functorial action of the power profunctor in `F`:
given `α : F ⟶ G`, produces a natural transformation
`powerProfunctor W F ⟶ powerProfunctor W G` by
post-composing with `α` at each component. -/
def powerProfunctorMapF (W : J ⥤ Type v)
    {F G : J ⥤ Type v} (α : F ⟶ G) :
    powerProfunctor (C := Type v) W F ⟶
      powerProfunctor (C := Type v) W G where
  app j :=
    { app := fun j' => HasPowers.mapVal (α.app j')
      naturality := fun {j₁ j₂} g => by
        simp only [powerProfunctor_obj_map,
          ← HasPowers.mapVal_comp]
        congr 1
        exact α.naturality g
    }
  naturality := fun {j₁ j₂} f => by
    ext j'
    simp only [NatTrans.comp_app, powerProfunctor_map_app]
    rw [← HasPowers.bimap_eq_mapIdx_mapVal,
      ← HasPowers.bimap_eq_mapVal_mapIdx]

/-- The weighted limit functor `(J ⥤ Type v) ⥤ Type v`
for a fixed weight `W`, sending `F` to the end of the
power profunctor `powerProfunctor W F`. -/
def typeWeightedLimitFunctor (W : J ⥤ Type v) :
    (J ⥤ Type v) ⥤ Type v where
  obj F := typeWeightedLimit W F
  map α := typeEnd.map J (powerProfunctorMapF W α)
  map_id F := by
    ext ⟨x, hx⟩
    simp only [typeWeightedLimit, typeEnd.map,
      powerProfunctorMapF, types_id_apply]
    apply Subtype.ext; ext j
    simp only [NatTrans.id_app, HasPowers.mapVal_id,
      types_id_apply]
  map_comp {F G H} α β := by
    ext ⟨x, hx⟩
    simp only [typeWeightedLimit, typeEnd.map,
      powerProfunctorMapF, types_comp_apply]
    apply Subtype.ext; ext j
    simp only [NatTrans.comp_app,
      HasPowers.mapVal_comp, types_comp_apply]

/-- The functorial action of the copower profunctor in `F`:
given `α : F ⟶ G`, produces a natural transformation
`copowerProfunctor W F ⟶ copowerProfunctor W G` by
applying `α` to the second component of each copower. -/
def copowerProfunctorMapF (W : Jᵒᵖ ⥤ Type v)
    {F G : J ⥤ Type v} (α : F ⟶ G) :
    copowerProfunctor (C := Type v) W F ⟶
      copowerProfunctor (C := Type v) W G where
  app j :=
    { app := fun j' =>
        HasCopowers.mapVal (α.app j')
      naturality := fun {j₁ j₂} g => by
        simp only [copowerProfunctor_obj_map,
          ← HasCopowers.mapVal_comp]
        congr 1
        exact α.naturality g
    }
  naturality := fun {j₁ j₂} f => by
    ext j'
    simp only [NatTrans.comp_app,
      copowerProfunctor_map_app]
    rw [← HasCopowers.bimap_eq_mapIdx_mapVal,
      ← HasCopowers.bimap_eq_mapVal_mapIdx]

/-- The weighted colimit functor `(J ⥤ Type v) ⥤ Type v`
for a fixed weight `W`, sending `F` to the coend of the
copower profunctor `copowerProfunctor W F`. -/
def typeWeightedColimitFunctor (W : Jᵒᵖ ⥤ Type v) :
    (J ⥤ Type v) ⥤ Type v where
  obj F := typeWeightedColimit W F
  map α :=
    typeCoend.map J (copowerProfunctorMapF W α)
  map_id _ := by
    ext ⟨_, _⟩; rfl
  map_comp _ _ := by
    ext ⟨_, _⟩; rfl

/-- The type-valued weighted limit `typeWeightedLimit W F`
is equivalent to the type of natural transformations
`W ⟶ F`.

The end of the power profunctor `(op j₁, j₂) ↦ W(j₁) → F(j₂)`
consists of families `x : (j : J) → W(j) → F(j)` satisfying
the wedge condition, which in `Type v` is exactly the naturality
condition for a natural transformation `W ⟶ F`. -/
def typeWeightedLimit.natTransEquiv
    (W F : J ⥤ Type v) :
    typeWeightedLimit W F ≃ (W ⟶ F) where
  toFun := fun ⟨x, hx⟩ =>
    { app := x
      naturality := fun {_ _} f => (hx f).symm }
  invFun := fun η =>
    ⟨η.app, fun {_ _} f => (η.naturality f).symm⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun _ => rfl

/-- The component isomorphism in `Type v` from
`natTransEquiv`: `typeWeightedLimit W F ≅ (W ⟶ F)`. -/
def typeWeightedLimit.natTransIso
    (W F : J ⥤ Type v) :
    typeWeightedLimit W F ≅ (W ⟶ F) where
  hom := (natTransEquiv W F).toFun
  inv := (natTransEquiv W F).invFun
  hom_inv_id := by
    ext ⟨_, _⟩; rfl
  inv_hom_id := by
    ext _; rfl

/-- The explicit end-based weighted limit functor
`typeWeightedLimitFunctor W` is naturally isomorphic to
`coyoneda.obj (op W)`, which sends `F ↦ (W ⟶ F)`. -/
def typeWeightedLimitFunctor.natIso
    (W : J ⥤ Type v) :
    typeWeightedLimitFunctor W ≅
      coyoneda.obj (Opposite.op W) :=
  NatIso.ofComponents
    (fun F => typeWeightedLimit.natTransIso W F)
    (fun {F G} α => by
      ext ⟨x, hx⟩
      rfl)

/-- Yoneda lemma for weighted limits: when the weight is
the representable functor `coyoneda.obj (op j)`, the
weighted limit evaluates to `F.obj j`.

This composes `natTransEquiv` (which identifies
`typeWeightedLimit W F` with `W ⟶ F`) with the
covariant Yoneda equivalence
`(coyoneda.obj (op j) ⟶ F) ≃ F.obj j`. -/
def typeWeightedLimit.yonedaEquiv
    (j : J) (F : J ⥤ Type v) :
    typeWeightedLimit (coyoneda.obj (Opposite.op j)) F
      ≃ F.obj j :=
  (natTransEquiv (coyoneda.obj (Opposite.op j)) F).trans
    coyonedaEquiv

/-- Forward direction of the co-Yoneda equivalence for
weighted colimits: sends a class `[k, (h, y)]` in the
coend to `F.map h y : F.obj j`. -/
def typeWeightedColimit.yonedaEquivFwd
    (j : J) (F : J ⥤ Type v) :
    typeWeightedColimit (yoneda.obj j) F →
      F.obj j :=
  Quot.lift
    (fun ⟨k, z⟩ => F.map z.1 z.2)
    (fun _ _ r => by
      cases r with
      | @intro i k f x =>
        simp only [copowerProfunctor_map_app,
          copowerProfunctor_obj_map,
          typesHasCopowers, HasCopowers.mapIdx,
          HasCopowers.desc, HasCopowers.inj,
          HasCopowers.mapVal,
          yoneda_obj_map, Quiver.Hom.unop_op]
        simp only [types_comp_apply]
        exact congrFun (F.map_comp f x.1) x.2)

/-- Backward direction of the co-Yoneda equivalence for
weighted colimits: sends `y : F.obj j` to the class of
`⟨j, (𝟙 j, y)⟩`. -/
def typeWeightedColimit.yonedaEquivInv
    (j : J) (F : J ⥤ Type v) :
    F.obj j → typeWeightedColimit (yoneda.obj j) F :=
  fun y => Quot.mk _ ⟨j, (𝟙 j, y)⟩

/-- Co-Yoneda lemma for weighted colimits: when the weight
is the representable functor `yoneda.obj j : Jᵒᵖ ⥤ Type v`,
the weighted colimit evaluates to `F.obj j`.

Forward: `[k, (h, y)] ↦ F.map h y`.
Backward: `y ↦ [j, (𝟙 j, y)]`. -/
def typeWeightedColimit.yonedaEquiv
    (j : J) (F : J ⥤ Type v) :
    typeWeightedColimit (yoneda.obj j) F ≃ F.obj j where
  toFun := yonedaEquivFwd j F
  invFun := yonedaEquivInv j F
  left_inv := by
    intro x
    induction x using Quot.ind with
    | mk a =>
      obtain ⟨k, h, y⟩ := a
      simp only [yonedaEquivFwd, yonedaEquivInv]
      symm
      apply Quot.sound
      have := typeCoendRel.intro (F :=
        copowerProfunctor (yoneda.obj j) F) h
        (show ((copowerProfunctor
          (yoneda.obj j) F).obj
            (Opposite.op j)).obj k from
          (𝟙 j, y))
      simp only [copowerProfunctor_map_app,
        copowerProfunctor_obj_map,
        typesHasCopowers, HasCopowers.mapIdx,
        HasCopowers.mapVal, HasCopowers.desc,
        HasCopowers.inj,
        yoneda_obj_map, Quiver.Hom.unop_op,
        types_comp_apply, Opposite.unop_op,
        Category.comp_id] at this
      exact this
  right_inv := by
    intro y
    simp only [yonedaEquivInv, yonedaEquivFwd]
    exact congrFun (F.map_id j) y

/-- The contravariant action of the power profunctor in
the weight `W`: given `α : W ⟶ W'`, produces
`powerProfunctor W' F ⟶ powerProfunctor W F` by
pre-composing with `α` at each component. -/
def powerProfunctorMapW (F : J ⥤ Type v)
    {W W' : J ⥤ Type v} (α : W ⟶ W') :
    powerProfunctor (C := Type v) W' F ⟶
      powerProfunctor (C := Type v) W F where
  app j :=
    { app := fun j' =>
        HasPowers.mapIdx (α.app j.unop)
      naturality := fun {j₁ j₂} g => by
        simp only [powerProfunctor_obj_map]
        rw [← HasPowers.bimap_eq_mapVal_mapIdx,
          ← HasPowers.bimap_eq_mapIdx_mapVal]
    }
  naturality := fun {j₁ j₂} f => by
    ext j' x
    simp only [NatTrans.comp_app,
      powerProfunctor_map_app, types_comp_apply]
    simp only [typesHasPowers, HasPowers.mapIdx,
      HasPowers.lift]
    funext w
    exact congrArg x
      (congrFun (α.naturality f.unop) w).symm

/-- The contravariant weighted limit functor in the weight:
for fixed `F`, sends `W ↦ typeWeightedLimit W F`.
Contravariant because the power profunctor is contravariant
in its indexing set. -/
def typeWeightedLimitFunctorInW (F : J ⥤ Type v) :
    (J ⥤ Type v)ᵒᵖ ⥤ Type v where
  obj W := typeWeightedLimit W.unop F
  map f :=
    typeEnd.map J (powerProfunctorMapW F f.unop)
  map_id W := by
    ext ⟨x, hx⟩
    simp only [typeWeightedLimit, typeEnd.map,
      powerProfunctorMapW, types_id_apply,
      Opposite.unop_op]
    apply Subtype.ext; ext j
    simp only [unop_id, NatTrans.id_app,
      typesHasPowers, HasPowers.mapIdx,
      HasPowers.lift, types_id_apply]
  map_comp {W₁ W₂ W₃} f g := by
    ext ⟨x, hx⟩
    simp only [typeWeightedLimit, typeEnd.map,
      powerProfunctorMapW, types_comp_apply,
      Opposite.unop_op]
    apply Subtype.ext; ext j
    simp only [unop_comp, NatTrans.comp_app,
      typesHasPowers, HasPowers.mapIdx,
      HasPowers.lift, types_comp_apply]

/-- The covariant action of the copower profunctor in
the weight `W`: given `α : W ⟶ W'`, produces
`copowerProfunctor W F ⟶ copowerProfunctor W' F` by
applying `α` to the first component of each copower. -/
def copowerProfunctorMapW (F : J ⥤ Type v)
    {W W' : Jᵒᵖ ⥤ Type v} (α : W ⟶ W') :
    copowerProfunctor (C := Type v) W F ⟶
      copowerProfunctor (C := Type v) W' F where
  app j :=
    { app := fun j' =>
        HasCopowers.mapIdx (α.app j)
      naturality := fun {j₁ j₂} g => by
        simp only [copowerProfunctor_obj_map]
        rw [← HasCopowers.bimap_eq_mapVal_mapIdx,
          ← HasCopowers.bimap_eq_mapIdx_mapVal]
    }
  naturality := fun {j₁ j₂} f => by
    ext j' x
    simp only [NatTrans.comp_app,
      copowerProfunctor_map_app, types_comp_apply]
    simp only [typesHasCopowers, HasCopowers.mapIdx,
      HasCopowers.desc, HasCopowers.inj]
    exact congrArg (fun w => (w, x.2))
      (congrFun (α.naturality f) x.1)

/-- The covariant weighted colimit functor in the weight:
for fixed `F`, sends `W ↦ typeWeightedColimit W F`. -/
def typeWeightedColimitFunctorInW (F : J ⥤ Type v) :
    (Jᵒᵖ ⥤ Type v) ⥤ Type v where
  obj W := typeWeightedColimit W F
  map α :=
    typeCoend.map J (copowerProfunctorMapW F α)
  map_id _ := by
    ext ⟨_, _⟩; rfl
  map_comp _ _ := by
    ext ⟨_, _⟩; rfl

/-- The weighted limit bifunctor
`(J ⥤ Type v)ᵒᵖ ⥤ (J ⥤ Type v) ⥤ Type v`, sending
`(W, F) ↦ typeWeightedLimit W F`. Contravariant in `W`,
covariant in `F`. -/
def typeWeightedLimitBifunctor :
    (J ⥤ Type v)ᵒᵖ ⥤ (J ⥤ Type v) ⥤ Type v where
  obj W := typeWeightedLimitFunctor W.unop
  map f :=
    { app := fun F =>
        typeEnd.map J (powerProfunctorMapW F f.unop)
      naturality := fun {F G} α => by
        ext ⟨x, hx⟩
        simp only [typeWeightedLimitFunctor,
          typeWeightedLimit, typeEnd.map,
          powerProfunctorMapW, powerProfunctorMapF,
          types_comp_apply]
        apply Subtype.ext; ext j
        simp only [typesHasPowers, HasPowers.mapIdx,
          HasPowers.mapVal, HasPowers.lift,
          types_comp_apply]
    }
  map_id W := by
    ext F ⟨x, hx⟩
    simp only [typeWeightedLimitFunctor,
      typeWeightedLimit, typeEnd.map,
      powerProfunctorMapW, NatTrans.id_app,
      types_id_apply]
    apply Subtype.ext; ext j
    simp only [unop_id, NatTrans.id_app,
      typesHasPowers, HasPowers.mapIdx,
      HasPowers.lift, types_id_apply]
  map_comp {W₁ W₂ W₃} f g := by
    ext F ⟨x, hx⟩
    simp only [typeWeightedLimitFunctor]
    change typeEnd.map J
        (powerProfunctorMapW F (f ≫ g).unop) ⟨x, hx⟩ =
      typeEnd.map J (powerProfunctorMapW F g.unop)
        (typeEnd.map J
          (powerProfunctorMapW F f.unop) ⟨x, hx⟩)
    simp only [typeEnd.map, powerProfunctorMapW]
    apply Subtype.ext; ext j
    simp only [unop_comp, NatTrans.comp_app,
      typesHasPowers, HasPowers.mapIdx,
      HasPowers.lift, types_comp_apply]

/-- The weighted colimit bifunctor
`(Jᵒᵖ ⥤ Type v) ⥤ (J ⥤ Type v) ⥤ Type v`, sending
`(W, F) ↦ typeWeightedColimit W F`. Covariant in both
arguments. -/
def typeWeightedColimitBifunctor :
    (Jᵒᵖ ⥤ Type v) ⥤ (J ⥤ Type v) ⥤ Type v where
  obj W := typeWeightedColimitFunctor W
  map α :=
    { app := fun F =>
        typeCoend.map J (copowerProfunctorMapW F α)
      naturality := fun {F G} β => by
        ext ⟨_, _⟩; rfl
    }
  map_id _ := by
    ext F ⟨_, _⟩; rfl
  map_comp _ _ := by
    ext F ⟨_, _⟩; rfl

end TypeWeightedLimits

/-!
## Ninja Yoneda and Co-Ninja Yoneda

The ninja Yoneda lemma expresses the end of a profunctor
as a weighted limit by the hom-profunctor, and dually, the
co-ninja Yoneda lemma expresses the coend as a weighted
colimit by the dual hom-profunctor.
-/

section NinjaYoneda

variable {J : Type v} [Category.{v} J]

/-- The end of a profunctor is equivalent to natural
transformations from the hom-profunctor to the uncurried
profunctor. This is the "expanded" form of the ninja
Yoneda lemma, identifying `typeEnd P` with
`Functor.hom J ⟶ Functor.uncurry.obj P`. -/
def typeEnd.homNatTransEquiv
    (P : Jᵒᵖ ⥤ J ⥤ Type v) :
    typeEnd P ≃
      (Functor.hom J ⟶ Functor.uncurry.obj P) where
  toFun x :=
    { app := fun ⟨a, k⟩ w =>
        (P.obj a).map w (x.val a.unop)
      naturality := fun {i j} f => by
        ext w
        simp only [Functor.hom_obj, types_comp_apply,
          Functor.hom_map, Functor.uncurry_obj_obj,
          Functor.uncurry_obj_map]
        conv_lhs => rw [Functor.map_comp,
          types_comp_apply, Functor.map_comp,
          types_comp_apply,
          x.property f.1.unop]
        rw [show f.1.unop.op = f.1 from
          Quiver.Hom.unop_op f.1]
        apply congrArg ((P.obj j.1).map f.2)
        exact (congr_fun ((P.map f.1).naturality w)
          (x.val i.1.unop)).symm
    }
  invFun α :=
    ⟨fun j => α.app (Opposite.op j, j) (𝟙 j),
     fun {i j} f => by
      have h1 := congr_fun
        (α.naturality (show (Opposite.op i, i) ⟶
          (Opposite.op i, j) from (𝟙 _, f)))
        (𝟙 i)
      simp only [Functor.hom_obj, types_comp_apply,
        Functor.hom_map, Functor.uncurry_obj_obj,
        Functor.uncurry_obj_map,
        Opposite.unop_op, unop_id,
        Category.id_comp] at h1
      rw [P.map_id, NatTrans.id_app] at h1
      simp only [types_id_apply] at h1
      have h2 := congr_fun
        (α.naturality (show (Opposite.op j, j) ⟶
          (Opposite.op i, j) from (f.op, 𝟙 _)))
        (𝟙 j)
      simp only [Functor.hom_obj, types_comp_apply,
        Functor.hom_map, Functor.uncurry_obj_obj,
        Functor.uncurry_obj_map,
        Opposite.unop_op,
        Quiver.Hom.unop_op,
        Category.comp_id] at h2
      rw [(P.obj (Opposite.op i)).map_id] at h2
      simp only [types_id_apply] at h2
      exact h1.symm.trans h2⟩
  left_inv x := by
    apply Subtype.ext; ext j
    change (P.obj (Opposite.op j)).map (𝟙 j)
      (x.val j) = x.val j
    rw [show (P.obj (Opposite.op j)).map (𝟙 j) =
      𝟙 _ from (P.obj (Opposite.op j)).map_id j]
    rfl
  right_inv α := by
    ext ⟨a, k⟩ w
    dsimp only []
    simp only [Opposite.op_unop]
    have h := congr_fun
      (α.naturality (show (a, a.unop) ⟶ (a, k)
        from (𝟙 _, w))) (𝟙 a.unop)
    simp only [Functor.hom_obj, types_comp_apply,
      Functor.hom_map, Functor.uncurry_obj_obj,
      Functor.uncurry_obj_map,
      unop_id, Category.id_comp] at h
    rw [P.map_id, NatTrans.id_app] at h
    simp only [types_id_apply] at h
    exact h.symm

/-- The ninja Yoneda lemma: the end of a profunctor
`P : Jᵒᵖ ⥤ J ⥤ Type v` equals the weighted limit of
`Functor.uncurry.obj P` weighted by the hom-profunctor
`Functor.hom J`, over the product category `Jᵒᵖ × J`. -/
def typeEnd.ninjaYonedaEquiv
    (P : Jᵒᵖ ⥤ J ⥤ Type v) :
    typeEnd P ≃ typeWeightedLimit
      (Functor.hom J) (Functor.uncurry.obj P) :=
  (typeEnd.homNatTransEquiv P).trans
    (typeWeightedLimit.natTransEquiv
      (Functor.hom J)
      (Functor.uncurry.obj P)).symm

/-- The ninja Yoneda lemma expressed as a natural
isomorphism of functors
`(Jᵒᵖ ⥤ J ⥤ Type v) ⥤ Type v`:
`typeEndFunctor J ≅ Functor.uncurry ⋙
  typeWeightedLimitFunctor (Functor.hom J)`. -/
def typeEndFunctor.ninjaYonedaNatIso :
    typeEndFunctor J ≅
      Functor.uncurry ⋙
        typeWeightedLimitFunctor (Functor.hom J) :=
  NatIso.ofComponents
    (fun P => (typeEnd.ninjaYonedaEquiv P).toIso)
    (fun {P Q} α => by
      ext ⟨x, hx⟩
      change (typeEnd.ninjaYonedaEquiv Q)
        (typeEnd.map J α ⟨x, hx⟩) =
        typeEnd.map _ (powerProfunctorMapF
          (Functor.hom J) (Functor.uncurry.map α))
          ((typeEnd.ninjaYonedaEquiv P) ⟨x, hx⟩)
      apply Subtype.ext; ext ⟨a, k⟩
      funext w
      change (Q.obj a).map w
        ((α.app a).app a.unop (x a.unop)) =
        (α.app a).app k
          ((P.obj a).map w (x a.unop))
      exact (FunctorToTypes.naturality
        (P.obj a) (Q.obj a) (α.app a) w
        (x a.unop)).symm)

/-- The co-ninja Yoneda lemma: the coend of a profunctor
`P : Jᵒᵖ ⥤ J ⥤ Type v` equals the weighted colimit of
`Functor.uncurry.obj P` weighted by the dual
hom-profunctor `homPre`, over `Jᵒᵖ × J`.

Forward: `⟨j, x⟩ ↦ ⟨(op j, j), (𝟙 j, x)⟩`.
Backward: `⟨(a, b), (w, y)⟩ ↦ ⟨a.unop, (P.obj a).map w y⟩`.
-/
def typeCoend.coNinjaYonedaEquiv
    (P : Jᵒᵖ ⥤ J ⥤ Type v) :
    typeCoend P ≃ typeWeightedColimit
      (homPre (C := J)) (Functor.uncurry.obj P) where
  toFun := Quot.lift
    (fun ⟨j, x⟩ => Quot.mk _
      ⟨(Opposite.op j, j), (𝟙 j, x)⟩)
    (fun _ _ r => by
      cases r with
      | @intro i j f x =>
        dsimp only []
        let cpf := copowerProfunctor
          (homPre (C := J)) (Functor.uncurry.obj P)
        have h1 := Quot.sound
          (typeCoendRel.intro (F := cpf)
            (show (Opposite.op j, i) ⟶
              (Opposite.op i, i) from (f.op, 𝟙 i))
            (show (cpf.obj
              (Opposite.op (Opposite.op i, i))).obj
                (Opposite.op j, i) from (𝟙 i, x)))
        simp only [cpf, copowerProfunctor_map_app,
          copowerProfunctor_obj_map,
          typesHasCopowers, HasCopowers.mapIdx,
          HasCopowers.mapVal, HasCopowers.desc,
          HasCopowers.inj,
          homPre_map, Functor.uncurry_obj_map,
          types_comp_apply,
          Quiver.Hom.unop_op,
          Category.id_comp,
          FunctorToTypes.map_id_apply] at h1
        have h2 := Quot.sound
          (typeCoendRel.intro (F := cpf)
            (show (Opposite.op j, i) ⟶
              (Opposite.op j, j) from (𝟙 _, f))
            (show (cpf.obj
              (Opposite.op (Opposite.op j, j))).obj
                (Opposite.op j, i) from (𝟙 j, x)))
        simp only [cpf, copowerProfunctor_map_app,
          copowerProfunctor_obj_map,
          typesHasCopowers, HasCopowers.mapIdx,
          HasCopowers.mapVal, HasCopowers.desc,
          HasCopowers.inj,
          homPre_map, Functor.uncurry_obj_map,
          types_comp_apply,
          unop_id,
          Category.id_comp, Category.comp_id,
          P.map_id, NatTrans.id_app] at h2
        exact h1.symm.trans h2)
  invFun := Quot.lift
    (fun ⟨⟨a, b⟩, w, y⟩ => Quot.mk _
      ⟨a.unop, (P.obj a).map w y⟩)
    (fun _ _ r => by
      cases r with
      | @intro k₁ k₂ g z =>
        obtain ⟨a₁, b₁⟩ := k₁
        obtain ⟨a₂, b₂⟩ := k₂
        obtain ⟨g₁, g₂⟩ := g
        obtain ⟨w, y⟩ := z
        simp only [copowerProfunctor_map_app,
          copowerProfunctor_obj_map,
          typesHasCopowers, HasCopowers.mapIdx,
          HasCopowers.mapVal, HasCopowers.desc,
          HasCopowers.inj,
          homPre_map, Functor.uncurry_obj_map,
          types_comp_apply]
        let r := typeCoendRel P
        calc Quot.mk r ⟨a₁.unop,
              (P.obj a₁).map
                (g₂ ≫ w ≫ g₁.unop) y⟩
            = Quot.mk r ⟨a₁.unop,
              (P.obj a₁).map g₁.unop
                ((P.obj a₁).map (g₂ ≫ w)
                  y)⟩ := by
              simp only [Functor.map_comp,
                types_comp_apply]
          _ = Quot.mk r ⟨a₂.unop,
              (P.map g₁).app a₂.unop
                ((P.obj a₁).map (g₂ ≫ w)
                  y)⟩ :=
              (Quot.sound
                (typeCoendRel.intro g₁.unop
                  ((P.obj a₁).map
                    (g₂ ≫ w) y))).symm
          _ = Quot.mk r ⟨a₂.unop,
              (P.obj a₂).map (g₂ ≫ w)
                ((P.map g₁).app b₁ y)⟩ := by
              simp only
                [FunctorToTypes.naturality]
          _ = Quot.mk r ⟨a₂.unop,
              (P.obj a₂).map w
                ((P.obj a₂).map g₂
                  ((P.map g₁).app b₁
                    y))⟩ := by
              simp only [Functor.map_comp,
                types_comp_apply])
  left_inv := by
    intro x
    induction x using Quot.ind with
    | mk a =>
      obtain ⟨j, x⟩ := a
      simp only [Opposite.unop_op]
      exact congrArg (Quot.mk _)
        (Sigma.ext rfl
          (by rw [heq_eq_eq,
            show (P.obj (Opposite.op j)).map
              (𝟙 j) x = x from
              FunctorToTypes.map_id_apply
                (F := P.obj (Opposite.op j))
                x]))
  right_inv := by
    intro x
    induction x using Quot.ind with
    | mk a =>
      obtain ⟨⟨a, b⟩, w, y⟩ := a
      dsimp only []
      simp only [Opposite.op_unop]
      let cpf := copowerProfunctor
        (homPre (C := J)) (Functor.uncurry.obj P)
      symm
      have h := Quot.sound
        (typeCoendRel.intro (F := cpf)
          (show (a, b) ⟶ (a, a.unop)
            from (𝟙 a, w))
          (show (cpf.obj
            (Opposite.op (a, a.unop))).obj
              (a, b) from (𝟙 a.unop, y)))
      simp only [cpf, copowerProfunctor_map_app,
        copowerProfunctor_obj_map,
        typesHasCopowers, HasCopowers.mapIdx,
        HasCopowers.mapVal, HasCopowers.desc,
        HasCopowers.inj,
        homPre_map, Functor.uncurry_obj_map,
        types_comp_apply,
        unop_id, Category.id_comp,
        Category.comp_id,
        P.map_id, NatTrans.id_app] at h
      exact h

/-- The co-ninja Yoneda lemma expressed as a natural
isomorphism of functors
`(Jᵒᵖ ⥤ J ⥤ Type v) ⥤ Type v`:
`typeCoendFunctor J ≅ Functor.uncurry ⋙
  typeWeightedColimitFunctor (homPre (C := J))`. -/
def typeCoendFunctor.coNinjaYonedaNatIso :
    typeCoendFunctor J ≅
      Functor.uncurry ⋙
        typeWeightedColimitFunctor
          (homPre (C := J)) :=
  NatIso.ofComponents
    (fun P =>
      (typeCoend.coNinjaYonedaEquiv P).toIso)
    (fun {P Q} α => by
      ext ⟨j, x⟩
      rfl)

/-- The right adjoint profunctor of the coend
adjunction at `Y` equals the slice profunctor of the
coyoneda embedding at `Y`: both send `(op j, k)` to
the function type `(k ⟶ j) → Y`. -/
theorem typeCoendRAdj_eq_sliceProfunctorPoly
    (Y : Type v) :
    typeCoendRAdj.obj J Y =
      sliceProfunctorPoly coyoneda Y := rfl

/-- Maps-out characterization of the coend:
`(typeCoend P → X) ≃ (P ⟶ sliceProfunctorPoly coyoneda X)`.
This restates the coend adjunction using the
coyoneda slice profunctor. -/
def typeCoend.mapsOutEquiv
    (P : Jᵒᵖ ⥤ J ⥤ Type v) (X : Type v) :
    (typeCoend P → X) ≃
      (P ⟶ sliceProfunctorPoly coyoneda X) :=
  (typeCoendAdj.homEquiv J P X).trans
    (Equiv.cast (by
      rw [typeCoendRAdj_eq_sliceProfunctorPoly]))

/-- The impredicative characterization of weighted
colimits in `Type v`: elements of
`typeWeightedColimit W F` correspond to natural
transformations from `weightedLimitFunctor W F`
to the identity functor `𝟭 (Type v)`. -/
def typeWeightedColimit.impredicative
    (W : Jᵒᵖ ⥤ Type v) (F : J ⥤ Type v) :
    (weightedLimitFunctor W F ⟶ 𝟭 (Type v)) ≃
      typeWeightedColimit W F :=
  (typeWeightedColimitCocone_isWeightedColimit
    W F).weightedColimitImpredicative

/-- The representable characterization of weighted
colimits in `Type v`: natural transformations from
`weightedLimitFunctor W F` to `G` correspond to
`G.obj (typeWeightedColimit W F)`. -/
def typeWeightedColimit.representable
    (W : Jᵒᵖ ⥤ Type v) (F : J ⥤ Type v)
    (G : Type v ⥤ Type v) :
    (weightedLimitFunctor W F ⟶ G) ≃
      G.obj (typeWeightedColimit W F) :=
  (typeWeightedColimitCocone_isWeightedColimit
    W F).weightedColimitRepresentable G

/-- Introduction rule for weighted limits: a function
`X → typeWeightedLimit W F` is equivalent to a weighted
limit of `homFromFunctor F X`, where
`homFromFunctor F X` sends `j ↦ X → F.obj j`. -/
def typeWeightedLimit.introEquiv
    (X : Type v) (W F : J ⥤ Type v) :
    (X → typeWeightedLimit W F) ≃
      typeWeightedLimit W
        (homFromFunctor F X) where
  toFun g :=
    ⟨fun j w x => (g x).val j w,
     fun {i j} f => by
       funext w; funext x
       exact congr_fun ((g x).property f) w⟩
  invFun h x :=
    ⟨fun j w => (h.val j w) x,
     fun {i j} f => by
       funext w
       exact congr_fun
         (congr_fun (h.property f) w) x⟩
  left_inv g := by ext x; rfl
  right_inv h := by rfl

/-- Post-compose a profunctor `P : Jᵒᵖ ⥤ J ⥤ Type v`
with the internal-hom functor
`coyoneda.obj (op X) : Type v ⥤ Type v`
(sending `Y ↦ X → Y`), yielding a new profunctor
whose value at `(op j, k)` is `X → (P.obj (op j)).obj k`. -/
abbrev profunctorPower
    (P : Jᵒᵖ ⥤ J ⥤ Type v) (X : Type v) :
    Jᵒᵖ ⥤ J ⥤ Type v :=
  P ⋙ (Functor.whiskeringRight J
    (Type v) (Type v)).obj
    (coyoneda.obj (Opposite.op X))

/-- Introduction rule for ends: a function
`X → typeEnd P` is equivalent to the end of the
profunctor `P` post-composed with the internal-hom
functor `coyoneda.obj (op X) : Type v ⥤ Type v`,
which sends `Y ↦ X → Y`. -/
def typeEnd.introEquiv
    (X : Type v) (P : Jᵒᵖ ⥤ J ⥤ Type v) :
    (X → typeEnd P) ≃
      typeEnd (profunctorPower P X) where
  toFun g :=
    ⟨fun j x => (g x).val j,
     fun {i j} f => by
       funext x
       exact (g x).property f⟩
  invFun h x :=
    ⟨fun j => (h.val j) x,
     fun {i j} f => by
       exact congr_fun (h.property f) x⟩
  left_inv g := by ext x; rfl
  right_inv h := by rfl

/-- Currying at the nat-trans level: a family
`X → (W ⟶ F)` corresponds to a single nat trans
`W ⋙ tensorLeft X ⟶ F`, where the tensor acts as
pointwise product `X × W(k)`. -/
def natTransCurryEquiv
    {K : Type v} [Category.{v} K]
    (X : Type v)
    (W F : K ⥤ Type v) :
    (X → (W ⟶ F)) ≃
      (W ⋙ MonoidalCategory.tensorLeft X ⟶ F) where
  toFun g :=
    { app := fun k ⟨x, w⟩ => (g x).app k w
      naturality := fun {k₁ k₂} f => by
        funext ⟨x, w⟩
        exact congr_fun ((g x).naturality f) w }
  invFun α x :=
    { app := fun k w => α.app k (x, w)
      naturality := fun {k₁ k₂} f => by
        funext w
        exact congr_fun (α.naturality f) (x, w) }
  left_inv g := by ext x; rfl
  right_inv α := by ext k ⟨x, w⟩; rfl

/-- The tensor-hom adjunction
`Types.tensorProductAdjunction X`, whiskered to the
functor category `K ⥤ Type v`, gives
`(W ⋙ tensorLeft X ⟶ F) ≃
  (W ⟶ F ⋙ coyoneda.obj (op X))`.
Composing with `natTransCurryEquiv` yields the
introduction equivalence
`(X → (W ⟶ F)) ≃ (W ⟶ F ⋙ coyoneda.obj (op X))`. -/
def natTransIntroEquiv
    {K : Type v} [Category.{v} K]
    (X : Type v)
    (W F : K ⥤ Type v) :
    (X → (W ⟶ F)) ≃
      (W ⟶ F ⋙ coyoneda.obj
        (Opposite.op X)) :=
  (natTransCurryEquiv X W F).trans
    (Adjunction.homEquiv
      (Adjunction.whiskerRight K
        (Types.tensorProductAdjunction X))
      W F)

/-- `Functor.uncurry` commutes with `profunctorPower`:
uncurrying and then post-composing with
`coyoneda.obj (op X)` equals uncurrying the
profunctor power. -/
theorem uncurry_profunctorPower_eq
    (X : Type v) (P : Jᵒᵖ ⥤ J ⥤ Type v) :
    Functor.uncurry.obj P ⋙
      coyoneda.obj (Opposite.op X) =
    Functor.uncurry.obj
      (profunctorPower P X) := rfl

/-- The end introduction equivalence factors through
the hom-nat-trans equivalence: its forward map agrees
with `homNatTransEquiv.symm ∘ natTransIntroEquiv ∘
(homNatTransEquiv ∘ ·)`. -/
theorem typeEnd.introEquiv_toFun_eq
    (X : Type v) (P : Jᵒᵖ ⥤ J ⥤ Type v)
    (g : X → typeEnd P) :
    (typeEnd.introEquiv X P) g =
      (typeEnd.homNatTransEquiv
        (profunctorPower P X)).symm
        ((uncurry_profunctorPower_eq X P).symm ▸
          (natTransIntroEquiv X
            (Functor.hom J)
            (Functor.uncurry.obj P))
          (fun x =>
            (typeEnd.homNatTransEquiv P)
              (g x))) := by
  apply Subtype.ext
  ext j
  simp only [introEquiv, homNatTransEquiv,
    natTransIntroEquiv, Equiv.symm]
  change (fun x => (g x).val j) =
    (fun x => ((P.obj (Opposite.op j)).map (𝟙 j))
      ((g x).val j))
  simp only [FunctorToTypes.map_id_apply]

/-- Impredicative characterization of coends: elements
of `typeCoend P` correspond to natural transformations
from `weightedLimitFunctor (homPre) (uncurry.obj P)` to
the identity functor on `Type v`.

Obtained by composing
`typeWeightedColimit.impredicative` with the co-ninja
Yoneda equivalence. -/
def typeCoend.impredicative
    (P : Jᵒᵖ ⥤ J ⥤ Type v) :
    (weightedLimitFunctor (homPre (C := J))
      (Functor.uncurry.obj P) ⟶ 𝟭 (Type v)) ≃
        typeCoend P :=
  (typeWeightedColimit.impredicative
    (homPre (C := J))
    (Functor.uncurry.obj P)).trans
    (typeCoend.coNinjaYonedaEquiv P).symm

/-- Representable characterization of coends: natural
transformations from
`weightedLimitFunctor (homPre) (uncurry.obj P)` to a
functor `G : Type v ⥤ Type v` correspond to
`G.obj (typeCoend P)`.

Obtained by composing
`typeWeightedColimit.representable` with `G` applied
to the co-ninja Yoneda equivalence. -/
def typeCoend.representable
    (P : Jᵒᵖ ⥤ J ⥤ Type v)
    (G : Type v ⥤ Type v) :
    (weightedLimitFunctor (homPre (C := J))
      (Functor.uncurry.obj P) ⟶ G) ≃
        G.obj (typeCoend P) :=
  let e := (typeCoend.coNinjaYonedaEquiv P).symm
  (typeWeightedColimit.representable
    (homPre (C := J))
    (Functor.uncurry.obj P) G).trans
    ((G.mapIso e.toIso).toEquiv)

/-- Functoriality of `sliceProfunctorPoly P` in the
target type: a morphism `φ : Y → Z` induces a nat trans
`sliceProfunctorPoly P Y ⟶ sliceProfunctorPoly P Z`
by post-composition. -/
def sliceProfunctorPoly.mapNatTrans
    (P : Jᵒᵖ ⥤ J ⥤ Type v)
    {Y Z : Type v} (φ : Y → Z) :
    sliceProfunctorPoly P Y ⟶
      sliceProfunctorPoly P Z where
  app a :=
    { app := fun _ h => φ ∘ h
      naturality := by intros; rfl }
  naturality := by intros; rfl

/-- The functor `Type v ⥤ (Jᵒᵖ ⥤ J ⥤ Type v)` sending
`Y` to `sliceProfunctorPoly P Y`, the profunctor
`(op j, k) ↦ P(op k, j) → Y`.

This is functorial in `Y` by post-composition.
It is the analogue for profunctor `P` of
`typeCoendRAdjFunctor J` (which is the special
case `P = coyoneda`). -/
def sliceProfunctorPolyFunctor
    (P : Jᵒᵖ ⥤ J ⥤ Type v) :
    Type v ⥤ (Jᵒᵖ ⥤ J ⥤ Type v) where
  obj Y := sliceProfunctorPoly P Y
  map φ := sliceProfunctorPoly.mapNatTrans P φ
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The copresheaf on `Type v` sending `Y` to
`typeEnd (sliceProfunctorPoly P Y)`, the end of
the profunctor `(op j, k) ↦ P(op k, j) → Y`.

This is the coend analogue of `weightedLimitFunctor`,
with `typeEndFunctor` playing the role of the weighted
limit: elements of `typeEnd (sliceProfunctorPoly P Y)`
are families `∀ j, P(op j, j) → Y` satisfying the
(dual) wedge condition. -/
def endLimitFunctor
    (P : Jᵒᵖ ⥤ J ⥤ Type v) :
    Type v ⥤ Type v :=
  sliceProfunctorPolyFunctor P ⋙ typeEndFunctor J

/-- The mapping-out formula for coends in terms of ends
(Milewski): `(typeCoend P → Y) ≃
typeEnd (sliceProfunctorPoly P Y)`.

An element of the right side is a family
`∀ j, P(op j, j) → Y` satisfying the dual wedge
condition, which is exactly the data of a function
from the coend quotient `typeCoend P` to `Y`. -/
def typeCoend.endEquiv
    (P : Jᵒᵖ ⥤ J ⥤ Type v) (Y : Type v) :
    (typeCoend P → Y) ≃
      typeEnd (sliceProfunctorPoly P Y) where
  toFun g :=
    ⟨fun j x => g (Quot.mk _ ⟨j, x⟩),
     fun {i j} f => by
       funext x
       exact congr_arg g (Quot.sound
         (typeCoendRel.intro f x))⟩
  invFun h :=
    Quot.lift
      (fun ⟨j, x⟩ => h.val j x)
      (fun _ _ r => by
        cases r with
        | intro f x =>
          exact congr_fun (h.property f) x)
  left_inv g := by
    funext q
    exact Quot.inductionOn q (fun _ => rfl)
  right_inv h := by
    apply Subtype.ext; ext j; rfl

/-- The natural isomorphism between
`endLimitFunctor P` and `coyoneda.obj (op (typeCoend P))`
as copresheaves on `Type v`.

Components at `Y` are `typeCoend.endEquiv P Y`, which
identifies `typeEnd (sliceProfunctorPoly P Y)` with
`typeCoend P → Y`.

This is the coend analogue of
`IsWeightedColimit.homNatIsoWeightedLimit`. -/
def coendHomNatIsoEnd
    (P : Jᵒᵖ ⥤ J ⥤ Type v) :
    endLimitFunctor P ≅
      coyoneda.obj (Opposite.op (typeCoend P)) :=
  NatIso.ofComponents
    (fun Y => (typeCoend.endEquiv P Y).symm.toIso)
    (fun {Y Z} f => by
      ext ⟨val, _⟩
      funext q
      exact Quot.inductionOn q (fun _ => rfl))

/-- Representable characterization of coends via ends:
natural transformations from `endLimitFunctor P` to a
functor `G : Type v ⥤ Type v` correspond to
`G.obj (typeCoend P)`.

This is the coend analogue of
`IsWeightedColimit.weightedColimitRepresentable`,
with `endLimitFunctor P` (sending
`Y ↦ typeEnd (sliceProfunctorPoly P Y)`) playing the
role of `weightedLimitFunctor W D`. -/
def typeCoend.endRepresentable
    (P : Jᵒᵖ ⥤ J ⥤ Type v)
    (G : Type v ⥤ Type v) :
    (endLimitFunctor P ⟶ G) ≃
      G.obj (typeCoend P) :=
  coyonedaEquivOfNatIso
    (coendHomNatIsoEnd P)

/-- Impredicative characterization of coends via ends:
elements of `typeCoend P` correspond to natural
transformations from `endLimitFunctor P` to the
identity functor on `Type v`.

This is the coend analogue of
`IsWeightedColimit.weightedColimitImpredicative`. -/
def typeCoend.endImpredicative
    (P : Jᵒᵖ ⥤ J ⥤ Type v) :
    (endLimitFunctor P ⟶ 𝟭 (Type v)) ≃
      typeCoend P :=
  coyonedaEquivOfNatIsoTypeId
    (coendHomNatIsoEnd P)

end NinjaYoneda

section PointwisePresheaf

universe u₁

variable
  {K : Type v} [Category.{v} K]
  {E : Type u₁} [Category.{v} E]

/-- The pointwise weighted limit presheaf: given
`D : K ⥤ (E ⥤ Type v)` with weight `W : K ⥤ Type v`,
produces the presheaf
`e ↦ typeWeightedLimit W (D.flip.obj e)` in
`E ⥤ Type v`.

At each `e : E`, `D.flip.obj e : K ⥤ Type v` sends
`j ↦ (D.obj j).obj e`, and the weighted limit
consists of families `(j : K) → W.obj j → D(j)(e)`
satisfying the wedge condition. -/
def pointwiseTypeWeightedLimit
    (W : K ⥤ Type v)
    (D : K ⥤ (E ⥤ Type v)) : E ⥤ Type v :=
  D.flip ⋙ typeWeightedLimitFunctor W

/-- The pointwise weighted colimit presheaf: given
`D : K ⥤ (E ⥤ Type v)` with weight
`W : Kᵒᵖ ⥤ Type v`, produces the presheaf
`e ↦ typeWeightedColimit W (D.flip.obj e)` in
`E ⥤ Type v`. -/
def pointwiseTypeWeightedColimit
    (W : Kᵒᵖ ⥤ Type v)
    (D : K ⥤ (E ⥤ Type v)) : E ⥤ Type v :=
  D.flip ⋙ typeWeightedColimitFunctor W

/-- The pointwise end presheaf: given
`P : Kᵒᵖ ⥤ K ⥤ (E ⥤ Type v)`, produces the presheaf
`e ↦ typeEnd (P(−)(−)(e))` in `E ⥤ Type v`.

At each `e : E`, the profunctor sends
`(op j, k) ↦ (P.obj (op j)).obj k |>.obj e`, and the
end consists of compatible families satisfying the
wedge condition at `e`. -/
def pointwiseTypeEnd
    (P : Kᵒᵖ ⥤ K ⥤ (E ⥤ Type v)) :
    E ⥤ Type v :=
  (P ⋙ flipFunctor K E (Type v)).flip ⋙
    typeEndFunctor K

/-- The pointwise coend presheaf: given
`P : Kᵒᵖ ⥤ K ⥤ (E ⥤ Type v)`, produces the presheaf
`e ↦ typeCoend (P(−)(−)(e))` in `E ⥤ Type v`. -/
def pointwiseTypeCoend
    (P : Kᵒᵖ ⥤ K ⥤ (E ⥤ Type v)) :
    E ⥤ Type v :=
  (P ⋙ flipFunctor K E (Type v)).flip ⋙
    typeCoendFunctor K

end PointwisePresheaf

end GebLean
