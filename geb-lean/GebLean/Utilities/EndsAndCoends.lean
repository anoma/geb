import Mathlib.CategoryTheory.Limits.Shapes.End
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

end TypeWeightedLimits

end GebLean
