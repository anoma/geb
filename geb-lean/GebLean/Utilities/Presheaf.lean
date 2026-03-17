import GebLean.Utilities.Opposites
import Mathlib.CategoryTheory.Functor.FunctorHom
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
import Mathlib.CategoryTheory.Topos.Classifier
import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.CategoryTheory.Subfunctor.Sieves
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Presheaf and Copresheaf Construction Functors

This module defines functors that send a category to its category of presheaves
or copresheaves.

## Main definitions

* `Copresheaf C` - The type of copresheaves on `C`, i.e., functors `C ⥤ Type v`
* `Presheaf C` - The type of presheaves on `C`, i.e., functors `Cᵒᵖ' ⥤ Type v`
* `copresheafConstruction` - Functor `Catᵒᵖ' ⥤ Cat` sending `C` to `C ⥤ Type v`
* `presheafConstruction` - Functor `Catᵒᵖ' ⥤ Cat` sending `C` to `Cᵒᵖ' ⥤ Type v`

Both constructions are contravariant because for a functor `F : C ⥤ D`,
precomposition induces functors in the opposite direction:
- The induced functor on copresheaves is `(D ⥤ Type v) ⥤ (C ⥤ Type v)` via
  precomposition with `F`.
- The induced functor on presheaves is `(Dᵒᵖ' ⥤ Type v) ⥤ (Cᵒᵖ' ⥤ Type v)` via
  precomposition with `F.op'`.

## Covariant Yoneda equivalences

* `coyonedaEquivOfNatIso` - If a copresheaf `F` is naturally isomorphic
  to the covariant hom-functor of `A`, then `(F ⟶ G) ≃ G.obj A`
* `coyonedaEquivOfNatIsoTypeId` - Specialization to `C = Type v` with
  `G = 𝟭 (Type v)`, giving `(F ⟶ 𝟭 (Type v)) ≃ A`

## Functorial covariant Yoneda natural isomorphisms

* `coyonedaNatIsoOfNatIso` - Lifts `coyonedaEquivOfNatIso` to a
  natural isomorphism of functors `(C ⥤ Type v) ⥤ Type v`,
  using `curriedCoyonedaLemma` (requires `SmallCategory C`)
* `coyonedaNatIsoOfNatIsoLarge` - General-universe version using
  `largeCurriedCoyonedaLemma` with `uliftFunctor`
* `coyonedaNatIsoOfNatIsoTypeId` - Specialization to `C = Type v`
* `uliftCoyonedaNatIsoOfNatIso` - Version using `uliftCoyoneda`,
  allowing copresheaf target `Type (max w v)` with `w ≠ v`
* `uliftCoyonedaNatIsoOfNatIsoTypeId` - Specialization to
  `C = Type v` with lifted codomain `Type (max w v)`
-/

universe v u

namespace GebLean

open CategoryTheory

/--
The copresheaf category of a category `C`: functors `C ⥤ Type v`.
-/
abbrev Copresheaf (C : Type u) [Category.{v} C] := C ⥤ Type v

/--
The presheaf category of a category `C`: functors `Cᵒᵖ' ⥤ Type v`.
-/
abbrev Presheaf (C : Type u) [Category.{v} C] := Cᵒᵖ' ⥤ Type v

/--
The map component of `copresheafConstruction`. For a functor `F : C ⥤ D`,
returns the precomposition functor `(D ⥤ Type v) ⥤ (C ⥤ Type v)`.
-/
def copresheafConstructionMap {C D : Cat.{v, u}} :
    (C ⥤ D) ⥤ (Cat.of (↑D ⥤ Type v) ⥤ Cat.of (↑C ⥤ Type v)) :=
  Functor.whiskeringLeft (↑C) (↑D) (Type v)

/--
The copresheaf construction functor (contravariant).

For a category `C`, this returns the category of copresheaves `C ⥤ Type v`.
For a functor `F : D ⥤ C` (which is a morphism `C ⟶ D` in `Catᵒᵖ'`), this
returns the precomposition functor `(C ⥤ Type v) ⥤ (D ⥤ Type v)` given by
`G ↦ F ⋙ G`.

This is contravariant: the induced functor on copresheaves goes in the opposite
direction to the original functor.
-/
def copresheafConstruction :
    Cat.{v, u}ᵒᵖ' ⥤ Cat.{max u v, max u v (v + 1)} where
  obj (C : Cat.{v, u}) := Cat.of (↑C ⥤ Type v)
  map {C D : Cat.{v, u}} (F : @Quiver.Hom Cat.{v, u}ᵒᵖ' _ C D) :=
    ((Functor.whiskeringLeft (↑D : Type u) (↑C : Type u) (Type v)).obj
      F.toFunctor).toCatHom
  map_id _ := by
    apply Cat.Hom.ext
    rfl
  map_comp _ _ := by
    apply Cat.Hom.ext
    rfl

/--
The map component of `presheafConstruction`. For a functor `F : C ⥤ D`,
returns the precomposition functor `(Dᵒᵖ' ⥤ Type v) ⥤ (Cᵒᵖ' ⥤ Type v)`.

Since `F : C ⥤ D` gives `F.op' : Cᵒᵖ' ⥤ Dᵒᵖ'`, precomposition with `F.op'`
maps presheaves on `D` to presheaves on `C`.
-/
def presheafConstructionMap {C D : Cat.{v, u}} :
    (C ⥤ D)ᵒᵖ' ⥤
    (Cat.of ((↑D : Type u)ᵒᵖ' ⥤ Type v) ⥤ Cat.of ((↑C : Type u)ᵒᵖ' ⥤ Type v)) :=
  Functor.opHom' (C := ↑C) (D := ↑D) ⋙
  Functor.whiskeringLeft (↑C : Type u)ᵒᵖ' (↑D : Type u)ᵒᵖ' (Type v)

/--
The presheaf construction functor (contravariant).

For a category `C`, this returns the category of presheaves `Cᵒᵖ' ⥤ Type v`.
For a functor `F : D ⥤ C` (which is a morphism `C ⟶ D` in `Catᵒᵖ'`), this
returns the precomposition functor `(Cᵒᵖ' ⥤ Type v) ⥤ (Dᵒᵖ' ⥤ Type v)` given
by `G ↦ F.op' ⋙ G`.

This is contravariant: the induced functor on presheaves goes in the opposite
direction to the original functor.
-/
def presheafConstruction :
    Cat.{v, u}ᵒᵖ' ⥤ Cat.{max u v, max u v (v + 1)} where
  obj (C : Cat.{v, u}) := Cat.of ((↑C : Type u)ᵒᵖ' ⥤ Type v)
  map {C D : Cat.{v, u}} (F : @Quiver.Hom Cat.{v, u}ᵒᵖ' _ C D) :=
    ((Functor.whiskeringLeft (↑D : Type u)ᵒᵖ' (↑C : Type u)ᵒᵖ' (Type v)).obj
      (Functor.op' F.toFunctor)).toCatHom
  map_id _ := by
    apply Cat.Hom.ext
    rfl
  map_comp _ _ := by
    apply Cat.Hom.ext
    rfl

/-! ### Pullbacks of presheaf morphisms

Computable pullback cone for morphisms in functor
categories `C ⥤ Type w`, constructed pointwise from
`Types.pullbackLimitCone` via
`PullbackCone.combine`.  At each object `T`, the
fiber is `{ (a, b) : F(T) × G(T) | f(a) = g(b) }`.
-/

section PresheafPullback

open Limits

universe w

variable {C : Type u} [Category.{v} C]
  {F G H : C ⥤ Type w}

/-- The pullback cone for two presheaf morphisms with
common target, obtained by combining the pointwise
pullback cones in `Type w`. -/
def presheafPullbackCone
    (f : F ⟶ H) (g : G ⟶ H) :
    PullbackCone f g :=
  PullbackCone.combine f g
    (fun X =>
      Types.pullbackCone (f.app X) (g.app X))
    (fun X =>
      (Types.pullbackLimitCone
        (f.app X) (g.app X)).isLimit)

/-- The presheaf pullback cone is a limit.

This is constructed directly via `isLimitAux`
rather than using `PullbackCone.combineIsLimit`
(which goes through `evaluationJointlyReflectsLimits`
and does not produce definitional reduction of lifts). -/
def presheafPullbackIsLimit
    (f : F ⟶ H) (g : G ⟶ H) :
    IsLimit (presheafPullbackCone f g) :=
  PullbackCone.isLimitAux _
    (fun s => {
      app := fun X a =>
        ⟨⟨s.fst.app X a, s.snd.app X a⟩,
          congr_fun (NatTrans.congr_app
            s.condition X) a⟩
      naturality := by
        intro X Y h
        ext a
        apply Subtype.ext
        let cone := presheafPullbackCone f g
        exact Prod.ext
          ((congr_fun (s.fst.naturality h)
              a).trans
            (congr_fun (cone.fst.naturality h)
              ⟨⟨s.fst.app X a,
                s.snd.app X a⟩, _⟩).symm)
          ((congr_fun (s.snd.naturality h)
              a).trans
            (congr_fun (cone.snd.naturality h)
              ⟨⟨s.fst.app X a,
                s.snd.app X a⟩, _⟩).symm)
    })
    (fun s => by ext X a; rfl)
    (fun s => by ext X a; rfl)
    (fun s m w => by
      ext X a
      apply Subtype.ext
      exact Prod.ext
        (congr_fun (NatTrans.congr_app
          (w WalkingCospan.left) X) a)
        (congr_fun (NatTrans.congr_app
          (w WalkingCospan.right) X) a))

/-- The pullback object of two presheaf morphisms. -/
abbrev presheafPullback
    (f : F ⟶ H) (g : G ⟶ H) : C ⥤ Type w :=
  (presheafPullbackCone f g).pt

/-- First projection from the presheaf pullback. -/
abbrev presheafPullbackFst
    (f : F ⟶ H) (g : G ⟶ H) :
    presheafPullback f g ⟶ F :=
  (presheafPullbackCone f g).fst

/-- Second projection from the presheaf pullback. -/
abbrev presheafPullbackSnd
    (f : F ⟶ H) (g : G ⟶ H) :
    presheafPullback f g ⟶ G :=
  (presheafPullbackCone f g).snd

/-- The first projection from the presheaf pullback,
applied pointwise, extracts the first component
of the underlying pair. -/
@[simp]
theorem presheafPullbackFst_app_eq
    (f : F ⟶ H) (g : G ⟶ H)
    (X : C)
    (p : (presheafPullback f g).obj X) :
    (presheafPullbackFst f g).app X p =
    p.val.1 :=
  rfl

/-- The second projection from the presheaf pullback,
applied pointwise, extracts the second component
of the underlying pair. -/
@[simp]
theorem presheafPullbackSnd_app_eq
    (f : F ⟶ H) (g : G ⟶ H)
    (X : C)
    (p : (presheafPullback f g).obj X) :
    (presheafPullbackSnd f g).app X p =
    p.val.2 :=
  rfl

/-- The universal morphism into the presheaf pullback,
given morphisms into the two factors whose compositions
with `f` and `g` agree. -/
abbrev presheafPullbackLift
    (f : F ⟶ H) (g : G ⟶ H)
    {P : C ⥤ Type w}
    (h₁ : P ⟶ F) (h₂ : P ⟶ G)
    (w : h₁ ≫ f = h₂ ≫ g) :
    P ⟶ presheafPullback f g :=
  PullbackCone.IsLimit.lift
    (presheafPullbackIsLimit f g) h₁ h₂ w

/-- Pointwise first projection of a lifted morphism
into the presheaf pullback: composing
`presheafPullbackLift` with `presheafPullbackFst`
at a specific object and element recovers the first
component. -/
@[simp]
theorem presheafPullbackLift_fst_app
    (f : F ⟶ H) (g : G ⟶ H)
    {P : C ⥤ Type w}
    (h₁ : P ⟶ F) (h₂ : P ⟶ G)
    (w : h₁ ≫ f = h₂ ≫ g) (X : C)
    (a : P.obj X) :
    (presheafPullbackFst f g).app X
      ((presheafPullbackLift f g
        h₁ h₂ w).app X a) =
      h₁.app X a :=
  congr_fun (NatTrans.congr_app
    (PullbackCone.IsLimit.lift_fst
      (presheafPullbackIsLimit f g)
      h₁ h₂ w) X) a

/-- Pointwise second projection of a lifted morphism
into the presheaf pullback: composing
`presheafPullbackLift` with `presheafPullbackSnd`
at a specific object and element recovers the second
component. -/
@[simp]
theorem presheafPullbackLift_snd_app
    (f : F ⟶ H) (g : G ⟶ H)
    {P : C ⥤ Type w}
    (h₁ : P ⟶ F) (h₂ : P ⟶ G)
    (w : h₁ ≫ f = h₂ ≫ g) (X : C)
    (a : P.obj X) :
    (presheafPullbackSnd f g).app X
      ((presheafPullbackLift f g
        h₁ h₂ w).app X a) =
      h₂.app X a :=
  congr_fun (NatTrans.congr_app
    (PullbackCone.IsLimit.lift_snd
      (presheafPullbackIsLimit f g)
      h₁ h₂ w) X) a

/-- The value component of a lifted element into
a presheaf pullback: applying the lift at a
specific object and element produces the pair
of the two component values. -/
@[simp]
theorem presheafPullbackLift_app_val
    (f : F ⟶ H) (g : G ⟶ H)
    {P : C ⥤ Type w}
    (h₁ : P ⟶ F) (h₂ : P ⟶ G)
    (w : h₁ ≫ f = h₂ ≫ g)
    (X : C) (a : P.obj X) :
    ((presheafPullbackLift f g
      h₁ h₂ w).app X a).val =
    (h₁.app X a, h₂.app X a) :=
  rfl

/-- Isomorphism of presheaf pullbacks induced by
isomorphisms on the sources.  Given `α : F₁ ≅ F₂` and
`β : G₁ ≅ G₂` with `f₁ = α.hom ≫ f₂` and
`g₁ = β.hom ≫ g₂`, the pullbacks of `(f₁, g₁)` and
`(f₂, g₂)` over `H` are isomorphic. -/
def presheafPullbackIsoOfIso
    {F₁ F₂ G₁ G₂ : C ⥤ Type w}
    {f₁ : F₁ ⟶ H} {f₂ : F₂ ⟶ H}
    {g₁ : G₁ ⟶ H} {g₂ : G₂ ⟶ H}
    (α : F₁ ≅ F₂) (β : G₁ ≅ G₂)
    (hf : f₁ = α.hom ≫ f₂)
    (hg : g₁ = β.hom ≫ g₂) :
    presheafPullback f₁ g₁ ≅
      presheafPullback f₂ g₂ where
  hom :=
    presheafPullbackLift f₂ g₂
      (presheafPullbackFst f₁ g₁ ≫ α.hom)
      (presheafPullbackSnd f₁ g₁ ≫ β.hom)
      (by
        rw [Category.assoc, Category.assoc,
          ← hf, ← hg]
        exact
          (presheafPullbackCone f₁ g₁).condition)
  inv :=
    presheafPullbackLift f₁ g₁
      (presheafPullbackFst f₂ g₂ ≫ α.inv)
      (presheafPullbackSnd f₂ g₂ ≫ β.inv)
      (by
        simp only [Category.assoc, hf, hg,
          Iso.inv_hom_id_assoc]
        exact
          (presheafPullbackCone f₂ g₂).condition)
  hom_inv_id := by
    apply PullbackCone.IsLimit.hom_ext
      (presheafPullbackIsLimit f₁ g₁) <;>
    simp only [Category.id_comp,
      Category.assoc,
      PullbackCone.IsLimit.lift_fst,
      PullbackCone.IsLimit.lift_fst_assoc,
      PullbackCone.IsLimit.lift_snd,
      PullbackCone.IsLimit.lift_snd_assoc,
      Iso.hom_inv_id, Category.comp_id]
  inv_hom_id := by
    apply PullbackCone.IsLimit.hom_ext
      (presheafPullbackIsLimit f₂ g₂) <;>
    simp only [Category.id_comp,
      Category.assoc,
      PullbackCone.IsLimit.lift_fst,
      PullbackCone.IsLimit.lift_fst_assoc,
      PullbackCone.IsLimit.lift_snd,
      PullbackCone.IsLimit.lift_snd_assoc,
      Iso.inv_hom_id, Category.comp_id]

@[reassoc (attr := simp)]
theorem presheafPullbackIsoOfIso_hom_fst
    {F₁ F₂ G₁ G₂ : C ⥤ Type w}
    {f₁ : F₁ ⟶ H} {f₂ : F₂ ⟶ H}
    {g₁ : G₁ ⟶ H} {g₂ : G₂ ⟶ H}
    (α : F₁ ≅ F₂) (β : G₁ ≅ G₂)
    (hf : f₁ = α.hom ≫ f₂)
    (hg : g₁ = β.hom ≫ g₂) :
    (presheafPullbackIsoOfIso α β hf hg).hom ≫
      presheafPullbackFst f₂ g₂ =
    presheafPullbackFst f₁ g₁ ≫ α.hom := by
  simp only [presheafPullbackIsoOfIso,
    PullbackCone.IsLimit.lift_fst]

@[reassoc (attr := simp)]
theorem presheafPullbackIsoOfIso_hom_snd
    {F₁ F₂ G₁ G₂ : C ⥤ Type w}
    {f₁ : F₁ ⟶ H} {f₂ : F₂ ⟶ H}
    {g₁ : G₁ ⟶ H} {g₂ : G₂ ⟶ H}
    (α : F₁ ≅ F₂) (β : G₁ ≅ G₂)
    (hf : f₁ = α.hom ≫ f₂)
    (hg : g₁ = β.hom ≫ g₂) :
    (presheafPullbackIsoOfIso α β hf hg).hom ≫
      presheafPullbackSnd f₂ g₂ =
    presheafPullbackSnd f₁ g₁ ≫ β.hom := by
  simp only [presheafPullbackIsoOfIso,
    PullbackCone.IsLimit.lift_snd]

@[simp]
theorem presheafPullbackCondition
    (f : F ⟶ H) (g : G ⟶ H) :
    presheafPullbackFst f g ≫ f =
      presheafPullbackSnd f g ≫ g :=
  (presheafPullbackCone f g).condition

/-- When the first morphism is the identity, the
presheaf pullback is isomorphic to the second source
via the second projection. -/
def presheafPullbackIdLeftIso
    (g : G ⟶ H) :
    presheafPullback (𝟙 H) g ≅ G where
  hom := presheafPullbackSnd (𝟙 H) g
  inv := presheafPullbackLift (𝟙 H) g
    g (𝟙 G) (by simp)
  hom_inv_id := by
    apply PullbackCone.IsLimit.hom_ext
      (presheafPullbackIsLimit ..)
    · have := presheafPullbackCondition (𝟙 H) g
      simp only [Category.comp_id] at this
      simp only [Category.assoc, Category.id_comp,
        PullbackCone.IsLimit.lift_fst]
      exact this.symm
    · simp only [Category.assoc,
        PullbackCone.IsLimit.lift_snd,
        Category.comp_id, Category.id_comp]
  inv_hom_id := by simp [presheafPullbackLift]

@[reassoc (attr := simp)]
theorem presheafPullbackIdLeftIso_inv_fst
    (g : G ⟶ H) :
    (presheafPullbackIdLeftIso g).inv ≫
      presheafPullbackFst (𝟙 H) g = g := by
  simp [presheafPullbackIdLeftIso,
    presheafPullbackLift]

/-- When the second morphism is the identity, the
presheaf pullback is isomorphic to the first source
via the first projection. -/
def presheafPullbackIdRightIso
    (f : F ⟶ H) :
    presheafPullback f (𝟙 H) ≅ F where
  hom := presheafPullbackFst f (𝟙 H)
  inv := presheafPullbackLift f (𝟙 H)
    (𝟙 F) f (by simp)
  hom_inv_id := by
    apply PullbackCone.IsLimit.hom_ext
      (presheafPullbackIsLimit ..)
    · simp only [Category.assoc,
        PullbackCone.IsLimit.lift_fst,
        Category.comp_id, Category.id_comp]
    · have := presheafPullbackCondition f (𝟙 H)
      simp only [Category.comp_id] at this
      simp only [Category.assoc, Category.id_comp,
        PullbackCone.IsLimit.lift_snd]
      exact this
  inv_hom_id := by simp [presheafPullbackLift]

@[reassoc (attr := simp)]
theorem presheafPullbackIdRightIso_inv_snd
    (f : F ⟶ H) :
    (presheafPullbackIdRightIso f).inv ≫
      presheafPullbackSnd f (𝟙 H) = f := by
  simp [presheafPullbackIdRightIso,
    presheafPullbackLift]

variable {F' G' H' K : C ⥤ Type w}

/-- Associativity isomorphism for iterated presheaf
pullbacks.  Given `f : F ⟶ H`, `g : G ⟶ H`,
`f' : G ⟶ H'`, `g' : K ⟶ H'`, there is a canonical
isomorphism between pulling back the outer pair with
`f'` composed via `snd`, and pulling back the outer
pair with `g` composed via `fst`. -/
def presheafPullbackAssocIso
    (f : F ⟶ H) (g : G ⟶ H)
    (f' : G ⟶ H') (g' : K ⟶ H') :
    presheafPullback
      (presheafPullbackSnd f g ≫ f') g' ≅
    presheafPullback
      f (presheafPullbackFst f' g' ≫ g) where
  hom :=
    presheafPullbackLift
      f (presheafPullbackFst f' g' ≫ g)
      (presheafPullbackFst
        (presheafPullbackSnd f g ≫ f') g' ≫
        presheafPullbackFst f g)
      (presheafPullbackLift f' g'
        (presheafPullbackFst
          (presheafPullbackSnd f g ≫ f') g' ≫
          presheafPullbackSnd f g)
        (presheafPullbackSnd
          (presheafPullbackSnd f g ≫ f') g')
        (by
          simp only [Category.assoc]
          exact presheafPullbackCondition
            (presheafPullbackSnd f g ≫ f') g'))
      (by
        simp only [Category.assoc,
          presheafPullbackCondition f g,
          PullbackCone.IsLimit.lift_fst_assoc])
  inv :=
    presheafPullbackLift
      (presheafPullbackSnd f g ≫ f') g'
      (presheafPullbackLift f g
        (presheafPullbackFst
          f (presheafPullbackFst f' g' ≫ g))
        (presheafPullbackSnd
          f (presheafPullbackFst f' g' ≫ g) ≫
          presheafPullbackFst f' g')
        (by
          simp only [Category.assoc]
          exact presheafPullbackCondition
            f (presheafPullbackFst f' g' ≫ g)))
      (presheafPullbackSnd
        f (presheafPullbackFst f' g' ≫ g) ≫
        presheafPullbackSnd f' g')
      (by
        simp only [Category.assoc,
          PullbackCone.IsLimit.lift_snd_assoc,
          presheafPullbackCondition f' g'])
  hom_inv_id := by
    apply PullbackCone.IsLimit.hom_ext
      (presheafPullbackIsLimit ..)
    · apply PullbackCone.IsLimit.hom_ext
        (presheafPullbackIsLimit f g) <;>
      simp only [Category.assoc, Category.id_comp,
        PullbackCone.IsLimit.lift_fst,
        PullbackCone.IsLimit.lift_snd,
        PullbackCone.IsLimit.lift_snd_assoc]
    · simp only [Category.assoc, Category.id_comp,
        PullbackCone.IsLimit.lift_snd,
        PullbackCone.IsLimit.lift_snd_assoc]
  inv_hom_id := by
    apply PullbackCone.IsLimit.hom_ext
      (presheafPullbackIsLimit ..)
    · simp only [Category.assoc, Category.id_comp,
        PullbackCone.IsLimit.lift_fst,
        PullbackCone.IsLimit.lift_fst_assoc]
    · apply PullbackCone.IsLimit.hom_ext
        (presheafPullbackIsLimit f' g') <;>
      simp only [Category.assoc, Category.id_comp,
        PullbackCone.IsLimit.lift_fst,
        PullbackCone.IsLimit.lift_snd,
        PullbackCone.IsLimit.lift_fst_assoc]

@[reassoc (attr := simp)]
theorem presheafPullbackAssocIso_hom_fst
    (f : F ⟶ H) (g : G ⟶ H)
    (f' : G ⟶ H') (g' : K ⟶ H') :
    (presheafPullbackAssocIso f g f' g').hom ≫
      presheafPullbackFst
        f (presheafPullbackFst f' g' ≫ g) =
    presheafPullbackFst
      (presheafPullbackSnd f g ≫ f') g' ≫
      presheafPullbackFst f g := by
  simp [presheafPullbackAssocIso,
    presheafPullbackLift]

@[reassoc (attr := simp)]
theorem presheafPullbackAssocIso_hom_snd_fst
    (f : F ⟶ H) (g : G ⟶ H)
    (f' : G ⟶ H') (g' : K ⟶ H') :
    (presheafPullbackAssocIso f g f' g').hom ≫
      presheafPullbackSnd
        f (presheafPullbackFst f' g' ≫ g) ≫
      presheafPullbackFst f' g' =
    presheafPullbackFst
      (presheafPullbackSnd f g ≫ f') g' ≫
      presheafPullbackSnd f g := by
  simp [presheafPullbackAssocIso,
    presheafPullbackLift]

@[reassoc (attr := simp)]
theorem presheafPullbackAssocIso_hom_snd_snd
    (f : F ⟶ H) (g : G ⟶ H)
    (f' : G ⟶ H') (g' : K ⟶ H') :
    (presheafPullbackAssocIso f g f' g').hom ≫
      presheafPullbackSnd
        f (presheafPullbackFst f' g' ≫ g) ≫
      presheafPullbackSnd f' g' =
    presheafPullbackSnd
      (presheafPullbackSnd f g ≫ f') g' := by
  simp [presheafPullbackAssocIso,
    presheafPullbackLift]

/-- Symmetry of the presheaf pullback:
`pullback f g ≅ pullback g f`. -/
def presheafPullbackSymIso
    (f : F ⟶ H) (g : G ⟶ H) :
    presheafPullback f g ≅
      presheafPullback g f where
  hom :=
    presheafPullbackLift g f
      (presheafPullbackSnd f g)
      (presheafPullbackFst f g)
      (presheafPullbackCondition f g).symm
  inv :=
    presheafPullbackLift f g
      (presheafPullbackSnd g f)
      (presheafPullbackFst g f)
      (presheafPullbackCondition g f).symm
  hom_inv_id := by
    apply PullbackCone.IsLimit.hom_ext
      (presheafPullbackIsLimit f g) <;>
    simp only [Category.id_comp, Category.assoc,
      PullbackCone.IsLimit.lift_fst,
      PullbackCone.IsLimit.lift_snd]
  inv_hom_id := by
    apply PullbackCone.IsLimit.hom_ext
      (presheafPullbackIsLimit g f) <;>
    simp only [Category.id_comp, Category.assoc,
      PullbackCone.IsLimit.lift_fst,
      PullbackCone.IsLimit.lift_snd]

@[reassoc (attr := simp)]
theorem presheafPullbackSymIso_hom_fst
    (f : F ⟶ H) (g : G ⟶ H) :
    (presheafPullbackSymIso f g).hom ≫
      presheafPullbackFst g f =
    presheafPullbackSnd f g := by
  simp only [presheafPullbackSymIso,
    PullbackCone.IsLimit.lift_fst]

@[reassoc (attr := simp)]
theorem presheafPullbackSymIso_hom_snd
    (f : F ⟶ H) (g : G ⟶ H) :
    (presheafPullbackSymIso f g).hom ≫
      presheafPullbackSnd g f =
    presheafPullbackFst f g := by
  simp only [presheafPullbackSymIso,
    PullbackCone.IsLimit.lift_snd]

end PresheafPullback

section PshClassifier

open Limits Opposite

variable (C : Type u) [Category.{v} C]

/-- The sieve presheaf on `C`: sends each `c` to the
type of sieves on `c`, with restriction given by sieve
pullback. -/
def pshSieveFunctor : Cᵒᵖ ⥤ Type (max u v) where
  obj c := Sieve c.unop
  map f S := S.pullback f.unop
  map_id _ := by
    funext S
    exact S.pullback_id
  map_comp f g := by
    funext S
    simp only [unop_comp]
    exact S.pullback_comp

/-- The terminal presheaf: the constant functor
to `PUnit`. -/
def pshTerminal : Cᵒᵖ ⥤ Type (max u v) :=
  (Functor.const Cᵒᵖ).obj PUnit

instance pshTerminalUnique
    (P : Cᵒᵖ ⥤ Type (max u v)) :
    Unique (P ⟶ pshTerminal C) where
  default :=
    { app := fun _ _ => PUnit.unit }
  uniq f := by
    ext T x
    dsimp [pshTerminal]
    exact Subsingleton.elim _ _

/-- `pshTerminal C` is a terminal object. -/
def pshTerminalIsTerminal :
    IsTerminal (pshTerminal C) :=
  IsTerminal.ofUnique _

/-- The truth morphism: sends the unique element
of the terminal presheaf to the maximal sieve at
each stage. -/
def pshSieveTruth :
    pshTerminal C ⟶ pshSieveFunctor C where
  app c _ := (⊤ : Sieve c.unop)
  naturality _ _ _ := by
    funext _
    exact Sieve.pullback_top.symm

/-- The characteristic map of a monomorphism
`m : U ⟶ X` in the presheaf category: at stage
`c`, sends `x : X.obj c` to the sieve of morphisms
along which `x` restricts into the range of `m`. -/
def pshSieveCharMap
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : U ⟶ X) :
    X ⟶ pshSieveFunctor C where
  app c x :=
    (Subfunctor.range m).sieveOfSection x
  naturality c₁ c₂ g := by
    funext x
    apply Sieve.ext
    intro V f
    dsimp [Subfunctor.sieveOfSection,
      Subfunctor.range, pshSieveFunctor]
    simp only [
      FunctorToTypes.map_comp_apply]

variable {C}

/-- The sieve of a section in the range of `m`
is the maximal sieve. -/
theorem pshSieveCharMap_of_range
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : U ⟶ X) (c : Cᵒᵖ) (u : U.obj c) :
    (Subfunctor.range m).sieveOfSection
      (m.app c u) = ⊤ := by
  apply Sieve.ext
  intro V f
  simp only [Sieve.top_apply, iff_true]
  dsimp [Subfunctor.sieveOfSection,
    Subfunctor.range]
  refine ⟨U.map f.op u, ?_⟩
  have := congr_fun (m.naturality f.op) u
  dsimp at this
  exact this

/-- If the sieve of a section equals `⊤`, the section
is in the range of `m` at that stage. -/
theorem pshSieveCharMap_top_mem_range
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : U ⟶ X) (c : Cᵒᵖ) (x : X.obj c)
    (h : (Subfunctor.range m).sieveOfSection x =
      ⊤) :
    x ∈ Set.range (m.app c) := by
  have hmem :
      ((Subfunctor.range m).sieveOfSection x).arrows
        (𝟙 c.unop) := by
    rw [h]
    trivial
  dsimp [Subfunctor.sieveOfSection,
    Subfunctor.range] at hmem
  simp only [FunctorToTypes.map_id_apply] at hmem
  exact hmem

/-- A monomorphism in a presheaf category over `Type`
is pointwise injective. -/
theorem pshMono_app_injective
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : U ⟶ X) [Mono m] (c : Cᵒᵖ) :
    Function.Injective (m.app c) :=
  (mono_iff_injective (m.app c)).mp
    ((NatTrans.mono_iff_mono_app m).mp
      inferInstance c)

/-- The commutativity condition of a pullback cone
implies at each stage that the section is in the range
of `m`. -/
theorem pshSieveConeMemRange
    {U X W : Cᵒᵖ ⥤ Type (max u v)}
    (m : U ⟶ X) (s_fst : W ⟶ X)
    (s_snd : W ⟶ pshTerminal C)
    (cond : s_fst ≫ pshSieveCharMap C m =
      s_snd ≫ pshSieveTruth C)
    (c : Cᵒᵖ) (w : W.obj c) :
    s_fst.app c w ∈ Set.range (m.app c) := by
  apply pshSieveCharMap_top_mem_range
  have := congr_fun (congr_app cond c) w
  dsimp at this
  exact this

/-- The classifier square commutes: `m ≫ χ(m)` equals
the composite through the terminal object and truth. -/
theorem pshClassifierComm
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : U ⟶ X) :
    m ≫ pshSieveCharMap C m =
      (pshTerminalIsTerminal C).from U ≫
        pshSieveTruth C := by
  ext c u
  exact pshSieveCharMap_of_range m c u

/-- The subobject classifier square is a pullback:
the natural transformation `m` is the pullback of
`truth` along `χ(m)`. -/
theorem pshSieveIsPullback
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : U ⟶ X) [Mono m] :
    IsPullback m
      ((pshTerminalIsTerminal C).from U)
      (pshSieveCharMap C m)
      (pshSieveTruth C) where
  w := pshClassifierComm m
  isLimit' := by
    have hmem : ∀ (s : PullbackCone
        (pshSieveCharMap C m) (pshSieveTruth C))
        (c : Cᵒᵖ) (w : s.pt.obj c),
        s.fst.app c w ∈
          Set.range (m.app c) :=
      fun s c w => pshSieveConeMemRange m
        s.fst s.snd s.condition c w
    have hinj := pshMono_app_injective m
    refine ⟨PullbackCone.isLimitAux'
      (PullbackCone.mk m
        ((pshTerminalIsTerminal C).from U)
        (pshClassifierComm m))
      fun s =>
      ⟨{ app := fun c w => (hmem s c w).choose
         naturality := fun c₁ c₂ f => by
           ext w
           apply hinj c₂
           have h1 := (hmem s c₂
             (s.pt.map f w)).choose_spec
           have h2 := (hmem s c₁ w).choose_spec
           have nat_m :=
             congr_fun (m.naturality f)
               ((hmem s c₁ w).choose)
           have nat_s :=
             congr_fun (s.fst.naturality f) w
           dsimp at h1 h2 nat_m nat_s
           change m.app c₂
             ((hmem s c₂
               (s.pt.map f w)).choose) =
             m.app c₂
               (U.map f
                 ((hmem s c₁ w).choose))
           rw [h1, nat_m, h2]
           exact nat_s },
       ?_, ?_, ?_⟩⟩
    · ext c w
      exact (hmem s c w).choose_spec
    · ext c w
      dsimp [pshTerminal]
      exact Subsingleton.elim _ _
    · intro l h₁ _
      ext c w
      apply hinj c
      have h1a :=
        congr_fun (congr_app h₁ c) w
      change m.app c (l.app c w) =
        s.fst.app c w at h1a
      rw [h1a]
      exact (hmem s c w).choose_spec.symm

/-- If `χ'` forms a pullback square with `m`,
`truth`, and the terminal map, and if `χ'.app d y`
equals the maximal sieve, then `y` is in the range
of `m.app d`. -/
theorem pshSieveTopImpliesRange
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : U ⟶ X) [Mono m]
    (χ' : X ⟶ pshSieveFunctor C)
    (hpb : IsPullback m
      ((pshTerminalIsTerminal C).from U)
      χ' (pshSieveTruth C))
    (d : Cᵒᵖ) (y : X.obj d)
    (htop : χ'.app d y =
      (⊤ : Sieve d.unop)) :
    y ∈ Set.range (m.app d) := by
  have hpb_d := hpb.map
    ((evaluation Cᵒᵖ
      (Type (max u v))).obj d)
  have hcond : (fun _ :
      (pshTerminal C).obj d => y) ≫
      χ'.app d =
    (fun _ => PUnit.unit) ≫
      (pshSieveTruth C).app d := by
    ext ⟨⟩
    dsimp [pshSieveTruth]
    exact htop
  obtain ⟨l, hl, _⟩ := hpb_d.exists_lift
    (fun _ : (pshTerminal C).obj d => y)
    (fun _ => PUnit.unit) hcond
  exact ⟨l PUnit.unit,
    congr_fun hl PUnit.unit⟩

/-- The characteristic map of a pullback square
for `truth` is uniquely determined: any `χ'` that
forms a pullback with `m` and `truth` equals
`pshSieveCharMap C m`. -/
theorem pshSieveCharMap_uniq
    {U X : Cᵒᵖ ⥤ Type (max u v)}
    (m : U ⟶ X) [Mono m]
    (χ' : X ⟶ pshSieveFunctor C)
    (hpb : IsPullback m
      ((pshTerminalIsTerminal C).from U)
      χ' (pshSieveTruth C)) :
    χ' = pshSieveCharMap C m := by
  ext d y
  apply Sieve.ext
  intro V f
  dsimp [pshSieveCharMap, Subfunctor.sieveOfSection,
    Subfunctor.range]
  have hnat :=
    congr_fun (χ'.naturality f.op) y
  dsimp [pshSieveFunctor] at hnat
  constructor
  · intro hf
    have htop : (χ'.app d y).pullback f =
        (⊤ : Sieve V) :=
      (Sieve.mem_iff_pullback_eq_top f).mp hf
    rw [← hnat] at htop
    exact pshSieveTopImpliesRange m χ' hpb
      (op V) (X.map f.op y) htop
  · rintro ⟨u, hu⟩
    have hcomm :=
      congr_fun (congr_app hpb.w (op V)) u
    dsimp [pshSieveTruth, pshSieveFunctor]
      at hcomm
    rw [Sieve.mem_iff_pullback_eq_top f]
    rw [← hnat, ← hu]
    exact hcomm

/-- The subobject classifier data for the presheaf
category `Cᵒᵖ ⥤ Type (max u v)`: the sieve functor
as `Ω`, the maximal-sieve map as `truth`, and the
sieve characteristic map as `χ`. -/
def pshClassifierData :
    Classifier (Cᵒᵖ ⥤ Type (max u v)) :=
  Classifier.mkOfTerminalΩ₀
    (pshTerminal C)
    (pshTerminalIsTerminal C)
    (pshSieveFunctor C)
    (pshSieveTruth C)
    (χ := fun m _ => pshSieveCharMap C m)
    (isPullback :=
      fun m _ => pshSieveIsPullback m)
    (uniq :=
      fun m _ χ' hpb =>
        pshSieveCharMap_uniq m χ' hpb)

instance PshClassifier :
    HasClassifier (Cᵒᵖ ⥤ Type (max u v)) :=
  ⟨⟨pshClassifierData⟩⟩

end PshClassifier

section CoPshClassifier

open Limits Opposite

variable (C : Type u) [Category.{v} C]

/-- Precomposition with `opOp C`, mapping functors
on `Cᵒᵖᵒᵖ` to functors on `C`. -/
private abbrev coPshΦ :=
  (Functor.whiskeringLeft C Cᵒᵖᵒᵖ
    (Type (max u v))).obj (opOp C)

/-- Precomposition with `unopUnop C`, mapping
functors on `C` to functors on `Cᵒᵖᵒᵖ`. -/
private abbrev coPshΨ :=
  (Functor.whiskeringLeft Cᵒᵖᵒᵖ C
    (Type (max u v))).obj (unopUnop C)

private def coPshClassifierData :
    Classifier (C ⥤ Type (max u v)) :=
  let c := pshClassifierData (C := Cᵒᵖ)
  let Φ := coPshΦ C
  let Ψ := coPshΨ C
  Classifier.mkOfTerminalΩ₀
    (Φ.obj c.Ω₀)
    (@IsTerminal.ofUnique _ _ (Φ.obj c.Ω₀)
      (fun P => {
        default :=
          { app := fun _ _ => PUnit.unit }
        uniq := fun f => by
          ext d x
          change PUnit.unit = f.app d x
          exact (PUnit.eq_punit _).symm }))
    (Φ.obj c.Ω)
    (Φ.map c.truth)
    (χ := fun m _ => Φ.map (c.χ (Ψ.map m)))
    (isPullback := fun m _ =>
      (c.isPullback (Ψ.map m)).map Φ)
    (uniq := fun m _ χ' hpb => by
      conv_lhs => rw [show χ' = Φ.map (Ψ.map χ')
        from rfl]
      exact congrArg Φ.map
        (c.uniq (Ψ.map m) (hpb.map Ψ)))

/-- The subobject classifier for the copresheaf
category `C ⥤ Type (max u v)`, transferred from
`PshClassifier` on `Cᵒᵖ` via precomposition with the
double-opposite equivalence `opOp C : C ⥤ Cᵒᵖᵒᵖ`. -/
instance CoPshClassifier :
    HasClassifier (C ⥤ Type (max u v)) :=
  ⟨⟨coPshClassifierData C⟩⟩

end CoPshClassifier

section CoyonedaIso

universe w

open Opposite

/--
If a copresheaf `F` is naturally isomorphic to the covariant
hom-functor of `A`, then natural transformations from `F` to
any copresheaf `G` correspond to elements of `G.obj A`.

This composes the bijection `(F ⟶ G) ≃ (coyoneda.obj (op A) ⟶ G)`
induced by the natural isomorphism with the covariant Yoneda
equivalence `(coyoneda.obj (op A) ⟶ G) ≃ G.obj A`.
-/
def coyonedaEquivOfNatIso
    {C : Type u} [Category.{v} C]
    {A : C} {F G : C ⥤ Type v}
    (i : F ≅ coyoneda.obj (op A)) :
    (F ⟶ G) ≃ G.obj A :=
  i.homFromEquiv.trans coyonedaEquiv

/--
Specialization of `coyonedaEquivOfNatIso` to `C = Type v` with
`G` the identity functor: if a copresheaf `F : Type v ⥤ Type v`
is naturally isomorphic to the covariant hom-functor of
`A : Type v`, then natural transformations from `F` to the
identity functor correspond to elements of `A`.
-/
def coyonedaEquivOfNatIsoTypeId
    {A : Type v} {F : Type v ⥤ Type v}
    (i : F ≅ coyoneda.obj (op A)) :
    (F ⟶ 𝟭 (Type v)) ≃ A :=
  coyonedaEquivOfNatIso i

/--
Natural isomorphism version of `coyonedaEquivOfNatIso`.
If a copresheaf `F` is naturally isomorphic to the
covariant hom-functor of `A`, then the representable
functor `G ↦ (F ⟶ G)` on the copresheaf category is
naturally isomorphic to the evaluation functor
`G ↦ G.obj A`.

This lifts `coyonedaEquivOfNatIso` from an object-level
equivalence to a natural isomorphism of functors
`(C ⥤ Type v) ⥤ Type v`, using `curriedCoyonedaLemma`.

The `SmallCategory` constraint (objects and morphisms
in the same universe) is needed so that hom-sets and
evaluation values both lie in `Type v`.
-/
def coyonedaNatIsoOfNatIso
    {C : Type v} [SmallCategory C]
    {A : C} {F : C ⥤ Type v}
    (i : F ≅ coyoneda.obj (op A)) :
    coyoneda.obj (op F) ≅
      (evaluation C (Type v)).obj A :=
  (coyoneda.mapIso i.op).symm ≪≫
    curriedCoyonedaLemma.app A

/--
General-universe natural isomorphism version of
`coyonedaEquivOfNatIso`, analogous to
`largeCurriedCoyonedaLemma`.

When `C : Type u` with `Category.{v} C` and `u ≠ v`,
the hom-type `(F ⟶ G)` lies in `Type (max u v)` while
`G.obj A` lies in `Type v`. The `uliftFunctor` bridges
this gap by lifting evaluation values to
`Type (max u v)`.

For `SmallCategory C` (where `u = v`), use
`coyonedaNatIsoOfNatIso` instead, which avoids the
`ULift` wrapper.
-/
def coyonedaNatIsoOfNatIsoLarge
    {C : Type u} [Category.{v} C]
    {A : C} {F : C ⥤ Type v}
    (i : F ≅ coyoneda.obj (op A)) :
    coyoneda.obj (op F) ≅
      ((evaluation C (Type v)).obj A ⋙
        uliftFunctor.{u}) :=
  (coyoneda.mapIso i.op).symm ≪≫
    largeCurriedCoyonedaLemma.app A

/--
Specialization of `coyonedaNatIsoOfNatIsoLarge` to
`C = Type v`: if a copresheaf
`F : Type v ⥤ Type v` is naturally isomorphic to the
covariant hom-functor of `A : Type v`, then the
representable functor `G ↦ (F ⟶ G)` is naturally
isomorphic to the evaluation-and-lift functor
`G ↦ ULift (G.obj A)`.

Because `Type v` with `Category.{v}` is not a
`SmallCategory` (its objects live in `Type (v + 1)`
while morphisms live in `Type v`), the `ULift` wrapper
is unavoidable in the functorial version.
The object-level `coyonedaEquivOfNatIsoTypeId` avoids
this because `Equiv` is universe-polymorphic.
-/
def coyonedaNatIsoOfNatIsoTypeId
    {A : Type v} {F : Type v ⥤ Type v}
    (i : F ≅ coyoneda.obj (op A)) :
    coyoneda.obj (op F) ≅
      ((evaluation (Type v) (Type v)).obj A ⋙
        uliftFunctor.{v + 1}) :=
  coyonedaNatIsoOfNatIsoLarge i

/--
Natural isomorphism for copresheaves isomorphic to a
universe-lifted covariant hom-functor. Given
`i : F ≅ uliftCoyoneda.{w}.obj (op A)` where
`F : C ⥤ Type (max w v)`, this produces a natural
isomorphism between the representable functor
`G ↦ (F ⟶ G)` and the lifted evaluation functor
`G ↦ ULift (G.obj A)`.

This generalizes `coyonedaNatIsoOfNatIsoLarge` by
allowing the copresheaf target universe to differ from
the morphism universe via `uliftCoyoneda`. The
construction uses `uliftCoyonedaRightOpCompCoyoneda`.
-/
def uliftCoyonedaNatIsoOfNatIso
    {C : Type u} [Category.{v} C]
    {A : C} {F : C ⥤ Type (max w v)}
    (i : F ≅ uliftCoyoneda.{w}.obj (op A)) :
    coyoneda.obj (op F) ≅
      ((evaluation C (Type (max w v))).obj A ⋙
        uliftFunctor.{u}) :=
  (coyoneda.mapIso i.op).symm ≪≫
    uliftCoyonedaRightOpCompCoyoneda.app A

/--
Specialization of `uliftCoyonedaNatIsoOfNatIso` to
`C = Type v`: if `F : Type v ⥤ Type (max w v)` is
naturally isomorphic to the universe-lifted
covariant hom-functor of `A : Type v`, then the
representable functor `G ↦ (F ⟶ G)` is naturally
isomorphic to the lifted evaluation functor
`G ↦ ULift (G.obj A)`.

The domain (`Type v`) and codomain (`Type (max w v)`)
of `F` can live at different universe levels. When
`w ≤ v`, `max w v = v` and this reduces to the
same-universe case of `coyonedaNatIsoOfNatIsoTypeId`.
-/
def uliftCoyonedaNatIsoOfNatIsoTypeId
    {A : Type v}
    {F : Type v ⥤ Type (max w v)}
    (i : F ≅ uliftCoyoneda.{w}.obj (op A)) :
    coyoneda.obj (op F) ≅
      ((evaluation (Type v) (Type (max w v))).obj A ⋙
        uliftFunctor.{v + 1}) :=
  uliftCoyonedaNatIsoOfNatIso i

end CoyonedaIso

/-! ## Yoneda Extension

The left Kan extension of a presheaf along an
endofunctor, computed pointwise as a quotient of
sigma types. Given `F : C ⥤ D` and `P : Cᵒᵖ ⥤ Type v`,
the Yoneda extension `(leftYonedaExt F).obj P` is the
presheaf whose value at `T : Cᵒᵖ` is the colimit

`colim_{(S : C, t : T.unop ⟶ F.obj S)} P.obj (op S)`

computed as a `Quot` of triples `(S, p, t)`. Two
triples are identified when they are connected by a
morphism in `C` making the evident diagrams commute.
-/

/-- The large Yoneda embedding: composes `yoneda`
with `uliftFunctor` to produce presheaves valued in
`Type (max u v)` rather than `Type v`. For
`C = Type v` (where `u = v + 1`), this gives
`(Type v)ᵒᵖ ⥤ Type (v + 1)` presheaves, matching
the presheaf universe of `PshTypeExpr (Type v)`. -/
def yonedaULift {C : Type u} [Category.{v} C] :
    C → (Cᵒᵖ ⥤ Type (max u v)) :=
  fun X => yoneda.obj X ⋙ uliftFunctor.{u}

/-- `yonedaULift X` evaluated at `op Y` gives
`ULift (Y ⟶ X)`. -/
@[simp]
theorem yonedaULift_obj
    {C : Type u} [Category.{v} C]
    (X : C) (Y : Cᵒᵖ) :
    (yonedaULift X).obj Y =
      ULift.{u} (Y.unop ⟶ X) :=
  rfl

/-- Functorial version of `yonedaULift`:
the Yoneda embedding postcomposed with universe
lifting, as a functor `C ⥤ (Cᵒᵖ ⥤ Type (max u v))`.
Satisfies `yonedaLarge.obj X = yonedaULift X`
definitionally. -/
def yonedaLarge (C : Type u) [Category.{v} C] :
    C ⥤ (Cᵒᵖ ⥤ Type (max u v)) :=
  yoneda ⋙
    (Functor.whiskeringRight Cᵒᵖ
      (Type v) (Type (max u v))).obj
      uliftFunctor.{u}

/-- `yonedaLarge.obj X` equals `yonedaULift X`. -/
@[simp]
theorem yonedaLarge_obj
    {C : Type u} [Category.{v} C] (X : C) :
    (yonedaLarge C).obj X = yonedaULift X :=
  rfl

section YonedaExtension

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]

/-- A triple `(S, p, t)` representing a generator
of the Yoneda extension colimit. Here `S : C` is a
witness object, `p : P.obj (op S)` is an element of
the presheaf at `S`, and `t : T.unop ⟶ F.obj S` is
a morphism in `D` factoring through `F`. -/
abbrev LeftYonedaExtSigma
    (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u v))
    (T : Dᵒᵖ) :=
  Σ (S : C), P.obj (Opposite.op S) ×
    (T.unop ⟶ F.obj S)

/-- The identification relation on `LeftYonedaExtSigma`:
`(S₁, p₁, t₁)` is related to `(S₂, p₂, t₂)` if
there exists `g : S₂ ⟶ S₁` such that `P.map g.op`
sends `p₁` to `p₂` and `t₂ ≫ F.map g = t₁`. -/
def LeftYonedaExtStep
    (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u v))
    (T : Dᵒᵖ)
    (x y : LeftYonedaExtSigma F P T) : Prop :=
  ∃ (g : y.1 ⟶ x.1),
    P.map g.op x.2.1 = y.2.1 ∧
    y.2.2 ≫ F.map g = x.2.2

/-- Transport a triple along a morphism
`k : T₁ ⟶ T₂` in `Cᵒᵖ` (i.e., `T₂.unop ⟶ T₁.unop`
in `C`). The witness `S` and element `p` are
unchanged; the morphism `t` is precomposed with
`k.unop`. -/
def leftYonedaExtSigmaMap
    (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u v))
    {T₁ T₂ : Dᵒᵖ} (k : T₁ ⟶ T₂)
    (x : LeftYonedaExtSigma F P T₁) :
    LeftYonedaExtSigma F P T₂ :=
  ⟨x.1, x.2.1, k.unop ≫ x.2.2⟩

/-- `leftYonedaExtSigmaMap` preserves the step
relation. -/
theorem leftYonedaExtSigmaMap_step
    (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u v))
    {T₁ T₂ : Dᵒᵖ} (k : T₁ ⟶ T₂)
    {x y : LeftYonedaExtSigma F P T₁}
    (h : LeftYonedaExtStep F P T₁ x y) :
    LeftYonedaExtStep F P T₂
      (leftYonedaExtSigmaMap F P k x)
      (leftYonedaExtSigmaMap F P k y) := by
  obtain ⟨g, hp, ht⟩ := h
  exact ⟨g, hp, by
    dsimp [leftYonedaExtSigmaMap]
    rw [Category.assoc, ht]⟩

/-- The Yoneda extension presheaf. At stage `T`,
an element is an equivalence class of triples
`(S, p, t)` under the identification relation. -/
def leftYonedaExtObj
    (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u v)) :
    Dᵒᵖ ⥤ Type (max u v) where
  obj T := Quot (LeftYonedaExtStep F P T)
  map k := Quot.map
    (leftYonedaExtSigmaMap F P k)
    (fun _ _ => leftYonedaExtSigmaMap_step F P k)
  map_id T := by
    funext q; induction q using Quot.inductionOn
    rename_i x
    change Quot.mk _
        (leftYonedaExtSigmaMap F P (𝟙 T) x)
      = Quot.mk _ x
    congr 1
    simp [leftYonedaExtSigmaMap, Category.id_comp]
  map_comp k₁ k₂ := by
    funext q; induction q using Quot.inductionOn
    rename_i x
    change Quot.mk _
        (leftYonedaExtSigmaMap F P (k₁ ≫ k₂) x)
      = Quot.mk _
        (leftYonedaExtSigmaMap F P k₂
          (leftYonedaExtSigmaMap F P k₁ x))
    congr 1
    simp [leftYonedaExtSigmaMap, Category.assoc]

/-- The action of a natural transformation
`α : P ⟶ Q` on a single triple: apply `α` to the
element component, leaving the witness object and
morphism unchanged. -/
def leftYonedaExtSigmaMapNat
    (F : C ⥤ D)
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ Q) (T : Dᵒᵖ)
    (x : LeftYonedaExtSigma F P T) :
    LeftYonedaExtSigma F Q T :=
  ⟨x.1, α.app (Opposite.op x.1) x.2.1, x.2.2⟩

/-- `leftYonedaExtSigmaMapNat` preserves the step
relation. -/
theorem leftYonedaExtSigmaMapNat_step
    (F : C ⥤ D)
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ Q) (T : Dᵒᵖ)
    {x y : LeftYonedaExtSigma F P T}
    (h : LeftYonedaExtStep F P T x y) :
    LeftYonedaExtStep F Q T
      (leftYonedaExtSigmaMapNat F α T x)
      (leftYonedaExtSigmaMapNat F α T y) := by
  obtain ⟨g, hp, ht⟩ := h
  refine ⟨g, ?_, ht⟩
  dsimp [leftYonedaExtSigmaMapNat]
  rw [← hp]
  exact (congr_fun (α.naturality g.op) x.2.1).symm

/-- The map component of the Yoneda extension
functor: given `α : P ⟶ Q`, produce a natural
transformation `leftYonedaExtObj F P ⟶ leftYonedaExtObj F Q`
by applying `α` to the element component of each
triple. -/
def leftYonedaExtMap
    (F : C ⥤ D)
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ Q) :
    leftYonedaExtObj F P ⟶ leftYonedaExtObj F Q where
  app T := Quot.map
    (leftYonedaExtSigmaMapNat F α T)
    (fun _ _ =>
      leftYonedaExtSigmaMapNat_step F α T)
  naturality T₁ T₂ k := by
    funext q; induction q using Quot.inductionOn
    rfl

/-- The Yoneda extension functor: given a
functor `F : C ⥤ D`, produces a functor between
presheaf categories. This is the left Kan extension
`Lan_{F.op}`, computed pointwise as a colimit of
sigma types. -/
def leftYonedaExt (F : C ⥤ D) :
    (Cᵒᵖ ⥤ Type (max u v)) ⥤
      (Dᵒᵖ ⥤ Type (max u v)) where
  obj P := leftYonedaExtObj F P
  map α := leftYonedaExtMap F α
  map_id P := by
    ext T q; induction q using Quot.inductionOn
    rfl
  map_comp α β := by
    ext T q; induction q using Quot.inductionOn
    rfl

/-- Map a `LeftYonedaExtSigma` triple along a natural
transformation `α : F ⟶ G` by postcomposing the
morphism component with `α.app`. -/
def leftYonedaExtSigmaAlpha
    {F G : C ⥤ D} (α : F ⟶ G)
    (P : Cᵒᵖ ⥤ Type (max u v)) (T : Dᵒᵖ)
    (x : LeftYonedaExtSigma F P T) :
    LeftYonedaExtSigma G P T :=
  ⟨x.1, x.2.1, x.2.2 ≫ α.app x.1⟩

/-- `leftYonedaExtSigmaAlpha` preserves the step
relation. -/
theorem leftYonedaExtSigmaAlpha_step
    {F G : C ⥤ D} (α : F ⟶ G)
    (P : Cᵒᵖ ⥤ Type (max u v)) (T : Dᵒᵖ)
    {x y : LeftYonedaExtSigma F P T}
    (h : LeftYonedaExtStep F P T x y) :
    LeftYonedaExtStep G P T
      (leftYonedaExtSigmaAlpha α P T x)
      (leftYonedaExtSigmaAlpha α P T y) := by
  obtain ⟨g, hp, ht⟩ := h
  exact ⟨g, hp, by
    dsimp [leftYonedaExtSigmaAlpha]
    rw [Category.assoc,
      ← α.naturality g,
      ← Category.assoc, ht]⟩

/-- The Yoneda extension as a functor from
`(C ⥤ D)` to presheaf functor categories.
On objects, this is `leftYonedaExt`. On morphisms, a
natural transformation `α : F ⟶ G` induces a
map by postcomposing the morphism component of
each triple with `α`. -/
def leftYonedaExtFunctor :
    (C ⥤ D) ⥤
      ((Cᵒᵖ ⥤ Type (max u v)) ⥤
        (Dᵒᵖ ⥤ Type (max u v))) where
  obj := leftYonedaExt
  map {F G} α :=
    { app := fun P =>
        { app := fun T =>
            Quot.map
              (leftYonedaExtSigmaAlpha α P T)
              (fun _ _ h =>
                leftYonedaExtSigmaAlpha_step
                  α P T h)
          naturality := fun T₁ T₂ k => by
            funext q
            induction q using Quot.inductionOn
            rename_i x
            change Quot.mk _ _ = Quot.mk _ _
            congr 1
            dsimp [leftYonedaExtSigmaAlpha,
              leftYonedaExtSigmaMap]
            simp only [Category.assoc] }
      naturality := fun P Q β => by
        ext T q
        induction q using Quot.inductionOn
        rfl }
  map_id F := by
    ext P T q
    induction q using Quot.inductionOn
    rename_i x
    change Quot.mk _ _ = Quot.mk _ _
    congr 1
    dsimp [leftYonedaExtSigmaAlpha]
    simp only [Category.comp_id]
  map_comp {F G H} α β := by
    ext P T q
    induction q using Quot.inductionOn
    rename_i x
    change Quot.mk _ _ = Quot.mk _ _
    congr 1
    dsimp [leftYonedaExtSigmaAlpha]
    simp only [Category.assoc]

/-- The counit of the Yoneda extension at a
large-Yoneda representable presheaf: maps
`(leftYonedaExt F).obj (yonedaULift X)` to
`yonedaULift (F.obj X)`. Sends a triple
`(S, ⟨f⟩, t)` to `⟨t ≫ F.map f⟩`. -/
def leftYonedaExtCounitULift (F : C ⥤ D) (X : C) :
    (leftYonedaExt F).obj (yonedaULift X) ⟶
      yonedaULift (F.obj X) where
  app T := Quot.lift
    (fun x => ⟨x.2.2 ≫ F.map x.2.1.down⟩)
    (fun x y ⟨g, hp, ht⟩ => by
      have hp' : g ≫ x.2.1.down = y.2.1.down :=
        congrArg ULift.down hp
      change (⟨x.2.2 ≫ F.map x.2.1.down⟩ :
        ULift.{u} _) =
          ⟨y.2.2 ≫ F.map y.2.1.down⟩
      congr 1
      rw [← ht, Category.assoc,
        ← F.map_comp, hp'])
  naturality T₁ T₂ k := by
    funext q; induction q using Quot.inductionOn
    rename_i x
    exact ULift.ext _ _ (Category.assoc _ _ _)

/-- The unit of the Yoneda extension at a
large-Yoneda representable presheaf: embeds
`yonedaULift (F.obj X)` into
`(leftYonedaExt F).obj (yonedaULift X)`. Sends
`⟨t⟩` to the equivalence class of
`(X, ⟨𝟙 X⟩, t)`. -/
def leftYonedaExtUnitULift (F : C ⥤ D) (X : C) :
    yonedaULift (F.obj X) ⟶
      (leftYonedaExt F).obj (yonedaULift X) where
  app T t := Quot.mk _ ⟨X, ⟨𝟙 X⟩, t.down⟩
  naturality T₁ T₂ k := by
    funext t; rfl

/-- `leftYonedaExtUnitULift ≫ leftYonedaExtCounitULift = 𝟙`.
Each `⟨t⟩` maps to `(X, ⟨𝟙 X⟩, t)` then to
`⟨t ≫ F.map (𝟙 X)⟩ = ⟨t⟩`. -/
theorem leftYonedaExtUnitULift_counit
    (F : C ⥤ D) (X : C) :
    leftYonedaExtUnitULift F X ≫
      leftYonedaExtCounitULift F X =
        𝟙 (yonedaULift (F.obj X)) := by
  ext T t
  change (⟨t.down ≫ F.map (𝟙 X)⟩ :
    ULift.{u} _) = t
  simp [ULift.ext_iff]

/-- `leftYonedaExtCounitULift ≫ leftYonedaExtUnitULift = 𝟙`.
Each triple `(S, ⟨f⟩, t)` maps to
`⟨t ≫ F.map f⟩` then to `(X, ⟨𝟙 X⟩, t ≫ F.map f)`,
which is identified with `(S, ⟨f⟩, t)` via `f`. -/
theorem leftYonedaExtCounitULift_unit
    (F : C ⥤ D) (X : C) :
    leftYonedaExtCounitULift F X ≫
      leftYonedaExtUnitULift F X =
        𝟙 ((leftYonedaExt F).obj (yonedaULift X)) := by
  ext T q; induction q using Quot.inductionOn
  rename_i x
  change Quot.mk _
      ⟨X, ⟨𝟙 X⟩, x.2.2 ≫ F.map x.2.1.down⟩
    = Quot.mk _ x
  exact Quot.sound ⟨x.2.1.down, by
    simp [yonedaULift, uliftFunctor], by simp⟩

/-- The Yoneda extension at a large-Yoneda
representable presheaf `yonedaULift X` is
isomorphic to `yonedaULift (F.obj X)`. This
generalizes `leftYonedaExtRepresentableIso` from
the small-category case. -/
def leftYonedaExtRepresentableULiftIso
    (F : C ⥤ D) (X : C) :
    (leftYonedaExt F).obj (yonedaULift X) ≅
      yonedaULift (F.obj X) where
  hom := leftYonedaExtCounitULift F X
  inv := leftYonedaExtUnitULift F X
  hom_inv_id := leftYonedaExtCounitULift_unit F X
  inv_hom_id := leftYonedaExtUnitULift_counit F X

end YonedaExtension

section YonedaExtensionKan

variable {C : Type v} [Category.{v} C]
variable {D : Type v} [Category.{v} D]

/-- The unit of the Yoneda extension at a
representable presheaf: embeds `yoneda.obj (F.obj X)`
into `(leftYonedaExt F).obj (yoneda.obj X)` by sending
a morphism `t : T.unop ⟶ F.obj X` to the
equivalence class of `(X, 𝟙 X, t)`. -/
def leftYonedaExtUnit (F : C ⥤ D) (X : C) :
    yoneda.obj (F.obj X) ⟶
      (leftYonedaExt F).obj (yoneda.obj X) where
  app T t :=
    Quot.mk _ ⟨X, 𝟙 X, t⟩
  naturality T₁ T₂ k := by
    funext t; rfl

/-- The counit (inverse) of the Yoneda extension at
a representable presheaf: maps
`(leftYonedaExt F).obj (yoneda.obj X)` back to
`yoneda.obj (F.obj X)` by sending `(S, f, t)` to
`t ≫ F.map f`. -/
def leftYonedaExtCounit (F : C ⥤ D) (X : C) :
    (leftYonedaExt F).obj (yoneda.obj X) ⟶
      yoneda.obj (F.obj X) where
  app T := Quot.lift
    (fun x => x.2.2 ≫ F.map x.2.1)
    (fun x y ⟨g, hp, ht⟩ => by
      dsimp
      rw [← ht, Category.assoc]
      congr 1
      rw [← F.map_comp]
      exact congr_arg F.map hp)
  naturality T₁ T₂ k := by
    funext q; induction q using Quot.inductionOn
    rename_i x
    change (k.unop ≫ x.2.2) ≫ F.map x.2.1
      = k.unop ≫ x.2.2 ≫ F.map x.2.1
    simp only [Category.assoc]

/-- The composition `leftYonedaExtUnit ≫ leftYonedaExtCounit`
is the identity on `yoneda.obj (F.obj X)`. Each
morphism `t` is sent to `(X, 𝟙 X, t)` then to
`t ≫ F.map (𝟙 X) = t`. -/
theorem leftYonedaExtUnit_counit
    (F : C ⥤ D) (X : C) :
    leftYonedaExtUnit F X ≫ leftYonedaExtCounit F X =
      𝟙 (yoneda.obj (F.obj X)) := by
  ext T t
  change t ≫ F.map (𝟙 X) = t
  simp

/-- The composition `leftYonedaExtCounit ≫ leftYonedaExtUnit`
is the identity on
`(leftYonedaExt F).obj (yoneda.obj X)`. Each triple
`(S, f, t)` is sent to `t ≫ F.map f` then to
`(X, 𝟙 X, t ≫ F.map f)`, which is identified with
`(S, f, t)` via the morphism `f : S ⟶ X`. -/
theorem leftYonedaExtCounit_unit
    (F : C ⥤ D) (X : C) :
    leftYonedaExtCounit F X ≫ leftYonedaExtUnit F X =
      𝟙 ((leftYonedaExt F).obj (yoneda.obj X)) := by
  ext T q; induction q using Quot.inductionOn
  rename_i x
  change Quot.mk _
      ⟨X, 𝟙 X, x.2.2 ≫ F.map x.2.1⟩
    = Quot.mk _ x
  exact Quot.sound ⟨x.2.1, by
    simp [yoneda], by simp⟩

/-- The Yoneda extension at a representable presheaf
`yoneda.obj X` is isomorphic to
`yoneda.obj (F.obj X)`. -/
def leftYonedaExtRepresentableIso
    (F : C ⥤ D) (X : C) :
    (leftYonedaExt F).obj (yoneda.obj X) ≅
      yoneda.obj (F.obj X) where
  hom := leftYonedaExtCounit F X
  inv := leftYonedaExtUnit F X
  hom_inv_id := leftYonedaExtCounit_unit F X
  inv_hom_id := leftYonedaExtUnit_counit F X

/-- The unit of the Yoneda extension as a natural
transformation from `F ⋙ yoneda` to
`yoneda ⋙ leftYonedaExt F`. At each `X : C`, this is
`leftYonedaExtUnit F X`. -/
def leftYonedaExtUnitNatTrans (F : C ⥤ D) :
    F ⋙ yoneda ⟶
      yoneda ⋙ leftYonedaExt F where
  app X := leftYonedaExtUnit F X
  naturality X Y g := by
    ext T t
    change Quot.mk
        (LeftYonedaExtStep F (yoneda.obj Y) T)
        ⟨Y, 𝟙 Y, t ≫ F.map g⟩
      = Quot.mk
        (LeftYonedaExtStep F (yoneda.obj Y) T)
        ⟨X, (yoneda.map g).app
          (Opposite.op X) (𝟙 X), t⟩
    exact Quot.sound ⟨g, by
      simp [yoneda_map_app], rfl⟩

/-- The pointwise action of the descent map on a
single triple `(S, p, t)`. Sends it to the element
`(G.map (yonedaEquiv.symm p)).app T (β_S(t))` of
`(G.obj P).obj T`. -/
def leftYonedaExtDescTriple (F : C ⥤ D)
    {G : (Cᵒᵖ ⥤ Type v) ⥤ (Dᵒᵖ ⥤ Type v)}
    (β : F ⋙ yoneda ⟶ yoneda ⋙ G)
    (P : Cᵒᵖ ⥤ Type v) (T : Dᵒᵖ)
    (x : LeftYonedaExtSigma F P T) :
    (G.obj P).obj T :=
  (G.map (yonedaEquiv.symm x.2.1)).app T
    ((β.app x.1).app T x.2.2)

/-- `leftYonedaExtDescTriple` respects the identification
relation: identified triples map to the same
element. -/
theorem leftYonedaExtDescTriple_step (F : C ⥤ D)
    {G : (Cᵒᵖ ⥤ Type v) ⥤ (Dᵒᵖ ⥤ Type v)}
    (β : F ⋙ yoneda ⟶ yoneda ⋙ G)
    (P : Cᵒᵖ ⥤ Type v) (T : Dᵒᵖ)
    {x y : LeftYonedaExtSigma F P T}
    (h : LeftYonedaExtStep F P T x y) :
    leftYonedaExtDescTriple F β P T x =
      leftYonedaExtDescTriple F β P T y := by
  obtain ⟨g, hp, ht⟩ := h
  dsimp [leftYonedaExtDescTriple]
  rw [← ht]
  have nat_β :=
    congr_fun (congr_app (β.naturality g) T)
      y.2.2
  dsimp [yoneda_map_app] at nat_β
  rw [nat_β]
  have hp' : yoneda.map g ≫
      yonedaEquiv.symm x.2.1 =
      yonedaEquiv.symm y.2.1 := by
    ext T' t
    change P.map (t ≫ g).op x.2.1 =
      P.map t.op y.2.1
    rw [op_comp, P.map_comp]
    change P.map t.op (P.map g.op x.2.1) = _
    rw [hp]
  change ((G.map (yoneda.map g) ≫
    G.map (yonedaEquiv.symm x.2.1)).app T)
    ((β.app y.1).app T y.2.2) = _
  rw [← G.map_comp, hp']

/-- The descent map from `leftYonedaExt F` to `G` induced
by `β : F ⋙ yoneda ⟶ yoneda ⋙ G`. For each presheaf
`P` and `T : Dᵒᵖ`, the map sends the equivalence class
of `(S, p, t)` to `(G.map (yonedaEquiv.symm p)).app T
((β.app S).app T t)`. -/
def leftYonedaExtDesc (F : C ⥤ D)
    {G : (Cᵒᵖ ⥤ Type v) ⥤ (Dᵒᵖ ⥤ Type v)}
    (β : F ⋙ yoneda ⟶ yoneda ⋙ G) :
    leftYonedaExt F ⟶ G where
  app P :=
    { app := fun T =>
        Quot.lift
          (leftYonedaExtDescTriple F β P T)
          (fun _ _ h =>
            leftYonedaExtDescTriple_step F β P T h)
      naturality := fun T₁ T₂ k => by
        funext q
        induction q using Quot.inductionOn
        rename_i x
        change leftYonedaExtDescTriple F β P T₂
            ⟨x.1, x.2.1, k.unop ≫ x.2.2⟩ =
          (G.obj P).map k
            (leftYonedaExtDescTriple F β P T₁ x)
        dsimp only [leftYonedaExtDescTriple]
        have := congr_fun
          ((β.app x.1 ≫ G.map
            (yonedaEquiv.symm x.2.1)
            ).naturality k) x.2.2
        dsimp at this ⊢
        exact this }
  naturality P Q α := by
    ext T q
    induction q using Quot.inductionOn
    rename_i x
    change leftYonedaExtDescTriple F β Q T
        ⟨x.1, α.app (Opposite.op x.1)
          x.2.1, x.2.2⟩ =
      (G.map α).app T
        (leftYonedaExtDescTriple F β P T x)
    dsimp [leftYonedaExtDescTriple]
    have comm :
        yonedaEquiv.symm
          (α.app (Opposite.op x.1) x.2.1)
        = yonedaEquiv.symm x.2.1 ≫ α := by
      apply yonedaEquiv.injective
      simp [yonedaEquiv_comp]
    rw [comm, G.map_comp]
    rfl

/-- The descent map factorizes through the unit:
`leftYonedaExtUnitNatTrans F ≫ Functor.whiskerLeft
yoneda (leftYonedaExtDesc F β) = β`. -/
theorem leftYonedaExtDesc_fac (F : C ⥤ D)
    {G : (Cᵒᵖ ⥤ Type v) ⥤ (Dᵒᵖ ⥤ Type v)}
    (β : F ⋙ yoneda ⟶ yoneda ⋙ G) :
    leftYonedaExtUnitNatTrans F ≫
      Functor.whiskerLeft yoneda
        (leftYonedaExtDesc F β) = β := by
  ext X T t
  change leftYonedaExtDescTriple F β
      (yoneda.obj X) T ⟨X, 𝟙 X, t⟩ =
    (β.app X).app T t
  dsimp only [leftYonedaExtDescTriple]
  have h : (yonedaEquiv (F := yoneda.obj X)
      ).symm (𝟙 X) = 𝟙 (yoneda.obj X) := by
    rw [← yonedaEquiv_yoneda_map (𝟙 X),
      Equiv.symm_apply_apply]
    exact yoneda.map_id X
  rw [h, G.map_id]
  rfl

/-- The descent map is the unique natural
transformation factorizing through the unit. -/
theorem leftYonedaExtDesc_uniq (F : C ⥤ D)
    {G : (Cᵒᵖ ⥤ Type v) ⥤ (Dᵒᵖ ⥤ Type v)}
    (β : F ⋙ yoneda ⟶ yoneda ⋙ G)
    (σ : leftYonedaExt F ⟶ G)
    (hσ : leftYonedaExtUnitNatTrans F ≫
      Functor.whiskerLeft yoneda σ = β) :
    σ = leftYonedaExtDesc F β := by
  ext P T q
  induction q using Quot.inductionOn
  rename_i x
  change (σ.app P).app T (Quot.mk _ x) =
    leftYonedaExtDescTriple F β P T x
  dsimp only [leftYonedaExtDescTriple]
  have himg : Quot.mk (LeftYonedaExtStep F P T) x =
      ((leftYonedaExt F).map
        (yonedaEquiv.symm x.2.1)).app T
        (Quot.mk _ ⟨x.1, 𝟙 x.1, x.2.2⟩) := by
    change _ = Quot.mk _
      (⟨x.1, (yonedaEquiv.symm x.2.1).app
        (Opposite.op x.1) (𝟙 x.1),
        x.2.2⟩ : LeftYonedaExtSigma F P T)
    have h : (yonedaEquiv.symm x.2.1).app
        (Opposite.op x.1) (𝟙 x.1) = x.2.1 :=
      congr_fun (P.map_id _) x.2.1
    rw [h]
  rw [himg]
  have hnat := congr_fun (congr_app
      (σ.naturality
        (yonedaEquiv.symm x.2.1)) T)
    (Quot.mk _ ⟨x.1, 𝟙 x.1, x.2.2⟩)
  dsimp at hnat ⊢
  rw [hnat]
  have hfac := congr_fun
    (congr_app (congr_app hσ x.1) T) x.2.2
  change (σ.app (yoneda.obj x.1)).app T
    (Quot.mk _ ⟨x.1, 𝟙 x.1, x.2.2⟩) =
    (β.app x.1).app T x.2.2 at hfac
  exact congrArg
    ((G.map (yonedaEquiv.symm x.2.1)).app T)
    hfac

instance leftYonedaExtLeftExtUnique (F : C ⥤ D)
    (s : Functor.LeftExtension yoneda
      (F ⋙ yoneda)) :
    Unique (Functor.LeftExtension.mk
      (leftYonedaExt F)
      (leftYonedaExtUnitNatTrans F) ⟶ s) where
  default := StructuredArrow.homMk
    (leftYonedaExtDesc F s.hom)
    (leftYonedaExtDesc_fac F s.hom)
  uniq f := by
    apply StructuredArrow.ext
    exact leftYonedaExtDesc_uniq F s.hom
      f.right (StructuredArrow.w f)

/-- The Yoneda extension is a left Kan extension
of `F ⋙ yoneda` along `yoneda`. -/
instance leftYonedaExt_isLeftKanExtension
    (F : C ⥤ D) :
    (leftYonedaExt F).IsLeftKanExtension
      (leftYonedaExtUnitNatTrans F) where
  nonempty_isUniversal :=
    ⟨Limits.IsInitial.ofUnique
      (X := Functor.LeftExtension.mk
        (leftYonedaExt F)
        (leftYonedaExtUnitNatTrans F))⟩

end YonedaExtensionKan

/-! ## Right Yoneda Extension

The right Kan extension of a presheaf along a
functor, computed pointwise as a subtype of a
product. Given `F : C ⥤ D` and
`P : Cᵒᵖ ⥤ Type (max u v)`, the right Yoneda
extension `(rightYonedaExt F).obj P` is the
presheaf whose value at `T : Dᵒᵖ` is the end

`∫_{S : C} (F.obj S ⟶ T.unop) → P.obj (op S)`

computed as a subtype of the product, consisting
of families natural in `S`.

Together with `leftYonedaExt F` (the left Kan
extension) and precomposition with `F.op`, these
form an adjoint triple:

`leftYonedaExt F ⊣ precompOp F ⊣ rightYonedaExt F`
-/

section RightYonedaExtension

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]

/-- A natural family for the right Yoneda
extension: for each `S : C` and
`t : F.obj S ⟶ T.unop`, an element of
`P.obj (op S)`, satisfying a naturality condition
in `S`. -/
structure RightYonedaExtFamily
    (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u v))
    (T : Dᵒᵖ) where
  family :
    (S : C) → (F.obj S ⟶ T.unop) →
      P.obj (Opposite.op S)
  naturality :
    ∀ {S₁ S₂ : C} (g : S₂ ⟶ S₁)
      (t : F.obj S₁ ⟶ T.unop),
      P.map g.op (family S₁ t) =
        family S₂ (F.map g ≫ t)

@[ext]
theorem RightYonedaExtFamily.ext'
    {F : C ⥤ D}
    {P : Cᵒᵖ ⥤ Type (max u v)}
    {T : Dᵒᵖ}
    {x y : RightYonedaExtFamily F P T}
    (h : ∀ (S : C) (t : F.obj S ⟶ T.unop),
      x.family S t = y.family S t) :
    x = y := by
  cases x; cases y
  congr 1
  funext S t
  exact h S t

/-- Transport a `RightYonedaExtFamily` along a
morphism `k : T₁ ⟶ T₂` in `Dᵒᵖ` by precomposing
the morphism argument with `k.unop`. -/
def rightYonedaExtFamilyMap
    (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u v))
    {T₁ T₂ : Dᵒᵖ} (k : T₁ ⟶ T₂)
    (x : RightYonedaExtFamily F P T₁) :
    RightYonedaExtFamily F P T₂ where
  family S t := x.family S (t ≫ k.unop)
  naturality g t := by
    rw [x.naturality g (t ≫ k.unop)]
    congr 1
    exact (Category.assoc _ _ _).symm

/-- The right Yoneda extension presheaf. At
stage `T`, an element is a natural family
indexed by `(S : C, t : F.obj S ⟶ T.unop)`. -/
def rightYonedaExtObj
    (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u v)) :
    Dᵒᵖ ⥤ Type (max u v) where
  obj T := RightYonedaExtFamily F P T
  map k := rightYonedaExtFamilyMap F P k
  map_id T := by
    funext x
    apply RightYonedaExtFamily.ext'
    intro S t
    dsimp [rightYonedaExtFamilyMap]
    congr 1
    exact Category.comp_id _
  map_comp k₁ k₂ := by
    funext x
    apply RightYonedaExtFamily.ext'
    intro S t
    dsimp [rightYonedaExtFamilyMap]
    congr 1
    exact (Category.assoc _ _ _).symm

/-- The action of a natural transformation
`α : P ⟶ Q` on a single family: apply `α` to
each element, leaving the witness object and
morphism unchanged. -/
def rightYonedaExtFamilyMapNat
    (F : C ⥤ D)
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ Q) (T : Dᵒᵖ)
    (x : RightYonedaExtFamily F P T) :
    RightYonedaExtFamily F Q T where
  family S t := α.app (Opposite.op S) (x.family S t)
  naturality g t := by
    have hα := congr_fun
      (α.naturality g.op) (x.family _ t)
    simp only [types_comp_apply] at hα
    rw [← hα, x.naturality g t]

/-- The map component of the right Yoneda
extension functor: given `α : P ⟶ Q`, produce a
natural transformation
`rightYonedaExtObj F P ⟶ rightYonedaExtObj F Q`
by applying `α` to the element component of each
family member. -/
def rightYonedaExtMap
    (F : C ⥤ D)
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ Q) :
    rightYonedaExtObj F P ⟶
      rightYonedaExtObj F Q where
  app T := rightYonedaExtFamilyMapNat F α T
  naturality T₁ T₂ k := by
    funext x
    apply RightYonedaExtFamily.ext'
    intro S t
    rfl

/-- The right Yoneda extension functor: given a
functor `F : C ⥤ D`, produces a functor between
presheaf categories. This is the right Kan
extension `Ran_{F.op}`, computed pointwise as an
end (subtype of a product). -/
def rightYonedaExt (F : C ⥤ D) :
    (Cᵒᵖ ⥤ Type (max u v)) ⥤
      (Dᵒᵖ ⥤ Type (max u v)) where
  obj P := rightYonedaExtObj F P
  map α := rightYonedaExtMap F α
  map_id P := by
    ext T x
    rfl
  map_comp α β := by
    ext T x
    rfl


/-- The action of a natural transformation
`α : F ⟶ G` on a right Yoneda extension
family: precomposes each index morphism
`t : G.obj S ⟶ T.unop` with `α.app S` to
get `F.obj S ⟶ T.unop`, then evaluates the
original family. -/
def rightYonedaExtFamilyAlpha
    {F G : C ⥤ D} (α : F ⟶ G)
    (P : Cᵒᵖ ⥤ Type (max u v))
    (T : Dᵒᵖ)
    (x : RightYonedaExtFamily F P T) :
    RightYonedaExtFamily G P T where
  family S t := x.family S (α.app S ≫ t)
  naturality {S₁ S₂} g t := by
    rw [x.naturality g (α.app S₁ ≫ t)]
    congr 1
    simp only [← Category.assoc,
      α.naturality]

/-- The action of `α : F ⟶ G` on families
preserves transport along `k`: precomposing
with `α` commutes with transport. -/
theorem rightYonedaExtFamilyAlpha_map
    {F G : C ⥤ D} (α : F ⟶ G)
    (P : Cᵒᵖ ⥤ Type (max u v))
    {T₁ T₂ : Dᵒᵖ} (k : T₁ ⟶ T₂)
    (x : RightYonedaExtFamily F P T₁) :
    rightYonedaExtFamilyAlpha α P T₂
      (rightYonedaExtFamilyMap F P k x) =
    rightYonedaExtFamilyMap G P k
      (rightYonedaExtFamilyAlpha α P T₁ x) :=
  by
  apply RightYonedaExtFamily.ext'
  intro S t
  dsimp [rightYonedaExtFamilyAlpha,
    rightYonedaExtFamilyMap]
  congr 1
  exact Category.assoc
    (α.app S) t k.unop

/-- The right Yoneda extension functor:
given a functor `F : C ⥤ D`, produces a
functor between presheaf categories via
right Kan extension. On objects, this is
`rightYonedaExt`. On morphisms, a natural
transformation `α : F ⟶ G` induces a map
by precomposing each family's index
morphism with `α`. -/
def rightYonedaExtFunctor :
    (C ⥤ D) ⥤
      ((Cᵒᵖ ⥤ Type (max u v)) ⥤
        (Dᵒᵖ ⥤ Type (max u v))) where
  obj := rightYonedaExt
  map {F G} α :=
    { app := fun P =>
        { app := fun T =>
            rightYonedaExtFamilyAlpha α P T
          naturality := fun T₁ T₂ k => by
            funext x
            exact rightYonedaExtFamilyAlpha_map
              α P k x }
      naturality := fun P Q β => by
        ext T x
        apply RightYonedaExtFamily.ext'
        intro S t
        rfl }
  map_id F := by
    ext P T x
    apply RightYonedaExtFamily.ext'
    intro S t
    dsimp [rightYonedaExtFamilyAlpha]
    simp only [Category.id_comp]
  map_comp {F G H} α β := by
    ext P T x
    apply RightYonedaExtFamily.ext'
    intro S t
    dsimp [rightYonedaExtFamilyAlpha]
    simp only [Category.assoc]

/-- The counit of the right Yoneda extension at
a fixed presheaf `P`:
`F.op ⋙ (rightYonedaExt F).obj P ⟶ P`.
At each `c : Cᵒᵖ`, evaluates a natural family
at `S = c.unop` and `t = 𝟙 (F.obj c.unop)`. -/
def rightYonedaExtCounit
    (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u v)) :
    F.op ⋙ (rightYonedaExt F).obj P ⟶ P where
  app c x :=
    x.family c.unop (𝟙 (F.obj c.unop))
  naturality {c d} g := by
    funext x
    dsimp [rightYonedaExt, rightYonedaExtObj,
      rightYonedaExtFamilyMap]
    simp only [Category.id_comp]
    have h := x.naturality g.unop
      (𝟙 (F.obj c.unop))
    simp only [Category.comp_id] at h
    exact h.symm

/-- Given a natural transformation
`β : F.op ⋙ G ⟶ P`, construct a natural
transformation `G ⟶ (rightYonedaExt F).obj P`.
At `T : Dᵒᵖ` and `q : G.obj T`, the family at
`(S, t)` is `β.app (op S) (G.map t.op q)`. -/
def rightYonedaExtLift
    (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u v))
    {G : Dᵒᵖ ⥤ Type (max u v)}
    (β : F.op ⋙ G ⟶ P) :
    G ⟶ (rightYonedaExt F).obj P where
  app T q :=
    { family := fun S t =>
        β.app (Opposite.op S) (G.map t.op q)
      naturality := fun g t => by
        have hβ := congr_fun
          (β.naturality g.op) (G.map t.op q)
        simp only [types_comp_apply,
          Functor.comp_obj, Functor.comp_map]
            at hβ
        rw [← hβ, ← types_comp_apply
          (G.map t.op) (G.map (F.op.map g.op)),
          ← G.map_comp]
        simp only [op_comp, Functor.op_map,
          Quiver.Hom.unop_op] }
  naturality {T₁ T₂} k := by
    funext q
    apply RightYonedaExtFamily.ext'
    intro S t
    dsimp [rightYonedaExt, rightYonedaExtObj,
      rightYonedaExtFamilyMap]
    rw [← types_comp_apply (G.map k)
      (G.map t.op), ← G.map_comp]

/-- The lift through `rightYonedaExtCounit`
recovers `β`: for each `c : Cᵒᵖ`,
`(rightYonedaExtLift F P β).app (F.op.obj c) ≫
  (rightYonedaExtCounit F P).app c = β.app c`. -/
theorem rightYonedaExtLift_fac
    (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u v))
    {G : Dᵒᵖ ⥤ Type (max u v)}
    (β : F.op ⋙ G ⟶ P)
    (c : Cᵒᵖ) :
    (rightYonedaExtLift F P β).app
      (F.op.obj c) ≫
      (rightYonedaExtCounit F P).app c =
    β.app c := by
  funext q
  dsimp [rightYonedaExtLift,
    rightYonedaExtCounit]
  simp

/-- The lift is unique: any `σ` satisfying the
factorization at each component equals the
canonical lift. -/
theorem rightYonedaExtLift_uniq
    (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u v))
    {G : Dᵒᵖ ⥤ Type (max u v)}
    (β : F.op ⋙ G ⟶ P)
    (σ : G ⟶ (rightYonedaExt F).obj P)
    (hσ : ∀ (c : Cᵒᵖ),
      σ.app (F.op.obj c) ≫
        (rightYonedaExtCounit F P).app c =
      β.app c) :
    σ = rightYonedaExtLift F P β := by
  ext T q
  apply RightYonedaExtFamily.ext'
  intro S t
  have h := congr_fun
    (hσ (Opposite.op S))
    (G.map t.op q)
  dsimp [rightYonedaExtCounit,
    rightYonedaExtLift] at h ⊢
  rw [← h]
  have hnat :=
    congrArg
      (fun x =>
        RightYonedaExtFamily.family
          x S (𝟙 (F.obj S)))
      (congr_fun (σ.naturality t.op) q)
  dsimp [rightYonedaExt, rightYonedaExtObj,
    rightYonedaExtFamilyMap] at hnat
  simp only [Category.id_comp] at hnat
  exact hnat.symm

/-- Precomposition with `F.op` as a functor
between presheaf categories. -/
abbrev precompOp (F : C ⥤ D) :
    (Dᵒᵖ ⥤ Type (max u v)) ⥤
      (Cᵒᵖ ⥤ Type (max u v)) :=
  (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
    (Type (max u v))).obj F.op

/-- The right adjunction of the adjoint triple:
`precompOp F ⊣ rightYonedaExt F`. The hom-set
bijection sends `β : F.op ⋙ P ⟶ Q` to the lift
`P ⟶ (rightYonedaExt F).obj Q`, and its inverse
whiskers by `F.op` and composes with the counit.
-/
def rightYonedaExtAdj (F : C ⥤ D) :
    precompOp F ⊣
      (rightYonedaExt F :
        (Cᵒᵖ ⥤ Type (max u v)) ⥤
          (Dᵒᵖ ⥤ Type (max u v))) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q =>
        { toFun := fun β =>
            rightYonedaExtLift F Q β
          invFun := fun σ =>
            Functor.whiskerLeft F.op σ ≫
              rightYonedaExtCounit F Q
          left_inv := fun β => by
            ext c q
            exact congr_fun
              (rightYonedaExtLift_fac F Q β c)
              q
          right_inv := fun σ =>
            (rightYonedaExtLift_uniq F Q
              (Functor.whiskerLeft F.op σ ≫
                rightYonedaExtCounit F Q)
              σ (fun _ => rfl)).symm } }

/-- For each right extension `(G, β)` of `P`
along `F.op`, there is a unique morphism to the
canonical right extension
`((rightYonedaExt F).obj P, counit)`. -/
instance rightYonedaExtRightExtUnique
    (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u v))
    (s : Functor.RightExtension F.op P) :
    Unique (s ⟶ Functor.RightExtension.mk
      ((rightYonedaExt F).obj P)
      (rightYonedaExtCounit F P)) where
  default := CostructuredArrow.homMk
    (rightYonedaExtLift F P s.hom)
    (by ext c q
        exact congr_fun
          (rightYonedaExtLift_fac F P
            s.hom c) q)
  uniq f := by
    apply CostructuredArrow.ext
    exact rightYonedaExtLift_uniq F P
      s.hom f.left (fun c =>
        congrArg (·.app c)
          (CostructuredArrow.w f))

/-- The right Yoneda extension
`(rightYonedaExt F).obj P` is a right Kan
extension of `P` along `F.op`. -/
instance rightYonedaExt_isRightKanExtension
    (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u v)) :
    ((rightYonedaExt F).obj P).IsRightKanExtension
      (rightYonedaExtCounit F P) where
  nonempty_isUniversal :=
    ⟨Limits.IsTerminal.ofUnique
      (Functor.RightExtension.mk
        ((rightYonedaExt F).obj P)
        (rightYonedaExtCounit F P))⟩

/-- The unit of the left Yoneda extension at
a fixed presheaf `P`:
`P ⟶ F.op ⋙ (leftYonedaExt F).obj P`.
At each `c : Cᵒᵖ`, sends `p : P.obj c` to the
equivalence class of `(c.unop, p, 𝟙)`. -/
def leftYonedaExtPresheafUnit
    (F : C ⥤ D)
    (P : Cᵒᵖ ⥤ Type (max u v)) :
    P ⟶ F.op ⋙ (leftYonedaExt F).obj P where
  app c p :=
    Quot.mk _ ⟨c.unop, p, 𝟙 (F.obj c.unop)⟩
  naturality {c d} g := by
    funext p
    apply (Quot.sound _).symm
    refine ⟨g.unop, ?_, ?_⟩
    · dsimp [leftYonedaExtSigmaMap]
    · dsimp [leftYonedaExtSigmaMap]
      simp only [Category.id_comp,
        Category.comp_id]

/-- Given a natural transformation
`α : P ⟶ F.op ⋙ Q`, construct a natural
transformation `(leftYonedaExt F).obj P ⟶ Q`.
At `T : Dᵒᵖ`, on a triple `(S, p, t)`, the
result is `Q.map t.op (α.app (op S) p)`. -/
def leftYonedaExtPresheafDesc
    (F : C ⥤ D)
    {P : Cᵒᵖ ⥤ Type (max u v)}
    {Q : Dᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ F.op ⋙ Q) :
    (leftYonedaExt F).obj P ⟶ Q where
  app T := Quot.lift
    (fun x => Q.map x.2.2.op
      (α.app (Opposite.op x.1) x.2.1))
    (fun x y ⟨g, hp, ht⟩ => by
      dsimp
      rw [← hp]
      have hα := congr_fun
        (α.naturality g.op) x.2.1
      simp only [types_comp_apply] at hα
      rw [hα]
      dsimp
      rw [← types_comp_apply
        (Q.map (F.map g).op)
        (Q.map y.2.2.op),
        ← Q.map_comp,
        ← op_comp, ht])
  naturality {T₁ T₂} k := by
    funext q
    induction q using Quot.inductionOn
    rename_i x
    change Q.map (k.unop ≫ x.2.2).op
        (α.app (Opposite.op x.1) x.2.1) =
      Q.map k (Q.map x.2.2.op
        (α.app (Opposite.op x.1) x.2.1))
    rw [← types_comp_apply
      (Q.map x.2.2.op)
      (Q.map k), ← Q.map_comp]
    congr 1

/-- The presheaf-level descent map factorizes
through the unit: for each `c : Cᵒᵖ`,
`(leftYonedaExtPresheafUnit F P).app c ≫
  (leftYonedaExtPresheafDesc F α).app (F.op.obj c) =
  α.app c`. -/
theorem leftYonedaExtPresheafDesc_fac
    (F : C ⥤ D)
    {P : Cᵒᵖ ⥤ Type (max u v)}
    {Q : Dᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ F.op ⋙ Q)
    (c : Cᵒᵖ) :
    (leftYonedaExtPresheafUnit F P).app c ≫
      (leftYonedaExtPresheafDesc F α).app
        (F.op.obj c) =
    α.app c := by
  funext p
  dsimp [leftYonedaExtPresheafUnit,
    leftYonedaExtPresheafDesc]
  simp

/-- The presheaf-level descent map is unique: any
`σ` satisfying the factorization at each component
equals the canonical descent. -/
theorem leftYonedaExtPresheafDesc_uniq
    (F : C ⥤ D)
    {P : Cᵒᵖ ⥤ Type (max u v)}
    {Q : Dᵒᵖ ⥤ Type (max u v)}
    (α : P ⟶ F.op ⋙ Q)
    (σ : (leftYonedaExt F).obj P ⟶ Q)
    (hσ : ∀ (c : Cᵒᵖ),
      (leftYonedaExtPresheafUnit F P).app c ≫
        σ.app (F.op.obj c) = α.app c) :
    σ = leftYonedaExtPresheafDesc F α := by
  ext T q
  induction q using Quot.inductionOn
  rename_i x
  change σ.app T (Quot.mk _ x) =
    Q.map x.2.2.op
      (α.app (Opposite.op x.1) x.2.1)
  have himg : Quot.mk
      (LeftYonedaExtStep F P T) x =
      ((leftYonedaExt F).obj P).map x.2.2.op
        (Quot.mk _
          ⟨x.1, x.2.1,
            𝟙 (F.obj x.1)⟩) := by
    change _ = Quot.mk _
      (leftYonedaExtSigmaMap F P x.2.2.op
        ⟨x.1, x.2.1, 𝟙 (F.obj x.1)⟩)
    dsimp [leftYonedaExtSigmaMap]
    simp
  rw [himg]
  have hnat := congr_fun
    (σ.naturality x.2.2.op)
    (Quot.mk _ ⟨x.1, x.2.1,
      𝟙 (F.obj x.1)⟩)
  simp only [types_comp_apply] at hnat
  rw [hnat]
  exact congrArg (Q.map x.2.2.op)
    (congr_fun
      (hσ (Opposite.op x.1)) x.2.1)

/-- The left adjunction of the adjoint triple:
`leftYonedaExt F ⊣ precompOp F`. The hom-set
bijection sends `α : P ⟶ F.op ⋙ Q` to the
descent `(leftYonedaExt F).obj P ⟶ Q`, and its
inverse whiskers by `F.op` after the unit. -/
def leftYonedaExtAdj (F : C ⥤ D) :
    (leftYonedaExt F :
      (Cᵒᵖ ⥤ Type (max u v)) ⥤
        (Dᵒᵖ ⥤ Type (max u v))) ⊣
      precompOp F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q =>
        { toFun := fun σ =>
            leftYonedaExtPresheafUnit F P ≫
              Functor.whiskerLeft F.op σ
          invFun := fun α =>
            leftYonedaExtPresheafDesc F α
          left_inv := fun σ =>
            (leftYonedaExtPresheafDesc_uniq F
              (leftYonedaExtPresheafUnit F P ≫
                Functor.whiskerLeft F.op σ)
              σ (fun _ => rfl)).symm
          right_inv := fun α => by
            ext c p
            exact congr_fun
              (leftYonedaExtPresheafDesc_fac
                F α c) p }
      homEquiv_naturality_left_symm :=
        fun f g => by
          ext T q
          induction q using Quot.inductionOn
          rfl
      homEquiv_naturality_right :=
        fun f g => by
          ext c p
          dsimp [leftYonedaExtPresheafUnit,
            precompOp] }

end RightYonedaExtension

section FunctorHomSections

variable {C : Type u} [Category.{v} C]

/-- Convert a section of `F.functorHom G` to
a natural transformation `F ⟶ G`. Each section
provides a `HomObj` at every stage; evaluating at
the identity morphism extracts the nat trans
components. -/
def functorHomSectionToNatTrans
    {F G : Cᵒᵖ ⥤ Type (max u v)}
    (s : (F.functorHom G).sections) :
    F ⟶ G where
  app c x := (s.val c).app c (𝟙 c) x
  naturality {c d} f := by
    ext x
    simp only [types_comp_apply]
    have hn := congr_fun
      ((s.val c).naturality f (𝟙 c)) x
    simp only [types_comp_apply] at hn
    rw [← hn]
    have h : (s.val d).app d (𝟙 d) =
      ((F.functorHom G).map f (s.val c)).app
        d (𝟙 d) := by
      rw [s.property f]
    rw [h]
    dsimp [Functor.functorHom,
      Functor.homObjFunctor]
    simp

/-- Convert a natural transformation `F ⟶ G` to
a global section of `F.functorHom G`. Uses
`HomObj.ofNatTrans`, which ignores the
representable parameter, giving a constant
section. -/
def natTransToFunctorHomSection
    {F G : Cᵒᵖ ⥤ Type (max u v)}
    (α : F ⟶ G) :
    (F.functorHom G).sections :=
  ⟨fun _ => Functor.HomObj.ofNatTrans α,
   fun {c d} f => by
    dsimp [Functor.functorHom,
      Functor.homObjFunctor]
    ext ⟨⟩
    simp [Functor.HomObj.ofNatTrans]⟩

theorem functorHomSection_roundTrip_left
    {F G : Cᵒᵖ ⥤ Type (max u v)}
    (α : F ⟶ G) :
    functorHomSectionToNatTrans
      (natTransToFunctorHomSection α) = α := by
  ext c x
  simp [functorHomSectionToNatTrans,
    natTransToFunctorHomSection]

theorem functorHomSection_roundTrip_right
    {F G : Cᵒᵖ ⥤ Type (max u v)}
    (s : (F.functorHom G).sections) :
    natTransToFunctorHomSection
      (functorHomSectionToNatTrans s) = s := by
  ext c Y f x
  dsimp [natTransToFunctorHomSection,
    functorHomSectionToNatTrans,
    Functor.HomObj.ofNatTrans]
  have hsec := congrArg
    (fun h => h.app Y (𝟙 Y) x) (s.property f)
  dsimp [Functor.functorHom,
    Functor.homObjFunctor] at hsec
  simp at hsec
  exact hsec.symm

theorem functorHomSection_val_app
    {F G : Cᵒᵖ ⥤ Type (max u v)}
    (s : (F.functorHom G).sections)
    {c d : Cᵒᵖ} (k : c ⟶ d)
    (x : F.obj d) :
    (s.val c).app d k x =
      (functorHomSectionToNatTrans s).app
        d x := by
  have hsec := congrArg
    (fun h => h.app d (𝟙 d) x)
    (s.property k)
  dsimp [Functor.functorHom,
    Functor.homObjFunctor] at hsec
  simp only [Category.comp_id] at hsec
  dsimp [functorHomSectionToNatTrans]
  exact hsec

end FunctorHomSections

section FunctorCategoryMonoidalClosed

/-! ## Monoidal closed structure on functor categories

The functor category `J ⥤ (Cᵒᵖ ⥤ Type w)` is monoidal closed.
This follows from the currying equivalence
`(J ⥤ Cᵒᵖ ⥤ Type w) ≌ (J × Cᵒᵖ ⥤ Type w)`
and the fact that `(J × Cᵒᵖ) ⥤ Type w` is
monoidal closed (`FunctorToTypes.monoidalClosed`).
-/

open CategoryTheory MonoidalCategory Functor

universe u₁ v₁ u₂ v₂

variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u₂} [Category.{v₂} C]

-- Abbreviation for the uncurried functor
-- category, where MonoidalClosed is available.
abbrev uncurriedFunctorCat
    (J : Type u₁) [Category.{v₁} J]
    (C : Type u₂) [Category.{v₂} C] :=
  J × Cᵒᵖ ⥤ Type max v₁ v₂ u₁ u₂

-- The right adjoint to tensoring by F in the
-- curried functor category, defined by
-- transporting through the currying equivalence.
-- Abbreviation for the currying equivalence at
-- the universes used in this section.
abbrev functorCatCurrying
    (J : Type u₁) [Category.{v₁} J]
    (C : Type u₂) [Category.{v₂} C] :
    (J ⥤ (Cᵒᵖ ⥤ Type max v₁ v₂ u₁ u₂)) ≌
    (J × Cᵒᵖ ⥤ Type max v₁ v₂ u₁ u₂) :=
  currying (C := J) (D := Cᵒᵖ)
    (E := Type max v₁ v₂ u₁ u₂)

-- The right adjoint to tensoring by F in the
-- curried functor category, defined via the
-- currying equivalence and the internal hom in
-- `(J × Cᵒᵖ) ⥤ Type w`.
def functorCatIhom
    (F : J ⥤ (Cᵒᵖ ⥤ Type max v₁ v₂ u₁ u₂)) :
    (J ⥤ (Cᵒᵖ ⥤ Type max v₁ v₂ u₁ u₂)) ⥤
    (J ⥤ (Cᵒᵖ ⥤ Type max v₁ v₂ u₁ u₂)) :=
  (functorCatCurrying J C).functor ⋙
    FunctorToTypes.rightAdj
      ((functorCatCurrying J C).functor.obj F) ⋙
    (functorCatCurrying J C).inverse

-- The adjunction `tensorLeft F ⊣ functorCatIhom
-- F`, constructed by transporting the existing
-- adjunction through the currying equivalence.
-- This works because uncurry preserves the
-- monoidal product definitionally.
-- The hom-set bijection for the tensor-hom
-- adjunction in the curried functor category.
-- Chains: `(F ⊗ G ⟶ H) ≃ (uncurry G ⟶
-- rightAdj(uncurry F)(uncurry H)) ≃ (G ⟶
-- ihom(F)(H))`.
def functorCatHomEquiv
    (F G H : J ⥤ (Cᵒᵖ ⥤
      Type max v₁ v₂ u₁ u₂)) :
    (F ⊗ G ⟶ H) ≃
    (G ⟶ (functorCatIhom F).obj H) :=
  let e := functorCatCurrying J C
  let F' := e.functor.obj F
  -- Step 1: (F ⊗ G ⟶ H) ≃ (uncurry(F ⊗ G)
  -- ⟶ uncurry H) = (F' ⊗ uncurry G ⟶ uncurry H)
  (e.fullyFaithfulFunctor.homEquiv
    (X := F ⊗ G) (Y := H)).trans
    -- Step 2: ≃ (uncurry G ⟶ rightAdj F'
    -- (uncurry H))
    ((FunctorToTypes.adj F').homEquiv
      (e.functor.obj G)
      (e.functor.obj H)|>.trans
    -- Step 3: ≃ (G ⟶ curry(rightAdj F'
    -- (uncurry H))) = (G ⟶ ihom(F)(H))
    -- using e.functor ⊣ e.inverse: (F(G) ⟶ B)
    -- ≃ (G ⟶ e.inverse(B))
    (e.toAdjunction.homEquiv G _))

def functorCatAdj
    (F : J ⥤ (Cᵒᵖ ⥤
      Type max v₁ v₂ u₁ u₂)) :
    tensorLeft F ⊣ functorCatIhom F :=
  Adjunction.mkOfHomEquiv
    { homEquiv := functorCatHomEquiv F }

instance functorCatClosed
    (F : J ⥤ (Cᵒᵖ ⥤
      Type max v₁ v₂ u₁ u₂)) :
    Closed F where
  rightAdj := functorCatIhom F
  adj := functorCatAdj F

instance functorCatMonoidalClosed
    (J : Type u₁) [Category.{v₁} J]
    (C : Type u₂) [Category.{v₂} C] :
    MonoidalClosed
      (J ⥤ (Cᵒᵖ ⥤ Type max v₁ v₂ u₁ u₂)) where

end FunctorCategoryMonoidalClosed

section PresheafAdjunctionProperties

/-! ## Presheaf adjunction properties

Given an adjunction `F ⊣ G` between categories `C` and
`D`, the induced Kan extensions and precomposition
functors on presheaf categories satisfy an adjoint
triple and interact as described in Lemma 3.1 and
Lemma 3.2 of
<https://ncatlab.org/nlab/show/functoriality+of+categories+of+presheaves#properties>.
-/

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]

/-- Given `adj : F ⊣ G`, precomposition by `F.op`
is left adjoint to precomposition by `G.op` on
presheaf categories. This is the image of `adj.op`
under the `whiskerLeft` construction, which lifts an
adjunction on base categories to functor categories
by precomposition. (Property 2 of nLab Lemma 3.1.) -/
def precompOpAdj {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) :
    precompOp F ⊣
      (precompOp G :
        (Cᵒᵖ ⥤ Type (max u v)) ⥤
          (Dᵒᵖ ⥤ Type (max u v))) :=
  adj.op.whiskerLeft (Type (max u v))

/-- Given `adj : F ⊣ G`, the left Kan extension
along `G` is isomorphic to precomposition by `F.op`.
Both are left adjoint to `precompOp G`, so they are
isomorphic by uniqueness of left adjoints.
(Property 5 of nLab Lemma 3.1.) -/
def precompOpIsoLeftYonedaExt {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) :
    (precompOp F :
      (Dᵒᵖ ⥤ Type (max u v)) ⥤
        (Cᵒᵖ ⥤ Type (max u v))) ≅
    leftYonedaExt G :=
  (precompOpAdj adj).leftAdjointUniq
    (leftYonedaExtAdj G)

/-- Given `adj : F ⊣ G`, the right Kan extension
along `F` is isomorphic to precomposition by `G.op`.
Both are right adjoint to `precompOp F`, so they are
isomorphic by uniqueness of right adjoints.
(Property 4 of nLab Lemma 3.1.) -/
def rightYonedaExtIsoPrecompOp
    {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) :
    (rightYonedaExt F :
      (Cᵒᵖ ⥤ Type (max u v)) ⥤
        (Dᵒᵖ ⥤ Type (max u v))) ≅
    precompOp G :=
  (rightYonedaExtAdj F).rightAdjointUniq
    (precompOpAdj adj)

/-- Given `adj : F ⊣ G`, the left Kan extensions
form an adjoint pair `leftYonedaExt F ⊣ leftYonedaExt G`.
The right adjoint of `leftYonedaExt F` is `precompOp F`,
which is isomorphic to `leftYonedaExt G` by property 5.
(Property 1 of nLab Lemma 3.1.) -/
def leftYonedaExtPairAdj {F : C ⥤ D}
    {G : D ⥤ C}
    (adj : F ⊣ G) :
    (leftYonedaExt F :
      (Cᵒᵖ ⥤ Type (max u v)) ⥤
        (Dᵒᵖ ⥤ Type (max u v))) ⊣
    leftYonedaExt G :=
  (leftYonedaExtAdj F).ofNatIsoRight
    (precompOpIsoLeftYonedaExt adj)

/-- Given `adj : F ⊣ G`, the right Kan extensions
form an adjoint pair `rightYonedaExt F ⊣
rightYonedaExt G`. The left adjoint of
`rightYonedaExt G` is `precompOp G`, which is
isomorphic to `rightYonedaExt F` by property 4.
(Property 3 of nLab Lemma 3.1.) -/
def rightYonedaExtAdj' {F : C ⥤ D} {G : D ⥤ C}
    (adj : F ⊣ G) :
    (rightYonedaExt F :
      (Cᵒᵖ ⥤ Type (max u v)) ⥤
        (Dᵒᵖ ⥤ Type (max u v))) ⊣
    rightYonedaExt G :=
  ((rightYonedaExtAdj G).ofNatIsoLeft
    (rightYonedaExtIsoPrecompOp adj).symm)

/-- When `F` is fully faithful, the inverse of
the unit `leftYonedaExtPresheafUnit` at presheaf `P`
and stage `c : Cᵒᵖ`. Sends the equivalence class
of `(S, q, t : F.obj S ⟶ F.obj c.unop)` to
`P.map (hF.preimage t).op q`. -/
def leftYonedaExtUnitInvApp
    {F : C ⥤ D}
    (hF : F.FullyFaithful)
    (P : Cᵒᵖ ⥤ Type (max u v))
    (c : Cᵒᵖ) :
    ((leftYonedaExt F).obj P).obj (F.op.obj c) →
      P.obj c :=
  Quot.lift
    (fun x =>
      P.map (hF.preimage x.2.2).op x.2.1)
    (fun x y ⟨g, hp, ht⟩ => by
      change P.map (hF.preimage x.2.2).op
        x.2.1 =
        P.map (hF.preimage y.2.2).op y.2.1
      rw [← hp, ← types_comp_apply
        (P.map g.op) (P.map _), ← P.map_comp,
        ← op_comp]
      have : hF.preimage y.2.2 ≫ g =
          hF.preimage x.2.2 :=
        hF.map_injective (by
          rw [F.map_comp, hF.map_preimage,
            hF.map_preimage, ht])
      rw [this])

/-- When `F` is fully faithful, applying the
unit and then the inverse is the identity. -/
theorem leftYonedaExtUnitInvApp_unit
    {F : C ⥤ D}
    (hF : F.FullyFaithful)
    (P : Cᵒᵖ ⥤ Type (max u v))
    (c : Cᵒᵖ)
    (p : P.obj c) :
    leftYonedaExtUnitInvApp hF P c
      ((leftYonedaExtPresheafUnit F P).app c p) =
      p := by
  dsimp [leftYonedaExtUnitInvApp,
    leftYonedaExtPresheafUnit]
  have : hF.preimage (𝟙 (F.obj c.unop)) =
      𝟙 c.unop :=
    hF.map_injective (by simp)
  rw [this]
  simp

/-- When `F` is fully faithful, applying the
inverse and then the unit is the identity. -/
theorem leftYonedaExtUnit_unitInvApp
    {F : C ⥤ D}
    (hF : F.FullyFaithful)
    (P : Cᵒᵖ ⥤ Type (max u v))
    (c : Cᵒᵖ)
    (q : ((leftYonedaExt F).obj P).obj
      (F.op.obj c)) :
    (leftYonedaExtPresheafUnit F P).app c
      (leftYonedaExtUnitInvApp hF P c q) = q := by
  induction q using Quot.inductionOn
  rename_i x
  dsimp [leftYonedaExtUnitInvApp,
    leftYonedaExtPresheafUnit]
  apply (Quot.sound _).symm
  refine ⟨hF.preimage x.2.2, ?_, ?_⟩
  · rfl
  · dsimp [leftYonedaExtSigmaMap]
    simp [hF.map_preimage]

/-- Naturality of `leftYonedaExtUnitInvApp` in the
stage variable: transporting along `F.op.map f` and
then reflecting is the same as reflecting and then
applying `Q.map f`. -/
theorem leftYonedaExtUnitInvApp_naturality
    {F : C ⥤ D}
    (hF : F.FullyFaithful)
    (Q : Cᵒᵖ ⥤ Type (max u v))
    {c d : Cᵒᵖ}
    (f : c ⟶ d)
    (q : ((leftYonedaExt F).obj Q).obj
      (F.op.obj c)) :
    leftYonedaExtUnitInvApp hF Q d
      (((leftYonedaExt F).obj Q).map
        (F.op.map f) q) =
      Q.map f
        (leftYonedaExtUnitInvApp hF Q c q) := by
  induction q using Quot.inductionOn
  rename_i x
  change Q.map (hF.preimage
      ((F.op.map f).unop ≫ x.2.2)).op
      x.2.1 =
    Q.map f (Q.map (hF.preimage x.2.2).op
      x.2.1)
  rw [← types_comp_apply
    (Q.map (hF.preimage x.2.2).op)
    (Q.map f), ← Q.map_comp]
  have hmor : (hF.preimage
        ((F.op.map f).unop ≫ x.2.2)).op =
      (hF.preimage x.2.2).op ≫ f := by
    apply Quiver.Hom.unop_inj
    exact hF.map_injective (by
      simp [F.map_comp, hF.map_preimage])
  rw [hmor]

/-- When `F` is fully faithful, `leftYonedaExt F` is
fully faithful. The preimage of
`α : (leftYonedaExt F).obj P ⟶ (leftYonedaExt F).obj Q`
is obtained by reflecting through the adjunction
unit, which is invertible when `F` is fully
faithful. (Lemma 3.2 of
<https://ncatlab.org/nlab/show/functoriality+of+categories+of+presheaves#properties>,
left Kan extension case.) -/
def leftYonedaExtFullyFaithful
    {F : C ⥤ D}
    (hF : F.FullyFaithful) :
    Functor.FullyFaithful
      (leftYonedaExt F :
        (Cᵒᵖ ⥤ Type (max u v)) ⥤
          (Dᵒᵖ ⥤ Type (max u v))) where
  preimage {P Q} α :=
    { app := fun c p =>
        leftYonedaExtUnitInvApp hF Q c
          (α.app (F.op.obj c)
            ((leftYonedaExtPresheafUnit F P).app
              c p))
      naturality := fun {c d} f => by
        funext p
        simp only [types_comp_apply]
        have hunit : (leftYonedaExtPresheafUnit
            F P).app d (P.map f p) =
            ((leftYonedaExt F).obj P).map
              (F.op.map f)
              ((leftYonedaExtPresheafUnit F P).app
                c p) :=
          congr_fun ((leftYonedaExtPresheafUnit
            F P).naturality f) p
        rw [hunit]
        have hα := congr_fun
          (α.naturality (F.op.map f))
          ((leftYonedaExtPresheafUnit F P).app
            c p)
        simp only [types_comp_apply] at hα
        rw [hα]
        exact leftYonedaExtUnitInvApp_naturality
          hF Q f _ }
  map_preimage {P Q} α := by
    ext T q
    induction q using Quot.inductionOn
    rename_i x
    let q₀ := Quot.mk
      (LeftYonedaExtStep F P
        (Opposite.op (F.obj x.1)))
      ⟨x.1, x.2.1, 𝟙 (F.obj x.1)⟩
    have himg : Quot.mk
        (LeftYonedaExtStep F P T) x =
        ((leftYonedaExt F).obj P).map
          x.2.2.op q₀ := by
      change _ = Quot.mk _
        (leftYonedaExtSigmaMap F P x.2.2.op _)
      dsimp [leftYonedaExtSigmaMap]
      simp
    rw [himg]
    have hnat_map := congr_fun
      (((leftYonedaExt F).map
        { app := fun c p =>
            leftYonedaExtUnitInvApp hF Q c
              (α.app (F.op.obj c)
                ((leftYonedaExtPresheafUnit
                  F P).app c p))
          naturality := by
            intro c d f; funext p
            simp only [types_comp_apply]
            have hunit :
                (leftYonedaExtPresheafUnit
                  F P).app d (P.map f p) =
                ((leftYonedaExt F).obj P).map
                  (F.op.map f)
                  ((leftYonedaExtPresheafUnit
                    F P).app c p) :=
              congr_fun
                ((leftYonedaExtPresheafUnit
                  F P).naturality f) p
            rw [hunit]
            have hα' := congr_fun
              (α.naturality (F.op.map f))
              ((leftYonedaExtPresheafUnit
                F P).app c p)
            simp only [types_comp_apply]
              at hα'
            rw [hα']
            exact
              leftYonedaExtUnitInvApp_naturality
                hF Q f _ }
        ).naturality x.2.2.op) q₀
    simp only [types_comp_apply] at hnat_map
    rw [hnat_map]
    have hnat_α := congr_fun
      (α.naturality x.2.2.op) q₀
    simp only [types_comp_apply] at hnat_α
    rw [hnat_α]
    apply congrArg
    exact leftYonedaExtUnit_unitInvApp hF Q
      (Opposite.op x.fst)
      (α.app (F.op.obj (Opposite.op x.fst))
        q₀)
  preimage_map {P Q} f := by
    ext c p
    dsimp
    change leftYonedaExtUnitInvApp hF Q c
        (((leftYonedaExt F).map f).app
          (F.op.obj c)
          ((leftYonedaExtPresheafUnit F P).app
            c p)) =
      f.app c p
    dsimp [leftYonedaExtPresheafUnit]
    change leftYonedaExtUnitInvApp hF Q c
        (Quot.mk _ ⟨c.unop, f.app c p,
          𝟙 (F.obj c.unop)⟩) =
      f.app c p
    dsimp [leftYonedaExtUnitInvApp]
    have : hF.preimage (𝟙 (F.obj c.unop)) =
        𝟙 c.unop :=
      hF.map_injective (by simp)
    rw [this]
    simp

/-- When `F` is fully faithful, the inverse of
the counit `rightYonedaExtCounit` at presheaf `Q`
and stage `c : Cᵒᵖ`. Sends `p : Q.obj c` to
the family `(S, t) ↦ Q.map (hF.preimage t).op p`.
-/
def rightYonedaExtCounitInvApp
    {F : C ⥤ D}
    (hF : F.FullyFaithful)
    (Q : Cᵒᵖ ⥤ Type (max u v))
    (c : Cᵒᵖ)
    (p : Q.obj c) :
    ((rightYonedaExt F).obj Q).obj
      (F.op.obj c) :=
  { family := fun S t =>
      Q.map (hF.preimage t).op p
    naturality := fun g t => by
      rw [← types_comp_apply
        (Q.map (hF.preimage t).op) (Q.map g.op),
        ← Q.map_comp, ← op_comp]
      have : g ≫ hF.preimage t =
          hF.preimage (F.map g ≫ t) :=
        (hF.map_injective (by
          rw [F.map_comp, hF.map_preimage,
            hF.map_preimage])).symm
      rw [this] }

/-- When `F` is fully faithful, applying the
counit inverse and then the counit is the
identity. -/
theorem rightYonedaExtCounitInvApp_counit
    {F : C ⥤ D}
    (hF : F.FullyFaithful)
    (Q : Cᵒᵖ ⥤ Type (max u v))
    (c : Cᵒᵖ)
    (p : Q.obj c) :
    (rightYonedaExtCounit F Q).app c
      (rightYonedaExtCounitInvApp hF Q c p) =
      p := by
  dsimp [rightYonedaExtCounitInvApp,
    rightYonedaExtCounit]
  have : hF.preimage (𝟙 (F.obj c.unop)) =
      𝟙 c.unop :=
    hF.map_injective (by simp)
  rw [this]
  simp

/-- When `F` is fully faithful, applying the
counit and then the counit inverse is the
identity. -/
theorem rightYonedaExtCounit_counitInvApp
    {F : C ⥤ D}
    (hF : F.FullyFaithful)
    (Q : Cᵒᵖ ⥤ Type (max u v))
    (c : Cᵒᵖ)
    (x : ((rightYonedaExt F).obj Q).obj
      (F.op.obj c)) :
    rightYonedaExtCounitInvApp hF Q c
      ((rightYonedaExtCounit F Q).app c x) =
      x := by
  apply RightYonedaExtFamily.ext'
  intro S t
  dsimp [rightYonedaExtCounitInvApp,
    rightYonedaExtCounit]
  rw [x.naturality (hF.preimage t)
    (𝟙 (F.obj c.unop))]
  simp [hF.map_preimage]

/-- Naturality of `rightYonedaExtCounitInvApp`
in the stage variable: reflecting and then
transporting along `F.op.map f` is the same
as applying `Q.map f` and then reflecting. -/
theorem rightYonedaExtCounitInvApp_naturality
    {F : C ⥤ D}
    (hF : F.FullyFaithful)
    (Q : Cᵒᵖ ⥤ Type (max u v))
    {c d : Cᵒᵖ}
    (f : c ⟶ d)
    (p : Q.obj c) :
    ((rightYonedaExt F).obj Q).map
      (F.op.map f)
      (rightYonedaExtCounitInvApp hF Q c p) =
    rightYonedaExtCounitInvApp hF Q d
      (Q.map f p) := by
  apply RightYonedaExtFamily.ext'
  intro S t
  dsimp [rightYonedaExtCounitInvApp,
    rightYonedaExt, rightYonedaExtObj,
    rightYonedaExtFamilyMap]
  have hmor :
      (hF.preimage (t ≫ F.map f.unop)).op =
        f ≫ (hF.preimage t).op := by
    apply Quiver.Hom.unop_inj
    exact hF.map_injective (by
      simp [F.map_comp, hF.map_preimage])
  rw [hmor, Q.map_comp]
  rfl

/-- When `F` is fully faithful, `rightYonedaExt F`
is fully faithful. The preimage of
`α : (rightYonedaExt F).obj P ⟶
  (rightYonedaExt F).obj Q`
is obtained by reflecting through the adjunction
counit, which is invertible when `F` is fully
faithful. (Lemma 3.2 of
<https://ncatlab.org/nlab/show/functoriality+of+categories+of+presheaves#properties>,
right Kan extension case.) -/
def rightYonedaExtFullyFaithful
    {F : C ⥤ D}
    (hF : F.FullyFaithful) :
    Functor.FullyFaithful
      (rightYonedaExt F :
        (Cᵒᵖ ⥤ Type (max u v)) ⥤
          (Dᵒᵖ ⥤ Type (max u v))) where
  preimage {P Q} α :=
    { app := fun c p =>
        (rightYonedaExtCounit F Q).app c
          (α.app (F.op.obj c)
            (rightYonedaExtCounitInvApp
              hF P c p))
      naturality := fun {c d} f => by
        funext p
        simp only [types_comp_apply]
        rw [← rightYonedaExtCounitInvApp_naturality
          hF P f p]
        have hα := congr_fun
          (α.naturality (F.op.map f))
          (rightYonedaExtCounitInvApp hF P c p)
        simp only [types_comp_apply] at hα
        rw [hα]
        have hε := congr_fun
          ((rightYonedaExtCounit F Q).naturality
            f)
          (α.app (F.op.obj c)
            (rightYonedaExtCounitInvApp
              hF P c p))
        simp only [types_comp_apply,
          Functor.comp_map] at hε
        exact hε }
  preimage_map {P Q} f := by
    ext c p
    dsimp
    change (rightYonedaExtCounit F Q).app c
        (((rightYonedaExt F).map f).app
          (F.op.obj c)
          (rightYonedaExtCounitInvApp
            hF P c p)) =
      f.app c p
    dsimp [rightYonedaExtCounitInvApp,
      rightYonedaExtCounit,
      rightYonedaExt, rightYonedaExtMap,
      rightYonedaExtFamilyMapNat]
    have : hF.preimage (𝟙 (F.obj c.unop)) =
        𝟙 c.unop :=
      hF.map_injective (by simp)
    rw [this]
    simp
  map_preimage {P Q} α := by
    ext T x
    apply RightYonedaExtFamily.ext'
    intro S t
    dsimp [rightYonedaExt, rightYonedaExtMap,
      rightYonedaExtFamilyMapNat]
    have hkey :
        rightYonedaExtCounitInvApp hF P
          (Opposite.op S) (x.family S t) =
        ((rightYonedaExt F).obj P).map
          t.op x := by
      apply RightYonedaExtFamily.ext'
      intro S' t'
      dsimp [rightYonedaExtCounitInvApp,
        rightYonedaExt, rightYonedaExtObj,
        rightYonedaExtFamilyMap]
      rw [x.naturality (hF.preimage t') t,
        hF.map_preimage]
    rw [hkey]
    have hα :=
      congrArg
        (fun y =>
          RightYonedaExtFamily.family y
            S (𝟙 (F.obj S)))
        (congr_fun (α.naturality t.op) x)
    dsimp [rightYonedaExt, rightYonedaExtObj,
      rightYonedaExtFamilyMap,
      rightYonedaExtCounit] at hα ⊢
    simp only [Category.id_comp] at hα
    exact hα

/-- When `F` is fully faithful, the unit of the
left Kan extension adjunction
`leftYonedaExt F ⊣ precompOp F` is a natural
isomorphism. This follows from `leftYonedaExt F`
being fully faithful (Lemma 3.2) and the
equivalence between fully faithful left adjoints
and invertible units (Riehl, Lemma 4.5.13). -/
theorem leftYonedaExtAdj_unit_isIso
    {F : C ⥤ D}
    (hF : F.FullyFaithful) :
    IsIso (leftYonedaExtAdj F :
      (leftYonedaExt F :
        (Cᵒᵖ ⥤ Type (max u v)) ⥤
          (Dᵒᵖ ⥤ Type (max u v))) ⊣
      precompOp F).unit :=
  haveI := (leftYonedaExtFullyFaithful hF).full
  haveI := (leftYonedaExtFullyFaithful hF).faithful
  inferInstance

/-- When `F` is fully faithful, the counit of the
right Kan extension adjunction
`precompOp F ⊣ rightYonedaExt F` is a natural
isomorphism. This follows from `rightYonedaExt F`
being fully faithful (Lemma 3.2) and the
equivalence between fully faithful right adjoints
and invertible counits (Riehl, Lemma 4.5.13). -/
theorem rightYonedaExtAdj_counit_isIso
    {F : C ⥤ D}
    (hF : F.FullyFaithful) :
    IsIso (rightYonedaExtAdj F :
      precompOp F ⊣
        (rightYonedaExt F :
          (Cᵒᵖ ⥤ Type (max u v)) ⥤
            (Dᵒᵖ ⥤ Type (max u v)))).counit :=
  haveI :=
    (rightYonedaExtFullyFaithful hF).full
  haveI :=
    (rightYonedaExtFullyFaithful hF).faithful
  inferInstance

end PresheafAdjunctionProperties

end GebLean
