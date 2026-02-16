import GebLean.Utilities.Opposites
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Yoneda

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

/-- The presheaf pullback cone is a limit. -/
def presheafPullbackIsLimit
    (f : F ⟶ H) (g : G ⟶ H) :
    IsLimit (presheafPullbackCone f g) :=
  PullbackCone.combineIsLimit f g
    (fun X =>
      Types.pullbackCone (f.app X) (g.app X))
    (fun X =>
      (Types.pullbackLimitCone
        (f.app X) (g.app X)).isLimit)

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

end PresheafPullback

section CoyonedaIso

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

end CoyonedaIso

end GebLean
