import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import GebLean.Utilities.Opposites
import GebLean.Utilities.Presheaf

/-!
# Slice and coslice category utilities

This module provides utilities for working with slice (over) and coslice (under)
categories, including equivalences involving opposite categories.

## Main definitions

* `underEquivOverOp'Op'` - Equivalence between `Under X` and `(Over X)ᵒᵖ'` in `Dᵒᵖ'`
* `overOpMapFunctor` - Functor `C ⥤ Cat` sending `y` to `(Over y)ᵒᵖ'`
* `OverOpPresheaf` - Presheaves on `(Over y)ᵒᵖ'`
* `overOpCopresheafFunctor` - Functor `Cᵒᵖ' ⥤ Cat` sending `y` to copresheaves on
  `(Over y)ᵒᵖ'`
* `OverCopresheaf` - Copresheaves on `Over y`
* `overCopresheafFunctor` - Functor `Cᵒᵖ' ⥤ Cat` sending `y` to copresheaves on
  `Over y`
* `overSelfProd` - Constructive self-product `A ×_X A` in `Over X`
* `overSelfProdFunctor` - The self-product functor `A ↦ A ×_X A`
-/

universe v u

namespace GebLean

open CategoryTheory

section OverUnderAccessors

variable {C : Type u} [Category.{v} C] {X : C}

/--
The left morphism of an Over morphism. This is the underlying morphism between
the source objects.

For `f : A ⟶ B` in `Over X`, `Over.left f : A.left ⟶ B.left`.
-/
abbrev Over.left {A B : Over X} (f : A ⟶ B) : A.left ⟶ B.left := f.left

/--
The right morphism of an Under morphism. This is the underlying morphism between
the target objects.

For `f : A ⟶ B` in `Under X`, `Under.right f : A.right ⟶ B.right`.
-/
abbrev Under.right {A B : Under X} (f : A ⟶ B) : A.right ⟶ B.right := f.right

/--
The left morphism of an Over morphism in `(Over X)ᵒᵖ'`. For `f : A ⟶ B` in
`(Over X)ᵒᵖ'`, the underlying morphism goes from `B.left` to `A.left`.

For `f : A ⟶ B` in `(Over X)ᵒᵖ'`, `Over.leftOp' f : B.left ⟶ A.left`.
-/
abbrev Over.leftOp' {A B : Over X} (f : @Quiver.Hom (Over X)ᵒᵖ' _ A B) :
    B.left ⟶ A.left := f.left

/--
The right morphism of an Under morphism in `(Under X)ᵒᵖ'`. For `f : A ⟶ B` in
`(Under X)ᵒᵖ'`, the underlying morphism goes from `B.right` to `A.right`.

For `f : A ⟶ B` in `(Under X)ᵒᵖ'`, `Under.rightOp' f : B.right ⟶ A.right`.
-/
abbrev Under.rightOp' {A B : Under X} (f : @Quiver.Hom (Under X)ᵒᵖ' _ A B) :
    B.right ⟶ A.right := f.right

end OverUnderAccessors

/-! ### Over morphism helpers for Type-valued slice categories

When working with `Over X` where `X : Type u`, morphisms are functions between
the left components that commute with the structure maps. These helpers provide
convenient ways to construct and destruct such morphisms.
-/

section OverTypeHelpers

variable {X : Type u}

/--
Extract the underlying function from an `Over X` morphism.
For `f : A ⟶ B` in `Over X`, this gives `f.left : A.left → B.left`.
-/
def overMorFn {A B : Over X} (f : A ⟶ B) : A.left → B.left := f.left

/--
The commutativity condition for an `Over X` morphism at a specific point.
For `f : A ⟶ B` in `Over X` and `a : A.left`, we have `B.hom (f.left a) = A.hom a`.
-/
lemma overMor_w {A B : Over X} (f : A ⟶ B) (a : A.left) :
    B.hom (f.left a) = A.hom a :=
  congrFun (Over.w f) a

/--
Round-trip: extracting the function from `Over.homMk` gives the original function.
-/
@[simp]
lemma overMorFn_homMk {A B : Over X} (fn : A.left → B.left)
    (h : B.hom ∘ fn = A.hom) : overMorFn (Over.homMk fn h) = fn := rfl

/--
Round-trip: the commutativity condition from `Over.homMk` holds pointwise.
-/
@[simp]
lemma overMor_w_homMk {A B : Over X} (fn : A.left → B.left)
    (h : B.hom ∘ fn = A.hom) (a : A.left) :
    overMor_w (Over.homMk fn h) a = congrFun h a := rfl

/--
Identity morphism in `Over X` has identity function.
-/
@[simp]
lemma overMorFn_id (A : Over X) : overMorFn (𝟙 A) = id := rfl

/--
Composition in `Over X` corresponds to function composition.
-/
@[simp]
lemma overMorFn_comp {A B C : Over X} (f : A ⟶ B) (g : B ⟶ C) :
    overMorFn (f ≫ g) = overMorFn g ∘ overMorFn f := rfl

/--
Extensionality for `Over X` morphisms: two morphisms are equal iff their
underlying functions are equal.
-/
lemma overMor_ext {A B : Over X} (f g : A ⟶ B)
    (h : overMorFn f = overMorFn g) : f = g :=
  Over.OverMorphism.ext h

end OverTypeHelpers

section UnderOverEquivalence

variable {D : Type u} [Category.{v} D] (X : D)

/--
Functor from `Under X` in `D` to `(Over X)ᵒᵖ'` in `Dᵒᵖ'`.

An object `(Y, f : X ⟶ Y)` in `Under X` maps to `(Y, f)` viewed as an object
in `Over (X : Dᵒᵖ')` (where `f : Y ⟶ X` in `Dᵒᵖ'`).

Morphisms are reversed: `g : u.right ⟶ v.right` in `D` becomes
`g : v.left ⟶ u.left` in `(Over X)ᵒᵖ'`.
-/
def underToOverOp'Op' : Under X ⥤ (@Over Dᵒᵖ' _ X)ᵒᵖ' where
  obj u := Over.mk (u.hom : @Quiver.Hom Dᵒᵖ' _ u.right X)
  map {u v} f := Over.homMk (f.right : @Quiver.Hom Dᵒᵖ' _ v.right u.right) (by
    dsimp [Over.mk]
    exact Under.w f)

/--
Functor from `(Over X)ᵒᵖ'` in `Dᵒᵖ'` to `Under X` in `D`.
-/
def overOp'Op'ToUnder : (@Over Dᵒᵖ' _ X)ᵒᵖ' ⥤ Under X where
  obj o := Under.mk (o.hom : @Quiver.Hom D _ X o.left)
  map {o p} f := Under.homMk (f.left : @Quiver.Hom D _ o.left p.left) (by
    dsimp [Under.mk]
    exact Over.w f)

/--
Unit isomorphism for the equivalence `Under X ≌ (Over (X : Dᵒᵖ'))ᵒᵖ'`.
-/
def underOverOp'Op'UnitIso :
    𝟭 (Under X) ≅ underToOverOp'Op' X ⋙ overOp'Op'ToUnder X :=
  NatIso.ofComponents
    (fun u => Under.isoMk (Iso.refl _) (by simp [underToOverOp'Op', overOp'Op'ToUnder]))
    (fun {u v} f => by
      ext
      simp [underToOverOp'Op', overOp'Op'ToUnder])

/--
Component isomorphism for counit: an object in `(Over X)ᵒᵖ'` is isomorphic to
the round-trip through Under and back.
-/
def underOverOp'Op'CounitComponent (o : (@Over Dᵒᵖ' _ X)ᵒᵖ') :
    (overOp'Op'ToUnder X ⋙ underToOverOp'Op' X).obj o ≅ o := by
  let lhs := (overOp'Op'ToUnder X ⋙ underToOverOp'Op' X).obj o
  have h_left_eq : lhs.left = o.left := rfl
  have h_hom_eq : lhs.hom = o.hom := rfl
  exact @Iso.refl (@Over Dᵒᵖ' _ X)ᵒᵖ' _ o

/--
Counit isomorphism for the equivalence `Under X ≌ (Over (X : Dᵒᵖ'))ᵒᵖ'`.
-/
def underOverOp'Op'CounitIso :
    overOp'Op'ToUnder X ⋙ underToOverOp'Op' X ≅ 𝟭 ((@Over Dᵒᵖ' _ X)ᵒᵖ') :=
  NatIso.ofComponents
    (fun o => underOverOp'Op'CounitComponent X o)
    (fun {o p} f => by
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
        underOverOp'Op'CounitComponent, Iso.refl_hom]
      apply Over.OverMorphism.ext
      simp only [underToOverOp'Op', overOp'Op'ToUnder, Under.homMk_right]
      unfold CategoryOp'Inst CategoryStruct.comp at *
      simp only []
      change 𝟙 p.left ≫ f.left = f.left ≫ 𝟙 o.left
      simp only [Category.comp_id, Category.id_comp])

/--
The under category of `X` in `D` is equivalent to the opposite of the over
category of `X` in `Dᵒᵖ'`.

This maps an arrow `f : X ⟶ Y` in `Under X` to the same arrow viewed as
`f : Y ⟶ X` in `Over X` (in `Dᵒᵖ'`), with morphisms reversed.
-/
def underEquivOverOp'Op' : Under X ≌ (@Over Dᵒᵖ' _ X)ᵒᵖ' where
  functor := underToOverOp'Op' X
  inverse := overOp'Op'ToUnder X
  unitIso := underOverOp'Op'UnitIso X
  counitIso := underOverOp'Op'CounitIso X
  functor_unitIso_comp X := by
    simp only [Functor.comp_obj, underOverOp'Op'UnitIso, NatIso.ofComponents_hom_app,
      underOverOp'Op'CounitIso, underOverOp'Op'CounitComponent, Iso.refl_hom]
    apply Over.OverMorphism.ext
    simp only [underToOverOp'Op', overOp'Op'ToUnder, Under.isoMk_hom_right, Iso.refl_hom]
    congr 1
    exact Category.comp_id _

end UnderOverEquivalence

section OverOpFunctors

variable (C : Type u) [Category.{v} C]

/--
The functor `C ⥤ Cat` sending `y` to `Cat.of ((Over y)ᵒᵖ')` and
`h : y ⟶ y'` to `(Over.map h).op' : (Over y)ᵒᵖ' ⥤ (Over y')ᵒᵖ'`.

This is `Over.mapFunctor` postcomposed with the opposite-category functor.
-/
def overOpMapFunctor : C ⥤ Cat :=
  Cat.postCompOpFunctor'.obj (Over.mapFunctor C)

/--
Precomposition with `(overOpMapFunctor C).map h` for a morphism `h : y ⟶ y'`.
-/
def precompOverOpMap {y y' : C} (h : y ⟶ y') :
    ((Over y')ᵒᵖ' ⥤ Type v) ⥤ ((Over y)ᵒᵖ' ⥤ Type v) :=
  (Functor.whiskeringLeft ((Over y)ᵒᵖ') (Over y')ᵒᵖ' (Type v)).obj
    ((overOpMapFunctor C).map h).toFunctor

/--
The type of presheaves on `(Over y)ᵒᵖ'` for a fixed `y : C`.
-/
abbrev OverOpPresheaf (y : C) := Presheaf (Over y)

/--
Functor `Cᵒᵖ' ⥤ Cat` sending `y` to the category of copresheaves on `(Over y)ᵒᵖ'`.

For a morphism `h : y ⟶ y'` in `Cᵒᵖ'` (which is `h : y' ⟶ y` as a C-morphism),
the induced functor is precomposition with `(Over.map h).op' : (Over y')ᵒᵖ' ⥤ (Over y)ᵒᵖ'`,
giving `((Over y)ᵒᵖ' ⥤ Type v) ⥤ ((Over y')ᵒᵖ' ⥤ Type v)`.
-/
def overOpCopresheafFunctor : Cᵒᵖ' ⥤ Cat :=
  Functor.op' (overOpMapFunctor C) ⋙ copresheafConstruction

/--
The type of copresheaves on `Over y` for a fixed `y : C`.
-/
abbrev OverCopresheaf (y : C) := Copresheaf (Over y)

/--
Precomposition with `(Over.mapFunctor C).map h` for a morphism `h : y ⟶ y'`.
-/
def precompOverMap {y y' : C} (h : y ⟶ y') :
    (Over y' ⥤ Type v) ⥤ (Over y ⥤ Type v) :=
  (Functor.whiskeringLeft (Over y) (Over y') (Type v)).obj
    ((Over.mapFunctor C).map h).toFunctor

/--
Functor `Cᵒᵖ' ⥤ Cat` sending `y` to the category of copresheaves on `Over y`.

For a morphism `h : y ⟶ y'` in `Cᵒᵖ'` (which is `h : y' ⟶ y` as a C-morphism),
the induced functor is precomposition with `Over.map h : Over y' ⥤ Over y`,
giving `(Over y ⥤ Type v) ⥤ (Over y' ⥤ Type v)`.
-/
def overCopresheafFunctor : Cᵒᵖ' ⥤ Cat :=
  Functor.op' (Over.mapFunctor C) ⋙ copresheafConstruction

end OverOpFunctors

/-! ## Constructive self-product in Over X

Products in `Over X` are pullbacks in the base category.
For `A : Over X`, the self-product `A ×_X A` has underlying
type `{ p : A.left × A.left // A.hom p.1 = A.hom p.2 }`.

We build the product constructively using:
- `Types.pullbackCone` / `Types.pullbackLimitCone` for
  the computable pullback in `Type`
- `pullbackConeEquivBinaryFan` to convert to a binary fan
  in `Over X`
- `IsLimit.pullbackConeEquivBinaryFanFunctor` to transfer
  the limit property
-/

section OverSelfProd

open Limits

variable {X : Type u}

/--
The pullback cone for `A.hom` with itself in `Type`.
-/
def overSelfPullbackCone (A : Over X) :
    PullbackCone A.hom A.hom :=
  Types.pullbackCone A.hom A.hom

/--
The pullback cone `overSelfPullbackCone A` is a limit.
-/
def overSelfPullbackIsLimit (A : Over X) :
    IsLimit (overSelfPullbackCone A) :=
  (Types.pullbackLimitCone A.hom A.hom).isLimit

/--
The binary fan in `Over X` corresponding to the self-pullback
of `A`.
-/
def overSelfProdFan (A : Over X) :
    BinaryFan A A :=
  pullbackConeEquivBinaryFan.functor.obj
    (overSelfPullbackCone A)

/--
The binary fan `overSelfProdFan A` is a limit in `Over X`.
-/
def overSelfProdIsLimit (A : Over X) :
    IsLimit (overSelfProdFan A) :=
  IsLimit.pullbackConeEquivBinaryFanFunctor
    (overSelfPullbackIsLimit A)

/--
The self-product object `A ×_X A` in `Over X`.
-/
abbrev overSelfProd (A : Over X) : Over X :=
  (overSelfProdFan A).pt

/--
First projection `A ×_X A ⟶ A`.
-/
abbrev overSelfProdFst (A : Over X) :
    overSelfProd A ⟶ A :=
  (overSelfProdFan A).fst

/--
Second projection `A ×_X A ⟶ A`.
-/
abbrev overSelfProdSnd (A : Over X) :
    overSelfProd A ⟶ A :=
  (overSelfProdFan A).snd

/--
Lift a morphism `f : A ⟶ B` to the self-product via the
universal property: `(fst ≫ f, snd ≫ f)`.
-/
def overSelfProdMap {A B : Over X} (f : A ⟶ B) :
    overSelfProd A ⟶ overSelfProd B :=
  (overSelfProdIsLimit B).lift
    (BinaryFan.mk
      (overSelfProdFst A ≫ f)
      (overSelfProdSnd A ≫ f))

end OverSelfProd

/-! ## The self-product functor -/

section OverSelfProdFunctor

open Limits

variable (X : Type u)

/--
The self-product functor `A ↦ A ×_X A` on `Over X`.

On morphisms, `f : A ⟶ B` maps to the universal lift of
`(fst ≫ f, snd ≫ f)` into `B ×_X B`.
-/
def overSelfProdFunctor : Over X ⥤ Over X where
  obj := overSelfProd
  map := overSelfProdMap
  map_id := fun A => by
    apply (overSelfProdIsLimit A).hom_ext
    intro ⟨j⟩
    simp only [Category.id_comp]
    exact (overSelfProdIsLimit A).fac _ _
  map_comp := fun {A B C} f g => by
    symm
    apply (overSelfProdIsLimit C).hom_ext
    intro ⟨j⟩
    simp only [overSelfProdMap, Category.assoc,
      (overSelfProdIsLimit C).fac,
      BinaryFan.mk]
    cases j
    all_goals {
      simp only []
      erw [← Category.assoc,
        (overSelfProdIsLimit B).fac]
    }

end OverSelfProdFunctor

/-! ## PUnit specialization

When `X = PUnit`, the fiber condition `A.hom a₁ = A.hom a₂`
is trivially satisfied, so the self-product reduces to the
ordinary product.
-/

section PUnitSpecialization

/--
When `X = PUnit`, the self-product type is equivalent to
the ordinary product, since the fiber condition is trivially
satisfied.
-/
def overSelfProd_punit_equiv
    (A : Over PUnit.{u + 1}) :
    (overSelfProd A).left ≃ A.left × A.left where
  toFun := fun ⟨⟨a₁, a₂⟩, _⟩ => (a₁, a₂)
  invFun := fun ⟨a₁, a₂⟩ =>
    ⟨⟨a₁, a₂⟩, by
      have : ∀ (x y : PUnit.{u + 1}), x = y :=
        fun x y => by cases x; cases y; rfl
      exact this _ _⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun _ => rfl

end PUnitSpecialization

/-! ## Coequalizers in Over X

Given morphisms `α β : A ⟶ B` in `Over X`, the coequalizer is the
quotient of `B.left` by the relation identifying `α.left a` with
`β.left a` for all `a : A.left`, equipped with the induced map to `X`.
-/

section OverCoequalizer

variable {X : Type u} {A B : Over X} (α β : A ⟶ B)

/--
The generating relation on `B.left` for the coequalizer of `α`
and `β` in `Over X`: `b₁ ~ b₂` when there exists `a : A.left`
with `α.left a = b₁` and `β.left a = b₂`.
-/
def overCoeqRel : B.left → B.left → Prop :=
  fun b₁ b₂ => ∃ a : A.left, α.left a = b₁ ∧ β.left a = b₂

/--
Well-definedness: `B.hom` respects `overCoeqRel α β`.
-/
private theorem overCoeqObj_wd (b₁ b₂ : B.left)
    (h : overCoeqRel α β b₁ b₂) :
    B.hom b₁ = B.hom b₂ := by
  obtain ⟨a, rfl, rfl⟩ := h
  have hα := congrFun (Over.w α) a
  have hβ := congrFun (Over.w β) a
  dsimp at hα hβ; rw [hα, hβ]

/--
The coequalizer object in `Over X`. The underlying type is
`Quot (overCoeqRel α β)`, with the structure map induced
from `B.hom`.
-/
def overCoeqObj : Over X :=
  Over.mk (Quot.lift B.hom (overCoeqObj_wd α β) :
    Quot (overCoeqRel α β) → X)

/--
The projection morphism `B ⟶ overCoeqObj α β` in `Over X`,
given by `Quot.mk`.
-/
def overCoeqπ : B ⟶ overCoeqObj α β :=
  Over.homMk (Quot.mk (overCoeqRel α β))

/--
The coequalizer condition: `α ≫ overCoeqπ α β = β ≫ overCoeqπ α β`.
-/
theorem overCoeq_condition :
    α ≫ overCoeqπ α β = β ≫ overCoeqπ α β := by
  ext a
  exact Quot.sound ⟨a, rfl, rfl⟩

/--
Universal factorization through the coequalizer. Given
`h : B ⟶ T` with `α ≫ h = β ≫ h`, produce
`overCoeqObj α β ⟶ T`.
-/
def overCoeqDesc {T : Over X} (h : B ⟶ T)
    (w : α ≫ h = β ≫ h) : overCoeqObj α β ⟶ T :=
  Over.homMk
    (Quot.lift h.left (fun b₁ b₂ ⟨a, h₁, h₂⟩ => by
      rw [← h₁, ← h₂]
      exact congrFun (congrArg (·.left) w) a))
    (by
      funext q; revert q; apply Quot.ind; intro b
      exact congrFun (Over.w h) b)

/--
Factorization property: `overCoeqπ ≫ overCoeqDesc = h`.
-/
theorem overCoeq_fac {T : Over X} (h : B ⟶ T)
    (w : α ≫ h = β ≫ h) :
    overCoeqπ α β ≫ overCoeqDesc α β h w = h := by
  ext b; rfl

/--
Uniqueness: any `m : overCoeqObj α β ⟶ T` satisfying
`overCoeqπ ≫ m = h` equals `overCoeqDesc α β h w`.
-/
theorem overCoeq_uniq {T : Over X} (h : B ⟶ T)
    (w : α ≫ h = β ≫ h)
    (m : overCoeqObj α β ⟶ T)
    (hm : overCoeqπ α β ≫ m = h) :
    m = overCoeqDesc α β h w := by
  ext q; revert q; apply Quot.ind; intro b
  exact congrFun (congrArg (·.left) hm) b

/--
The coequalizer projection is an epimorphism: if
`overCoeqπ ≫ f₁ = overCoeqπ ≫ f₂` then `f₁ = f₂`.
-/
theorem overCoeq_epi {T : Over X}
    (f₁ f₂ : overCoeqObj α β ⟶ T)
    (heq : overCoeqπ α β ≫ f₁ =
      overCoeqπ α β ≫ f₂) :
    f₁ = f₂ := by
  ext q; revert q; apply Quot.ind; intro b
  exact congrFun (congrArg (·.left) heq) b

end OverCoequalizer

/-! ## Wide products in Over X

Given a family `F : I → Over X`, the product has underlying type
`Σ x : X, (i : I) → { a : (F i).left // (F i).hom a = x }`,
with projection to `X` given by `Sigma.fst`.
-/

section OverProduct

variable {X : Type u} {I : Type u} (F : I → Over X)

/--
The fiber of the wide product over a point `x : X`:
tuples `(a_i)_{i:I}` with each `a_i` in the fiber of
`(F i).hom` over `x`.
-/
def overProdFiber (x : X) : Type u :=
  (i : I) → { a : (F i).left // (F i).hom a = x }

/--
The total type of the wide product: pairs `(x, f)` where
`x : X` and `f` is a tuple in `overProdFiber F x`.
-/
def overProdType : Type u :=
  Σ x : X, overProdFiber F x

/--
The wide product object in `Over X`.
-/
def overProdObj : Over X :=
  Over.mk (Sigma.fst : overProdType F → X)

/--
The `i`-th projection from the wide product.
-/
def overProdπ (i : I) : overProdObj F ⟶ F i :=
  Over.homMk
    (fun ⟨_, f⟩ => (f i).val)
    (by funext ⟨_, f⟩; exact (f i).property)

/--
Universal lift into the wide product: given a cone
`(π_i : S ⟶ F i)`, produce `S ⟶ overProdObj F`.
-/
def overProdLift {S : Over X}
    (π : ∀ i, S ⟶ F i) : S ⟶ overProdObj F :=
  Over.homMk
    (fun s => (⟨S.hom s,
      fun i => ⟨(π i).left s,
        congrFun (Over.w (π i)) s⟩⟩ :
      overProdType F))

/--
Factorization: composing the lift with a projection
recovers the original morphism.
-/
theorem overProd_fac {S : Over X}
    (π : ∀ i, S ⟶ F i) (i : I) :
    overProdLift F π ≫ overProdπ F i = π i := by
  ext s; rfl

/--
Uniqueness of the lift into the wide product.
-/
theorem overProd_uniq {S : Over X}
    (π : ∀ i, S ⟶ F i)
    (m : S ⟶ overProdObj F)
    (hm : ∀ i, m ≫ overProdπ F i = π i) :
    m = overProdLift F π := by
  apply Over.OverMorphism.ext
  funext s
  have h_base : (m.left s).1 = S.hom s :=
    congrFun (Over.w m) s
  have h_comp : ∀ i,
      ((m.left s).2 i).val = (π i).left s :=
    fun i =>
      congrFun (congrArg (·.left) (hm i)) s
  revert h_base h_comp
  generalize m.left s = ms
  intro h_base h_comp
  obtain ⟨x, f⟩ := ms
  dsimp at h_base h_comp
  subst h_base
  congr 1
  funext i
  exact Subtype.ext (h_comp i)

end OverProduct

/-! ## Equalizers in Over X

Given morphisms `f g : A ⟶ B` in `Over X`, the equalizer has
underlying type `{ a : A.left // f.left a = g.left a }`, with
the structure map inherited from `A.hom`.
-/

section OverEqualizer

variable {X : Type u} {A B : Over X} (f g : A ⟶ B)

/--
The equalizer object in `Over X`: the subtype of `A.left`
on which `f` and `g` agree.
-/
def overEqObj : Over X :=
  Over.mk (A.hom ∘ Subtype.val :
    { a : A.left // f.left a = g.left a } → X)

/--
The inclusion morphism from the equalizer into `A`.
-/
def overEqι : overEqObj f g ⟶ A :=
  Over.homMk Subtype.val

/--
The equalizer condition:
`overEqι ≫ f = overEqι ≫ g`.
-/
theorem overEq_condition :
    overEqι f g ≫ f = overEqι f g ≫ g := by
  ext ⟨_, h⟩; exact h

/--
Universal lift into the equalizer: given `h : S ⟶ A`
with `h ≫ f = h ≫ g`, produce `S ⟶ overEqObj f g`.
-/
def overEqLift {S : Over X} (h : S ⟶ A)
    (w : h ≫ f = h ≫ g) : S ⟶ overEqObj f g :=
  Over.homMk
    (fun s => ⟨h.left s,
      congrFun (congrArg (·.left) w) s⟩)
    (by funext s; exact congrFun (Over.w h) s)

/--
Factorization: composing the lift with the inclusion
recovers the original morphism.
-/
theorem overEq_fac {S : Over X} (h : S ⟶ A)
    (w : h ≫ f = h ≫ g) :
    overEqLift f g h w ≫ overEqι f g = h := by
  ext s; rfl

/--
Uniqueness of the lift into the equalizer.
-/
theorem overEq_uniq {S : Over X} (h : S ⟶ A)
    (w : h ≫ f = h ≫ g)
    (m : S ⟶ overEqObj f g)
    (hm : m ≫ overEqι f g = h) :
    m = overEqLift f g h w := by
  apply Over.OverMorphism.ext
  funext s
  exact Subtype.ext
    (congrFun (congrArg (·.left) hm) s)

end OverEqualizer

end GebLean
