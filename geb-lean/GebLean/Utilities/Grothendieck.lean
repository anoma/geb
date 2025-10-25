import Mathlib.CategoryTheory.Category.Cat.AsSmall
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Whiskering
import GebLean.Utilities.Opposites

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

universe w u v u₁ v₁ u₂ v₂

namespace GebLean

open CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {D : Type u₁} [Category.{v₁} D]

/--
The contravariant Grothendieck construction for a functor `F' : Cᵒᵖ' ⥤ Cat`
gives a category whose

* objects `X` consist of `X.base : C` and `X.fiber : F'.obj base`
* morphisms `f : X ⟶ Y` consist of
  `base : X.base ⟶ Y.base` and
  `f.fiber : X.fiber ⟶ (F'.map base).obj Y.fiber`

In the `ᵒᵖ'` form, the corresponding definition is:
-/
structure GrothendieckContra' (F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}) where
  /-- The underlying object in `C` -/
  base : C
  /-- The object in the fiber of the base object. -/
  fiber : F'.obj base

namespace GrothendieckContra'

variable {F' : Cᵒᵖ' ⥤ Cat.{v₂, u₂}}

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

/-- The identity morphism in the contravariant Grothendieck category.
-/
def id (X : GrothendieckContra' F') : Hom X X where
  base := 𝟙 X.base
  fiber := eqToHom (Functor.congr_obj (F'.map_id X.base).symm X.fiber)

instance (X : GrothendieckContra' F') : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms in the contravariant Grothendieck category.
-/
def comp {X Y Z : GrothendieckContra' F'} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  fiber := f.fiber ≫ (F'.map f.base).map g.fiber ≫
    eqToHom (symm <| Functor.congr_obj (F'.map_comp g.base f.base) Z.fiber)

attribute [local simp] eqToHom_map Functor.map_id

instance : Category (GrothendieckContra' F') where
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
theorem id_fiber (X : GrothendieckContra' F') :
    (id X).fiber = eqToHom (Functor.congr_obj (F'.map_id X.base).symm X.fiber) := rfl

@[simp]
theorem comp_base {X Y Z : GrothendieckContra' F'} (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).base = f.base ≫ g.base := rfl

@[simp]
theorem comp_fiber {X Y Z : GrothendieckContra' F'} (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).fiber = f.fiber ≫ (F'.map f.base).map g.fiber ≫
      eqToHom (symm <| Functor.congr_obj (F'.map_comp g.base f.base) Z.fiber) := rfl

theorem congr {X Y : GrothendieckContra' F'} {f g : X ⟶ Y} (h : f = g) :
    f.fiber = g.fiber ≫ eqToHom (by subst h; rfl) := by
  subst h
  simp

@[simp]
theorem base_eqToHom {X Y : GrothendieckContra' F'} (h : X = Y) :
    (eqToHom h).base = eqToHom (congrArg GrothendieckContra'.base h) := by
  subst h
  rfl

private lemma fiber_eq_of_obj_eq (X : GrothendieckContra' F') :
    X.fiber = (F'.map (id X).base).obj X.fiber := by
  rw [id_base]
  exact Functor.congr_obj (F'.map_id X.base).symm X.fiber

@[simp]
theorem fiber_eqToHom {X Y : GrothendieckContra' F'} (h : X = Y) :
    (eqToHom h).fiber = eqToHom (by subst h; exact fiber_eq_of_obj_eq X) := by
  subst h
  rfl

lemma eqToHom_eq {X Y : GrothendieckContra' F'} (hF : X = Y) :
    eqToHom hF = { base := eqToHom (by subst hF; rfl)
                   fiber := eqToHom (by subst hF; exact fiber_eq_of_obj_eq X) } := by
  subst hF
  rfl

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
def transportIso (x : GrothendieckContra' F') {c : C} (α : x.base ≅ c) :
    x.transport α.inv ≅ x := sorry

end Transport

/--
The forgetful functor from `GrothendieckContra' F'` to `C`.
-/
@[simps]
def forget : GrothendieckContra' F' ⥤ C where
  obj X := X.base
  map f := f.base

section Functoriality

variable {F' G' H' : Cᵒᵖ' ⥤ Cat}

/--
A natural transformation `α : F' ⟶ G'` induces a functor between the corresponding
contravariant Grothendieck constructions.
-/
def map (α : F' ⟶ G') : GrothendieckContra' F' ⥤ GrothendieckContra' G' where
  obj X := ⟨X.base, (α.app X.base).obj X.fiber⟩
  map {X Y} f := ⟨f.base, (α.app X.base).map f.fiber ≫
    (eqToHom (α.naturality f.base)).app Y.fiber⟩
  map_id := sorry
  map_comp := sorry

@[simp]
theorem map_obj (α : F' ⟶ G') (X : GrothendieckContra' F') :
    (map α).obj X = ⟨X.base, (α.app X.base).obj X.fiber⟩ := rfl

@[simp]
theorem map_map (α : F' ⟶ G') {X Y : GrothendieckContra' F'} (f : X ⟶ Y) :
    (map α).map f = ⟨f.base, (α.app X.base).map f.fiber ≫
      (eqToHom (α.naturality f.base)).app Y.fiber⟩ := rfl

theorem functor_comp_forget {α : F' ⟶ G'} :
    GrothendieckContra'.map α ⋙ GrothendieckContra'.forget =
    GrothendieckContra'.forget :=
  sorry

theorem map_id_eq : map (𝟙 F') = 𝟙 (Cat.of <| GrothendieckContra' F') :=
  sorry

def mapIdIso : map (𝟙 F') ≅ 𝟙 (Cat.of <| GrothendieckContra' F') :=
  sorry

theorem map_comp_eq (α : F' ⟶ G') (β : G' ⟶ H') :
    map (α ≫ β) = map α ⋙ map β :=
  sorry

def mapCompIso (α : F' ⟶ G') (β : G' ⟶ H') :
    map (α ≫ β) ≅ map α ⋙ map β :=
  sorry

section UniverseScaling

variable {F' G' : Cᵒᵖ' ⥤ Cat.{v, u}}

/--
Inverse of the equivalence relating Grothendieck constructions across universes.
-/
def compAsSmallFunctorEquivalenceInverse :
    GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}) ⥤ GrothendieckContra' F' :=
  sorry

/--
The functor part of the equivalence relating Grothendieck constructions
across universes.
-/
def compAsSmallFunctorEquivalenceFunctor :
    GrothendieckContra' F' ⥤ GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}) :=
  sorry

/--
Equivalence relating Grothendieck constructions across universes, showing that
the construction respects universe scaling.
-/
def compAsSmallFunctorEquivalence :
    GrothendieckContra' F' ≌ GrothendieckContra' (F' ⋙ Cat.asSmallFunctor.{w}) :=
  sorry

/--
Natural isomorphism for whiskering with universe-scaling functor.
-/
def mapWhiskerRightAsSmallFunctor (α : F' ⟶ G') :
    map (Functor.whiskerRight α Cat.asSmallFunctor.{w}) ≅
    compAsSmallFunctorEquivalenceInverse (F' := F') ⋙ map α ⋙
      compAsSmallFunctorEquivalenceFunctor (F' := G') :=
  sorry

end UniverseScaling

end Functoriality

/--
The contravariant Grothendieck construction as a functor from the functor
category `(Cᵒᵖ' ⥤ Cat)` to the over category over the base category.
-/
def functor {E : Type u} [Category.{v} E] :
    (Eᵒᵖ' ⥤ Cat.{v, u}) ⥤ Over (T := Cat.{v, u}) (Cat.of Eᵒᵖ') :=
  sorry

section TypeToCategory

variable {F' : Cᵒᵖ' ⥤ Type w}

/--
The functor from the contravariant Grothendieck construction to the
category of elements.
-/
def grothendieckTypeToCatFunctor :
    GrothendieckContra' (F' ⋙ typeToCat) ⥤ F'.Elements :=
  sorry

/--
The inverse functor from the category of elements to the contravariant
Grothendieck construction.
-/
def grothendieckTypeToCatInverse :
    F'.Elements ⥤ GrothendieckContra' (F' ⋙ typeToCat) :=
  sorry

/--
Equivalence between the contravariant Grothendieck construction on `F' ⋙ typeToCat`
and the category of elements of `F'`.
-/
def grothendieckTypeToCat :
    GrothendieckContra' (F' ⋙ typeToCat) ≌ F'.Elements :=
  sorry

end TypeToCategory

section Pre

variable {E : Type u₂} [Category.{v₂} E]
variable (G : E ⥤ C)
variable {F' : Cᵒᵖ' ⥤ Cat.{w, v}}

/--
A functor `G : E ⥤ C` induces a functor between the contravariant Grothendieck
constructions.
-/
def pre : GrothendieckContra' (functorOp' G ⋙ F') ⥤ GrothendieckContra' F' :=
  sorry

/--
The weak inverse to `pre` when `G` is an equivalence.
-/
def preInv [G.IsEquivalence] :
    GrothendieckContra' F' ⥤ GrothendieckContra' (functorOp' G ⋙ F') :=
  sorry

/--
When `G` is an equivalence, `pre G` is also an equivalence.
-/
def preEquivalence [G.IsEquivalence] :
    GrothendieckContra' (functorOp' G ⋙ F') ≌ GrothendieckContra' F' :=
  sorry

end Pre

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
  map_id := sorry
  map_comp := sorry

/--
The fiber inclusion functor is faithful.
-/
instance faithful_ι (c : C) : (ι c : F'.obj c ⥤ GrothendieckContra' F').Faithful :=
  sorry

/--
Natural transformation induced by a morphism in the base category.
-/
@[simps]
def ιNatTrans {c d : C} (f : c ⟶ d) : F'.map f ⋙ ι c ⟶ ι d where
  app := sorry
  naturality := sorry

/--
Construct a functor from the contravariant Grothendieck construction given
compatible functors from each fiber.
-/
def functorFrom (G : ∀ (c : C), F'.obj c ⥤ T)
    (h : ∀ {c d : C} (f : c ⟶ d), G d ⟶ F'.map f ⋙ G c) :
    GrothendieckContra' F' ⥤ T where
  obj X := (G X.base).obj X.fiber
  map f := sorry
  map_id := sorry
  map_comp := sorry

/--
The fiber inclusion composed with `functorFrom` recovers the original fiber functor.
-/
theorem ιCompFunctorFrom (G : ∀ (c : C), F'.obj c ⥤ T)
    (h : ∀ {c d : C} (f : c ⟶ d), G d ⟶ F'.map f ⋙ G c) (c : C) :
    ι c ⋙ functorFrom G h = G c :=
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
