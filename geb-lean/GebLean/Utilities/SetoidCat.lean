import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Setoid.Basic

/-!
# Category of Setoids

This module defines the category of setoids, where objects are types equipped
with equivalence relations and morphisms are functions that preserve the
equivalence relation.

## Main definitions

* `SetoidBundle`: A type bundled with an equivalence relation.
* `SetoidHom`: Morphisms between setoids (equivalence-preserving functions).
* `SetoidCat`: The category of setoids.
-/

namespace GebLean

universe u

/-- The quotient by `trueSetoid` (where all elements are related) is a
    subsingleton. All elements are identified in the quotient. -/
instance Quotient.trueSetoid_subsingleton (α : Sort*) :
    Subsingleton (Quotient (@trueSetoid α)) where
  allEq := by
    intro a b
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact Quotient.sound trivial

/--
A type bundled with an equivalence relation (setoid structure).
-/
structure SetoidBundle where
  /-- The carrier type. -/
  carrier : Type u
  /-- The equivalence relation on the carrier. -/
  rel : Setoid carrier

namespace SetoidBundle

/--
Construct a `SetoidBundle` from a type with a `Setoid` instance.
-/
def of (α : Type u) [s : Setoid α] : SetoidBundle := ⟨α, s⟩

instance : CoeSort SetoidBundle (Type u) where
  coe X := X.carrier

/--
The setoid instance on the carrier.
-/
instance instSetoid (X : SetoidBundle) : Setoid X.carrier := X.rel

end SetoidBundle

/--
A morphism of setoids: a function that preserves the equivalence relation.
-/
structure SetoidHom (X Y : SetoidBundle) where
  /-- The underlying function. -/
  toFun : X.carrier → Y.carrier
  /-- The function preserves the equivalence relation. -/
  map_rel : ∀ a b, X.rel.r a b → Y.rel.r (toFun a) (toFun b)

namespace SetoidHom

variable {X Y Z : SetoidBundle}

instance : CoeFun (SetoidHom X Y) (fun _ => X.carrier → Y.carrier) where
  coe f := f.toFun

@[ext]
theorem ext {f g : SetoidHom X Y} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g
  congr
  funext x
  exact h x

/--
The identity morphism on a setoid.
-/
def id (X : SetoidBundle) : SetoidHom X X where
  toFun := _root_.id
  map_rel := fun _ _ h => h

/--
Composition of setoid morphisms.
-/
def comp (g : SetoidHom Y Z) (f : SetoidHom X Y) : SetoidHom X Z where
  toFun := g.toFun ∘ f.toFun
  map_rel := fun _ _ hab => g.map_rel _ _ (f.map_rel _ _ hab)

@[simp]
theorem id_apply (x : X.carrier) : (SetoidHom.id X) x = x := rfl

@[simp]
theorem comp_apply (g : SetoidHom Y Z) (f : SetoidHom X Y) (x : X.carrier) :
    (g.comp f) x = g (f x) := rfl

theorem comp_assoc {W : SetoidBundle} (h : SetoidHom Z W) (g : SetoidHom Y Z)
    (f : SetoidHom X Y) : (h.comp g).comp f = h.comp (g.comp f) := by
  ext x
  rfl

theorem id_comp (f : SetoidHom X Y) : (SetoidHom.id Y).comp f = f := by
  ext x
  rfl

theorem comp_id (f : SetoidHom X Y) : f.comp (SetoidHom.id X) = f := by
  ext x
  rfl

end SetoidHom

open CategoryTheory

/--
The category of setoids.
-/
instance SetoidCat : Category SetoidBundle where
  Hom := SetoidHom
  id := SetoidHom.id
  comp := fun f g => SetoidHom.comp g f
  id_comp := SetoidHom.comp_id
  comp_id := SetoidHom.id_comp
  assoc := fun f g h => (SetoidHom.comp_assoc h g f).symm

namespace SetoidBundle

/--
The quotient functor from `SetoidCat` to `Type`.
This sends each setoid to its quotient type.
-/
def quotientFunctor : SetoidBundle ⥤ Type u where
  obj X := Quotient X.rel
  map f := Quotient.map' f.toFun f.map_rel
  map_id X := by
    ext ⟨x⟩
    rfl
  map_comp f g := by
    ext ⟨x⟩
    rfl

/--
The forgetful functor from `SetoidCat` to `Type`.
This sends each setoid to its carrier type.
-/
def forgetful : SetoidBundle ⥤ Type u where
  obj X := X.carrier
  map f := f.toFun
  map_id _ := rfl
  map_comp _ _ := rfl

/--
The natural transformation from the forgetful functor to the quotient functor.
-/
def quotientNat : forgetful ⟶ quotientFunctor :=
  { app := fun X => Quotient.mk X.rel
    naturality := fun _ _ _ => rfl }

end SetoidBundle

/-! ## Setoid Natural Transformations

For functors into SetoidBundle, we can define a weaker notion of natural
transformation where naturality holds up to the setoid equivalence relation,
rather than strictly. This captures "proof-irrelevant" naturality.
-/

open CategoryTheory

variable {C : Type*} [Category C]

/--
A setoid natural transformation between functors F, G : C ⥤ SetoidBundle.
The naturality condition holds up to the setoid equivalence relation on
the target, rather than as strict equality.
-/
structure SetoidNatTrans (F G : C ⥤ SetoidBundle) where
  /-- The component morphisms. -/
  app : ∀ A : C, SetoidHom (F.obj A) (G.obj A)
  /-- Naturality up to setoid equivalence. -/
  naturality_rel : ∀ {A B : C} (f : A ⟶ B) (x : (F.obj A).carrier),
    (G.obj B).rel.r
      ((app B).comp (F.map f) x)
      ((G.map f).comp (app A) x)

namespace SetoidNatTrans

variable {F G H : C ⥤ SetoidBundle}

/--
The identity setoid natural transformation.
-/
def id (F : C ⥤ SetoidBundle) : SetoidNatTrans F F where
  app := fun A => SetoidHom.id (F.obj A)
  naturality_rel := fun f x => by
    simp only [SetoidHom.id, SetoidHom.comp]
    exact (F.obj _).rel.refl _

/--
Composition of setoid natural transformations.
-/
def comp (β : SetoidNatTrans G H) (α : SetoidNatTrans F G) :
    SetoidNatTrans F H where
  app := fun A => (β.app A).comp (α.app A)
  naturality_rel := fun {A B} f x => by
    simp only [SetoidHom.comp_apply]
    have hα := α.naturality_rel f x
    have hβ := β.naturality_rel f (α.app A x)
    have hβ' := (β.app B).map_rel _ _ hα
    exact (H.obj B).rel.trans hβ' hβ

end SetoidNatTrans

/--
A setoid natural isomorphism between functors F, G : C ⥤ SetoidBundle.
This is a pair of setoid natural transformations that are inverses
up to the setoid equivalence relations.
-/
structure SetoidNatIso (F G : C ⥤ SetoidBundle) where
  /-- The forward transformation. -/
  hom : SetoidNatTrans F G
  /-- The inverse transformation. -/
  inv : SetoidNatTrans G F
  /-- Inverse composed with hom equals identity (strictly). -/
  inv_hom_id : ∀ A, (inv.app A).comp (hom.app A) = SetoidHom.id (F.obj A)
  /-- Hom composed with inverse is equivalent to identity. -/
  hom_inv_rel : ∀ A (x : (G.obj A).carrier),
    (G.obj A).rel.r ((hom.app A).comp (inv.app A) x) x

namespace SetoidNatIso

variable {F G H : C ⥤ SetoidBundle}

/--
The identity setoid natural isomorphism.
-/
def refl (F : C ⥤ SetoidBundle) : SetoidNatIso F F where
  hom := SetoidNatTrans.id F
  inv := SetoidNatTrans.id F
  inv_hom_id := fun _ => rfl
  hom_inv_rel := fun A x => (F.obj A).rel.refl x

/--
Symmetry for setoid natural isomorphisms.
Note: This requires the stricter condition that BOTH round-trips are strict.
For the general case where only one is strict, we have an asymmetric structure.
-/
def symm (iso : SetoidNatIso F G)
    (h : ∀ A, (iso.hom.app A).comp (iso.inv.app A) = SetoidHom.id (G.obj A)) :
    SetoidNatIso G F where
  hom := iso.inv
  inv := iso.hom
  inv_hom_id := h
  hom_inv_rel := fun A x => by
    have h := iso.inv_hom_id A
    change (F.obj A).rel.r (((iso.inv.app A).comp (iso.hom.app A)) x) x
    rw [h]
    exact (F.obj A).rel.refl x

end SetoidNatIso

/--
A setoid equivalence between a category and a category of setoid-valued functors.
This captures the situation where we have an equivalence "up to setoid relations"
on one side.

The asymmetry reflects that one category (PolyPresentationLoc) has quotients
already taken, while the other (D ⥤ SetoidBundle) tracks equivalences explicitly.
-/
structure SetoidEquivalence (D : Type*) [Category D]
    (P : Type*) [Category P] where
  /-- The functor from P to setoid-valued copresheaves. -/
  toSetoidCopresheaf : P ⥤ (D ⥤ SetoidBundle.{u})
  /-- The density functor from setoid-valued copresheaves to P. -/
  fromSetoidCopresheaf : (D ⥤ SetoidBundle.{u}) ⥤ P
  /-- The counit is a strict natural isomorphism (P has quotients). -/
  counitIso : toSetoidCopresheaf ⋙ fromSetoidCopresheaf ≅ 𝟭 P
  /-- The unit component for each functor F is a setoid natural isomorphism. -/
  unitIso : ∀ F : D ⥤ SetoidBundle.{u},
    SetoidNatIso F (toSetoidCopresheaf.obj (fromSetoidCopresheaf.obj F))
  /-- Naturality of the unit with respect to morphisms in D ⥤ SetoidBundle,
      up to setoid equivalence. For α : F ⟶ G and each object A : D,
      the diagram commutes up to the setoid relation on the target. -/
  unit_naturality_rel : ∀ {F G : D ⥤ SetoidBundle.{u}} (α : F ⟶ G) (A : D)
    (x : (F.obj A).carrier),
    ((toSetoidCopresheaf.obj (fromSetoidCopresheaf.obj G)).obj A).rel.r
      (((unitIso G).hom.app A).comp (α.app A) x)
      (((toSetoidCopresheaf.map (fromSetoidCopresheaf.map α)).app A).comp
        ((unitIso F).hom.app A) x)

end GebLean
