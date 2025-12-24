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

end GebLean
