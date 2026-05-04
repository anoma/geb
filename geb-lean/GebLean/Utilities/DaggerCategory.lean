import Mathlib.CategoryTheory.Category.Basic

/-!
# Dagger Categories

A dagger category is a category equipped with an involutive
contravariant identity-on-objects endofunctor: for each morphism
`f : A ⟶ B` there is a designated `dagger f : B ⟶ A` satisfying
the three axioms below.
-/

namespace GebLean

open CategoryTheory

universe u v

/-- A dagger category is a category `C` with an involutive,
identity-on-objects, contravariant operation on morphisms. -/
class DaggerCategory (C : Type u) [Category.{v} C] where
  /-- The dagger of a morphism `f : A ⟶ B`. -/
  dagger : {A B : C} → (A ⟶ B) → (B ⟶ A)
  /-- The dagger of an identity morphism is the identity. -/
  dagger_id : ∀ (A : C), dagger (𝟙 A) = 𝟙 A
  /-- The dagger reverses composition. -/
  dagger_comp :
    ∀ {A B D : C} (f : A ⟶ B) (g : B ⟶ D),
    dagger (f ≫ g) = dagger g ≫ dagger f
  /-- The dagger is its own inverse. -/
  dagger_involutive :
    ∀ {A B : C} (f : A ⟶ B), dagger (dagger f) = f

end GebLean
