import Mathlib.CategoryTheory.Monad.Basic
import GebLean.Utilities.ComputableLimits

namespace GebLean

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C]

/-- Given a family of chosen binary products
`X × B(X)` for each object `X`, defines the
functor `X ↦ X × B(X)`. -/
def idBehaviorFunctor
    (B : C ⥤ C)
    (prod : (X : C) →
      ChosenBinaryProduct X (B.obj X)) :
    C ⥤ C where
  obj := fun X => (prod X).obj
  map := fun {X Y} f =>
    (prod Y).lift
      ((prod X).fst ≫ f)
      ((prod X).snd ≫ B.map f)
  map_id := fun X => by
    symm
    exact (prod X).lift_uniq _ _
      (𝟙 _) (by simp) (by simp)
  map_comp := fun {X Y Z} f g => by
    symm
    apply (prod Z).lift_uniq
    · rw [Category.assoc,
        (prod Z).lift_fst,
        ← Category.assoc,
        (prod Y).lift_fst,
        Category.assoc]
    · rw [Category.assoc,
        (prod Z).lift_snd,
        ← Category.assoc,
        (prod Y).lift_snd,
        Category.assoc,
        Functor.map_comp]

/-- An abstract GSOS rule in the sense of
Turi-Plotkin, parameterized by a signature
endofunctor `Sigma`, a behavior endofunctor `B`,
a monad `T`, and chosen binary products for the
identity-behavior pairing.

A GSOS rule is a natural transformation
`Sigma(X × B(X)) → B(T(X))`. -/
@[ext]
structure GSOSRule
    (Sigma : C ⥤ C)
    (B : C ⥤ C)
    (T : Monad C)
    (prod :
      (X : C) →
        ChosenBinaryProduct X (B.obj X))
    where
  rule :
    idBehaviorFunctor B prod ⋙ Sigma ⟶
    T.toFunctor ⋙ B

end GebLean
