import Mathlib.CategoryTheory.Monad.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

namespace GebLean

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C]

/--
A chosen binary product of `X` and `Y`: an apex with
projections satisfying the universal property.
-/
structure ChosenBinaryProduct (X Y : C) where
  apex : C
  fst : apex ⟶ X
  snd : apex ⟶ Y
  isLimit : IsLimit (BinaryFan.mk fst snd)

namespace ChosenBinaryProduct

variable {X Y : C} (p : ChosenBinaryProduct X Y)

def lift {W : C} (f : W ⟶ X) (g : W ⟶ Y) :
    W ⟶ p.apex :=
  p.isLimit.lift (BinaryFan.mk f g)

@[reassoc (attr := simp)]
theorem lift_fst {W : C} (f : W ⟶ X) (g : W ⟶ Y) :
    p.lift f g ≫ p.fst = f :=
  p.isLimit.fac (BinaryFan.mk f g)
    ⟨WalkingPair.left⟩

@[reassoc (attr := simp)]
theorem lift_snd {W : C} (f : W ⟶ X) (g : W ⟶ Y) :
    p.lift f g ≫ p.snd = g :=
  p.isLimit.fac (BinaryFan.mk f g)
    ⟨WalkingPair.right⟩

theorem hom_ext {W : C} {f g : W ⟶ p.apex}
    (h₁ : f ≫ p.fst = g ≫ p.fst)
    (h₂ : f ≫ p.snd = g ≫ p.snd) :
    f = g := by
  apply p.isLimit.hom_ext
  intro ⟨j⟩
  cases j <;> assumption

end ChosenBinaryProduct

/--
Given a family of chosen binary products `X ⨯ B(X)` for
each object `X`, defines the functor `X ↦ X ⨯ B(X)`.
-/
def idBehaviorFunctor
    (B : C ⥤ C)
    (prod : (X : C) → ChosenBinaryProduct X (B.obj X)) :
    C ⥤ C where
  obj := fun X => (prod X).apex
  map := fun {X Y} f =>
    (prod Y).lift
      ((prod X).fst ≫ f)
      ((prod X).snd ≫ B.map f)
  map_id := fun X => by
    apply (prod X).hom_ext
    · simp
    · simp
  map_comp := fun {X Y Z} f g => by
    apply (prod Z).hom_ext
    · rw [Category.assoc,
        ChosenBinaryProduct.lift_fst,
        ChosenBinaryProduct.lift_fst,
        ChosenBinaryProduct.lift_fst_assoc,
        Category.assoc]
    · rw [Category.assoc,
        ChosenBinaryProduct.lift_snd,
        ChosenBinaryProduct.lift_snd,
        ChosenBinaryProduct.lift_snd_assoc,
        Category.assoc, Functor.map_comp]

/--
An abstract GSOS rule in the sense of Turi-Plotkin,
parameterized by a signature endofunctor `Sigma`, a
behavior endofunctor `B`, a monad `T`, and chosen binary
products for the identity-behavior pairing.

A GSOS rule is a natural transformation
`Sigma(X × B(X)) → B(T(X))`.
-/
@[ext]
structure GSOSRule
    (Sigma : C ⥤ C)
    (B : C ⥤ C)
    (T : Monad C)
    (prod :
      (X : C) → ChosenBinaryProduct X (B.obj X))
    where
  rule :
    idBehaviorFunctor B prod ⋙ Sigma ⟶
    T.toFunctor ⋙ B

end GebLean
