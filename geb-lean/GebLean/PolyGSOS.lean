import GebLean.PolyDistributiveLaw
import GebLean.Utilities.GSOSRule
import GebLean.Utilities.LambdaBialgebra

namespace GebLean

open CategoryTheory

universe u

variable {X : Type u}

/--
The object component of the identity-behavior functor
for polynomial endofunctors: `A ↦ A ×_X Q(A)` where
`Q = polyEndoFunctor X Q_poly`.
-/
def polyIdBehaviorObj
    (Q : PolyEndo X) (A : Over X) : Over X :=
  overPullback A ((polyEndoFunctor X Q).obj A)

/--
The morphism component of the identity-behavior functor:
given `f : A ⟶ B`, produce
`A ×_X Q(A) ⟶ B ×_X Q(B)` via `(f, Q(f))`.
-/
def polyIdBehaviorMap
    (Q : PolyEndo X) {A B : Over X} (f : A ⟶ B) :
    polyIdBehaviorObj Q A ⟶ polyIdBehaviorObj Q B :=
  overPullbackMap f ((polyEndoFunctor X Q).map f)

/--
The identity-behavior functor `A ↦ A ×_X Q(A)` on
`Over X`, where `Q = polyEndoFunctor X Q_poly`.
-/
def polyIdBehaviorFunctor
    (Q : PolyEndo X) : Over X ⥤ Over X where
  obj := polyIdBehaviorObj Q
  map := polyIdBehaviorMap Q
  map_id := fun A => by
    apply Over.OverMorphism.ext; funext p
    simp only [
      polyIdBehaviorMap, overPullbackMap]
    rfl
  map_comp := fun {A B C} f g => by
    apply Over.OverMorphism.ext; funext p
    simp only [
      polyIdBehaviorMap, overPullbackMap,
      Over.homMk_left, Over.comp_left]
    congr 1

/--
A GSOS rule for polynomial endofunctors on `Over X`.
Given signature `P` and behavior `Q`, a GSOS rule is
a natural transformation
`P(A ×_X Q(A)) → Q(T_P(A))`
where `T_P` is the free monad on `P`.
-/
@[ext]
structure PolyGSOSRule (P Q : PolyEndo X) where
  rule :
    polyIdBehaviorFunctor Q ⋙
      polyEndoFunctor X P ⟶
    (polyFreeMonad X P).toFunctor ⋙
      polyEndoFunctor X Q

end GebLean
