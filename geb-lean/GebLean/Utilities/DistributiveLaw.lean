import Mathlib.CategoryTheory.Monad.Basic

namespace GebLean

open CategoryTheory

universe v u

/--
A distributive law of a monad `T` over a comonad `D` on a
category `C` consists of a natural transformation
`dist : D ⋙ T ⟶ T ⋙ D` (where composition is diagrammatic)
satisfying four coherence axioms relating the monad
unit/multiplication to the comonad counit/comultiplication.
-/
@[ext]
structure DistributiveLaw
    {C : Type u} [Category.{v} C]
    (T : Monad C) (D : Comonad C) where
  dist :
    D.toFunctor ⋙ T.toFunctor ⟶
    T.toFunctor ⋙ D.toFunctor
  unit : ∀ (X : C),
    T.η.app (D.toFunctor.obj X) ≫ dist.app X =
      D.toFunctor.map (T.η.app X)
  mul : ∀ (X : C),
    T.μ.app (D.toFunctor.obj X) ≫ dist.app X =
      T.toFunctor.map (dist.app X) ≫
      dist.app (T.toFunctor.obj X) ≫
      D.toFunctor.map (T.μ.app X)
  counit : ∀ (X : C),
    dist.app X ≫ D.ε.app (T.toFunctor.obj X) =
      T.toFunctor.map (D.ε.app X)
  comul : ∀ (X : C),
    T.toFunctor.map (D.δ.app X) ≫
      dist.app (D.toFunctor.obj X) ≫
      D.toFunctor.map (dist.app X) =
      dist.app X ≫ D.δ.app (T.toFunctor.obj X)

end GebLean
