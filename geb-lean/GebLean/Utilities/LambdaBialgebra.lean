import Mathlib.CategoryTheory.Monad.Algebra
import GebLean.Utilities.DistributiveLaw

namespace GebLean

open CategoryTheory

universe v u

/--
A lambda-bialgebra for a distributive law `law : T∘D ⟹ D∘T`
is an object equipped with both a `T`-algebra structure and
a `D`-coalgebra structure, subject to a pentagonal
compatibility condition mediated by the distributive law:

```
         T(d)         λ_X         D(a)
  T(X) -------> T(D(X)) ----> D(T(X)) ----> D(X)
   |                                          ^
   | a                                      d |
   v                                          |
   X ─────────────────────────────────────────┘
```
-/
structure LambdaBialgebra
    {C : Type u} [Category.{v} C]
    {T : Monad C} {D : Comonad C}
    (law : DistributiveLaw T D) where
  carrier : C
  algebra :
    T.toFunctor.obj carrier ⟶ carrier
  coalgebra :
    carrier ⟶ D.toFunctor.obj carrier
  algebra_unit :
    T.η.app carrier ≫ algebra = 𝟙 carrier
  algebra_assoc :
    T.μ.app carrier ≫ algebra =
      T.toFunctor.map algebra ≫ algebra
  coalgebra_counit :
    coalgebra ≫ D.ε.app carrier = 𝟙 carrier
  coalgebra_coassoc :
    coalgebra ≫ D.δ.app carrier =
      coalgebra ≫ D.toFunctor.map coalgebra
  compat :
    T.toFunctor.map coalgebra ≫
      law.dist.app carrier ≫
      D.toFunctor.map algebra =
    algebra ≫ coalgebra

namespace LambdaBialgebra

variable
  {C : Type u} [Category.{v} C]
  {T : Monad C} {D : Comonad C}
  {law : DistributiveLaw T D}

def toMonadAlgebra (B : LambdaBialgebra law) :
    T.Algebra where
  A := B.carrier
  a := B.algebra
  unit := B.algebra_unit
  assoc := B.algebra_assoc

def toComonadCoalgebra (B : LambdaBialgebra law) :
    D.Coalgebra where
  A := B.carrier
  a := B.coalgebra
  counit := B.coalgebra_counit
  coassoc := B.coalgebra_coassoc

/--
A morphism of lambda-bialgebras is a morphism of the
underlying objects that is simultaneously a `T`-algebra
homomorphism and a `D`-coalgebra homomorphism.
-/
@[ext]
structure Hom
    (A B : LambdaBialgebra law) where
  hom : A.carrier ⟶ B.carrier
  algebra_comm :
    A.algebra ≫ hom =
      T.toFunctor.map hom ≫ B.algebra
  coalgebra_comm :
    hom ≫ B.coalgebra =
      A.coalgebra ≫ D.toFunctor.map hom

namespace Hom

def id (A : LambdaBialgebra law) : Hom A A where
  hom := 𝟙 A.carrier
  algebra_comm := by simp
  coalgebra_comm := by simp

def comp
    {P Q R : LambdaBialgebra law}
    (f : Hom P Q) (g : Hom Q R) :
    Hom P R where
  hom := f.hom ≫ g.hom
  algebra_comm := by
    rw [← Category.assoc, f.algebra_comm,
      Category.assoc, g.algebra_comm,
      ← Category.assoc, ← T.toFunctor.map_comp]
  coalgebra_comm := by
    rw [Category.assoc, g.coalgebra_comm,
      ← Category.assoc, f.coalgebra_comm,
      Category.assoc, ← D.toFunctor.map_comp]

end Hom

instance : CategoryStruct
    (LambdaBialgebra law) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

instance : Category
    (LambdaBialgebra law) where
  id_comp f := Hom.ext (Category.id_comp f.hom)
  comp_id f := Hom.ext (Category.comp_id f.hom)
  assoc f g h :=
    Hom.ext (Category.assoc f.hom g.hom h.hom)

/--
The forgetful functor from the category of
lambda-bialgebras to the underlying category.
-/
def forget : LambdaBialgebra law ⥤ C where
  obj B := B.carrier
  map f := f.hom

instance : (forget (law := law)).Faithful where
  map_injective h := Hom.ext h

end LambdaBialgebra

end GebLean
