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

def toMonadAlgebraHom
    {A B : LambdaBialgebra law}
    (f : Hom A B) :
    A.toMonadAlgebra.Hom B.toMonadAlgebra where
  f := f.hom
  h := f.algebra_comm.symm

def toComonadCoalgebraHom
    {A B : LambdaBialgebra law}
    (f : Hom A B) :
    A.toComonadCoalgebra.Hom
      B.toComonadCoalgebra where
  f := f.hom
  h := f.coalgebra_comm.symm

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

section LiftedFunctors

variable
  {C : Type u} [Category.{v} C]
  {T : Monad C} {D : Comonad C}
  (law : DistributiveLaw T D)

/--
Given a distributive law `law : T∘D ⟹ D∘T`, we can lift
the comonad `D` to an endofunctor on the Eilenberg-Moore
category `T.Algebra`.  On objects, `(A, a) ↦ (DA, λ_A ≫ Da)`.
-/
def liftComonadObj (alg : T.Algebra) :
    T.Algebra where
  A := D.toFunctor.obj alg.A
  a := law.dist.app alg.A ≫
    D.toFunctor.map alg.a
  unit := by
    -- (η ≫ dist) ≫ D(a) = D(η) ≫ D(a) = D(η ≫ a) = D(id)
    rw [reassoc_of% (law.unit alg.A),
      ← D.toFunctor.map_comp, alg.unit,
      D.toFunctor.map_id]
  assoc := by
    -- LHS: use dist law mul to expand (μ ≫ dist)
    rw [reassoc_of% (law.mul alg.A)]
    -- Now: T(dist) ≫ dist_{TA} ≫ D(μ) ≫ D(a)
    -- Combine D(μ ≫ a) = D(T(a) ≫ a) by algebra assoc
    rw [← D.toFunctor.map_comp,
      alg.assoc, D.toFunctor.map_comp]
    -- Now: T(dist) ≫ dist_{TA} ≫ D(T(a)) ≫ D(a)
    -- Use naturality of dist at a
    rw [← reassoc_of% (law.dist.naturality alg.a)]
    -- Now: T(dist) ≫ T(D(a)) ≫ dist ≫ D(a)
    -- Combine T(dist ≫ D(a))
    rw [← T.toFunctor.map_comp_assoc]

def liftComonadMap
    {alg₁ alg₂ : T.Algebra}
    (f : alg₁ ⟶ alg₂) :
    liftComonadObj law alg₁ ⟶
    liftComonadObj law alg₂ where
  f := D.toFunctor.map f.f
  h := by
    simp only [liftComonadObj]
    -- Goal: T(D(f)) ≫ dist ≫ D(a₂) =
    --       (dist ≫ D(a₁)) ≫ D(f)
    -- RHS: reassociate
    rw [Category.assoc]
    -- Now: ... = dist ≫ D(a₁) ≫ D(f)
    -- RHS: combine D.map
    rw [← D.toFunctor.map_comp]
    -- Now: ... = dist ≫ D(a₁ ≫ f)
    -- Use algebra hom: a₁ ≫ f = T(f) ≫ a₂
    rw [← f.h]
    -- Now: ... = dist ≫ D(T(f) ≫ a₂)
    -- Split D.map
    rw [D.toFunctor.map_comp]
    -- Now: ... = dist ≫ D(T(f)) ≫ D(a₂)
    -- Use naturality of dist at f
    simp only [reassoc_of%
      (law.dist.naturality f.f)]

/--
The endofunctor on `T.Algebra` induced by lifting the
comonad `D` through the distributive law.
-/
def liftComonad : T.Algebra ⥤ T.Algebra where
  obj := liftComonadObj law
  map f := liftComonadMap law f
  map_id alg := by
    apply Monad.Algebra.Hom.ext
    simp [liftComonadMap, liftComonadObj]
  map_comp f g := by
    simp only [liftComonadMap]
    congr 1
    simp

/--
The counit of the lifted comonad: `ε_A` as a `T`-algebra
homomorphism from `(DA, λ_A ≫ Da)` to `(A, a)`.
-/
def liftComonadCounit (alg : T.Algebra) :
    liftComonadObj law alg ⟶ alg where
  f := D.ε.app alg.A
  h := by
    simp only [liftComonadObj]
    rw [Category.assoc,
      D.ε.naturality alg.a]
    simp only [Functor.id_map]
    rw [← Category.assoc, law.counit]

/--
The comultiplication of the lifted comonad: `δ_A` as a
`T`-algebra homomorphism from `(DA, λ_A ≫ Da)` to
`(D²A, λ_{DA} ≫ D(λ_A) ≫ D²(a))`.
-/
def liftComonadComul (alg : T.Algebra) :
    liftComonadObj law alg ⟶
    liftComonadObj law (liftComonadObj law alg)
    where
  f := D.δ.app alg.A
  h := by
    simp only [liftComonadObj]
    -- RHS: reassociate
    rw [Category.assoc]
    -- Use naturality of δ at alg.a
    rw [D.δ.naturality alg.a]
    simp only [Functor.comp_map]
    -- Now: ... = dist ≫ δ_{TA} ≫ D(D(a))
    -- Use dist law comul (reversed)
    rw [← Category.assoc
      (law.dist.app alg.A),
      ← law.comul alg.A]
    rw [D.toFunctor.map_comp]
    simp only [Category.assoc]

/--
The natural transformation providing the counit of the
lifted comonad.
-/
def liftComonadEps :
    liftComonad law ⟶ 𝟭 T.Algebra where
  app := liftComonadCounit law
  naturality := fun {X Y} f => by
    apply Monad.Algebra.Hom.ext
    simp [liftComonadCounit, liftComonadMap,
      liftComonad, D.ε.naturality]

/--
The natural transformation providing the comultiplication
of the lifted comonad.
-/
def liftComonadDelta :
    liftComonad law ⟶
    liftComonad law ⋙ liftComonad law where
  app := liftComonadComul law
  naturality := fun {X Y} f => by
    apply Monad.Algebra.Hom.ext
    simp [liftComonadComul, liftComonadMap,
      liftComonad, D.δ.naturality]

/--
The comonad on `T.Algebra` obtained by lifting `D` through
the distributive law.
-/
def liftedComonad : Comonad T.Algebra where
  toFunctor := liftComonad law
  ε := liftComonadEps law
  δ := liftComonadDelta law
  left_counit alg := by
    apply Monad.Algebra.Hom.ext
    simp [liftComonadEps, liftComonadDelta,
      liftComonadCounit, liftComonadComul,
      liftComonad, liftComonadMap,
      liftComonadObj]
  right_counit alg := by
    apply Monad.Algebra.Hom.ext
    simp [liftComonadEps, liftComonadDelta,
      liftComonadCounit, liftComonadComul,
      liftComonad, liftComonadMap,
      liftComonadObj]
  coassoc alg := by
    apply Monad.Algebra.Hom.ext
    simp [liftComonadDelta, liftComonadComul,
      liftComonad, liftComonadMap,
      liftComonadObj]

/--
Given a distributive law `law : T∘D ⟹ D∘T`, we can lift
the monad `T` to an endofunctor on the co-Eilenberg-Moore
category `D.Coalgebra`.  On objects,
`(A, d) ↦ (TA, Td ≫ λ_A)`.
-/
def liftMonadObj (coalg : D.Coalgebra) :
    D.Coalgebra where
  A := T.toFunctor.obj coalg.A
  a := T.toFunctor.map coalg.a ≫
    law.dist.app coalg.A
  counit := by
    -- (T(d) ≫ dist) ≫ ε_{TX} = T(d) ≫ T(ε) = T(d ≫ ε) = T(id)
    rw [Category.assoc, law.counit,
      ← T.toFunctor.map_comp, coalg.counit,
      T.toFunctor.map_id]
  coassoc := by
    -- LHS: (T(d) ≫ dist) ≫ D.δ(TX)
    -- Use comul commutativity (reversed) on dist ≫ D.δ
    rw [Category.assoc, ← law.comul coalg.A]
    -- Now: T(d) ≫ T(D.δ) ≫ dist_{DX} ≫ D(dist)
    -- Combine T.map, use coalg coassoc, split
    rw [← T.toFunctor.map_comp_assoc,
      coalg.coassoc, T.toFunctor.map_comp_assoc]
    -- Now: T(d) ≫ T(D(d)) ≫ dist_{DX} ≫ D(dist)
    -- Use naturality of dist at d
    rw [reassoc_of%
      (law.dist.naturality coalg.a)]
    -- Now: T(d) ≫ dist ≫ D(T(d)) ≫ D(dist)
    -- Combine D.map and reassociate
    rw [← D.toFunctor.map_comp,
      ← Category.assoc]

def liftMonadMap
    {coalg₁ coalg₂ : D.Coalgebra}
    (f : coalg₁ ⟶ coalg₂) :
    liftMonadObj law coalg₁ ⟶
    liftMonadObj law coalg₂ where
  f := T.toFunctor.map f.f
  h := by
    simp only [liftMonadObj]
    -- Goal: (T(d₁) ≫ dist) ≫ D(T(f)) =
    --       T(f) ≫ T(d₂) ≫ dist
    -- RHS: combine T.map
    rw [← T.toFunctor.map_comp_assoc]
    -- Now RHS: T(f ≫ d₂) ≫ dist
    -- Use coalgebra hom: f ≫ d₂ = d₁ ≫ D(f)
    rw [← f.h]
    -- Now RHS: T(d₁ ≫ D(f)) ≫ dist
    -- Split T.map
    rw [T.toFunctor.map_comp_assoc]
    -- Now RHS: T(d₁) ≫ T(D(f)) ≫ dist
    -- Use naturality of dist at f
    simp only [Category.assoc,
      ← Functor.comp_map,
      law.dist.naturality]

/--
The endofunctor on `D.Coalgebra` induced by lifting the
monad `T` through the distributive law.
-/
def liftMonad : D.Coalgebra ⥤ D.Coalgebra where
  obj := liftMonadObj law
  map f := liftMonadMap law f
  map_id coalg := by
    apply Comonad.Coalgebra.Hom.ext
    simp [liftMonadMap, liftMonadObj]
  map_comp f g := by
    simp only [liftMonadMap]
    congr 1
    simp

/--
The unit of the lifted monad: `η_A` as a `D`-coalgebra
homomorphism from `(A, d)` to `(TA, Td ≫ λ_A)`.
-/
def liftMonadUnit (coalg : D.Coalgebra) :
    coalg ⟶ liftMonadObj law coalg where
  f := T.η.app coalg.A
  h := by
    simp only [liftMonadObj]
    -- d ≫ D(η) = η ≫ T(d) ≫ dist
    -- Use naturality of η at d
    rw [← reassoc_of%
      (T.η.naturality coalg.a)]
    congr 1
    exact (law.unit coalg.A).symm

/--
The multiplication of the lifted monad: `μ_A` as a
`D`-coalgebra homomorphism from
`(T²A, T²d ≫ T(λ_A) ≫ λ_{TA})` to `(TA, Td ≫ λ_A)`.
-/
def liftMonadMul (coalg : D.Coalgebra) :
    liftMonadObj law (liftMonadObj law coalg) ⟶
    liftMonadObj law coalg where
  f := T.μ.app coalg.A
  h := by
    simp only [liftMonadObj]
    simp only [T.toFunctor.map_comp, Category.assoc]
    -- Use naturality of μ at d and mul commutativity
    conv_rhs =>
      rw [← Category.assoc,
        show T.μ.app coalg.A ≫
          T.toFunctor.map coalg.a =
          T.toFunctor.map (T.toFunctor.map coalg.a)
            ≫ T.μ.app (D.toFunctor.obj coalg.A)
          from (T.μ.naturality coalg.a).symm,
        Category.assoc, law.mul coalg.A]

/--
The natural transformation providing the unit of the
lifted monad.
-/
def liftMonadEta :
    𝟭 D.Coalgebra ⟶ liftMonad law where
  app := liftMonadUnit law
  naturality := fun {X Y} f => by
    apply Comonad.Coalgebra.Hom.ext
    simp only [liftMonadUnit, liftMonadMap,
      liftMonad]
    exact T.η.naturality f.f

/--
The natural transformation providing the multiplication
of the lifted monad.
-/
def liftMonadMu :
    liftMonad law ⋙ liftMonad law ⟶
    liftMonad law where
  app := liftMonadMul law
  naturality := fun {X Y} f => by
    apply Comonad.Coalgebra.Hom.ext
    simp only [liftMonadMul, liftMonadMap,
      liftMonad]
    exact T.μ.naturality f.f

/--
The monad on `D.Coalgebra` obtained by lifting `T` through
the distributive law.
-/
def liftedMonad : Monad D.Coalgebra where
  toFunctor := liftMonad law
  η := liftMonadEta law
  μ := liftMonadMu law
  left_unit coalg := by
    apply Comonad.Coalgebra.Hom.ext
    simp [liftMonadEta, liftMonadMu,
      liftMonadUnit, liftMonadMul,
      liftMonad, liftMonadMap,
      liftMonadObj]
  right_unit coalg := by
    apply Comonad.Coalgebra.Hom.ext
    simp [liftMonadEta, liftMonadMu,
      liftMonadUnit, liftMonadMul,
      liftMonad, liftMonadMap,
      liftMonadObj]
  assoc coalg := by
    apply Comonad.Coalgebra.Hom.ext
    simp only [liftMonadMu, liftMonadMul,
      liftMonad, liftMonadMap,
      liftMonadObj]
    exact T.assoc coalg.A

end LiftedFunctors

section Equivalences

variable
  {C : Type u} [Category.{v} C]
  {T : Monad C} {D : Comonad C}
  (law : DistributiveLaw T D)

/--
A lambda-bialgebra yields a coalgebra of the lifted comonad
on `T.Algebra`.  The coalgebra structure map `d` becomes a
`T`-algebra homomorphism by the pentagonal compatibility law.
-/
def LambdaBialgebra.toLiftedComonadCoalgebra
    (B : LambdaBialgebra law) :
    (liftedComonad law).Coalgebra where
  A := B.toMonadAlgebra
  a :=
    { f := B.coalgebra
      h := B.compat }
  counit := by
    apply Monad.Algebra.Hom.ext
    exact B.coalgebra_counit
  coassoc := by
    apply Monad.Algebra.Hom.ext
    exact B.coalgebra_coassoc

/--
A coalgebra of the lifted comonad on `T.Algebra` yields a
lambda-bialgebra.  The `T`-algebra structure comes from the
carrier algebra, and the `D`-coalgebra structure from the
coalgebra map, which is a `T`-algebra homomorphism; this
homomorphism property is exactly the pentagonal compatibility.
-/
def liftedComonadCoalgebra_toLambdaBialgebra
    (coal : (liftedComonad law).Coalgebra) :
    LambdaBialgebra law where
  carrier := coal.A.A
  algebra := coal.A.a
  coalgebra := coal.a.f
  algebra_unit := coal.A.unit
  algebra_assoc := coal.A.assoc
  coalgebra_counit := by
    have := coal.counit
    simp only [liftedComonad, liftComonadEps,
      liftComonadCounit] at this
    exact congrArg Monad.Algebra.Hom.f this
  coalgebra_coassoc := by
    have := coal.coassoc
    simp only [liftedComonad, liftComonadDelta,
      liftComonadComul, liftComonad,
      liftComonadMap, liftComonadObj] at this
    exact congrArg Monad.Algebra.Hom.f this
  compat := coal.a.h

/--
A lambda-bialgebra morphism yields a coalgebra morphism of
the lifted comonad.
-/
def LambdaBialgebra.Hom.toLiftedComonadCoalgebraHom
    {B₁ B₂ : LambdaBialgebra law}
    (f : LambdaBialgebra.Hom B₁ B₂) :
    B₁.toLiftedComonadCoalgebra law ⟶
    B₂.toLiftedComonadCoalgebra law where
  f :=
    { f := f.hom
      h := f.algebra_comm.symm }
  h := by
    apply Monad.Algebra.Hom.ext
    exact f.coalgebra_comm.symm

/--
A coalgebra morphism of the lifted comonad yields a
lambda-bialgebra morphism.
-/
def liftedComonadCoalgebraHom_toLambdaBialgebraHom
    {coal₁ coal₂ : (liftedComonad law).Coalgebra}
    (f : coal₁ ⟶ coal₂) :
    LambdaBialgebra.Hom
      (liftedComonadCoalgebra_toLambdaBialgebra law coal₁)
      (liftedComonadCoalgebra_toLambdaBialgebra
        law coal₂) where
  hom := f.f.f
  algebra_comm := f.f.h.symm
  coalgebra_comm := by
    have := f.h
    simp only [liftedComonad, liftComonad,
      liftComonadMap, liftComonadObj] at this
    exact (congrArg Monad.Algebra.Hom.f this).symm

/--
The functor from the lambda-bialgebra category to the
category of coalgebras of the lifted comonad on `T.Algebra`.
-/
def lambdaBialgebraToLiftedComonadCoalgebra :
    LambdaBialgebra law ⥤
    (liftedComonad law).Coalgebra where
  obj B := B.toLiftedComonadCoalgebra law
  map f := f.toLiftedComonadCoalgebraHom law
  map_id _ := by
    apply Comonad.Coalgebra.Hom.ext
    apply Monad.Algebra.Hom.ext
    rfl
  map_comp _ _ := by
    apply Comonad.Coalgebra.Hom.ext
    apply Monad.Algebra.Hom.ext
    rfl

/--
The functor from coalgebras of the lifted comonad on
`T.Algebra` to the lambda-bialgebra category.
-/
def liftedComonadCoalgebraToLambdaBialgebra :
    (liftedComonad law).Coalgebra ⥤
    LambdaBialgebra law where
  obj coal :=
    liftedComonadCoalgebra_toLambdaBialgebra law coal
  map f :=
    liftedComonadCoalgebraHom_toLambdaBialgebraHom
      law f
  map_id _ := by
    apply LambdaBialgebra.Hom.ext
    rfl
  map_comp _ _ := by
    apply LambdaBialgebra.Hom.ext
    rfl

/--
The round-trip `LambdaBialgebra → Coalgebra → LambdaBialgebra`
is the identity on carriers, algebras, and coalgebras.
-/
private theorem roundTrip_carrier
    (B : LambdaBialgebra law) :
    ((liftedComonadCoalgebraToLambdaBialgebra law).obj
      ((lambdaBialgebraToLiftedComonadCoalgebra
        law).obj B)).carrier =
    B.carrier := rfl

/--
The identity morphism on `B.carrier` viewed as a hom from
`B` to the round-trip of `B` (unit direction).
-/
private def unitHom
    (B : LambdaBialgebra law) :
    B ⟶ (lambdaBialgebraToLiftedComonadCoalgebra law
      ⋙ liftedComonadCoalgebraToLambdaBialgebra
        law).obj B where
  hom := 𝟙 B.carrier
  algebra_comm := by simp; rfl
  coalgebra_comm := by simp; rfl

/--
The identity morphism on `B.carrier` viewed as a hom from
the round-trip of `B` to `B` (unit inverse direction).
-/
private def unitInv
    (B : LambdaBialgebra law) :
    (lambdaBialgebraToLiftedComonadCoalgebra law
      ⋙ liftedComonadCoalgebraToLambdaBialgebra
        law).obj B ⟶ B where
  hom := 𝟙 B.carrier
  algebra_comm := by
    change _ ≫ 𝟙 B.carrier =
      T.toFunctor.map (𝟙 B.carrier) ≫ B.algebra
    simp; rfl
  coalgebra_comm := by
    change 𝟙 B.carrier ≫ B.coalgebra =
      B.coalgebra ≫ D.toFunctor.map (𝟙 B.carrier)
    simp

private def unitIsoComponent
    (B : LambdaBialgebra law) :
    B ≅ (lambdaBialgebraToLiftedComonadCoalgebra law
      ⋙ liftedComonadCoalgebraToLambdaBialgebra
        law).obj B where
  hom := unitHom law B
  inv := unitInv law B
  hom_inv_id := LambdaBialgebra.Hom.ext
    (Category.id_comp _)
  inv_hom_id := LambdaBialgebra.Hom.ext
    (Category.id_comp _)

private def counitHom
    (coal : (liftedComonad law).Coalgebra) :
    (liftedComonadCoalgebraToLambdaBialgebra law ⋙
      lambdaBialgebraToLiftedComonadCoalgebra
        law).obj coal ⟶ coal where
  f :=
    { f := 𝟙 coal.A.A
      h := by
        change T.toFunctor.map (𝟙 coal.A.A) ≫
          coal.A.a =
          coal.A.a ≫ 𝟙 coal.A.A
        simp only [Functor.map_id, Category.id_comp,
          Category.comp_id] }
  h := by
    apply Monad.Algebra.Hom.ext
    change coal.a.f ≫
      D.toFunctor.map (𝟙 coal.A.A) =
      𝟙 coal.A.A ≫ coal.a.f
    simp only [Functor.map_id, Category.id_comp]
    erw [Category.comp_id]

private def counitInv
    (coal : (liftedComonad law).Coalgebra) :
    coal ⟶
    (liftedComonadCoalgebraToLambdaBialgebra law ⋙
      lambdaBialgebraToLiftedComonadCoalgebra
        law).obj coal where
  f :=
    { f := 𝟙 coal.A.A
      h := by
        change T.toFunctor.map (𝟙 coal.A.A) ≫
          coal.A.a = coal.A.a ≫ 𝟙 coal.A.A
        simp only [Functor.map_id, Category.id_comp,
          Category.comp_id] }
  h := by
    apply Monad.Algebra.Hom.ext
    change coal.a.f ≫
      D.toFunctor.map (𝟙 coal.A.A) =
      𝟙 coal.A.A ≫ coal.a.f
    simp only [Functor.map_id, Category.id_comp]
    erw [Category.comp_id]

private def counitIsoComponent
    (coal : (liftedComonad law).Coalgebra) :
    (liftedComonadCoalgebraToLambdaBialgebra law ⋙
      lambdaBialgebraToLiftedComonadCoalgebra
        law).obj coal ≅ coal where
  hom := counitHom law coal
  inv := counitInv law coal
  hom_inv_id := by
    apply Comonad.Coalgebra.Hom.ext
    apply Monad.Algebra.Hom.ext
    exact Category.id_comp _
  inv_hom_id := by
    apply Comonad.Coalgebra.Hom.ext
    apply Monad.Algebra.Hom.ext
    exact Category.id_comp _

/--
Lambda-bialgebras for a distributive law `law` are
equivalent, as categories, to coalgebras of the lifted
comonad `liftedComonad law` on `T.Algebra`.
-/
def lambdaBialgebraEquivLiftedComonadCoalgebra :
    LambdaBialgebra law ≌
    (liftedComonad law).Coalgebra where
  functor :=
    lambdaBialgebraToLiftedComonadCoalgebra law
  inverse :=
    liftedComonadCoalgebraToLambdaBialgebra law
  unitIso := NatIso.ofComponents
    (unitIsoComponent law)
    (fun {X Y} f => by
      apply LambdaBialgebra.Hom.ext
      change f.hom ≫ 𝟙 Y.carrier =
        𝟙 X.carrier ≫ f.hom
      exact (Category.comp_id f.hom).trans
        (Category.id_comp f.hom).symm)
  counitIso := NatIso.ofComponents
    (counitIsoComponent law)
    (fun {X Y} f => by
      apply Comonad.Coalgebra.Hom.ext
      apply Monad.Algebra.Hom.ext
      change f.f.f ≫ 𝟙 Y.A.A =
        𝟙 X.A.A ≫ f.f.f
      exact (Category.comp_id f.f.f).trans
        (Category.id_comp f.f.f).symm)
  functor_unitIso_comp _ := by
    apply Comonad.Coalgebra.Hom.ext
    apply Monad.Algebra.Hom.ext
    exact Category.id_comp _

end Equivalences

end GebLean
