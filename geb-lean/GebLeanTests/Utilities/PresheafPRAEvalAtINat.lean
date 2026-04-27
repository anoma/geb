import GebLean.PresheafPRA

/-!
# Tests for (I, J, P, Z)-Naturality of praPolyEvalAtIFunctor

Type-signature sanity checks and small-example tests for
`praPolyEvalAtIFunctor` and friends in `GebLean.PresheafPRA`.
-/

open GebLean CategoryTheory

attribute [local instance] CategoryTheory.uliftCategory

/-! ## Type-signature sanity -/

example :
    praPolyEvalAtISource.{0, 0, 0, 0, 0, 0} (Cat.of PUnit) ⥤
      praPolyEvalTarget.{0, 0, 0, 0, 0, 0} :=
  praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0} (Cat.of PUnit)

example : Cat.{0, 1} :=
  praPolyEvalAtISource.{0, 0, 0, 0, 0, 0} (Cat.of PUnit)

example : Cat.{0, 1} :=
  praPolyEvalTarget.{0, 0, 0, 0, 0, 0}

example :
    praPolyEvalAtISourceFib.{0, 0, 0, 0, 0, 0} (Cat.of PUnit) =
    praPolyEvalAtISourceFib.{0, 0, 0, 0, 0, 0} (Cat.of PUnit) :=
  rfl

example :
    praEvalTargetFibre.{0, 0, 0, 0, 0, 0} =
    praEvalTargetFibre.{0, 0, 0, 0, 0, 0} :=
  rfl

example :
    praPolyEvalTarget.{0, 0, 0, 0, 0, 0} =
    praPolyEvalTarget.{0, 0, 0, 0, 0, 0} :=
  rfl

example :
    praEvalAtBifunctor.{0, 0, 0, 0, 0, 0} PUnit PUnit =
    praEvalAtBifunctor.{0, 0, 0, 0, 0, 0} PUnit PUnit :=
  rfl

/-! ## Bridge-lemma collapse at a small concrete base -/

section CollapseTest

example
    (X : praPolyEvalAtISource.{0, 0, 0, 0, 0, 0}
      (Cat.of PUnit)) :
    GrothendieckContraFunctor.objBase
      ((praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
          (Cat.of PUnit)).obj X) =
    GrothendieckContraFunctor.objBase X :=
  praPolyEvalAtIFunctor_base.{0, 0, 0, 0, 0, 0} (Cat.of PUnit) X

example
    (X : praPolyEvalAtISource.{0, 0, 0, 0, 0, 0}
      (Cat.of PUnit)) :
    GrothendieckContraFunctor.objFiber
      ((praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
          (Cat.of PUnit)).obj X) =
    ((praPolyEvalAtINatTrans.{0, 0, 0, 0, 0, 0}
          (Cat.of PUnit)).app
        (Opposite.op
          (GrothendieckContraFunctor.objBase X))).toFunctor.obj
      (GrothendieckContraFunctor.objFiber X) :=
  praPolyEvalAtIFunctor_fibre.{0, 0, 0, 0, 0, 0} (Cat.of PUnit) X

example
    {X Y : praPolyEvalAtISource.{0, 0, 0, 0, 0, 0}
      (Cat.of PUnit)}
    (f : X ⟶ Y) :
    GrothendieckContraFunctor.homFiber
      ((praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
          (Cat.of PUnit)).map f) =
    ((praPolyEvalAtINatTrans.{0, 0, 0, 0, 0, 0}
          (Cat.of PUnit)).app
        (Opposite.op
          (GrothendieckContraFunctor.objBase X))).toFunctor.map
      (GrothendieckContraFunctor.homFiber f) :=
  praPolyEvalAtIFunctor_map_homFiber.{0, 0, 0, 0, 0, 0}
    (Cat.of PUnit) f

end CollapseTest

/-! ## Pointwise-accessor compatibility -/

section AccessorCompat

example :
    praEvalAtFunctor.{0, 0, 0, 0, 0, 0} PUnit PUnit =
    praEvalAtFunctor.{0, 0, 0, 0, 0, 0} PUnit PUnit :=
  rfl

example (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} PUnit PUnit)
    (Z : PUnitᵒᵖ ⥤ Type 0) (j : PUnitᵒᵖ) :
    praEvalAt.{0, 0, 0, 0, 0, 0} PUnit PUnit P Z j =
    praEvalAt.{0, 0, 0, 0, 0, 0} PUnit PUnit P Z j :=
  rfl

example (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} PUnit PUnit)
    (Z : PUnitᵒᵖ ⥤ Type 0) {j : PUnitᵒᵖ}
    (x : praEvalAt.{0, 0, 0, 0, 0, 0} PUnit PUnit P Z j) :
    praEvalAt_index.{0, 0, 0, 0, 0, 0} PUnit PUnit P Z x =
    x.1 :=
  rfl

example (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} PUnit PUnit)
    (Z : PUnitᵒᵖ ⥤ Type 0) {j : PUnitᵒᵖ}
    (x : praEvalAt.{0, 0, 0, 0, 0, 0} PUnit PUnit P Z j) :
    praEvalAt_mor.{0, 0, 0, 0, 0, 0} PUnit PUnit P Z x =
    x.2 :=
  rfl

example (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} PUnit PUnit)
    (Z : PUnitᵒᵖ ⥤ Type 0) (j : PUnitᵒᵖ)
    (a : praPositions.{0, 0, 0, 0, 0, 0} PUnit PUnit P j)
    (η : praDirectionsAt.{0, 0, 0, 0, 0, 0}
          PUnit PUnit P j a ⟶ Z) :
    praEvalAt_mk.{0, 0, 0, 0, 0, 0} PUnit PUnit P Z j a η =
    ⟨a, η⟩ :=
  rfl

end AccessorCompat

/-! ## Functoriality -/

section FunctorialityTest

example (X : praPolyEvalAtISource.{0, 0, 0, 0, 0, 0}
    (Cat.of PUnit)) :
    (praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
        (Cat.of PUnit)).map (𝟙 X) =
      𝟙 ((praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
          (Cat.of PUnit)).obj X) :=
  (praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
    (Cat.of PUnit)).map_id X

example {X Y Z : praPolyEvalAtISource.{0, 0, 0, 0, 0, 0}
    (Cat.of PUnit)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
        (Cat.of PUnit)).map (f ≫ g) =
      (praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
          (Cat.of PUnit)).map f ≫
        (praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
          (Cat.of PUnit)).map g :=
  (praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
    (Cat.of PUnit)).map_comp f g

end FunctorialityTest

/-! ## Universe polymorphism -/

section UniversePoly

-- u_I = 1: use ULift.{1, 0} PUnit : Type 1.
example :
    praPolyEvalAtISource.{1, 0, 0, 0, 0, 0}
        (Cat.of (ULift.{1, 0} PUnit)) ⥤
      praPolyEvalTarget.{1, 0, 0, 0, 0, 0} :=
  praPolyEvalAtIFunctor.{1, 0, 0, 0, 0, 0}
    (Cat.of (ULift.{1, 0} PUnit))

-- u_J = 1: I can still be Cat.of PUnit.
example :
    praPolyEvalAtISource.{0, 0, 1, 0, 0, 0} (Cat.of PUnit) ⥤
      praPolyEvalTarget.{0, 0, 1, 0, 0, 0} :=
  praPolyEvalAtIFunctor.{0, 0, 1, 0, 0, 0} (Cat.of PUnit)

-- w_I = 1: I can still be Cat.of PUnit.
example :
    praPolyEvalAtISource.{0, 0, 0, 0, 1, 0} (Cat.of PUnit) ⥤
      praPolyEvalTarget.{0, 0, 0, 0, 1, 0} :=
  praPolyEvalAtIFunctor.{0, 0, 0, 0, 1, 0} (Cat.of PUnit)

end UniversePoly

/-! ## Bridge theorem -/

section BridgeTheorem

example
    (I : Cat.{0, 0}) (J : Cat.{0, 0})
    (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} I J)
    (Z : ↑(presheafCat.{0, 0, 0} I)) :
    ((praEvalAtFunctor.{0, 0, 0, 0, 0, 0} (↑I) (↑J)).obj P).obj Z =
    (ULift.down.{1, 1}
      (ULiftHom.objDown.{1, 1}
        (GrothendieckContraFunctor.objFiber
          ((praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0} I).obj
            (praPolyEvalAtISourceObj.{0, 0, 0, 0, 0, 0}
              I J P Z)))) :
      (↑J)ᵒᵖ ⥤ Type 0) :=
  praEvalAtFunctor_via_praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
    I J P Z

end BridgeTheorem
