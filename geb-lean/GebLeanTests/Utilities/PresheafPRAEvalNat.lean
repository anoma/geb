import GebLean

namespace GebLeanTests.Utilities.PresheafPRAEvalNat

open GebLean
open CategoryTheory

/-! ## Type-signature sanity -/

example : Cat.{0, 0}ᵒᵖ ⥤ Cat.{0, 0} → Cat.{0, 0}ᵒᵖ ⥤ Cat.{0, 0} →
    Type _ := fun G F => LaxNatTransContraData G F

example : Cat.{0, 0}ᵒᵖ ⥤ Cat.{_, _} :=
  praPolyEvalSourceOverI.{0, 0, 0, 0, 0, 0}

example : Cat.{0, 0}ᵒᵖ ⥤ Cat.{_, _} :=
  praPolyEvalTargetOverI.{0, 0, 0, 0, 0, 0}

example :
    LaxNatTransContraData
      praPolyEvalSourceOverI.{0, 0, 0, 0, 0, 0}
      praPolyEvalTargetOverI.{0, 0, 0, 0, 0, 0} :=
  praPolyEvalLaxNatTrans.{0, 0, 0, 0, 0, 0}

/-! ## LaxNatTransContraData framework sanity -/

example (G : Cat.{0, 0}ᵒᵖ ⥤ Cat.{0, 0}) :
    LaxNatTransContraData G G :=
  LaxNatTransContraData.id G

example (G : Cat.{0, 0}ᵒᵖ ⥤ Cat.{0, 0}) :
    LaxNatTransContraData G G :=
  (LaxNatTransContraData.id G).comp (LaxNatTransContraData.id G)

example (G : Cat.{0, 0}ᵒᵖ ⥤ Cat.{0, 0}) :
    LaxNatTransContraData G G :=
  LaxNatTransContraData.ofNatTrans (𝟙 G)

/-! ## Bridge collapse -/

example (I : Cat.{0, 0}) :
    praPolyEvalLaxNatTrans.{0, 0, 0, 0, 0, 0}.app I =
    praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0} I :=
  praPolyEvalAtIFunctor_eq_praPolyEvalLaxNatTrans_app I

section WeakBridge
variable (I : Cat.{0, 0}) (J : Cat.{0, 0})
  (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} I J)
  (Z : ↑(presheafCat.{0, 0, 0} I))

example : ((praEvalAtFunctor.{0, 0, 0, 0, 0, 0} I J).obj P).obj Z =
    (ULift.down.{1, 1}
      (ULiftHom.objDown.{1, 1}
        (GrothendieckContraFunctor.objFiber
          ((praPolyEvalLaxNatTrans.{0, 0, 0, 0, 0, 0}.app I).obj
            (praPolyEvalAtISourceObj.{0, 0, 0, 0, 0, 0}
              I J P Z)))) :
      Jᵒᵖ ⥤ Type 0) :=
  praEvalAtFunctor_via_praPolyEvalLaxNatTrans I J P Z

end WeakBridge

end GebLeanTests.Utilities.PresheafPRAEvalNat
