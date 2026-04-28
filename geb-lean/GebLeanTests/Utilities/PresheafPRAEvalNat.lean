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

end GebLeanTests.Utilities.PresheafPRAEvalNat
