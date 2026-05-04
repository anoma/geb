import GebLean

namespace GebLean.Test.LayeredEquivalence

open CategoryTheory
open Layer1

section Layer1Tests

def exampleDepData : DepData where
  objT := Nat
  morT := fun n m => Fin (n + m)

def exampleCopresheaf : CopresheafData :=
  depToCopresheafData exampleDepData

def roundTrip1 : DepData :=
  copresheafDataToDep exampleCopresheaf

def anotherDepData : DepData where
  objT := Bool
  morT := fun _ _ => Unit

end Layer1Tests

section FunctorTests

def testDepData : DepData where
  objT := Fin 3
  morT := fun _ _ => Bool

def testCopresheaf : CopresheafData :=
  depToCopresheafData testDepData

def testFunctor : Obj ⥤ Type :=
  mkCopresheaf testCopresheaf

end FunctorTests

section EquivalenceTests

def smallDepData : DepData where
  objT := Bool
  morT := fun _ _ => Unit

def smallCopresheaf : CopresheafData :=
  depToCopresheafData smallDepData

def backToDepData : DepData :=
  copresheafDataToDep smallCopresheaf

def myDepData : DepData where
  objT := Fin 5
  morT := fun _ _ => Bool

def myCopresheaf : CopresheafData :=
  depToCopresheafData myDepData

end EquivalenceTests

end GebLean.Test.LayeredEquivalence
