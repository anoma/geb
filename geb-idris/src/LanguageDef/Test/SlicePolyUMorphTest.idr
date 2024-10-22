module LanguageDef.Test.SlicePolyUMorphTest

import Test.TestLibrary
import LanguageDef.SlicePolyUMorph

%default total

-----------------------
-----------------------
---- Catamorphisms ----
-----------------------
-----------------------

TNatF : SPFData Unit Unit
TNatF =
  SPFD
    (\_ => Either Unit Unit)
    (\_, ep, _ => eitherElim (\_ => Void) (\_ => Unit) ep)

TNat : Type
TNat = SPFDmu {x=Unit} TNatF ()

alg123 :
  SliceMorphism {a=Unit}
    (InterpSPFData TNatF (InterpSPFData TNatF (const Nat)))
    (const Nat)
alg123 () (Left () ** dm) = 1 -- n = 0
alg123 () (Right () ** dm) = case dm () () of
  (Left () ** dm') => 2 -- n = 1
  (Right () ** dm') => 3 + dm' () () -- n > 1

test123 : TNat -> Nat
test123 = spfdCataComp {x=Unit} {spfd=TNatF} {a=(const Nat)} alg123 ()

test123_0 :
  test123 (InSPFm () (Left () ** \_ => IdrisUtils.voidF _)) = 1
test123_0 = Refl

test123_1 :
  test123
    (InSPFm () (Right () ** \(), () =>
      InSPFm () (Left () ** \_ => IdrisUtils.voidF _))) = 2
test123_1 = Refl

test123_2 :
  test123
    (InSPFm () (Right () ** \(), () =>
      InSPFm () (Right () ** \(), () =>
        InSPFm () (Left () ** \_ => IdrisUtils.voidF _)))) = 4
test123_2 = Refl

test123_3 :
  test123
    (InSPFm () (Right () ** \(), () =>
      InSPFm () (Right () ** \(), () =>
        InSPFm () (Right () ** \(), () =>
          InSPFm () (Left () ** \_ => IdrisUtils.voidF _))))) = 5
test123_3 = Refl

test123_4 :
  test123
    (InSPFm () (Right () ** \(), () =>
      InSPFm () (Right () ** \(), () =>
        InSPFm () (Right () ** \(), () =>
          InSPFm () (Right () ** \(), () =>
            InSPFm () (Left () ** \_ => IdrisUtils.voidF _)))))) = 7
test123_4 = Refl

test123_5 :
  test123
    (InSPFm () (Right () ** \(), () =>
      InSPFm () (Right () ** \(), () =>
        InSPFm () (Right () ** \(), () =>
          InSPFm () (Right () ** \(), () =>
            InSPFm () (Right () ** \(), () =>
              InSPFm () (Left () ** \_ => IdrisUtils.voidF _))))))) = 8
test123_5 = Refl

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
slicePolyUMorphTest : IO ()
slicePolyUMorphTest = do
  putStrLn ""
  putStrLn "=========================="
  putStrLn "Begin SlicePolyUMorphTest:"
  putStrLn "--------------------------"
  putStrLn ""
  putStrLn "------------------------"
  putStrLn "End SlicePolyUMorphTest."
  putStrLn "========================"
  pure ()
