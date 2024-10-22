module LanguageDef.Test.FinPolyTest

import Test.TestLibrary
import LanguageDef.FinPoly
import LanguageDef.Test.PolyIndTypesTest

%default total

-------------------------------------------
-------------------------------------------
---- Lawvere/profunctor representation ----
-------------------------------------------
-------------------------------------------

T0StarterExp : List Nat
T0StarterExp = []

T0Starter : RawOp 0 0
T0Starter = rawOpFromList T0StarterExp

T0MakerExp : List Nat
T0MakerExp = [0, 0]

T0Maker : RawOp 1 2
T0Maker = rawOpFromList T0MakerExp

T0DepMakerExp : List Nat
T0DepMakerExp = [0, 1, 1]

T0DepMaker : RawOp 2 3
T0DepMaker = rawOpFromList T0DepMakerExp

T1StarterExp : List Nat
T1StarterExp = []

T1Starter : RawOp 0 0
T1Starter = rawOpFromList T1StarterExp

T1IdExp : List Nat
T1IdExp = [0]

T1Id : RawOp 1 1
T1Id = rawOpFromList T1IdExp

T1MakerExp : List Nat
T1MakerExp = [0, 0, 1, 1]

T1Maker : RawOp 2 4
T1Maker = rawOpFromList T1MakerExp

T1Maker1dom : SortInterpretation 2
T1Maker1dom = [PolyIndTypesTest.Test0, Sigma PolyIndTypesTest.Test1]

T1Maker1t1 : InterpRawOpProd T1Maker T1Maker1dom
T1Maker1t1 =
  [T0Starter (),
   T0Maker $ T0Mk (T0Starter ()) (T0Starter ()),
   (T0Starter () ** T1Starter () T1Start),
   (T0Maker $ T0Mk (T0Starter ()) (T0Starter ()) **
    T1Id (T0Maker $ T0Mk (T0Starter ()) (T0Starter ())) ())]

T1ComposerExp : List Nat
T1ComposerExp = [0, 0, 0, 1, 1]

T1Composer : RawOp 2 5
T1Composer = rawOpFromList T1ComposerExp

T1DistribExp : List Nat
T1DistribExp = [0, 0, 0, 1]

T1Distrib : RawOp 2 4
T1Distrib = rawOpFromList T1DistribExp

T1DepComposerExp : List Nat
T1DepComposerExp = [0, 1, 1, 1, 1, 1]

T1DepComposer : RawOp 2 6
T1DepComposer = rawOpFromList T1DepComposerExp

T1TelescopeExp : List Nat
T1TelescopeExp = [0, 1, 1, 1, 1, 1, 1]

T1Telescope : RawOp 2 7
T1Telescope = rawOpFromList T1TelescopeExp

T1SortOpListExp : List (List Nat)
T1SortOpListExp =
  [ T1StarterExp
  , T1IdExp
  , T1MakerExp
  , T1ComposerExp
  , T1DistribExp
  , T1DepComposerExp
  , T1TelescopeExp
  ]

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
finPolyTest : IO ()
finPolyTest = do
  putStrLn ""
  putStrLn "=================="
  putStrLn "Begin FinPolyTest:"
  putStrLn "------------------"
  putStrLn ""
  putStrLn "----------------"
  putStrLn "End FinPolyTest."
  putStrLn "================"
  pure ()
