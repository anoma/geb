module LanguageDef.Test.PolyIndTypesTest

import Test.TestLibrary
import LanguageDef.PolyIndTypes

%default total

--------------------------------------------
--------------------------------------------
---- Finitary inductive-inductive types ----
--------------------------------------------
--------------------------------------------

-- See `Test0` and `Test` from "Dependent-pair induction" in `DiagramCatTest`.

t0Starter : FinIndIndF1Constr
t0Starter = FII1c 0 0 []

t0Maker : FinIndIndF1Constr
t0Maker = FII1c 2 0 []

t0DepMaker : FinIndIndF1Constr
t0DepMaker = FII1c 1 2 [ FZ, FZ ]

T0F : FinIndIndF1
T0F = FII1 [ t0Starter, t0Maker, t0DepMaker ]

t1Starter : FinIndIndF2Constr T0F
t1Starter = FII2c 0 0 FF2AZ

T1F : FinIndIndF2 T0F
T1F = FII2 [ t1Starter ]

T01F : FinIndInd
T01F = (T0F ** T1F)

T0 : Type
T0 = FinIndIndMu1 T01F

T1 : T0 -> Type
T1 = FinIndIndMu2 T01F

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
polyIndTypesTest : IO ()
polyIndTypesTest = do
  putStrLn ""
  putStrLn "======================="
  putStrLn "Begin PolyIndTypesTest:"
  putStrLn "-----------------------"
  putStrLn ""
  putStrLn "---------------------"
  putStrLn "End PolyIndTypesTest."
  putStrLn "====================="
  pure ()
