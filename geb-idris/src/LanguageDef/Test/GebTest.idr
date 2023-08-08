module LanguageDef.Test.GebTest

import Test.TestLibrary
import LanguageDef.Geb

%default total

--------------------
--------------------
---- FinMatrixT ----
--------------------
--------------------

public export
NM1 : NatMatrix
NM1 = [ [ 10 , 3 ] , [] , [ 1, 5, 9 ] ]

public export
TFM1 : Type
TFM1 = FinMatrixT NM1

public export
tfm1t1 : TFM1
tfm1t1 = MkFinMatrixT NM1 2 [0, 2, 7]

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
gebTest : IO ()
gebTest = do
  putStrLn ""
  putStrLn "=============="
  putStrLn "Begin GebTest:"
  putStrLn "--------------"
  putStrLn ""
  putStrLn "----------"
  putStrLn "FinMatrixT"
  putStrLn "----------"
  putStrLn ""
  putStrLn $ "NM1 = " ++ show NM1
  putStrLn $ "tfm1t1 = " ++ showFinMatrixT tfm1t1
  putStrLn ""
  putStrLn "------------"
  putStrLn "End GebTest."
  putStrLn "============"
  pure ()

export
partial
gebTestPotentiallyNonTerminating : IO ()
gebTestPotentiallyNonTerminating = pure ()
