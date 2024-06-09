module LanguageDef.Test.RopeCatTest

import Test.TestLibrary
import LanguageDef.RopeCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
ropeCatTest : IO ()
ropeCatTest = do
  putStrLn ""
  putStrLn "=================="
  putStrLn "Begin RopeCatTest:"
  putStrLn "------------------"
  putStrLn ""
  putStrLn "----------------"
  putStrLn "End RopeCatTest."
  putStrLn "================"
  pure ()
