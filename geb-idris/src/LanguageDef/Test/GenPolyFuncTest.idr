module LanguageDef.Test.GenPolyFuncTest

import Test.TestLibrary
import LanguageDef.Test.ProgFinSetTest
import LanguageDef.GenPolyFunc

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
genPolyFuncTest : IO ()
genPolyFuncTest = do
  putStrLn ""
  putStrLn "======================"
  putStrLn "Begin GenPolyFuncTest:"
  putStrLn "----------------------"
  putStrLn ""
  putStrLn "--------------------"
  putStrLn "End GenPolyFuncTest."
  putStrLn "===================="
  pure ()
