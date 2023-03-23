module LanguageDef.Test.AdjunctionsTest

import Test.TestLibrary
import LanguageDef.Test.ProgFinSetTest
import LanguageDef.Adjunctions

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
adjunctionsTest : IO ()
adjunctionsTest = do
  putStrLn ""
  putStrLn "======================"
  putStrLn "Begin AdjunctionsTest:"
  putStrLn "----------------------"
  putStrLn ""
  putStrLn "--------------------"
  putStrLn "End AdjunctionsTest."
  putStrLn "===================="
  pure ()
