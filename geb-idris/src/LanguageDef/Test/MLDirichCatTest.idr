module LanguageDef.Test.MLDirichCatTest

import Test.TestLibrary
import LanguageDef.MLDirichCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
mlDirichCatTest : IO ()
mlDirichCatTest = do
  putStrLn ""
  putStrLn "======================"
  putStrLn "Begin MLDirichCatTest:"
  putStrLn "----------------------"
  putStrLn ""
  putStrLn "--------------------"
  putStrLn "End MLDirichCatTest."
  putStrLn "===================="
  pure ()
