module LanguageDef.Test.FinCatTest

import Test.TestLibrary
import LanguageDef.FinCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
finCatTest : IO ()
finCatTest = do
  putStrLn ""
  putStrLn "================="
  putStrLn "Begin FinCatTest:"
  putStrLn "-----------------"
  putStrLn ""
  putStrLn "---------------"
  putStrLn "End FinCatTest."
  putStrLn "==============="
  pure ()
