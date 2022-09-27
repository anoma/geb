module LanguageDef.Test.ADTCatTest

import Test.TestLibrary
import LanguageDef.ADTCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
adtCatTest : IO ()
adtCatTest = do
  putStrLn ""
  putStrLn "================="
  putStrLn "Begin ADTCatTest:"
  putStrLn "-----------------"
  putStrLn ""
  putStrLn "---------------"
  putStrLn "End ADTCatTest."
  putStrLn "==============="
  pure ()
