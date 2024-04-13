module LanguageDef.Test.IntFamCatTest

import Test.TestLibrary
import LanguageDef.IntFamCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
intFamCatTest : IO ()
intFamCatTest = do
  putStrLn ""
  putStrLn "===================="
  putStrLn "Begin IntFamCatTest:"
  putStrLn "--------------------"
  putStrLn ""
  putStrLn "------------------"
  putStrLn "End IntFamCatTest."
  putStrLn "=================="
  pure ()
