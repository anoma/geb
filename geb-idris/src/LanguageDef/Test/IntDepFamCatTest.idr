module LanguageDef.Test.IntDepFamCatTest

import Test.TestLibrary
import LanguageDef.IntDepFamCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
intDepFamCatTest : IO ()
intDepFamCatTest = do
  putStrLn ""
  putStrLn "======================="
  putStrLn "Begin IntDepFamCatTest:"
  putStrLn "-----------------------"
  putStrLn ""
  putStrLn "---------------------"
  putStrLn "End IntDepFamCatTest."
  putStrLn "====================="
  pure ()
