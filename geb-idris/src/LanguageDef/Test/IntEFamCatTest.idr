module LanguageDef.Test.IntEFamCatTest

import Test.TestLibrary
import LanguageDef.IntEFamCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
intEFamCatTest : IO ()
intEFamCatTest = do
  putStrLn ""
  putStrLn "====================="
  putStrLn "Begin IntEFamCatTest:"
  putStrLn "---------------------"
  putStrLn ""
  putStrLn "-------------------"
  putStrLn "End IntEFamCatTest."
  putStrLn "==================="
  pure ()
