module LanguageDef.Test.IntUFamCatTest

import Test.TestLibrary
import LanguageDef.IntUFamCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
intUFamCatTest : IO ()
intUFamCatTest = do
  putStrLn ""
  putStrLn "====================="
  putStrLn "Begin IntUFamCatTest:"
  putStrLn "---------------------"
  putStrLn ""
  putStrLn "-------------------"
  putStrLn "End IntUFamCatTest."
  putStrLn "==================="
  pure ()
