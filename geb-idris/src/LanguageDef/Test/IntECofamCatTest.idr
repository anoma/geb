module LanguageDef.Test.IntECofamCatTest

import Test.TestLibrary
import LanguageDef.IntECofamCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
intECofamCatTest : IO ()
intECofamCatTest = do
  putStrLn ""
  putStrLn "======================="
  putStrLn "Begin IntECofamCatTest:"
  putStrLn "-----------------------"
  putStrLn ""
  putStrLn "---------------------"
  putStrLn "End IntECofamCatTest."
  putStrLn "====================="
  pure ()
