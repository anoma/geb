module LanguageDef.Test.DiPolyFuncTest

import Test.TestLibrary
import LanguageDef.DiPolyFunc

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
diPolyFuncTest : IO ()
diPolyFuncTest = do
  putStrLn ""
  putStrLn "====================="
  putStrLn "Begin DiPolyFuncTest:"
  putStrLn "---------------------"
  putStrLn ""
  putStrLn "-------------------"
  putStrLn "End DiPolyFuncTest."
  putStrLn "==================="
  pure ()
