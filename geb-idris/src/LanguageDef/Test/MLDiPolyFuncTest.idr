module LanguageDef.Test.MLDiPolyFuncTest

import Test.TestLibrary
import LanguageDef.MLDiPolyFunc

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
mlDiPolyFuncTest : IO ()
mlDiPolyFuncTest = do
  putStrLn ""
  putStrLn "======================="
  putStrLn "Begin MLDiPolyFuncTest:"
  putStrLn "-----------------------"
  putStrLn ""
  putStrLn "---------------------"
  putStrLn "End MLDiPolyFuncTest."
  putStrLn "====================="
  pure ()
