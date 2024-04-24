module LanguageDef.Test.IntFactCatFuncTest

import Test.TestLibrary
import LanguageDef.IntFactCatFunc

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
intFactCatFuncTest : IO ()
intFactCatFuncTest = do
  putStrLn ""
  putStrLn "========================="
  putStrLn "Begin IntFactCatFuncTest:"
  putStrLn "-------------------------"
  putStrLn ""
  putStrLn "-----------------------"
  putStrLn "End IntFactCatFuncTest."
  putStrLn "======================="
  pure ()
