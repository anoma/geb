module LanguageDef.Test.IntParamCatTest

import Test.TestLibrary
import LanguageDef.IntParamCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
intParamCatTest : IO ()
intParamCatTest = do
  putStrLn ""
  putStrLn "======================"
  putStrLn "Begin IntParamCatTest:"
  putStrLn "----------------------"
  putStrLn ""
  putStrLn "--------------------"
  putStrLn "End IntParamCatTest."
  putStrLn "===================="
  pure ()
