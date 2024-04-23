module LanguageDef.Test.MLBundleCatTest

import Test.TestLibrary
import LanguageDef.MLBundleCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
mlBundleCatTest : IO ()
mlBundleCatTest = do
  putStrLn ""
  putStrLn "======================"
  putStrLn "Begin MLBundleCatTest:"
  putStrLn "----------------------"
  putStrLn ""
  putStrLn "--------------------"
  putStrLn "End MLBundleCatTest."
  putStrLn "===================="
  pure ()
