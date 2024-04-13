module LanguageDef.Test.IntBundleTest

import Test.TestLibrary
import LanguageDef.IntBundle

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
intBundleTest : IO ()
intBundleTest = do
  putStrLn ""
  putStrLn "===================="
  putStrLn "Begin IntBundleTest:"
  putStrLn "--------------------"
  putStrLn ""
  putStrLn "------------------"
  putStrLn "End IntBundleTest."
  putStrLn "=================="
  pure ()
