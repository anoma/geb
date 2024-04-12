module LanguageDef.Test.BundleCatTest

import Test.TestLibrary
import LanguageDef.BundleCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
bundleCatTest : IO ()
bundleCatTest = do
  putStrLn ""
  putStrLn "===================="
  putStrLn "Begin BundleCatTest:"
  putStrLn "--------------------"
  putStrLn ""
  putStrLn "------------------"
  putStrLn "End BundleCatTest."
  putStrLn "=================="
  pure ()
