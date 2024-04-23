module LanguageDef.Test.IntBundleCatTest

import Test.TestLibrary
import LanguageDef.IntBundleCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
intBundleCatTest : IO ()
intBundleCatTest = do
  putStrLn ""
  putStrLn "======================="
  putStrLn "Begin IntBundleCatTest:"
  putStrLn "-----------------------"
  putStrLn ""
  putStrLn "---------------------"
  putStrLn "End IntBundleCatTest."
  putStrLn "====================="
  pure ()
