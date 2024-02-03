module LanguageDef.Test.DisliceCatTest

import Test.TestLibrary
import LanguageDef.DisliceCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
disliceCatTest : IO ()
disliceCatTest = do
  putStrLn ""
  putStrLn "====================="
  putStrLn "Begin DisliceCatTest:"
  putStrLn "---------------------"
  putStrLn ""
  putStrLn "-------------------"
  putStrLn "End DisliceCatTest."
  putStrLn "==================="
  pure ()
