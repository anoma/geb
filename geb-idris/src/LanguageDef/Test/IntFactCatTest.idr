module LanguageDef.Test.IntFactCatTest

import Test.TestLibrary
import LanguageDef.IntFactCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
intFactCatTest : IO ()
intFactCatTest = do
  putStrLn ""
  putStrLn "====================="
  putStrLn "Begin IntFactCatTest:"
  putStrLn "---------------------"
  putStrLn ""
  putStrLn "-------------------"
  putStrLn "End IntFactCatTest."
  putStrLn "==================="
  pure ()
