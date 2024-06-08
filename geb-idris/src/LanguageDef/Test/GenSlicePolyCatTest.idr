module LanguageDef.Test.GenSlicePolyCatTest

import Test.TestLibrary
import LanguageDef.GenSlicePolyCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
genSlicePolyCatTest : IO ()
genSlicePolyCatTest = do
  putStrLn ""
  putStrLn "=========================="
  putStrLn "Begin GenSlicePolyCatTest:"
  putStrLn "--------------------------"
  putStrLn ""
  putStrLn "------------------------"
  putStrLn "End GenSlicePolyCatTest."
  putStrLn "========================"
  pure ()
