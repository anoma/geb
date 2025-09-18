module LanguageDef.Test.SlicePolyDifuncTest

import Test.TestLibrary
import LanguageDef.SlicePolyDifunc
import LanguageDef.DislicePolyCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
slicePolyDifuncTest : IO ()
slicePolyDifuncTest = do
  putStrLn ""
  putStrLn "==========================="
  putStrLn "Begin SlicePolyDifuncTest:"
  putStrLn "--------------------------"
  putStrLn ""
  putStrLn "------------------------"
  putStrLn "End SlicePolyDifuncTest."
  putStrLn "========================="
  pure ()
