module LanguageDef.Test.SlicePolyUMorphTest

import Test.TestLibrary
import LanguageDef.SlicePolyUMorph

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
slicePolyUMorphTest : IO ()
slicePolyUMorphTest = do
  putStrLn ""
  putStrLn "=========================="
  putStrLn "Begin SlicePolyUMorphTest:"
  putStrLn "--------------------------"
  putStrLn ""
  putStrLn "------------------------"
  putStrLn "End SlicePolyUMorphTest."
  putStrLn "========================"
  pure ()
