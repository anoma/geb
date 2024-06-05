module LanguageDef.Test.SlicePolyDialgTest

import Test.TestLibrary
import LanguageDef.SlicePolyDialg

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
slicePolyDialgTest : IO ()
slicePolyDialgTest = do
  putStrLn ""
  putStrLn "========================="
  putStrLn "Begin SlicePolyDialgTest:"
  putStrLn "-------------------------"
  putStrLn ""
  putStrLn "-----------------------"
  putStrLn "End SlicePolyDialgTest."
  putStrLn "======================="
  pure ()
