module LanguageDef.Test.SliceFuncCatTest

import Test.TestLibrary
import LanguageDef.SliceFuncCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
sliceFuncCatTest : IO ()
sliceFuncCatTest = do
  putStrLn ""
  putStrLn "======================="
  putStrLn "Begin SliceFuncCatTest:"
  putStrLn "-----------------------"
  putStrLn ""
  putStrLn "---------------------"
  putStrLn "End SliceFuncCatTest."
  putStrLn "====================="
  pure ()
