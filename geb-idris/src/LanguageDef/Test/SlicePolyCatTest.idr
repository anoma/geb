module LanguageDef.Test.SlicePolyCatTest

import Test.TestLibrary
import LanguageDef.SlicePolyCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
slicePolyCatTest : IO ()
slicePolyCatTest = do
  putStrLn ""
  putStrLn "======================="
  putStrLn "Begin SlicePolyCatTest:"
  putStrLn "-----------------------"
  putStrLn ""
  putStrLn "---------------------"
  putStrLn "End SlicePolyCatTest."
  putStrLn "====================="
  pure ()
