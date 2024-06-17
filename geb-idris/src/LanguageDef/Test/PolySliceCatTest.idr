module LanguageDef.Test.PolySliceCatTest

import Test.TestLibrary
import LanguageDef.PolySliceCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
polySliceCatTest : IO ()
polySliceCatTest = do
  putStrLn ""
  putStrLn "======================="
  putStrLn "Begin PolySliceCatTest:"
  putStrLn "-----------------------"
  putStrLn ""
  putStrLn "---------------------"
  putStrLn "End PolySliceCatTest."
  putStrLn "====================="
  pure ()
