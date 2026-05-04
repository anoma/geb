module LanguageDef.Test.SlPolyIntCatTest

import Test.TestLibrary
import LanguageDef.SlPolyIntCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
slPolyIntCatTest : IO ()
slPolyIntCatTest = do
  putStrLn ""
  putStrLn "======================="
  putStrLn "Begin SlPolyIntCatTest:"
  putStrLn "-----------------------"
  putStrLn ""
  putStrLn "---------------------"
  putStrLn "End SlPolyIntCatTest."
  putStrLn "====================="
  pure ()
