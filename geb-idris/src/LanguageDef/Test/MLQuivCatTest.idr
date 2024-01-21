module LanguageDef.Test.MLQuivCatTest

import Test.TestLibrary
import LanguageDef.MLQuivCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
mlQuivCatTest : IO ()
mlQuivCatTest = do
  putStrLn ""
  putStrLn "===================="
  putStrLn "Begin MLQuivCatTest:"
  putStrLn "--------------------"
  putStrLn ""
  putStrLn "------------------"
  putStrLn "End MLQuivCatTest."
  putStrLn "=================="
  pure ()
