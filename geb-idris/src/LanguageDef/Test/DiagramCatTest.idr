module LanguageDef.Test.DiagramCatTest

import Test.TestLibrary
import LanguageDef.Test.ProgFinSetTest
import LanguageDef.DiagramCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
diagramCatTest : IO ()
diagramCatTest = do
  putStrLn ""
  putStrLn "====================="
  putStrLn "Begin DiagramCatTest:"
  putStrLn "---------------------"
  putStrLn ""
  putStrLn "--------------------"
  putStrLn "End DiagramCatTest."
  putStrLn "===================="
  pure ()
