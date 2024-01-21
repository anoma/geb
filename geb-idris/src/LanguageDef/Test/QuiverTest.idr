module LanguageDef.Test.QuiverTest

import Test.TestLibrary
import LanguageDef.Quiver

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
quiverTest : IO ()
quiverTest = do
  putStrLn ""
  putStrLn "================="
  putStrLn "Begin QuiverTest:"
  putStrLn "-----------------"
  putStrLn ""
  putStrLn "---------------"
  putStrLn "End QuiverTest."
  putStrLn "==============="
  pure ()
