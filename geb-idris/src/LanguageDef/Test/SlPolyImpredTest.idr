module LanguageDef.Test.SlPolyImpredTest

import Test.TestLibrary
import LanguageDef.SlPolyImpred

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
slPolyImpredTest : IO ()
slPolyImpredTest = do
  putStrLn ""
  putStrLn "======================="
  putStrLn "Begin SlPolyImpredTest:"
  putStrLn "-----------------------"
  putStrLn ""
  putStrLn "---------------------"
  putStrLn "End SlPolyImpredTest."
  putStrLn "====================="
  pure ()
