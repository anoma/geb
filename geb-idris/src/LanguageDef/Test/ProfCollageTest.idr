module LanguageDef.Test.ProfCollageTest

import Test.TestLibrary
import LanguageDef.ProfCollage

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
profCollageTest : IO ()
profCollageTest = do
  putStrLn ""
  putStrLn "======================"
  putStrLn "Begin ProfCollageTest:"
  putStrLn "----------------------"
  putStrLn ""
  putStrLn "--------------------"
  putStrLn "End ProfCollageTest."
  putStrLn "===================="
  pure ()
