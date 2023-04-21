module LanguageDef.Test.TheoriesTest

import Test.TestLibrary
import LanguageDef.Theories

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
theoriesTest : IO ()
theoriesTest = do
  putStrLn ""
  putStrLn "==================="
  putStrLn "Begin TheoriesTest:"
  putStrLn "-------------------"
  putStrLn ""
  putStrLn "-----------------"
  putStrLn "End TheoriesTest."
  putStrLn "================="
  pure ()
