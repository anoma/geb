module LanguageDef.Test.GebToposTest

import Test.TestLibrary
import LanguageDef.Test.ProgFinSetTest
import LanguageDef.GebTopos

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
gebToposTest : IO ()
gebToposTest = do
  putStrLn ""
  putStrLn "==================="
  putStrLn "Begin GebToposTest:"
  putStrLn "-------------------"
  putStrLn ""
  putStrLn "-----------------"
  putStrLn "End GebToposTest."
  putStrLn "================="
  pure ()
