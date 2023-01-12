module LanguageDef.Test.ProgFinSetTest

import Test.TestLibrary
import LanguageDef.ProgFinSet

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
progFinSetTest : IO ()
progFinSetTest = do
  putStrLn ""
  putStrLn "====================="
  putStrLn "Begin ProgFinSetTest:"
  putStrLn "---------------------"
  putStrLn ""
  putStrLn "-------------------"
  putStrLn "End ProgFinSetTest."
  putStrLn "==================="
  pure ()
