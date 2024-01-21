module LanguageDef.Test.MLQuivUnivTest

import Test.TestLibrary
import LanguageDef.MLQuivUniv

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
mlQuivUnivTest : IO ()
mlQuivUnivTest = do
  putStrLn ""
  putStrLn "====================="
  putStrLn "Begin MLQuivUnivTest:"
  putStrLn "---------------------"
  putStrLn ""
  putStrLn "-------------------"
  putStrLn "End MLQuivUnivTest."
  putStrLn "==================="
  pure ()
