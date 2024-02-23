module LanguageDef.Test.MLQuivPolyTest

import Test.TestLibrary
import LanguageDef.MLQuivPoly

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
mlQuivPolyTest : IO ()
mlQuivPolyTest = do
  putStrLn ""
  putStrLn "====================="
  putStrLn "Begin MLQuivPolyTest:"
  putStrLn "---------------------"
  putStrLn ""
  putStrLn "-------------------"
  putStrLn "End MLQuivPolyTest."
  putStrLn "==================="
  pure ()
