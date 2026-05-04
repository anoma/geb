module LanguageDef.Test.SpanCospanTest

import Test.TestLibrary
import LanguageDef.SpanCospan

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
spanCospanTest : IO ()
spanCospanTest = do
  putStrLn ""
  putStrLn "====================="
  putStrLn "Begin SpanCospanTest:"
  putStrLn "---------------------"
  putStrLn ""
  putStrLn "-------------------"
  putStrLn "End SpanCospanTest."
  putStrLn "==================="
  pure ()
