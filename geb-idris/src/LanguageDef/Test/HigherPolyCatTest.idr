module LanguageDef.Test.HigherPolyCatTest

import Test.TestLibrary
import LanguageDef.HigherPolyCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
higherPolyCatTest : IO ()
higherPolyCatTest = do
  putStrLn ""
  putStrLn "========================"
  putStrLn "Begin HigherPolyCatTest:"
  putStrLn "------------------------"
  putStrLn ""
  putStrLn "----------------------"
  putStrLn "End HigherPolyCatTest."
  putStrLn "======================"
  pure ()
