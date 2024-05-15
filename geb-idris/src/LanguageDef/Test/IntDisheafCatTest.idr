module LanguageDef.Test.IntDisheafCatTest

import Test.TestLibrary
import LanguageDef.IntDisheafCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
intDisheafCatTest : IO ()
intDisheafCatTest = do
  putStrLn ""
  putStrLn "========================"
  putStrLn "Begin IntDisheafCatTest:"
  putStrLn "------------------------"
  putStrLn ""
  putStrLn "----------------------"
  putStrLn "End IntDisheafCatTest."
  putStrLn "======================"
  pure ()
