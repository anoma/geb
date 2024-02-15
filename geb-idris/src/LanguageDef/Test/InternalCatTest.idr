module LanguageDef.Test.InternalCatTest

import Test.TestLibrary
import LanguageDef.InternalCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
internalCatTest : IO ()
internalCatTest = do
  putStrLn ""
  putStrLn "======================"
  putStrLn "Begin InternalCatTest:"
  putStrLn "----------------------"
  putStrLn ""
  putStrLn "--------------------"
  putStrLn "End InternalCatTest."
  putStrLn "===================="
  pure ()
