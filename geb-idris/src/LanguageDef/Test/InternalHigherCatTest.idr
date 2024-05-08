module LanguageDef.Test.InternalHigherCatTest

import Test.TestLibrary
import LanguageDef.InternalHigherCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
internalHigherCatTest : IO ()
internalHigherCatTest = do
  putStrLn ""
  putStrLn "============================"
  putStrLn "Begin InternalHigherCatTest:"
  putStrLn "----------------------------"
  putStrLn ""
  putStrLn "--------------------------"
  putStrLn "End InternalHigherCatTest."
  putStrLn "=========================="
  pure ()
