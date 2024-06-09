module LanguageDef.Test.HelixCatTest

import Test.TestLibrary
import LanguageDef.HelixCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
helixCatTest : IO ()
helixCatTest = do
  putStrLn ""
  putStrLn "==================="
  putStrLn "Begin HelixCatTest:"
  putStrLn "-------------------"
  putStrLn ""
  putStrLn "-----------------"
  putStrLn "End HelixCatTest."
  putStrLn "================="
  pure ()
