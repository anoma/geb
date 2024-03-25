module LanguageDef.Test.PolyDifuncTest

import Test.TestLibrary
import LanguageDef.PolyDifunc

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
polyDifuncTest : IO ()
polyDifuncTest = do
  putStrLn ""
  putStrLn "======================"
  putStrLn "Begin PolyDifuncTest:"
  putStrLn "----------------------"
  putStrLn ""
  putStrLn "--------------------"
  putStrLn "End PolyDifuncTest."
  putStrLn "===================="
  pure ()
