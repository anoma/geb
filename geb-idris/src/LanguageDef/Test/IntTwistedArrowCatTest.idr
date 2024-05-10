module LanguageDef.Test.IntTwistedArrowCatTest

import Test.TestLibrary
import LanguageDef.IntTwistedArrowCat

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
intTwistedArrowCatTest : IO ()
intTwistedArrowCatTest = do
  putStrLn ""
  putStrLn "============================="
  putStrLn "Begin IntTwistedArrowCatTest:"
  putStrLn "-----------------------------"
  putStrLn ""
  putStrLn "---------------------------"
  putStrLn "End IntTwistedArrowCatTest."
  putStrLn "==========================="
  pure ()
