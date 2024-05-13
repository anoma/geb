module LanguageDef.Test.QTypeTest

import Test.TestLibrary
import LanguageDef.QType

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
qtypeTest : IO ()
qtypeTest = do
  putStrLn ""
  putStrLn "================"
  putStrLn "Begin QTypeTest:"
  putStrLn "----------------"
  putStrLn ""
  putStrLn "--------------"
  putStrLn "End QTypeTest."
  putStrLn "=============="
  pure ()
