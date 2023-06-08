module LanguageDef.Test.GebTest

import Test.TestLibrary
import LanguageDef.Geb

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
gebTest : IO ()
gebTest = do
  putStrLn ""
  putStrLn "=============="
  putStrLn "Begin GebTest:"
  putStrLn "--------------"
  putStrLn ""
  putStrLn "------------"
  putStrLn "End GebTest."
  putStrLn "============"
  pure ()
