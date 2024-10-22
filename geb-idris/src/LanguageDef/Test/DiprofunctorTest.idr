module LanguageDef.Test.DiprofunctorTest

import Test.TestLibrary
import LanguageDef.Diprofunctor

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
diprofunctorTest : IO ()
diprofunctorTest = do
  putStrLn ""
  putStrLn "======================="
  putStrLn "Begin DiprofunctorTest:"
  putStrLn "-----------------------"
  putStrLn ""
  putStrLn "---------------------"
  putStrLn "End DiprofunctorTest."
  putStrLn "====================="
  pure ()
