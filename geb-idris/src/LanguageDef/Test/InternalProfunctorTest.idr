module LanguageDef.Test.InternalProfunctorTest

import Test.TestLibrary
import LanguageDef.InternalProfunctor

%default total

----------------------------------
----------------------------------
----- Exported test function -----
----------------------------------
----------------------------------

export
internalProfunctorTest : IO ()
internalProfunctorTest = do
  putStrLn ""
  putStrLn "============================="
  putStrLn "Begin InternalProfunctorTest:"
  putStrLn "-----------------------------"
  putStrLn ""
  putStrLn "---------------------------"
  putStrLn "End InternalProfunctorTest."
  putStrLn "==========================="
  pure ()
